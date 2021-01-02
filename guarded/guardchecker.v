From MetaCoq.Guarded Require Import printers.
From MetaCoq.Checker Require Import Checker. 
From MetaCoq.Template Require Import utils BasicAst Ast AstUtils.
From MetaCoq.Template Require Import Universes Environment Reflect LiftSubst. 
From MetaCoq.Template.utils Require Import MCRTree. 

From MetaCoq.Guarded Require Import Except util Trace Inductives.

(** * Guard Checker *)

(** List of known defects:
  - The used MetaCoq reduction (from the Checker) does not handle projections.
  - constants and constant unfolding is not handled faithfully in MetaCoq. 
    The guardedness checker will be able to unfold constants even when they should be opaque. 

  - I don't currently understand the exact reasons why restrictions of subterm info flow through dependent matches is needed in some cases. I have documented what is restricted, but not why it is needed.

  - there are likely tons of bugs (e.g. dB off-by-ones) in code which I couldn't properly test due to the slow reduction.
    
  - good luck with attempting to formally verify any of this stuff :DD
*)


Open Scope exc_scope.
Unset Guard Checking.

(*Definition print {A} (a : A) : exc unit := *)
  (*ret (print a).*)

Implicit Types (Σ : global_env) (Γ : context) (ρ : pathsEnv). 


(** ** Environments for keeping track of subterm information *)

(** Environments annotated with marks on recursive arguments *)

(** proper subterm (strict) or loose subterm (may be equal to the recursive argument, i.e. not a proper subterm) *)
Inductive size := Loose | Strict. 
(* induces a lattice with Loose < Strict *)

Definition size_eqb (s1 s2 : size) := 
  match s1, s2 with 
  | Loose, Loose => true
  | Strict, Strict => true
  | _, _ => false
  end.
Instance reflect_size : ReflectEq size.
Proof. 
  refine {| eqb := size_eqb |}. 
  intros [] []; constructor; congruence. 
Defined.

(** greatest lower bound/infimum of size information *)
Definition size_glb s1 s2 := 
  match s1, s2 with 
  | Strict, Strict => Strict
  | _, _ => Loose
  end.

(** possible specifications for a term:
   - Not_subterm: when the size of a term is not related to the recursive argument of the fixpoint
   - Subterm: when the term is a subterm of the recursive argument
     the [wf_paths] argument specifies which subterms of the term are recursive 
     -- this is just the whole recursive structure of the term's type again, for nested matches 
        (possibly not the trivial recargs tree that could also be looked up in the environment: for nested inductives, this is instantiated)
   - Dead_code: when the term has been built by elimination over an empty type. Is also used for evars.
 *) 
Inductive subterm_spec := 
  | Subterm (s : size) (r : wf_paths)
  | Dead_code
  | Not_subterm. 

Definition subterm_spec_eqb (s1 s2 : subterm_spec) := 
  match s1, s2 with
  | Dead_code, Dead_code => true
  | Not_subterm, Not_subterm => true
  | Subterm size1 tree1, Subterm size2 tree2 => 
      (size1 == size2) && (tree1 == tree2)
  | _, _ => false
  end.
Instance reflect_subterm_spec : ReflectEq subterm_spec.
Proof. 
  refine {| eqb := subterm_spec_eqb |}.  
  intros [] []; unfold subterm_spec_eqb; finish_reflect. 
Defined. 

(** printer for subterm specs *)
Definition print_inductive Σ (i : inductive) := getInductiveName Σ i.(inductive_mind) i.(inductive_ind).
Definition print_list {X} (f : X -> string) l := 
  (List.fold_left (fun acc e => acc +s "; " +s f e) l "[ ") +s " ]".

Definition print_recarg Σ r := 
  match r with
  | Norec => "Norec"
  | Mrec i => "Mrec(" +s print_inductive Σ i +s ")"
  | Imbr i => "Imbr(" +s print_inductive Σ i +s ")"
  end.

Fixpoint print_wf_paths Σ (t : wf_paths) := 
  match t with 
  | Param i j => "Param " +s natToString i +s " " +s natToString j
  | Node r l => "Node " +s print_recarg Σ r +s " " +s print_list (print_wf_paths Σ) l 
  | Rec i l => "Rec " +s natToString i +s " " +s print_list (print_wf_paths Σ) l
  end.

Definition print_size s := 
  match s with
  | Loose => "Loose"
  | Strict => "Strict"
  end.

Definition print_subterm_spec Σ (s : subterm_spec) :=
  match s with 
  | Subterm s paths => "Subterm " +s print_size s +s " (" +s print_wf_paths Σ paths +s ")"
  | Dead_code => "Dead_code"
  | Not_subterm => "Not_subterm"
  end.


(** Given a tree specifying the recursive structure of a term, generate a subterm spec. *)
(** (used e.g. when matching on an element of inductive type) *)
Definition spec_of_tree t : exc subterm_spec:= 
  b <- eq_wf_paths t mk_norec;;
  if b then ret $ Not_subterm else ret $ Subterm Strict t.

(** Intersection of subterm specs. 
   Main use: when determining the subterm info for a match, we take the glb of the subterm infos for the branches.
*)
(** Dead_code is neutral element and Not_subterm least element. For Subterms, we intersect the recursive paths and the size. *)
(** Example for the handling of Dead_code:
    <<
      match n as n return n <> 0 -> nat with
      | 0 => fun H => match H with end
      | S k => fun _ => k
      end
    >>
    In the above case, the first branch would get spec [Dead_code] and the second one a [Subterm]. 
    The full match is then a [Subterm].
*)
Definition subterm_spec_glb2 s1 s2 : exc subterm_spec := 
  match s1, s2 with 
  | _, Dead_code => ret s1
  | Dead_code, _ => ret s2
  | Not_subterm, _ => ret s1
  | _, Not_subterm => ret s2
  | Subterm a1 t1, Subterm a2 t2 => 
      inter <- inter_wf_paths t1 t2;;
      inter <- except (OtherErr "subterm_spec_glb2" "inter_wf_paths failed: empty intersection") $ inter;;
      ret $ Subterm (size_glb a1 a2) inter
  end.

(** Greatest lower bound of a list of subterm specs. *)
(** Important: the neutral element is [Dead_code] -- for matches over empty types, we thus get [Dead_code]. *)
Definition subterm_spec_glb (sl : list subterm_spec) : exc subterm_spec := 
  List.fold_left (fun acc s => acc <- acc;; subterm_spec_glb2 acc s) sl (ret Dead_code). 

(** *** Guard env *)

(** Environment to keep track of guardedness information *)
Record guard_env := 
  { 
    (** the local environment *)
    loc_env : context;
    (** de Bruijn index of the last fixpoint in this block (starting at 0) *)
    (** i.e. in a block of [n] fixpoints, the dBs of the fixes are:
        [rel_min_fix], ..., [rel_min_fix + n - 1]
    *)
    rel_min_fix : nat;
    (** de Bruijn context containing subterm information *)
    guarded_env : list subterm_spec;
  }.
Implicit Type (G : guard_env). 

(** Make an initial guard_env after entering a fixpoint to check.
  [recarg] is the index of the recursive argument, starting at 0. 
    e.g. for [fix r (n1 : nat) (n2 : nat) {struct n1} := ....] it would be 0.
  [tree] is the recursion tree for the inductive type of the recursive argument.
*)
Definition init_guard_env Γ recarg tree :=
  {| 
    loc_env := Γ;
    (** Rel 0 -> recursive argument, 
       Rel recarg -> first "proper" (non-recursive) argument,
       Rel (S recarg) -> last fixpoint in this block 
    *)
    rel_min_fix := 1 + recarg;
    guarded_env := [Subterm Loose tree]
  |}.

(** Push a binder with name [na], type [type] and subterm specification [spec] *)
Definition push_guard_env G '(na, type, spec) := 
  {|
    loc_env := G.(loc_env) ,, vass na type;
    rel_min_fix := S (G.(rel_min_fix));
    guarded_env := spec :: G.(guarded_env);
  |}.

(** add a new inner variable which is not a subterm *)
Definition push_nonrec_guard_env G '(na, type) := 
  push_guard_env G (na, type, Not_subterm).

(** Update the subterm spec of dB [i] to [new_spec] *)
Definition update_guard_spec G i new_spec := 
  {| 
    loc_env := G.(loc_env);
    rel_min_fix := G.(rel_min_fix);
    guarded_env := update_list G.(guarded_env) i new_spec 
  |}.

(** lookup subterm information for de Bruijn index [p] *)
Definition lookup_subterm G p := 
  match nth_error G.(guarded_env) p with 
  | Some spec => spec
  | None => Not_subterm
  end.

(** push a local context as [Not_subterm]s *)
Definition push_context_guard_env G Γ := 
  let n := length Γ in 
  {| 
    loc_env := G.(loc_env) ,,, Γ ;
    rel_min_fix := G.(rel_min_fix) + n;
    guarded_env := Nat.iter n (fun acc => Not_subterm :: acc) G.(guarded_env);
  |}. 

(** push fixes to the guard env as [Not_subterm]s *)
Definition push_fix_guard_env G (mfix : mfixpoint term) := 
  let n := length mfix in
  {|
    loc_env := push_assumptions_context (mfix_names mfix, mfix_types mfix) G.(loc_env);
    rel_min_fix := G.(rel_min_fix) + n;
    guarded_env := Nat.iter n (fun acc => Not_subterm :: acc) G.(guarded_env);
  |}.


(** ** Stack *)
(** A stack is used to maintain subterm information for elements which are (morally) applied to the term currently under observation, and which would really be applied if we could fully reduce with concrete values. 
  [SClosure] is used for efficiency reasons: we don't want to compute subterm information for everything, so this is done on demand. It thus captures the term and the guardedness environment it's in.
  [SArg] represents subterm information for a term for which we actually have computed that information. *)
(** Example where this is used: 
  << 
    match complex_fun n with 
    | 0 => fun t => ...
    | S n => fun t => ...
    end k
  >>
  Here, the [fun t => ...] inside the match-branches would be checked with a stack having the subterm info for [k] at the head, as that term would really be applied to the [k].  
*)
(** (Note however that not all subterm information is allowed to flow through matches like that, see the functions below. ) *)
Inductive stack_element := 
  | SClosure G (t : term)
  | SArg (s : subterm_spec). 

(** Print stack elements *)
Definition print_stack_element Σ z := 
  match z with 
  | SClosure G t => "SClosure " +s "G" +s (bruijn_print Σ G.(loc_env) t) (* NOTE omitting G *)
  | SArg s => "SArg " +s print_subterm_spec Σ s
  end.

(** Push a list of closures [l] with guard env [G] to the stack *)
Definition push_stack_closures G l stack := 
  List.fold_right (fun h acc => (SClosure G h) :: acc) l stack. 

(** Push a list of args [l] to the stack *)
Definition push_stack_args l stack := 
  List.fold_right (fun h acc => SArg h :: acc) l stack. 

(** Get the recarg the root node of [t] is annotated with. *)
Definition destruct_recarg (t : wf_paths) := destruct_node t (fun r _ => Some r) None. 

(** Check that the recarg [r] is an [Mrec] or [Imbr] node with [ind]. *)
Definition match_recarg_inductive (ind : inductive) (r : recarg) := 
  match r with
  | Norec => false
  | Mrec i | Imbr i => i == ind
  end.

(** ** Building recargs trees *)
(** In some cases, we need to restrict the subterm information flowing through a dependent match.
  In this case, we re-calculate an approximation of the recargs tree and intersect with it. 
*)
(* TODO: I don't know at this point a) why these restrictions are needed for soundness
                                    b) how the recargs tree calculated in the following differs from the one we already have statically computed -- for most purposes it seems to be identical (?) 
*)

(** To construct the recargs tree, the code makes use of [ra_env : list (recarg * wf_paths)], a de Bruijn context containing the recursive tree and the inductive for elements of an (instantiated) inductive type, and [(Norec, mk_norec)] for elements of non-inductive type.  

  Importantly, the recargs tree (of type wf_paths) may make references to other elements in the [ra_env] (via the [Param] constructor).
*)

(** Add the types of inner mutual inductives to a recargs environment. This is used in the context of nested inductives.
  Specifically, for the j-th inductive in the block, we add [(Imbr $ mkInd ind_kn j, Param 0 j)], i.e. an inner inductive with a direct recursive reference to the j-th inductive in the block. 
  The rest of the env is lifted accordingly.
  *)
Definition ra_env_push_inner_inductives_with_params ra_env ind_kn ntypes := 
  (** make inner inductive types (Imbr in the tree) with recursive references for the individual types *)
  let rc := rev $ mapi (fun i t => (Imbr (mkInd ind_kn i), t)) 
                       (mk_rec_calls (X := recarg) ntypes) in
  (** lift the existing ra_env *)
  let ra_env := map (fun '(r, t) => (r, rtree_lift ntypes t)) ra_env in
  rc ++ ra_env. 

(** Add the types of mutual inductives as assumptions to the local context (the first inductive body at dB 0)
  The inductive types are instantiated with the (uniform) parameters in [pars]. 
*)
Definition context_push_ind_with_params Σ Γ (mib : mutual_inductive_body) (pars : list term) : exc context := 
  let num_bodies := length mib.(ind_bodies) in
  (* get relevance *)
  fst_body <- except (OtherErr "context_push_ind_with_params" "mutual inductive has no bodies") $
    nth_error mib.(ind_bodies) 0;;
  let relev := fst_body.(ind_relevance) in
  (* function: push one inductive to the context *)
  let push_ind := fun (specif : one_inductive_body) Γ =>
    let na := {|binder_name := nAnon; binder_relevance := relev|} in
    (* get the type instantiated with params *)
    ty_inst <- hnf_prod_apps Σ Γ specif.(ind_type) pars;;
    ret $ Γ ,, vass na ty_inst 
  in 
  List.fold_right (fun i acc => acc <- acc;; push_ind i acc) (ret Γ) mib.(ind_bodies).



(** Move the first [n] prods of [c] into the context as elements of non-recursive type. *)
Fixpoint ra_env_decompose_prod Σ Γ (ra_env : list (recarg * wf_paths)) n (c : term) {struct c} : exc (context * list (recarg * wf_paths) * term) :=
  match n with 
  | 0 => ret (Γ, ra_env, c)
  | S n => 
    c_whd <- whd_all Σ Γ c;;
    match c_whd with
    | tProd na ty body =>
      let Γ' := Γ ,, vass na ty in 
      let ra_env' := (Norec, mk_norec) :: ra_env in
      ra_env_decompose_prod Σ Γ' ra_env' n body
    | _ => raise (OtherErr "ra_env_decompose_prod" "not enough prods") 
    end
  end.

(** Create the recursive tree for a nested inductive [ind] applied to arguments [args]. *)
(** In particular: starting from the tree [tree], we instantiate parameters suitably (with [args]) to handle nested inductives. *)
(** [tree] is used to decide when to traverse nested inductives. *)
(** [ra_env] is used to keep track of the subterm information of dB variables. 
   It need not bind all variables occurring in [t]: to unbound indices, we implicitly assign [Norec].*)
Fixpoint build_recargs_nested Σ ρ Γ (ra_env : list (recarg * wf_paths)) (tree : wf_paths) (ind: inductive) (args: list term) {struct args}: exc wf_paths := 
  (** if the tree [tree] already disallows recursion, we don't need to go further *)
  b_eq <- equal_wf_paths tree mk_norec;;
  if b_eq : bool then ret tree else (
  '(mib, oib) <- lookup_mind_specif Σ ind;;
  static_trees <- except (OtherErr "build_recargs_nested" "lookup_paths failed")$ lookup_paths_all ρ ind;;
  (** determine number of (non-) uniform parameters *)
  let num_unif_params := num_uniform_params mib in
  let num_non_unif_params := mib.(ind_npars) - num_unif_params in
  (** get the instantiations for the uniform parameters *)
  (** Note that in Coq, all parameters after the first non-uniform parameter are treated as non-uniform -- thus we can just take a prefix of the list *)
  let inst_unif := firstn num_unif_params args in
  let num_mut_inds := length mib.(ind_bodies) in
  (** extend the environment with the inductive definitions applied to the parameters *)
  Γ' <- context_push_ind_with_params Σ Γ mib inst_unif;;
  (** do the same for the ra environment: 
    for the j-th inductive, 
    the recarg is Imbr (for the container), 
    the trees are direct recursive references [Param 0 j] *)
  let ra_env' := ra_env_push_inner_inductives_with_params ra_env ind.(inductive_mind) num_mut_inds in

  (** lift the parameters we instantiate with by the number of types: 
    the dB layout we setup is: 
        [inductive types defined in the container of the nested ind], [the environment the parameters are assuming]
    Since we insert the inductive types when we use the parameters to instantiate the recargs tree, we thus have to lift the parameters by the number of mutual types of the container.
  *)
  let inst_unif_lifted := map (lift0 num_mut_inds) inst_unif in

  (** In case of mutual inductive types, we use the recargs tree which was
    computed statically. This is fine because nested inductive types with
    mutually recursive containers are not supported -- meaning we need not instantiate in that case. 
    In the case that there are no mutual inductives, we use the argument tree [tree].*)
  trees <- (if num_mut_inds == 1 
    then arg_sizes <- wf_paths_constr_args_sizes tree;; ret [arg_sizes]
    else unwrap $ map (fun tree => wf_paths_constr_args_sizes tree) static_trees);;

  (** function: make the recargs tree for the [j]-th inductive in the block with body [oib].
    Essentially, we instantiate the corresponding recargs tree in [trees] with the parameters in [inst_unif]. *)
  let mk_ind_recargs (j : nat) (oib : one_inductive_body) : exc wf_paths :=
    (** get constructor types (with parameters), assuming that the mutual inductives are at [0]...[num_mut_inds-1]*)
    let constrs := map (fun '((_, c), _) => c) oib.(ind_ctors) in
    (** abstract the parameters of the recursive occurrences of the inductive type in the constructor types *)
    (** we assume that at indices [0]... [num_mut_inds-1], the inductive types are instantiated _with_ the parameters *)
    let abstracted_constrs := abstract_params_mind_constrs num_mut_inds num_unif_params constrs in
    (** build the trees for the constructors, instantiated with the uniform parameters [inst_unif] *) 
    paths <- unwrap $ mapi (fun k c => (* [k]-th constructor with abstracted type [c] *)
        (** instantiate the abstracted constructor types with the parameters we are interested in. *)
        c_inst <- hnf_prod_apps Σ Γ' c inst_unif_lifted;;
        (** move non-uniform parameters into the context *) 
        '(Γ', ra_env', c') <- ra_env_decompose_prod Σ Γ' ra_env' num_non_unif_params c_inst;;
        (** first fetch the trees for this constructor  *)
        constr_trees <- except (IndexErr "build_recargs_nested/mk_ind_recargs" "no tree for inductive" j) $ 
          nth_error trees j;;
        arg_trees <- except (IndexErr "build_recargs_nested/mk_ind_recargs" "no tree for constructor" k) $ 
          nth_error constr_trees k;; 
        (** recursively build the trees for the constructor's arguments, potentially traversing nested inductives *)
        build_recargs_constructors Σ ρ Γ' ra_env' arg_trees c'
      ) abstracted_constrs;;
      (** make the tree for this nested inductive *)
      ret $ mk_ind_paths (Imbr (mkInd ind.(inductive_mind) j)) paths
  in
  (** create the trees for all the bodies *)
  ind_recargs <- unwrap $ mapi mk_ind_recargs mib.(ind_bodies);;
  (** now, given the bodies, make the mutual inductive trees *)
  trees <- except (OtherErr "build_recargs_nested" "creating trees failed") $ mk_rec ind_recargs;;
  (** return the tree for our particular inductive type *)
  tree_ind <- except (IndexErr "build_recargs_nested" "created trees malformed" ind.(inductive_ind)) $ 
    nth_error trees ind.(inductive_ind);;
  ret tree_ind)

(** Build the recargs tree for a term [t] -- in practice, [t] will be the type of a constructor argument. *)
(** In the case that [t] contains nested inductive calls, [tree] is used to decide when to traverse nested inductives. *)
(** [ra_env] is used to keep track of the subterm information of dB variables. 
   It need not bind all variables occurring in [t]: to unbound indices, we implicitly assign [Norec].*)
(** This code is very close to check_positive in indtypes.ml, but does no positivity check and does not compute the number of recursive arguments. *)
(** In particular, this code handles nested inductives as described above. *)
with build_recargs Σ ρ Γ (ra_env : list (recarg * wf_paths)) (tree : wf_paths) (t : term) {struct t}: exc wf_paths := 
  t_whd <- whd_all Σ Γ t;;
  let '(x, args) := decompose_app t_whd in
  match x with 
  | tProd na type body => 
      (** simply enter the prod, adding the quantified element as assumption of non-recursive type (even though the type may in fact be inductive, for the purpose of determining the recargs tree of [t], this is irrelevant)*)
      assert (args == []) (OtherErr "build_recargs" "tProd case: term is ill-typed");;
      let Γ' := Γ ,, vass na type in
      let ra_env' := (Norec, mk_norec) :: ra_env in
      build_recargs Σ ρ Γ' ra_env' tree body
  | tRel k => 
      (** free variables are allowed and assigned Norec *)
      catchE (k_ra <- except (OtherErr "" "") $ nth_error ra_env k;; ret (snd k_ra)) 
            (fun _ => ret mk_norec)
  | tInd ind _ => 
    (** if the given tree for [t] allows it (i.e. has an inductive as label at the root), we traverse a nested inductive *)
    match destruct_recarg tree with 
    | None => raise $ OtherErr "build_recargs" "tInd case: malformed recargs tree"
    | Some (Imbr ind') | Some (Mrec ind') => 
        if ind == ind' then build_recargs_nested Σ ρ Γ ra_env tree ind args 
                       else ret mk_norec
    | _ => ret mk_norec 
    end
  | _ => ret mk_norec
  end

  

(** [build_recargs_constructors Σ Γ ra_env trees c] builds a list of each of the constructor [c]'s argument's recursive structures, instantiating nested inductives suitably.  
  We assume that [c] excludes parameters -- these should already be contained in the environment. 

  [trees] is a list of trees for the constructor's argument types, used to determine when to traverse nested inductive types.

  [ra_env] is used to keep track of the recursive trees of dB variables. 
   It need not bind all variables occurring in [t]: to unbound indices, we implicitly assign [Norec] with a trivial recursive tree.
*)
with build_recargs_constructors Σ ρ Γ (ra_env : list (recarg * wf_paths)) (trees : list wf_paths) (c : term) {struct c}: exc (list wf_paths) := 
  let recargs_constr_rec := fix recargs_constr_rec Γ (ra_env : list (recarg * wf_paths)) (trees : list wf_paths) (lrec :list wf_paths) (c : term) {struct c} : exc (list wf_paths) := 
    c_whd <- whd_all Σ Γ c;;
    let '(x, args) := decompose_app c_whd in
    match x with 
    | tProd na type body => 
        (* the constructor has an argument of type [type] *)
        assert (args == []) (OtherErr "build_recargs_constructors" "tProd case: ill-typed term");;
        (* compute the recursive structure of [type] *)
        first_tree <- except (ProgrammingErr "build_recargs_constructors" "trees is too short") $
          hd trees;;
        rec_tree <- build_recargs Σ ρ Γ ra_env first_tree type;;
        (* [na] of type [type] can be assumed to be of non-recursive type for this purpose *)
        let Γ' := Γ ,, vass na type in
        let ra_env' := (Norec, mk_norec) :: ra_env in 
        (* process the rest of the constructor type *)
        rest_trees <- except (OtherErr "build_recargs_constructors" "trees list too short") $ 
          tl trees;;
        recargs_constr_rec Γ' ra_env' rest_trees (rec_tree :: lrec) body
    | _ => 
        (* we have processed all the arguments of the constructor -- reverse to get a valid dB-indexed context *)
        ret $ rev lrec  
    end
  in recargs_constr_rec Γ ra_env trees [] c. 


(** [get_recargs_approx env tree ind args] builds an approximation of the recargs
tree for [ind], knowing [args] that are applied to it. 
The argument [tree] is used to know when candidate nested types should be traversed, pruning the tree otherwise. *)
(* TODO: figure out in which cases with nested inductives this isn't actually the identity *)
Definition get_recargs_approx Σ ρ Γ (tree : wf_paths) (ind : inductive) (args : list term) : exc wf_paths := 
  (* starting with ra_env = [] seems safe because any unbound tRel will be assigned Norec *)
  build_recargs_nested Σ ρ Γ [] tree ind args. 


(** [restrict_spec_for_match Σ Γ spec rtf] restricts the size information in [spec] to what is allowed to flow through a match with return-type function (aka predicate) [rtf] in environment (Σ, Γ). *)
(** [spec] is the glb of the subterm specs of the match branches*)
(** (this is relevant for cases where we go into recursion with the result of a match) *)
(* TODO: how does get_recargs_approx play into this?*)
Definition restrict_spec_for_match Σ ρ Γ spec (rtf : term) : exc subterm_spec := 
  if spec == Not_subterm then ret Not_subterm
  else 
  '(rtf_context, rtf) <- decompose_lam_assum Σ Γ rtf;;
  (* if the return-type function is not dependent, no restriction is needed *)
  if negb(rel_range_occurs 0 (length rtf_context) rtf) then ret spec 
  else
    (* decompose the rtf into context and rest and check if there is an inductive at the head *)
    let Γ' := Γ ,,, rtf_context in
    '(rtf_context', rtf') <- decompose_prod_assum Σ Γ rtf;;
    let Γ'' := Γ' ,,, rtf_context' in
    rtf'_whd <- whd_all Σ Γ rtf';;
    let '(i, args) := decompose_app rtf'_whd in 
    match i with 
    | tInd ind _ => (* there's an inductive [ind] at the head under the lambdas, prods, and lets *)
        match spec with 
        | Dead_code => ret Dead_code
        | Subterm size tree => 
            (** intersect with approximation obtained by unfolding *)
            (* TODO: when does get_recargs_approx actually do something other than identity? *)
            recargs <- get_recargs_approx Σ ρ Γ tree ind args;;
            recargs <- inter_wf_paths tree recargs;;
            recargs <- except (OtherErr "restrict_spec_for_match" "intersection failed: empty") $ recargs;;
            ret (Subterm size recargs)
        | _ => (** we already caught this case above *)
            raise $ OtherErr "restrict_spec_for_match" "this should not be reachable" 
        end
    | _ => ret Not_subterm
    end.


(** ** Checking fixpoints *)


(** Given a subterm spec for a term to match on, compute the subterm specs for the binders bound by a match in the individual branches. *)
(** In [match c as z in ci y_s return P with |C_i x_s => t end]
   [branches_specif Σ G c_spec ind] returns a list of [x_s]'s specs knowing
   [c_spec]. *)
 (** [ind] is the inductive we match on. *)
Definition branches_binders_specif Σ G (discriminant_spec : subterm_spec) (ind : inductive) : exc list (list subterm_spec) := 
  (** get the arities of the constructors (without lets, without parameters) *)
  constr_arities <- (
    '(_, oib) <- lookup_mind_specif Σ ind;;
    ret $ map snd oib.(ind_ctors));;
  unwrap $ mapi (fun i (ar : nat) => 
    match discriminant_spec return exc (list subterm_spec)  with 
    | Subterm _ tree => 
        (** check if the tree refers to the same inductive as we are matching on *)
        recarg_info <- except (OtherErr "branches_binders_specif" "malformed tree") $ destruct_recarg tree;;
        if negb (match_recarg_inductive ind recarg_info) then
          (** the tree talks about a different inductive than we are matching on, so all the constructor's arguments cannot be subterms  *)
          ret $ tabulate (fun _ => Not_subterm) ar
        else 
          (** get trees for the arguments of the i-th constructor *)
          constr_args_sizes <- wf_paths_constr_args_sizes tree;;
          args_sizes <- except (IndexErr "branches_binders_specif" "no tree for constructor" i) $
            nth_error constr_args_sizes i;;
          (** this should hopefully be long enough and agree with the arity of the constructor *)
          assert (length args_sizes == ar) (OtherErr "branches_binders_specif" "number of constructor arguments don't agree");;
          (** for each arg of the constructor: generate a strict subterm spec if they are recursive, otherwise Not_subterm. 
            These do also contain the recursive tree for that argument to enable nested matches. *)
          trees <- unwrap $ map spec_of_tree args_sizes;;
          ret trees
    | Dead_code => 
        (* just propagate *)
        ret $ tabulate (fun _ => Dead_code) ar
    | Not_subterm => 
        (* just propagate *)
        ret $ tabulate (fun _ => Not_subterm) ar
    end
    ) constr_arities.

(** [subterm_specif Σ G stack t] computes the recursive structure of [t] applied to arguments with the subterm structures given by the [stack]. 
  [G] collects subterm information about variables which are in scope. 
*)
Fixpoint subterm_specif Σ ρ G (stack : list stack_element) t {struct t}: exc subterm_spec:= 
  t_whd <- whd_all Σ G.(loc_env) t;;
  let '(f, l) := decompose_app t_whd in 
  match f with 
  | tRel k => 
      (** we abstract from applications: if [t] is a subterm, then also [t] applied to [l] is a subterm *)
      (*trace ("subterm_specif : tRel :: is subterm " +s bruijn_print Σ G.(loc_env) t_whd);;*)
      ret $ lookup_subterm G k
  | tCase ind_relev rtf discriminant branches => 
      let '(ind, relev) := ind_relev in
      (** push l to the stack *)
      let stack' := push_stack_closures G stack l in
      (** get subterm info for the discriminant *)
      discriminant_spec <- subterm_specif Σ ρ G [] discriminant;;
      (** get subterm info for the binders in the branches *)
      branches_binders_specs <- branches_binders_specif Σ G discriminant_spec (fst ind);;
      (** determine subterm info for the full branches *)
      branches_specs <- unwrap $ mapi (fun i branch => 
        binder_specs <- except (IndexErr "subterm_specif" "branches_binders_specif result is too short" i) $ 
          nth_error branches_binders_specs i;;
        (* we push this to the stack, not directly to the guard env, because we haven't entered the lambdas introducing this branch's binders yet *)
        let stack_br := push_stack_args stack' binder_specs in
        subterm_specif Σ ρ G stack_br branch) (map snd branches);;
      (** take their glb -- in case of no branches, this yields [Dead_code] (absurd elimination) *)
        (* TODO *)
      (*match branches_specs with *)
      (*| [a;b] => raise (X := unit) (OtherErr "" (thunk a))*)
      (*| _ => raise (X := unit) (OtherErr "" "wrong")*)
      (*end;;*)
      spec <- subterm_spec_glb branches_specs;;
      (** restrict the subterm info according to the rtf *)
      restrict_spec_for_match Σ ρ G.(loc_env) spec rtf 
  | tFix mfix mfix_ind => 
      (*trace ("subterm_specif : tFix :: enter " +s bruijn_print Σ G.(loc_env) t_whd);;*)
      cur_fix <- except (IndexErr "subterm_specif" "invalid fixpoint index" mfix_ind) $ nth_error mfix mfix_ind;;
      (** if the co-domain isn't an inductive, this surely can't be a subterm *)
      ind_cod <- (has_inductive_codomain Σ G.(loc_env) cur_fix.(dtype));; 
      if negb ind_cod then ret Not_subterm 
      else 
        '(context, cur_fix_codomain) <- decompose_prod Σ G.(loc_env) cur_fix.(dtype);;
        let Γ' := G.(loc_env) ,,, context in 
        (** if we can't find the inductive, just handle it as [Not_subterm]. *)
        catchMap (find_inductive Σ Γ' cur_fix_codomain) (fun _ => ret Not_subterm) $ fun '((ind, _), _) => 
        let num_fixes := length mfix in
        (** get the recursive structure for the recursive argument's type*)
        rectree <- lookup_ind_subterms Σ ind;;
        (** push fixpoints to the guard env *)
        let G' := push_fix_guard_env G mfix in
        (** we let the current fixpoint be a strict subterm *)
        (* TODO: is this sound? why is it needed? nested fixes? *)
        let G' := update_guard_spec G' (num_fixes - mfix_ind) (Subterm Strict rectree) in
        let decreasing_arg := cur_fix.(rarg) in
        let body := cur_fix.(dbody) in 
        (** number of abstractions (including the one for the decreasing arg) that the body is under *)
        let num_abstractions := S decreasing_arg in
        (** split into context up to (including) the decreasing arg and the rest of the body *)
        '(context, body') <- decompose_lam_n_assum Σ G'.(loc_env) num_abstractions body;;
        (** add the arguments as Not_subterm *)
        let G'' := push_context_guard_env G' context in 
        (** push the arguments [l] _ in guard env [G] _ *)
        let stack' := push_stack_closures G stack l in
        (** before we go on to check the body: if there are enough arguments on the stack, 
          we can use the subterm information on the stack for the decreasing argument of 
          the nested fixpoint (instead of taking Not_subterm) *)
        (** we check the body with an empty stack as it isn't directly applied to something*)
        if Nat.ltb (length stack') num_abstractions then subterm_specif Σ ρ G'' [] body' else
          decreasing_arg_stackel <- except (IndexErr "subterm_specif" "stack' too short" decreasing_arg) $ 
            nth_error stack' decreasing_arg;;
          arg_spec <- stack_element_specif Σ ρ decreasing_arg_stackel;;
          let G'' := update_guard_spec G'' 0 arg_spec in 
          subterm_specif Σ ρ G'' [] body'
  | tLambda x ty body => 
      (* TODO *)
     (*raise (X := unit) (OtherErr "" (thunk t));;*)
     (*trace ("subterm_specif : tLambda :: enter " +s bruijn_print Σ G.(loc_env) t_whd);;*)
     assert (l == []) (OtherErr "subterm_specif" "reduction is broken");;
     (** get the subterm spec of what the lambda would be applied to (or Not_subterm if [stack] is empty)*)
     '(spec, stack') <- extract_stack_hd Σ ρ stack;;
     subterm_specif Σ ρ (push_guard_env G (x, ty, spec)) stack' body 
  | tEvar _ _ => 
      (* evars are okay *)
      (*ret Dead_code*)
      raise $ OtherErr "subterm_specif" "the guardedness checker does not handle evars"
  | tProj p t => 
      (** compute the spec for t *)
      (** TODO: why do we do this with the stack (instead of the empty stack)?
        shouldn't _the result_ of the projection be applied to the elements of the stack?? *)
      t_spec <- subterm_specif Σ ρ G stack t;;
      match t_spec with 
      | Subterm _ paths => 
          arg_trees <- wf_paths_constr_args_sizes paths;;
          match arg_trees with 
          | [arg_tree] => 
              (** get the tree of the projected argument *)
              let proj_arg := snd p in
              proj_arg_tree <- except (IndexErr "subterm_specif" "malformed recursive tree" proj_arg) $ 
                nth_error arg_tree proj_arg;;
                (** make a spec out of it *)
              spec_of_tree proj_arg_tree
          | _ => raise $ OtherErr "subterm_specif" "projection on type having a number of constructors ≠ 1"
          end
      | Dead_code => ret Dead_code
      | Not_subterm => ret Not_subterm
      end
  | _ => ret Not_subterm
  end

(** given a stack element, compute its subterm specification *)
with stack_element_specif Σ ρ stack_el {struct stack_el} : exc subterm_spec := 
  match stack_el with 
  | SClosure G t => 
      (*trace ((thunk (print_id ((Σ, G.(loc_env), t)))));;*)
      subterm_specif Σ ρ G [] t
  | SArg spec => ret spec
  end

(** get the subterm specification for the top stack element together with the rest of the stack*)
with extract_stack_hd Σ ρ stack {struct stack} : exc (subterm_spec * list stack_element) := 
  match stack with 
  | [] => ret (Not_subterm, [])
  | h :: stack => 
      spec <- stack_element_specif Σ ρ h;;
      ret (spec, stack)
  end.

(** Check that a term [t] with subterm spec [spec] can be applied to a fixpoint whose recursive argument has subterm structure [tree]*)
Definition check_is_subterm spec tree := 
  match spec with 
  | Subterm Strict tree' => 
      (* TODO: find an example where the inclusion checking is needed -- probably with nested inductives? *)
      incl_wf_paths tree tree'
  | Dead_code => 
      (** [spec] been constructed by elimination of an empty type, so this is fine *)
      ret true
  | _ => ret false
  end.


 

(** We use this function to filter the subterm information for arguments applied to a match, stored in the [stack], to 
  what is allowed to flow through a match, obtaining the stack of subterm information for what would be applied to 
  the match branches after the match is reduced. 
  [rtf] is the return-type function of the match (aka the match predicate). 

  Assuming that the return-type function has the shape 
    [λ x, ∀ (x1 : T1) (x2 : T2) .... (xn : Tn). T]
  where x is applied to the discriminant of the match, 
  we allow the subterm information to the applicants corresponding to the xi to flow through, 
    IF the Ti has the shape 
      [Ti = ∀ y1 ... yn let z1 ... let zm := _ in IND t1 t2 ... tk]
    (where the prods and lets can appear in arbitrary permutations) and IND is an inductive type.
    In that case, we infer an approximate recargs tree for IND applied to t1 .... tk and 
    intersect it with the subterm tree of xi in the stack. 
  All other subterm information is truncated to Not_subterm. 

  TODO: why do we have these constraints given by the rtf? 
*)
Definition filter_stack_domain Σ ρ Γ (rtf : term) (stack : list stack_element) : exc (list stack_element) := 
  '(rtf_context, rtf_body) <- decompose_lam_assum Σ Γ rtf;; 
   (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if negb (rel_range_occurs 0 (length rtf_context) rtf_body) then ret stack 
  else
    (* enter the rtf context *)
    let Γ' := Γ ,,, rtf_context in
    let filter_stack := fix filter_stack Γ t stack : exc (list stack_element) := 
      t' <- whd_all Σ Γ t;;
      match stack, t' with 
      | elem :: stack', tProd na ty t0 => 
        (* the element [elem] in the stack would be applied to what corresponds to the [∀ na : ty, t0] in the rtf *)
        let d := vass na ty in 
        (* decompose the type [ty] of [na] *)
        '(ctx, ty) <- decompose_prod_assum Σ Γ ty;;
        let Γ' := Γ ,,, ctx in
        (* now in the context of the type *)
        whd_ty <- whd_all Σ Γ' ty;;
        (* decompose the rest of the type again and check if the LHS is an inductive *)
        let (ty', ty_args) := decompose_app whd_ty in
        (* compute what is allowed to flow through *)
        elem' <- match ty' with
          | tInd ind univ =>  
              (* it's an inductive *)
              (* inspect the corresponding subterm spec on the stack *)
              spec' <- stack_element_specif Σ ρ elem;;
              match spec' with 
              | Not_subterm | Dead_code => ret elem (* don't restrict *)
              | Subterm s path => 
                  (** intersect with an approximation of the unfolded tree for [ind] *)
                  (* TODO : when does get_recargs_approx give something other than identity ? *)
                  recargs <- get_recargs_approx Σ ρ Γ path ind ty_args;;
                  path' <- inter_wf_paths path recargs;;
                  path' <- except (OtherErr "filter_stack_domain" "intersection of trees failed: empty") path' ;;
                  (* update the recargs tree to [path'] *)
                  ret $ SArg (Subterm s path') 
              end
                 | _ => ret $ SArg Not_subterm (* if not an inductive, the subterm information is not propagated *) 
          end;;
        (** NOTE: the Coq impl goes into recursion with Γ' ,, d. I believe that is wrong and have fixed it here. *)
        rest <- filter_stack (Γ ,, d) t0 stack';;
        ret (elem' :: rest)
      | _, _ => 
          (* the rest of the stack is restricted to No_subterm, subterm information is not allowed to flow through *)
          ret (List.fold_right (fun _ acc => SArg (Not_subterm) :: acc) [] stack)
      end
    in filter_stack Γ' rtf_body stack.

(** 
  The main checker descending into the recursive structure of a term.
  Checks if [t] only makes valid recursive calls, with variables (and their subterm information) being tracked in the context [G].

  [stack] is the list of constructor's argument specification and arguments that will be applied after reduction.
  For example: for the term [(match .. with |.. => t end) u], [t] will be checked with (the subterm information of) [u] on the stack. This is needed as we (of course) might not be able to reduce the match, but still want to be able to reason about [t] being applied to [u] after reduction.

  [trees] is the list of recursive structures for the decreasing arguments of the mutual fixpoints.*)
Fixpoint check_rec_call (num_fixes : nat) (decreasing_args : list nat) trees
Σ ρ G (stack : list stack_element) (t : term) {struct t} : exc unit := 
  let check_rec_call' := check_rec_call num_fixes decreasing_args trees Σ ρ in 

  (** if [t] does not make recursive calls, then it is guarded: *)
  if negb(rel_range_occurs G.(rel_min_fix) num_fixes t) then ret tt
  else 
    t_whd <- whd_βιζ Σ G.(loc_env) t;;
    (* FIXME: the guardedness checker will not be able to determine guardedness of this function since we wrap the match in there; thus l will not be determined as a subterm (as [] isn't) *)
    let (f, l) := decompose_app t_whd in  
    (** NOTE : I have annotated some of the cases with conditions on guardedness, but these are partially incomplete as the [stack] of 'virtually applied' arguments complicates verbal descriptions quite a bit. 
      The commented code is likely more informative. *)
    match f with 
    | tRel p =>
        (** check if [p] is a fixpoint (of the block of fixpoints we are currently checking),i.e. we are making a recursive call *)
        if Nat.leb G.(rel_min_fix) p && Nat.ltb p (G.(rel_min_fix) + num_fixes) then
          trace ("check_rec_call : tRel :: " +s bruijn_print Σ G.(loc_env) t);;
          (** check calls in the argument list, initialized to an empty stack*)
          _ <- list_iter (check_rec_call' G []) l;;
          trace ("check_rec_call : tRel :: checked arguments");;
          (** get the position of the invoked fixpoint in the mutual block *)
          let rec_fixp_index := G.(rel_min_fix) + num_fixes -1 - p in
          (** get the decreasing argument of the recursive call *)
          decreasing_arg <- except (IndexErr "check_rec_call" "invalid fixpoint index" rec_fixp_index) $ 
            nth_error decreasing_args rec_fixp_index;;
          (** push the arguments as closures on the stack -- we don't infer their full subterm information yet *)
          let stack' := push_stack_closures G stack l in 
          (** get the stack entry for the decreasing argument *)
          z <- except (IndexErr "check_rec_call" "not enough arguments for recursive fix call" decreasing_arg) $ 
            nth_error stack' decreasing_arg;;
          (** get the tree for the recursive argument type *)
          recarg_tree <- except (IndexErr "check_rec_call" "no tree for the recursive argument" rec_fixp_index) $ 
            nth_error trees rec_fixp_index;;
          (** infer the subterm spec of the applied argument *)
          rec_subterm_spec <- stack_element_specif Σ ρ z;;
          trace ("check_rec_call : tRel :: spec for decreasing arg is " +s (print_subterm_spec Σ rec_subterm_spec));;
          (** verify that it is a subterm *)
          b_subt <-(check_is_subterm rec_subterm_spec recarg_tree);; 
          if negb b_subt
          then 
            match z with 
            | SClosure z z' => raise $ GuardErr "check_rec_call" "illegal recursive call (could not ensure that argument is decreasing)"
            | SArg _ => 
                (* TODO: check if this is the right error *)
                raise $ GuardErr "check_rec_call" "fix was partially applied"
            end
          else  
          ret tt
        else ret tt

    (** Assume we are checking the fixpoint f. For checking [g a1 ... am]:
      if - g = match d return rtf with | Ci xi1 ... xin => bi end
         - f is guarded with respect to the set of subterms S in a1 ... am
         - f is guarded with respect to the set of subterms S in the return-type function rtf
         - f is guarded with respect to the set of subterms S in the discriminant d
         - for each branch Ci xi1 ... xin => bi where S' := S ∪ { xij | the constructor Ci is recursive in the argument xij }:
            f is guarded with respect to S' in the branch body
            bi (virtually) applied to a1 ... am, where we restrict the subterm information of a1 ... am to 
            what is allowed to flow through the rtf
      then f is guarded with respect to the set of subterms S in [g a1 ... am].
    *)
    | tCase ind_nparams_relev rtf discriminant branches => 
        (** match discriminant : ind return rtf with [branches] end *)
        let '((ind, nparams), relev) := ind_nparams_relev in
        catchE (
          (** check the arguments [l] it is applied to, the return-type function and the discriminant *)
          _ <- list_iter (check_rec_call' G []) l;;
          _ <- check_rec_call' G [] rtf;;
          _ <- check_rec_call' G [] discriminant;;
          (** compute the recursive argument info for the binders of each branch by looking at the tree *)
          discriminant_spec <- subterm_specif Σ ρ G [] discriminant;; 
          case_branch_specs <- branches_binders_specif Σ G discriminant_spec ind;; 
          (** push arguments on stack *)
          let stack' := push_stack_closures G stack l in
          (** filter the stack to only contain the subterm info which is allowed to propagate through matches *)
          stack' <- filter_stack_domain Σ ρ G.(loc_env) rtf stack';;
          (** check the branches of the matches *)
          list_iteri (fun i '(_, branch) =>
              branch_spec <- except (IndexErr "check_rec_call" "branch specs too short" i) $ 
                nth_error case_branch_specs i;;
              (** push the rec arg specs for the binders introduced by the branch *)
              let stack_branch := push_stack_args stack' branch_spec in
              (** check the branch *)
              check_rec_call' G stack_branch branch) 
            branches
        )  
        (fun err => 
          (** if the checking goes wrong, we can still try harder by reducing the match away if possible *)
          discriminant <- whd_all Σ G.(loc_env) discriminant;;
          let '(hd, _) := decompose_app discriminant in
          match hd with 
          | tConstruct _ _ _ => 
             (*just check the whole thing again with the reduced discriminant *)
              check_rec_call' G [] (mkApps (tCase ind_nparams_relev rtf discriminant branches) l)
          | _ => raise err
          end
        )

    (** Assume we are checking the fixpoint f. 
       This implements the following rule for checking the term [g a1 ... am]:
       if - g = fix g (y1:T1)...(yp:Tp) {struct yp} := e 
          - f is guarded with respect to the set of subterms S in a1 ... am        
          - f is guarded with respect to the set of subterms S in T1 ... Tp        
          - ap is a sub-term of the recursive argument of f and f is guarded with respect to the set of subterms S ∪ {yp} in e
           OR ap is not a sub-term of the recursive argument of f and f is guarded with respect to the set of subterms S in e
       then f is guarded with respect to the set of subterms S in (g a1 ... am). *)
    | tFix mfix_inner fix_ind => 
        this_fix <- except (OtherErr "check_rec_call" "tFix: malformed fixpoint") $ nth_error mfix_inner fix_ind;;
        let decreasing_arg := rarg this_fix in 
        trace $ "check_rec_call : tFix :: " +s (bruijn_print Σ G.(loc_env) t_whd);;
        catchE (
          (** check args *)
          _ <- list_iter (check_rec_call' G []) l;;
          (** check types *)
          _ <- list_iter (check_rec_call' G []) (mfix_types mfix_inner);;
          (** push arguments onto the stack *)
          let stack' := push_stack_closures G stack l in 
          (** update the env with the rec. fixes *)
          let G' := push_fix_guard_env G mfix_inner in 
          list_iteri (fun j body => 
            if (fix_ind == j) && Nat.ltb decreasing_arg (length stack') then
              (** we have subterm information for the decreasing arg on the stack *)
              rec_arg_stackel <- except (ProgrammingErr "check_rec_call" "should be unreachable") $ 
                nth_error stack' decreasing_arg;; 
              (** compute the subterm spec for the recursive argument *)
              rec_arg_spec <- stack_element_specif Σ ρ rec_arg_stackel;;
              (** check the body of the fix after entering under the arguments and adding rec_arg_spec as the specification for [decreasing_arg] *)
              check_nested_fix_body num_fixes decreasing_args trees Σ ρ G' decreasing_arg rec_arg_spec body
            else 
              (** just check the body with an empty stack *)
              check_rec_call' G' [] body)
            (mfix_bodies mfix_inner))
          $ fun err => 
            (** try to reduce the fix away by looking for a constructor in l[decreasing_arg] *)
            if Nat.leb (length l) decreasing_arg then raise err else
            rec_arg_term <- except (ProgrammingErr "check_rec_call" "should be unreachable") $ 
              nth_error l decreasing_arg;;
            rec_arg_term <- whd_all Σ G.(loc_env) rec_arg_term;;
            let '(hd, _) := decompose_app rec_arg_term in 
            match hd with 
            | tConstruct _ _ _ => 
                let before := firstn decreasing_arg l in 
                let after := skipn (S decreasing_arg) l in
                (* try again with the reduced recursive argument *)
                check_rec_call' G [] (mkApps (tFix mfix_inner fix_ind) (before ++ rec_arg_term :: after))
            | _ => raise err
            end

    | tConst kname univ => 
        if is_evaluable_const Σ kname then 
          (** check the arguments *)
          catchE (list_iter (check_rec_call' G []) l) $ fun e => 
          (** an error occurred, maybe it goes better if we apply the arguments and reduce the constant? *)
            val <- except (ProgrammingErr "check_rec_call" "constant lookup failed") $ get_const_value Σ kname;;
            check_rec_call' G stack (tApp val l)
        else 
          (** just check the arguments without fallback *)
          list_iter (check_rec_call' G []) l

    | tLambda x ty body =>
        (** l is empty or reduction is broken *)
        _ <- assert (l == []) (OtherErr "check_rec_call" "tLambda : reduction is broken");;
        (** check the type *)
        check_rec_call' G [] ty;;
        (** we take the subterm spec at the head of the stack (corresponding to the element which will be applied to this lambda), or No_subterm if the stack is empty *)
        '(spec, stack') <- extract_stack_hd Σ ρ stack;;
        (** and check the body in the updated environment with the spec for this applied element *)
        check_rec_call' (push_guard_env G (x, ty, spec)) stack' body


    | tProd x ty body => 
        (** the list [l] should be empty, otherwise the term is ill-typed *)
        _ <- assert (l == []) (OtherErr "check_rec_call" "tProd: input term is ill-typed");;
        (*TODO Coq doesn't like the following check *)
        (*_ <- assert (stack == []) "tProd: stack should be empty";;*)
        (** check the type *)
        check_rec_call' G [] ty;;
        (** check the body: x is not a subterm *)
        check_rec_call' (push_nonrec_guard_env G (x, ty)) [] body

    | tCoFix mfix_inner fix_ind => 
        (** check the arguments *)
        _ <- list_iter (check_rec_call' G []) l;;
        (** check the types of the mfixes *)
        _ <- list_iter (check_rec_call' G []) (map dtype mfix_inner);;
        (** check the bodies *)
        let G' := push_fix_guard_env G mfix_inner in
        list_iter (check_rec_call' G' []) (map dbody mfix_inner)

    | tInd _ _ | tConstruct _ _ _ => 
        (** just check the arguments *)
        list_iter (check_rec_call' G []) l

    | tProj p c =>
        catchE (
          (** check arguments *)
          _ <- list_iter (check_rec_call' G []) l;;
          check_rec_call' G [] c)
        $ fun exn => 
          (* if this fails, try to reduce the projection by looking for a constructor in c *)
          c <- whd_all Σ G.(loc_env) c;;
          let '(hd, _) := decompose_app c in 
          match hd with 
          | tConstruct _ _ _ => 
              (* FIXME: currently, this handling is quite pointless as MetaCoq does not implement reduction of projections properly. *)
              raise exn
          | _ => raise exn
          end  

    | tVar id => 
        (* FIXME: environments for named variables do not seem to be properly implemented in MetaCoq.
          However, I think they are only ever used for section variables in Coq, I believe. *)
        raise (ProgrammingErr "check_rec_call" "handling of named variables is unimplemented")

    | tSort _ => 
        (* a sort shouldn't be applied to anything; guardedness is fine of course *)
        assert (l == []) $ OtherErr "check_rec_call" "tSort: ill-typed term"

    | tEvar _ _ => 
        (** the RHS [l] is not checked because it is considered as the evar's context *)
        (** NOTE: the guard checker is not really supposed to be dealing with evars -- it should be called on evar-free terms;
          see https://github.com/coq/coq/issues/9333#issuecomment-453235650*)
        raise $ OtherErr "check_rec_call" "guard checker should not be called on terms containing evars"
    | tApp _ _ | tLetIn  _ _ _ _ | tCast _ _ _ => raise (OtherErr "check_rec_call" "beta-zeta-iota reduction is broken")
    end

(** Check the body [body] of a nested fixpoint with decreasing argument [decr] (dB index) and subterm spec [sub_spec] for the recursive argument.*)
(** We recursively enter the body of the fix, adding the non-recursive arguments preceding [decr] to the guard env and finally add the decreasing argument with [sub_spec], before continuing to check the rest of the body *)
with check_nested_fix_body (num_fixes : nat) (decreasing_args : list nat) trees
Σ ρ G (decr : nat) (sub_spec : subterm_spec) (body : term) {struct decr}: exc unit := 
  let check_rec_call' := check_rec_call num_fixes decreasing_args trees Σ ρ in
  (** reduce the body *)
  body_whd <- whd_all Σ G.(loc_env) body;;
  match body with 
  | tLambda x ty body => 
      _ <- check_rec_call' G [] ty;; 
      match decr with 
      | 0 =>
        (** we have arrived at the recursive arg *)
        check_rec_call' (push_guard_env G (x, ty, sub_spec)) [] body 
      | S n => 
        (** push to env as non-recursive variable and continue recursively *)
        let G' := push_nonrec_guard_env G (x, ty) in  
        check_nested_fix_body num_fixes decreasing_args trees Σ ρ G' n sub_spec body
      end
  | _ => raise $ OtherErr "check_nested_fix_body" "illformed inner fix body"
  end.

(** Check if [def] is a guarded fixpoint body, with arguments up to (and including)
  the recursive argument being introduced in the context [G]. 
  [G] has been initialized with initial guardedness information on the recursive argument.
  [trees] is a list of recursive structures for the decreasing arguments of the mutual fixpoints.
  [recpos] is a list with the recursive argument indices of the mutually defined fixpoints.
*)
Definition check_one_fix Σ ρ G (recpos : list nat) (trees : list wf_paths) (def : term) : exc unit := 
  check_rec_call (length recpos) recpos trees Σ ρ G [] def.  


(** Extract the [inductive] that [fixp] is doing recursion over (and check that the recursion is indeed over an inductive).
  Moreover give the body of [fixp] after the recursive argument and the environment (updated from [Γ])
  that contains the arguments up to (and including) the recursive argument (of course also the fixpoints). *)
Definition inductive_of_mutfix Σ Γ (fixp : mfixpoint term) : exc (list inductive * list (context * term)):= 
  trace "inductive_of_mutfix : enter";;
  let number_of_fixes := length fixp in
  assert (number_of_fixes != 0) (OtherErr "inductive_of_mutfix" "ill-formed fix");;
  let ftypes := mfix_types fixp in
  let fnames := mfix_names fixp in 
  let fbodies := mfix_bodies fixp in
  (** push fixpoints to environment *)
  let Γ_fix := push_assumptions_context (fnames, ftypes) Γ in
  let nvect := map rarg fixp in 

  (** Check the i-th definition [fixdef] of the mutual inductive block where k is the recursive argument, 
    making sure that no invalid recursive calls are in the types of the first [k] arguments, 
    make sure that the recursion is over an inductive type, 
    and return that inductive together with the body of [fixdef] after the recursive arguement
    together with its context. *)
  let find_ind i k fixdef : exc (inductive * (context * term)):= 
      (** check that a rec call to the fixpoint [fixdef] does not appear in the [k] first abstractions,
        that the recursion is over an inductive, and 
        gives the inductive and the body + environment of [fixdef] after introducing the first [k] arguments *)
      let check_occur := fix check_occur Γ n (def : term) {struct def}: exc (inductive * (context * term)) := 
        (** n is the number of lambdas we're under/aka the dB from which the mutual fixes are starting:
          n ... n + number_of_fixes - 1 *)
        def_whd <- whd_all Σ Γ def;;
        match def_whd with 
        | tLambda x t body => 
            assert (negb(rel_range_occurs n number_of_fixes t)) 
              (GuardErr "inductive_of_mutfix" "bad occurrence of recursive call");;
            let Γ' := Γ ,, (vass x t) in
            if n == k then (** becomes true once we have entered [k] inner lambdas*)
              (** so now the rec arg should be at dB 0 and [t] is the type we are doing recursion over *)
              (** get the inductive type of the fixpoint, ensuring that it is an inductive *)
              '((ind, _), _) <- catchE (find_inductive Σ Γ t) (fun _ => raise $ GuardErr "inductive_of_mutfix" "recursion not on inductive");;
              '(mib, _) <- lookup_mind_specif Σ ind;;
              if mib.(ind_finite) != Finite then (* ensure that it is an inductive *)
                raise $ GuardErr "inductive_of_mutfix" "recursion not on inductive"
              else
                (** now return the inductive, the env after taking the inductive argument and all arguments before it, and the rest of the fix's body *)
                ret (ind, (Γ', body))
            else check_occur Γ' (S n) body
        | _ => 
            (** not a lambda -> we do not have enough arguments and can't find the recursive one *)
            raise $ GuardErr "inductive_of_mutfix" "not enough abstractions in fix body" 
        end
      in 
      (** check that recursive occurences are nice and extract inductive + fix body *)
      res <- check_occur Γ_fix 0 fixdef;; 
      let '(ind, _) := res in
      '(_, oib) <- lookup_mind_specif Σ ind;;
      (*if oib.(ind_relevance) == Irrelevant && *)
      (* TODO some sprop checking for relevance *)
      ret res
  in 
  (** now iterate this on all the fixpoints of the mutually recursive block *)
  rv <- unwrap $ map2_i find_ind nvect fbodies;;
  trace "inductive_of_mutfix : leave";;
  (** return the list of inductives as well as the fixpoint bodies in their context *)
  ret (map fst rv : list inductive, map snd rv : list (context * term)).




(** The entry point for checking fixpoints. 
  [Σ]: the global environment with all definitions used in [mfix]. 
  [ρ]: the global environment of wf_paths (for every inductive in Σ, this should contain the wf_paths).
  [Γ]: the local environment in which the fixpoint is defined.
  [mfix]: the fixpoint to check.
*)
Definition check_fix Σ ρ Γ (mfix : mfixpoint term) : exc unit := 
  (** check that the recursion is over inductives and get those inductives 
    as well as the bodies of the fixpoints *)
  trace "enter check_fix";;
  '(minds, rec_defs) <- inductive_of_mutfix Σ Γ mfix;;
  (** get the inductive definitions -- note that the mibs should all be the same*)
  specifs <- unwrap $ map (lookup_mind_specif Σ) minds;;
  let mibs := map fst specifs in
  let oibs := map snd specifs in
  rec_trees <- unwrap $ map (fun ind => except (OtherErr "check_fix" "lookup_paths failed") $ lookup_paths ρ ind) minds;;

  (** the environments with arguments introduced by the fix; 
     for fix rec1 a1 ... an := .... with rec2 b1 ... bm := ... 
     the environment for rec1 would be 
      [an, ...., a1, rec2, rec1]
     and the one for rec2
      [bm, ...., b1, rec2, rec1]
  *)
  let fix_envs := map fst rec_defs in     
  let fix_bodies := map snd rec_defs in   (** the bodies under the respective [fix_envs] *)
  let rec_args := map rarg mfix in 

  _ <- unwrap $ mapi (fun i fix_body => 
    fix_env <- except (IndexErr "check_fix" "fix_envs too short" i) $ nth_error fix_envs i;;
    rec_tree <- except (IndexErr "check_fix" "rec_trees too short" i) $ nth_error rec_trees i;;
    rec_arg <- except (IndexErr "check_fix" "rec args too short" i) $ nth_error rec_args i;;
    (** initial guard env *)
    let G := init_guard_env fix_env rec_arg rec_tree in
    (** check the one fixpoint *)
    check_one_fix Σ ρ G rec_args rec_trees fix_body 
    ) fix_bodies;;
  ret tt.
