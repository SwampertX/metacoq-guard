From MetaCoq.Utils Require Import utils MCMSets.
From MetaCoq.Common Require Import BasicAst Universes Environment Reflect.
From MetaCoq.Template Require Import Ast AstUtils LiftSubst Pretty Checker.

From MetaCoq.Guarded Require Import MCRTree Inductives.

(** * Guard Checker *)

(** List of known defects:
  - The used MetaCoq reduction (from the Checker) does not handle projections.
  - constants and constant unfolding is not handled faithfully in MetaCoq. 
    The guardedness checker will be able to unfold constants even when they should be opaque. 

  - I don't currently understand the exact reasons why restrictions of subterm info flow through dependent matches is needed in some cases.
    I have documented what is restricted, but not why it is needed.

  - there are likely tons of bugs (e.g. dB off-by-ones) in code which I couldn't properly test due to the slow reduction.
    
  - good luck with attempting to formally verify any of this stuff :DD
*)


Open Scope exc_scope.

(*Definition print {A} (a : A) : exc unit := *)
  (*ret (print a).*)

(* YJ: pathsEnv := list (kername * (list wf_paths)) *)
Implicit Types (Σ : global_env_ext) (Γ : context) (ρ : pathsEnv). 


(** ** Environments for keeping track of subterm information *)

(** Environments annotated with marks on recursive arguments *)

(** proper subterm (strict) or loose subterm (may be equal to the recursive argument, i.e. not a proper subterm) *)
Inductive size := Large | Strict. 
(* induces a lattice with Large < Strict *)

Definition size_eqb (s1 s2 : size) := 
  match s1, s2 with 
  | Large, Large => true
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
  | _, _ => Large
  end.

(* Set Default Goal Selector "all". *)
Module Natset := MSetAVL.Make Nat.
Instance reflect_natset : ReflectEq Natset.t.
Proof.
  refine {| eqb := Natset.equal |}.
  intros [t1 t1o]. induction t1.
  intros [t2 t2o]. induction t2.
  cbn.
  - destruct t1o. constructor.
Admitted.
(** possible specifications for a term:
   - Not_subterm: when the size of a term is not related to the recursive argument of the fixpoint
   - Subterm: when the term is a subterm of the recursive argument
     the [wf_paths] argument specifies which subterms of the term are recursive 
     -- this is just the whole recursive structure of the term's type again, for nested matches 
        (possibly not the trivial recargs tree that could also be looked up in the environment: for nested inductives, this is instantiated)
   - Dead_code: when the term has been built by elimination over an empty type. Is also used for evars.
 *) 
Inductive subterm_spec := 
  | Subterm (l : Natset.t) (s : size) (r : wf_paths)
  | Dead_code
  | Not_subterm
  | Internally_bound_subterm (l : Natset.t). 

Definition subterm_spec_eqb (s1 s2 : subterm_spec) := 
  match s1, s2 with
  | Dead_code, Dead_code => true
  | Not_subterm, Not_subterm => true
  | Subterm l1 size1 tree1, Subterm l2 size2 tree2 => 
      (l1 == l2) && (size1 == size2) && (tree1 == tree2)
  | Internally_bound_subterm l1, Internally_bound_subterm l2 =>
      (l1 == l2)
  | _, _ => false
  end.
Instance reflect_subterm_spec : ReflectEq subterm_spec.
Proof. 
  refine {| eqb := subterm_spec_eqb |}.  
  intros [] []; unfold subterm_spec_eqb; finish_reflect. 
Defined. 

(** printer for subterm specs *)
(* Definition print_inductive Σ (i : inductive) := getInductiveName Σ i.(inductive_mind) i.(inductive_ind). *)
(* Definition print_list {X} (f : X -> string) l :=  *)
(*   (List.fold_left (fun acc e => acc +s "; " +s f e) l "[ ") +s " ]". *)

Definition print_recarg Σ r := 
  match r with
  | Norec => "Norec"
  | Mrec (RecArgInd i) => "Mrec(" ++ string_of_kername i.(inductive_mind) ++ ")"
  | Mrec (RecArgPrim c) => "Mrec(" ++ string_of_kername c ++ ")"
  end.

Fixpoint print_wf_paths Σ (t : wf_paths) := 
  match t with 
  | Param i j => "Param " ++ string_of_nat i ++ " " ++ string_of_nat j
  | Node r l => "Node " ++ print_recarg Σ r ++ " " ++ print_list (print_wf_paths Σ) ";" l 
  | Rec i l => "Rec " ++ string_of_nat i ++ " " ++ print_list (print_wf_paths Σ) ";" l
  end.

Definition print_size s := 
  match s with
  | Large => "Large"
  | Strict => "Strict"
  end.

(** TODO *)
Definition print_subterm_spec Σ (s : subterm_spec) :=
  match s with 
  | Subterm l s paths => "Subterm " ++ print_size s ++ " (" ++ print_wf_paths Σ paths ++ ")"
  | Dead_code => "Dead_code"
  | Not_subterm => "Not_subterm"
  | Internally_bound_subterm l => ""
  end.


(** Given a tree specifying the recursive structure of a term, generate a subterm spec. *)
(** (used e.g. when matching on an element of inductive type) *)
Definition spec_of_tree t : exc subterm_spec:= 
  if eq_wf_paths t mk_norec
  then ret $ Not_subterm
  else ret $ Subterm Natset.empty Strict t.

Definition merge_internal_subterms l1 l2 := Natset.union l1 l2.

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
Definition inter_spec s1 s2 : exc subterm_spec := 
  match s1, s2 with 
  | _, Dead_code => ret s1
  | Dead_code, _ => ret s2
  | Not_subterm, _ => ret s1
  | _, Not_subterm => ret s2
  | Internally_bound_subterm l1, Internally_bound_subterm l2 => ret (Internally_bound_subterm (merge_internal_subterms l1 l2))
  | Subterm l1 a1 t1, Internally_bound_subterm l2 => ret (Subterm (merge_internal_subterms l1 l2) a1 t1)
  | Internally_bound_subterm l1, Subterm l2 a2 t2 => ret (Subterm (merge_internal_subterms l1 l2) a2 t2)
  | Subterm l1 a1 t1, Subterm l2 a2 t2 =>
      inter <- except (OtherErr "inter_spec" "inter_wf_paths failed: empty intersection") $ inter_wf_paths t1 t2;;
      ret $ Subterm (merge_internal_subterms l1 l2) (size_glb a1 a2) inter
  end.

(** Greatest lower bound of a list of subterm specs. *)
(** Important: the neutral element is [Dead_code] -- for matches over empty types, we thus get [Dead_code]. *)
Definition subterm_spec_glb (sl : list subterm_spec) : exc subterm_spec := 
  List.fold_left (fun acc s => acc <- acc;; inter_spec acc s) sl (ret Dead_code). 

(** *** Guard env *)

(** Environment to keep track of guardedness information *)
(* YJ: [loc_env] is virtually [list (kername * option term)].
  
  It is of length equals to [an; ... ; a1; fixk; ... ; fix1] for [fixi]
  where i ∈ [1,k], and the recursive argument of [fixi] is the n-th (ie. a_n, dB 0).
*)
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
(* YJ: again, the shape is [recarg; ... ; arg1; fixk; ... fix1]
so [rel_min_fix] being [1+recarg_pos] makes sense.
*)
(* Counterpart: [make_renv] *)
Definition init_guard_env Γ recarg tree :=
  {| 
    loc_env := Γ;
    (** Rel 0 -> recursive argument, YJ: due to ind_of_mutfix
       Rel recarg -> first "proper" (non-recursive) argument,
       Rel (S recarg) -> last fixpoint in this block YJ: look at check_fix
    *)
    rel_min_fix := S recarg;
    guarded_env := [Subterm Natset.empty Large tree] 
    (* YJ : the single element corresponds to the head of [loc_env], ie the recursive argument *)
  |}.

(** Push a binder with name [na], type [type] and subterm specification [spec] *)
Definition push_var G '(na, type, spec) := 
  {|
    loc_env := G.(loc_env) ,, vass na type;
    rel_min_fix := S (G.(rel_min_fix));
    guarded_env := spec :: G.(guarded_env);
  |}.

Definition push_let G '(na, c, type, spec) := 
  {|
    loc_env := G.(loc_env) ,, vdef na c type;
    rel_min_fix := S (G.(rel_min_fix));
    guarded_env := spec :: G.(guarded_env);
  |}.

(** add a new inner variable which is not a subterm *)
(* Shorthand, no counterpart *)
Definition push_var_nonrec G '(na, type) := 
  push_var G (na, type, Not_subterm).

(** Update the subterm spec of dB [i] to [new_spec] *)
(* Counterpart: [assign_var_spec] *)
Definition update_guard_spec G i new_spec := 
  {| 
    loc_env := G.(loc_env);
    rel_min_fix := G.(rel_min_fix);
    guarded_env := update_list G.(guarded_env) i new_spec 
  |}.

Definition push_var_guard_env G n na ty :=
  let spec := if Nat.leb 1 n then Internally_bound_subterm (Natset.singleton n) else Not_subterm in
  push_var G (na, ty, spec).

(** YJ: is it safe to None => Not_subterm since initialization yields
  G.guarded_env := [Subterm Large tree] ?
  - First thought: probably okay since we "split" the fixpoint s.t. recarg
    has dB index = 0. Any index greater than that is not a recarg for sure. *)
(** lookup subterm information for de Bruijn index [p] *)
(* Counterpart: [subterm_var] *)
Definition lookup_subterm G p := 
  match nth_error G.(guarded_env) p with 
  | Some spec => spec
  | None => Not_subterm
  end.

(** push a local context as [Not_subterm]s *)
(* Counterpart: [push_ctxt_renv] *)
Definition push_context_guard_env G Γ := 
  let n := length Γ in 
  {| 
    loc_env := G.(loc_env) ,,, Γ ;
    rel_min_fix := G.(rel_min_fix) + n;
    guarded_env := Nat.iter n (fun acc => Not_subterm :: acc) G.(guarded_env);
  |}. 

(** push fixes to the guard env as [Not_subterm]s *)
(* Counterpart: [push_fix_renv] *)
Definition push_fix_guard_env G (mfix : mfixpoint term) := 
  let n := length mfix in
  {|
    loc_env := push_assumptions_context (map dname mfix, map dtype mfix) G.(loc_env);
    rel_min_fix := G.(rel_min_fix) + n;
    guarded_env := Nat.iter n (fun acc => Not_subterm :: acc) G.(guarded_env);
  |}.


(** ** Stack for commutative β-ι-cuts *)
(** A stack is used to maintain subterm information for elements which are (morally) applied to the term currently under observation, and which would really be applied if we could fully reduce with concrete values. 
  [SClosure] is used for efficiency reasons: we don't want to compute subterm information for everything, so this is done on demand. It thus captures the term and the guardedness environment it's in.
  [SArg] represents subterm information for a term for which we actually have computed that information. *)
(** This is used to simulate commutative cuts (commutation of β-ι-redexes):
  1) Consider
    <<
      match ... with 
      | 0 => fun t => ...
      | S n => fun t => ...
      end k
    >>
    Morally, this is the same as
    <<
      match ... with 
      | 0 => ... [k/t]
      | S n => ... [k/t]
      end 
    >>

    This commutation is implemented using the stack: (the subterm info of) k is put on the stack when checking the match branches.

  2) Moreover, this can also be used in the other direction:
    <<
      f (match ... with | 0 => ... | S n => ... end)
    >>
    is morally the same as 
    << match ... with | 0 => f ... | S n => f ... end)
  
    This morally justifies why matches can be treated as subterms when all branches are subterms.
*)
(** Note however that NOT all subterm information is allowed to flow through matches like that, see the functions below. 
  Namely, particular restrictions need to apply based on the return-type function:

  1) When subterm information is flowing into matches (case 1 above), a check is implemented by [filter_stack_domain].
    Essentially, the following restriction applies:

    Assuming that the return-type function has the shape 
        [λ (x1) (x2) .... (xn). B]
    * If it is not dependent, i.e. B does not contain x1 through xn, then no restrictions apply.
    * If [B = ∀ (y1:T1) ... (ym :Tm). T]
      we allow the subterm information to the applicants corresponding to the yi to flow through, 
        IF the Ti has the shape 
         [Ti = ∀ z1 ... zk. IND t1 t2 ... tl]
        and IND is an inductive type.
        In that case, we infer an approximate recargs tree for IND applied to t1 .... tk and 
        intersect it with the subterm tree for yi on the stack. 
      All other subterm information is truncated to Not_subterm. 

  2) When subterm information is flowing out of matches (case 2 above), a check is implemented by [restrict_spec_for_match].
  Essentially, the following restriction applies:
    Assume the return-type function has the shape [λ (x1 : T1) ... (xn : Tn). B]. 
    * If it is not dependent, i.e. x1 through xn do not appear in B, then no restrictions apply.
    * If it is dependent and 
      [B = ∀ y1 ... ym. I t1 ... tk]
      and I is an inductive, 
      then subterm information is allowed to propagate. The subterm tree is intersected with the one for [I] computed by [get_recargs_approx].
 
*)
(**
  Lacking restrictions to the information allowed to pass through matches in this way were cause for a soundness bug in 2013.
  See https://sympa.inria.fr/sympa/arc/coq-club/2013-12/msg00119.html.
*)

Inductive fix_check_result :=
  | NeedReduce (Γ : context) (e : fix_guard_error)
  | NoNeedReduce.

Inductive stack_element := 
  (* Arguments in the evaluation stack.
    [t] is typed in [G]
    [nbinders] is the number of binders added in the current env on top of [G.genv]
    TODO [r] denotes if reduction is needed.
    *)
  | SClosure (r : fix_check_result) G (nbinders : nat) (t : term)
  (* arguments applied to a "match": only their spec flows through the match *)
  | SArg (s : subterm_spec). 

(** Print stack elements *)
Definition print_stack_element Σ z := 
  match z with 
  (** TODO *)
  | SClosure _ G _ t => "SClosure " ++ "G" ++ (print_term Σ (ctx_names G.(loc_env)) true t) (* NOTE omitting G *)
  | SArg s => "SArg " ++ print_subterm_spec Σ s
  end.

Definition fix_check_result_or (x y : fix_check_result) := match x with
  | NeedReduce _ _ => x
  | NoNeedReduce => y
end.

Notation "x ||| y" := (fix_check_result_or x y).

Fixpoint needreduce_of_stack (stack : list stack_element) : fix_check_result :=
  match stack with
    | []                               => NoNeedReduce
    | (SArg _)                    :: l => needreduce_of_stack l
    | (SClosure needreduce _ _ _) :: l => needreduce ||| needreduce_of_stack l
  end. 

Definition redex_level := List.length.
Arguments redex_level {A} _.

Definition push_stack_closure G needreduce t stack := 
  (SClosure needreduce G 0 t) :: stack.

(** Push a list of closures [l] with guard env [G] to the stack, [NoNeedReduce] by default *)
Definition push_stack_closures G l stack := 
  List.fold_right (push_stack_closure G NoNeedReduce) l stack. 

(** Push a list of args [l] to the stack *)
Definition push_stack_args l stack := 
  List.fold_right (fun spec stack => SArg spec :: stack) stack l. 

(** Lift the elements in stack by k. *)
Definition lift_stack_element (k : nat) (elt : stack_element) : stack_element :=
  match elt with
    | SClosure needreduce s n c => SClosure needreduce s (n+k) c
    | _                         => elt
  end.

Definition lift_stack (k : nat) := List.map (lift_stack_element k).


(** Check that the recarg [r] is an [Mrec] or [Imbr] node with [ind]. *)
(* Counterpart: [match_inductive] *)
Definition match_recarg_inductive (ind : inductive) (r : recarg) := 
  match r with
  | Mrec (RecArgInd i) => i == ind
  | Norec | Mrec (RecArgPrim _) => false
  end.

(** ** Building recargs trees *)

(** Given the subterm spec of the discriminant, compute the subterm specs for the binders bound by the branches of the match. *)
(** In [match c as z in ci y_s return P with |C_i x_s => t end]
   [branches_specif Σ G c_spec ind] returns a list of [x_s]'s specs knowing
   [c_spec].  [ind] is the inductive we match on. *)
(** Complexity: Quadratic in the number of constructors of [ind] due to calling the linear [wf_paths_constr_args_sizes] every iteration. *)
Definition branches_binders_specif Σ G (discriminant_spec : subterm_spec) (ind : inductive) : exc list (list subterm_spec) := 
  (** get the arities of the constructors (without lets, without parameters) *)
  constr_arities <- (
    '(_, oib) <- lookup_mind_specif Σ ind;;
    ret $ map cstr_arity oib.(ind_ctors));;
  unwrap $ mapi (fun i (ar : nat) => 
    match discriminant_spec return exc (list subterm_spec) with 
    | Subterm _ _ tree => 
      (** check if the tree refers to the same inductive as we are matching on *)
        (** get the root node (Norec, Mrec etc) of the recarg tree of the discriminant, which cannot be Empty. *)
        recarg_info <- except (OtherErr "branches_binders_specif" "malformed tree") $ destruct_recarg tree;;
        if negb (match_recarg_inductive ind recarg_info) then
          (** the tree talks about a different inductive than we are matching on, so all the constructor's arguments cannot be subterms  *)
          (** in principle, the only place that calls [branches_binders_specif] is [subterm_specif] when specifying a [tCase].
            In that case, the [ind] argument is given by the type of discriminant,
            so it shouldn't differ from that contained in [discriminant_spec] *)
          ret $ tabulate (fun _ => Not_subterm) ar (** TODO: should throw error instead? ProgrammingError? *)
        else 
          (** get trees for the arguments of the i-th constructor *)
          (** YJ: perhaps too much work, just need to map on the i-th branch
            instead of all constructors? 
            
            Also "size" here means "tree". Idk why the ambiguity :/ *)
          args_sizes <- wf_paths_constr_args_sizes tree i;; (* list (list wf_paths) *)
          (** this should hopefully be long enough and agree with the arity of the constructor *)
          assert (length args_sizes == ar) (OtherErr "branches_binders_specif" "number of constructor arguments don't agree");;
          (** for each arg of the constructor: generate a strict subterm spec if
            they are recursive, otherwise Not_subterm.  The generated spec also
            contains the recursive tree for that argument to enable nested matches. *)
          trees <- unwrap $ map spec_of_tree args_sizes;;
          ret trees
    (* for the other cases, just propagate the discriminant_spec *)
    | Dead_code | Not_subterm | Internally_bound_subterm _ =>
        ret $ tabulate (fun _ => discriminant_spec) ar
    end
    ) constr_arities.

(** A reimplementation of [branches_binders_specif] that is linear. *)
Definition branches_specif Σ G (discriminant_spec : subterm_spec) (ind : inductive) : exc list (list subterm_spec) := 
  (** get the arities of the constructors (without lets, without parameters) *)
  constr_arities <- (
    '(_, oib) <- lookup_mind_specif Σ ind;;
    ret $ map cstr_arity oib.(ind_ctors));;
  (** if discriminant is a subterm, return a [exc (list (list wf_paths))], otherwise a [exc subterm_spec] *)
  all_constr_args_sizes <- match discriminant_spec return exc (list (list wf_paths) + subterm_spec) with 
    | Subterm _ _ tree => 
      (** check if the tree refers to the same inductive as we are matching on *)
        (** get the root node (Norec, Mrec etc) of the recarg tree of the discriminant, which cannot be Empty. *)
        recarg_info <- except (OtherErr "branches_binders_specif" "malformed tree") $ destruct_recarg tree;;
        if negb (match_recarg_inductive ind recarg_info) then
          (** the tree talks about a different inductive than we are matching on, so all the constructor's arguments cannot be subterms  *)
          (** in principle, the only place that calls [branches_binders_specif] is [subterm_specif] when specifying a [tCase].
            In that case, the [ind] argument is given by the type of discriminant,
            so it shouldn't differ from that contained in [discriminant_spec] *)
          ret $ inr Not_subterm 
        else 
          (** get trees for the arguments of the i-th constructor *)
           trees <- wf_paths_all_constr_args_sizes tree;; (* list (list wf_paths) *)
          ret $ inl trees
    (* for the other cases, just propagate the discriminant_spec *)
    | Dead_code | Not_subterm | Internally_bound_subterm _ => ret $ inr discriminant_spec
    end;;
  res <- match all_constr_args_sizes with
    | inr spec =>
        ret $ map (fun ar => (repeat spec ar)) constr_arities
    | inl all_constr_args_sizes =>
        unwrap $ mapi (fun i (ar : nat) => 
          args_sizes <- except (IndexErr "branches_binders_specif" "no tree for constructor" i) $ nth_error all_constr_args_sizes i;; (* list (wf_paths) *)
          assert (length args_sizes == ar) (OtherErr "branches_binders_specif" "number of constructor arguments don't agree");;
          trees <- unwrap $ map spec_of_tree args_sizes;;
          ret trees
          ) constr_arities
    end;;
  ret res.

Definition check_inductive_codomain := has_inductive_codomain.

(** In some cases, we need to restrict the subterm information flowing through a dependent match, see the explanation above.
  In this case, we calculate an approximation of the recargs tree and intersect with it. 

  This code is conceptually quite similar to the positivity checker.
*)
(* TODO: I don't know at this point how the recargs tree calculated in the following differs from the one we already have statically computed -- for most purposes it seems to be identical (?) 
*)

(** To construct the recargs tree, the code makes use of [ra_env : list (recarg * wf_paths)], a de Bruijn context containing the recursive tree and the inductive for elements of an (instantiated) inductive type, and [(Norec, mk_norec)] for elements of non-inductive type.  

  Importantly, the recargs tree (of type wf_paths) may make references to other elements in the [ra_env] (via the [Param] constructor).
*)

Definition ienv := context * list (recarg * wf_paths).

Open Scope list.

Definition ienv_push_var '(Γ, ra_env) kn ty ra : ienv := ((Γ ,, vass kn ty) , ((Norec, ra) :: ra_env)).

Definition ienv_push_inductive Σ '(Γ, ra_env) ind (pars : list term) : exc ienv := 
  (** Add the types of inner mutual inductives to a recargs environment. This is used in the context of nested inductives.
    Specifically, for the j-th inductive in the block, we add [(Imbr $ mkInd ind_kn j, Param 0 j)], i.e. an inner inductive with a direct recursive reference to the j-th inductive in the block. 
    The rest of the env is lifted accordingly.
    *)
  let ra_env_push_inner_inductives_with_params ntypes : list (recarg × wf_paths) := 
    (** make inner inductive types (Imbr in the tree) with recursive references for the individual types *)
    let rc := rev $ mapi (fun i t => (Mrec (RecArgInd (mkInd ind.(inductive_mind) i)), t)) 
                        (mk_rec_calls (X := recarg) ntypes) in
    (** lift the existing ra_env *)
    let ra_env' := map (fun '(r, t) => (r, rtree_lift ntypes t)) ra_env in
    rc ++ ra_env' 
  in

  (** Add the types of mutual inductives as assumptions to the local context (the first inductive body at dB 0)
    The inductive types are instantiated with the (uniform) parameters in [pars]. 
  *)
  '(mib, oib) <- lookup_mind_specif Σ ind;;
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
  Γ' <- List.fold_right (fun i acc => acc <- acc;; push_ind i acc) (ret Γ) mib.(ind_bodies);;
  let ra_env' := ra_env_push_inner_inductives_with_params num_bodies in
  ret (Γ', ra_env').

(** Move the first [n] prods of [c] into the context as elements of non-recursive type. *)
Fixpoint ienv_decompose_prod Σ ienv n (c : term) {struct n} : exc (context * list (recarg * wf_paths) * term) :=
  let '(Γ, ra_env) := ienv in
  match n with 
  | 0 => ret (ienv, c)
  | S n => 
    c_whd <- whd_all Σ Γ c;;
    match c_whd with
    | tProd na ty body =>
      let Γ' := Γ ,, vass na ty in 
      let ra_env' := (Norec, mk_norec) :: ra_env in
      ienv_decompose_prod Σ (Γ', ra_env') n body
    | _ => raise (OtherErr "ra_env_decompose_prod" "not enough prods") 
    end
  end.

(** TODO: missing [abstract_mind_lc]. *)

Definition is_primitive_positive_container Σ c :=
  match Retroknowledge.retro_array Σ.(retroknowledge) with
  | Some c' => c == c'
  | None => false
  end.

(** Create the recursive tree for a nested inductive [ind] applied to arguments [args]. *)
(** In particular: starting from the tree [tree], we instantiate parameters suitably (with [args]) to handle nested inductives. *)
(** [tree] is used to decide when to traverse nested inductives. *)
(** [ra_env] is used to keep track of the subterm information of dB variables. 
   It need not bind all variables occurring in [t]: to unbound indices, we implicitly assign [Norec].*)
#[bypass_check(guard)]
Fixpoint build_recargs_nested Σ ρ ienv (tree : wf_paths) (ind: inductive) (args: list term) {struct args}: exc wf_paths := 
  (** if the tree [tree] already disallows recursion, we don't need to go further *)
  if equal_wf_paths tree mk_norec : bool then ret tree else (
  let '(Γ, ra_env) := ienv in
  '(mib, oib) <- lookup_mind_specif Σ ind;;
  static_trees <- except (OtherErr "build_recargs_nested" "lookup_paths failed")$ lookup_paths_all ρ ind;;
  (** determine number of (non-) uniform parameters *)
  let num_unif_params := num_uniform_params mib in (* Counterpart: [auxnpar] *)
  let num_non_unif_params := mib.(ind_npars) - num_unif_params in (* Counterpart: [nonrecpar] *)
  (** get the instantiations for the uniform parameters *)
  (** Note that in Coq, all parameters after the first non-uniform parameter are treated as non-uniform -- thus we can just take a prefix of the list *)
  let inst_unif := firstn num_unif_params args in (* Counterpart: [lpar] *)
  let num_mut_inds := length mib.(ind_bodies) in (* Counterpart: [auxntyp] *)
  (** extend the environment with the inductive definitions applied to the parameters *)
  (** do the same for the ra environment: 
    for the j-th inductive, the recarg is Mrec (RecArgPrim) (for the container), the trees are direct recursive references [Param 0 j] *)
  ienv' <- ienv_push_inductive Σ (Γ, ra_env) ind inst_unif;;
  let '(Γ', ra_env') := ienv' in

  (** lift the parameters we instantiate with by the number of types: 
    the dB layout we setup is: 
        [inductive types defined in the container of the nested ind], [the environment the parameters are assuming]
    Since we insert the inductive types when we use the parameters to instantiate the recargs tree, we thus have to lift the parameters by the number of mutual types of the container.
  *)
  let inst_unif_lifted := map (lift0 num_mut_inds) inst_unif in (* Counterpart: [lpar'] *)

  (** In case of mutual inductive types, we use the recargs tree which was
    computed statically. This is fine because nested inductive types with
    mutually recursive containers are not supported -- meaning we need not instantiate in that case. 
    In the case that there are no mutual inductives, we use the argument tree [tree].*)
  trees <- (if num_mut_inds == 1 
    then arg_sizes <- wf_paths_all_constr_args_sizes tree;; ret [arg_sizes]
    else unwrap $ map wf_paths_all_constr_args_sizes static_trees);;

  (** function: make the recargs tree for the [j]-th inductive in the block with body [oib].
    Essentially, we instantiate the corresponding recargs tree in [trees] with the parameters in [inst_unif]. *)
  let mk_ind_recargs (j : nat) (oib : one_inductive_body) : exc wf_paths :=
    (** get constructor types (with parameters), assuming that the mutual inductives are at [0]...[num_mut_inds-1]*)
    let constrs := map cstr_type oib.(ind_ctors) in
    (** abstract the parameters of the recursive occurrences of the inductive type in the constructor types *)
    (** we assume that at indices [0]... [num_mut_inds-1], the inductive types are instantiated _with_ the parameters *)
    let abstracted_constrs := abstract_params_mind_constrs num_mut_inds num_unif_params constrs in
    (** build the trees for the constructors, instantiated with the uniform parameters [inst_unif] *) 
    paths <- unwrap $ mapi (fun k c => (* [k]-th constructor with abstracted type [c] *)
        (** instantiate the abstracted constructor types with the parameters we are interested in. *)
        c_inst <- hnf_prod_apps Σ Γ' c inst_unif_lifted;;
        (** move non-uniform parameters into the context *) 
        '(Γ', ra_env', c') <- ienv_decompose_prod Σ ienv' num_non_unif_params c_inst;;
        (** first fetch the trees for this constructor  *)
        constr_trees <- except (IndexErr "build_recargs_nested/mk_ind_recargs" "no tree for inductive" j) $ 
          nth_error trees j;;
        arg_trees <- except (IndexErr "build_recargs_nested/mk_ind_recargs" "no tree for constructor" k) $ 
          nth_error constr_trees k;; 
        (** recursively build the trees for the constructor's arguments, potentially traversing nested inductives *)
        build_recargs_constructors Σ ρ (Γ',ra_env') arg_trees c'
      ) abstracted_constrs;;
      (** make the tree for this nested inductive *)
      ret $ mk_ind_paths (Mrec (RecArgInd (mkInd ind.(inductive_mind) j))) paths
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
with build_recargs Σ ρ ienv (tree : wf_paths) (t : term) {struct t}: exc wf_paths := 
  let '(Γ, ra_env) := ienv in
  t_whd <- whd_all Σ Γ t;;
  let '(x, args) := decompose_app t_whd in
  match x with 
  | tProd na type body => 
      (** simply enter the prod, adding the quantified element as assumption of non-recursive type (even though the type may in fact be inductive, for the purpose of determining the recargs tree of [t], this is irrelevant)*)
      assert (args == []) (OtherErr "build_recargs" "tProd case: term is ill-typed");;
      build_recargs Σ ρ (ienv_push_var ienv na type mk_norec) tree body
  | tRel k => 
      (** free variables are allowed and assigned Norec *)
      catchE (k_ra <- except (OtherErr "" "") $ nth_error ra_env k;; ret (snd k_ra)) 
            (fun _ => ret mk_norec)
  | tInd ind _ => 
    (** if the given tree for [t] allows it (i.e. has an inductive as label at the root), we traverse a nested inductive *)
    match destruct_recarg tree with 
    | None => raise $ OtherErr "build_recargs" "tInd case: malformed recargs tree"
    | Some (Mrec (RecArgInd ind')) => 
        if ind == ind' then build_recargs_nested Σ ρ ienv tree ind args 
                       else ret mk_norec
    | Some (Norec) | Some (Mrec (RecArgPrim _)) => ret mk_norec 
    end
  | tConst c _ => if is_primitive_positive_container Σ c then ret mk_norec
      else match destruct_recarg tree with 
      | None => raise $ OtherErr "build_recargs" "tInd case: malformed recargs tree"
      | Some (Mrec (RecArgPrim c')) => 
          if c == c' then build_recargs_nested_primitive Σ ρ ienv tree c args 
                      else ret mk_norec
      | Some (Norec) | Some (Mrec (RecArgInd _)) => ret mk_norec 
      end
  | _ => ret mk_norec
  end


with build_recargs_nested_primitive Σ ρ (ienv : ienv) tree (c : kername) (args : list term) {struct tree} : exc wf_paths :=
  if eq_wf_paths tree mk_norec then ret tree
  else
  let '(Γ, ra_env) := ienv in
  let ntypes := 1 in (* Primitive types are modelled by non-mutual inductive types *)
  let ra_env' : list (recarg * wf_paths) := map (fun '(r, t) => (r, rtree_lift ntypes t)) ra_env in
  let ienv' : context * list (recarg * wf_paths) := (Γ, ra_env') in
  constr_sizes <- wf_paths_constr_args_sizes tree 0;; (* list wf_paths *)
  paths <- unwrap $ map2 (build_recargs Σ ρ ienv') constr_sizes args;;
  recargs <- except (OtherErr "build_recargs_nested_primitive" "calling hd on an empty list")
                    (mk_rec [mk_node (Mrec (RecArgPrim c)) paths]);;
  except (OtherErr "build_recargs_nested_primitive" "calling hd on an empty list") $ hd recargs
  

(** [build_recargs_constructors Σ Γ ra_env trees c] builds a list of each of the constructor [c]'s argument's recursive structures, instantiating nested inductives suitably.  
  We assume that [c] excludes parameters -- these should already be contained in the environment. 

  [trees] is a list of trees for the constructor's argument types, used to determine when to traverse nested inductive types.

  [ra_env] is used to keep track of the recursive trees of dB variables. 
   It need not bind all variables occurring in [t]: to unbound indices, we implicitly assign [Norec] with a trivial recursive tree.
*)
with build_recargs_constructors Σ ρ ienv (trees : list wf_paths) (c : term) {struct c}: exc (list wf_paths) := 
  let '(Γ, ra_env) := ienv in
  let recargs_constr_rec := fix recargs_constr_rec ienv (trees : list wf_paths) (lrec :list wf_paths) (c : term) {struct c} : exc (list wf_paths) := 
    c_whd <- whd_all Σ Γ c;;
    let '(x, args) := decompose_app c_whd in
    match x with 
    | tProd na type body => 
        (* the constructor has an argument of type [type] *)
        assert (args == []) (OtherErr "build_recargs_constructors" "tProd case: ill-typed term");;
        (* compute the recursive structure of [type] *)
        first_tree <- except (ProgrammingErr "build_recargs_constructors" "trees is too short") $
          hd trees;;
        rec_tree <- build_recargs Σ ρ ienv first_tree type;;
        (* [na] of type [type] can be assumed to be of non-recursive type for this purpose *)
        let Γ' := Γ ,, vass na type in
        let ra_env' := (Norec, mk_norec) :: ra_env in 
        (* process the rest of the constructor type *)
        rest_trees <- except (OtherErr "build_recargs_constructors" "trees list too short") $ 
          tl trees;;
        recargs_constr_rec (Γ',ra_env') rest_trees (rec_tree :: lrec) body
    | _ => 
        (* we have processed all the arguments of the constructor -- reverse to get a valid dB-indexed context *)
        ret $ rev lrec  
    end
  in recargs_constr_rec (Γ,ra_env) trees [] c. 


(** [get_recargs_approx env tree ind args] builds an approximation of the recargs
tree for [ind], knowing [args] that are applied to it. 
The argument [tree] is used to know when candidate nested types should be traversed, pruning the tree otherwise. *)
(* TODO: figure out in which cases with nested inductives this isn't actually the identity *)
Definition get_recargs_approx Σ ρ Γ (tree : wf_paths) (ind : inductive) (args : list term) : exc wf_paths := 
  (* starting with ra_env = [] seems safe because any unbound tRel will be assigned Norec *)
  build_recargs_nested Σ ρ (Γ,[]) tree ind args.


(** [restrict_spec_for_match Σ Γ spec rtf] restricts the size information in [spec] to what is allowed to flow through a match with return-type function (aka predicate) [rtf] in environment (Σ, Γ). *)
(** [spec] is the glb of the subterm specs of the match branches. 
    This is relevant for cases where we go into recursion with the result of a match.
*)
(** 
  Assume the return-type function has the shape [λ (x1 : T1) ... (xn : Tn). B]. 
 * If it is not dependent, i.e. x1 through xn do not appear in B, then no restrictions apply.
 * If it is dependent and 
    [B = ∀ y1 ... ym. I t1 ... tk]
    and I is an inductive, 
    then subterm information is allowed to propagate. The subterm tree is intersected with the one for [I] computed by [get_recargs_approx].
 *)
(* TODO: how does get_recargs_approx play into this?*)
Definition restrict_spec_for_match Σ ρ Γ spec (rtf : term) : exc subterm_spec := 
  match spec with
  | Not_subterm | Internally_bound_subterm _ => ret spec
  | _ => 
    '(rtf_context, rtf) <- decompose_lam_assum Σ Γ rtf;;
    (* if the return-type function is not dependent, no restriction is needed *)
    if negb(rel_range_occurs 1 (length rtf_context) rtf) then ret spec 
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
          | Subterm l size tree => 
              (** intersect with approximation obtained by unfolding *)
              (* TODO: when does get_recargs_approx actually do something other than identity? *)
              recargs <- get_recargs_approx Σ ρ Γ tree ind args;;
              recargs <- except (OtherErr "restrict_spec_for_match" "intersection failed: empty") $ inter_wf_paths tree recargs;;
              ret (Subterm l size recargs)
          | _ => (** we already caught this case above *)
              raise $ OtherErr "restrict_spec_for_match" "this should not be reachable" 
          end
      | _ => ret Not_subterm
      end
    end.


(** ** Checking fixpoints *)



(** [subterm_specif Σ G stack t] computes the recursive structure of [t] applied to arguments with the subterm structures given by the [stack]. 
  [G] collects subterm information about variables which are in scope. 
*)
#[bypass_check(guard)]
Fixpoint subterm_specif Σ ρ G (stack : list stack_element) t {struct t}: exc subterm_spec:= 
  t_whd <- whd_all Σ G.(loc_env) t;;
  let '(f, l) := decompose_app t_whd in 
  match f with 
  | tRel k => 
      (** we abstract from applications: if [t] is a subterm, then also [t] applied to [l] is a subterm *)
      (*trace ("subterm_specif : tRel :: is subterm " ++ bruijn_print Σ G.(loc_env) t_whd);;*)
      ret $ lookup_subterm G k
  | tCase ind_relev rtf discriminant branches =>
    (* YJ: [ind] is the inductive type we are matching on *)
      let ind := ind_relev.(ci_ind) in
      (** push l to the stack *)
      let stack' := push_stack_closures G stack l in
      (** get subterm info for the discriminant *)
      discriminant_spec <- subterm_specif Σ ρ G [] discriminant;;
      (** get subterm info for the binders in the constructor branches of the discriminant.
        use [branches_binder_specif] for the original, (arguably) equivalent implementation *)
      branches_binders_specs <- branches_specif Σ G discriminant_spec ind;;
      (** determine subterm info for the full branches *)
      (** YJ: why mapi on [map snd branches] instead of map on [branches]?
        maybe there is a deep meaning (eg. (fst branch) means something else,
        also, its existence in AST seems redundant too. Probably I am missing
        some detail.)
        
        There are two "branches" here. One is the constructor branches of the
        (wf_path tree of) inductive type; the other being branches of the
        match body, named [branches] here. These two SHOULD correspond perfectly.
        Call them ctr_branch and match_branch respectively.

        We then iterate through [match_branch]es. They should be sorted according
        to the order of the [ctr_branch]es by the parser/constructor. To do
        [subterm_specif] on a particular branch, you need to know the [binder_specif]
        for that [ctr_branch]. For example,
        
        <<
        match n with 0 => 0 | S n' => [body] end
        >>
        
        to check the second branch, [body], one needs to know that [n'] binds a
        subterm. This is the purpose of the line above - to generate a spec of
        [
          [], [Strict Subterm [tree_of_nat]]
        ]
        before checking [body].
        *)
      branches_specs <- unwrap $ mapi (fun i branch => 
        binder_specs <- except (IndexErr "subterm_specif" "branches_binders_specif result is too short" i) $ 
          nth_error branches_binders_specs i;;
        (* we push this to the stack, not directly to the guard env, because we haven't entered the lambdas introducing this branch's binders yet *)
        let stack_br := push_stack_args binder_specs stack' in
        subterm_specif Σ ρ G stack_br branch) (map bbody branches);;
      (** YJ: first guess: now we have a [subterm_spec] for each match_branch.
        Now the case is a strict subterm if every branch is a strict subterm.
        If one is loose, then the result is loose.
        Therefore we see a partial order: strict >= loose >= not_subterm and we are taking glb.
        There comes the intuition!!
        Note that in Gimenez's paper, the linear order is reversed and one takes
        the "union" aka least upper bound instead, but they are isomorphic.
      *)
      (** take their glb -- in case of no branches, this yields [Dead_code] (absurd elimination) *)
      spec <- subterm_spec_glb branches_specs;;
      (** restrict the subterm info according to the rtf *)
      restrict_spec_for_match Σ ρ G.(loc_env) spec rtf.(preturn) 
  | tFix mfix mfix_ind => 
      (*trace ("subterm_specif : tFix :: enter " ++ bruijn_print Σ G.(loc_env) t_whd);;*)
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
        rectree <- except (OtherErr "subterm_specif" "lookup_paths failed") $ lookup_paths ρ ind;;
        (** push fixpoints to the guard env *)
        let G' := push_fix_guard_env G mfix in
        (** we let the current fixpoint be a strict subterm *)
        (* TODO: is this sound? why is it needed? nested fixes? *)
        let G' := update_guard_spec G' (num_fixes - mfix_ind) (Subterm Natset.empty Strict rectree) in
        let decreasing_arg := cur_fix.(rarg) in
        let body := cur_fix.(dbody) in 
        (** number of abstractions (including the one for the decreasing arg) that the body is under *)
        let num_abstractions := S decreasing_arg in
        (** split into context up to (including) the decreasing arg and the rest of the body *)
        '(context, body') <- decompose_lam_n_assum Σ G'.(loc_env) num_abstractions body;;
        (** push the arguments [l] _ in guard env [G] _ *)
        let stack' := push_stack_closures G stack l in
        (** add the arguments as Not_subterm *)
        let G'' := push_context_guard_env G' context in 
        (** before we go on to check the body: if there are enough arguments on the stack, 
          we can use the subterm information on the stack for the decreasing argument of 
          the nested fixpoint (instead of taking Not_subterm) *)
        (** we check the body with an empty stack as it isn't directly applied to something*)
        if Nat.ltb (length stack') num_abstractions then subterm_specif Σ ρ G'' [] body' else
          decreasing_arg_stackel <- except (IndexErr "subterm_specif" "stack' too short" decreasing_arg) $ 
            nth_error stack' decreasing_arg;;
          arg_spec <- stack_element_specif Σ ρ decreasing_arg_stackel;;
          let G'' := update_guard_spec G'' 1 arg_spec in 
          subterm_specif Σ ρ G'' [] body'
  | tLambda x ty body => 
      (* TODO *)
     (*raise (X := unit) (OtherErr "" (thunk t));;*)
     (*trace ("subterm_specif : tLambda :: enter " ++ bruijn_print Σ G.(loc_env) t_whd);;*)
     assert (l == []) (OtherErr "subterm_specif" "reduction is broken");;
     (** get the subterm spec of what the lambda would be applied to (or Not_subterm if [stack] is empty)*)
     '(spec, stack') <- extract_stack_hd Σ ρ stack;;
     subterm_specif Σ ρ (push_var G (x, ty, spec)) stack' body 
  | tEvar _ _ => 
      (* evars are okay *)
      ret Dead_code
      (* raise $ OtherErr "subterm_specif" "the guardedness checker does not handle evars" *)
  | tProj p t => 
      (** compute the spec for t *)
      (** TODO: why do we do this with the stack (instead of the empty stack)?
        shouldn't _the result_ of the projection be applied to the elements of the stack?? *)
      t_spec <- subterm_specif Σ ρ G stack t;;
      match t_spec with 
      | Subterm _ _ paths => 
          arg_trees <- wf_paths_constr_args_sizes paths 0;;
              (** get the tree of the projected argument *)
          let proj_arg := p.(proj_arg) in
          proj_arg_tree <- except (IndexErr "subterm_specif" "malformed recursive tree" proj_arg) $ 
            nth_error arg_trees proj_arg;;
            (** make a spec out of it *)
          spec_of_tree proj_arg_tree
      | Dead_code | Not_subterm | Internally_bound_subterm _ => ret t_spec
      end
  | _ => ret Not_subterm
  end

(** given a stack element, compute its subterm specification *)
with stack_element_specif Σ ρ stack_el {struct stack_el} : exc subterm_spec := 
  match stack_el with 
  | SClosure _ G _ t => 
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

Definition set_iota_specif (nr : nat) spec := match spec with
  | Not_subterm => if Nat.leb 1 nr then Internally_bound_subterm (Natset.singleton nr) else Not_subterm
  | spec => spec
  end.

Definition illegal_rec_call G fixpt elt := match elt with
  | SClosure _ G_arg _ arg =>
    let le_lt_vars :=
      let '(_, le_vars, lt_vars) :=
        List.fold_left (fun '(i, le, lt) sbt => match sbt with
          | Subterm _ Strict _ | Dead_code           => (S i, le,    i::lt)
          | Subterm _ Large _                        => (S i, i::le, lt)
          | Internally_bound_subterm _ | Not_subterm => (S i, le,    lt)
          end) G.(guarded_env) (1, [], [])
      in (le_vars, lt_vars)
    in RecursionOnIllegalTerm fixpt (G_arg.(loc_env), arg) le_lt_vars
  | SArg _ =>
    (* Typically the case of a recursive call encapsulated under a
       rewriting before been applied to the parameter of a constructor *)
    NotEnoughArgumentsForFixCall fixpt
  end.

Definition set_need_reduce_one Γ nr err rs := update_list rs (#|rs| - nr) (NeedReduce Γ err).

Definition set_need_reduce Γ l err rs := Natset.fold (fun n => set_need_reduce_one Γ n err) l rs.

Definition set_need_reduce_top Γ err rs := set_need_reduce_one Γ (List.length rs) err rs.

Inductive check_subterm_result :=
  | InvalidSubterm
  | NeedReduceSubterm (l : Natset.t). (* empty = NoNeedReduce *)

(** Check that a term [t] with subterm spec [spec] can be applied to a fixpoint whose recursive argument has subterm structure [tree]*)
Definition check_is_subterm spec tree := 
  match spec with 
  | Subterm need_reduce Strict tree' => 
      (* TODO: find an example where the inclusion checking is needed -- probably with nested inductives? *)
      if incl_wf_paths tree tree' then NeedReduceSubterm need_reduce
      else InvalidSubterm
  | Dead_code => 
      (** [spec] been constructed by elimination of an empty type, so this is fine *)
      NeedReduceSubterm Natset.empty
  | Not_subterm | Subterm _ Large _ => InvalidSubterm
  | Internally_bound_subterm l => NeedReduceSubterm l
  end.


 

(** We use this function to filter the subterm information for arguments applied to a match, stored in the [stack], to 
  what is allowed to flow through a match, obtaining the stack of subterm information for what would be applied to 
  the match branches after the match is reduced. 
  [rtf] is the return-type function of the match (aka the match predicate). 

  Assuming that the return-type function has the shape 
    [λ (x1) (x2) .... (xn). B]
  If it is not dependent, i.e. B does not contain x1 through xn, then no restrictions apply.
  If [B = ∀ (y1:T1) ... (ym :Tm). T]
  we allow the subterm information to the applicants corresponding to the yi to flow through, 
    IF the Ti has the shape 
      [Ti = ∀ z1 ... zk. IND t1 t2 ... tl]
    and IND is an inductive type.
    In that case, we infer an approximate recargs tree for IND applied to t1 .... tk and 
    intersect it with the subterm tree for yi on the stack. 
  All other subterm information is truncated to Not_subterm. 
*)
Definition filter_stack_domain Σ ρ Γ nr (rtf : term) (stack : list stack_element) : exc (list stack_element) := 
  '(rtf_context, rtf_body) <- decompose_lam_assum Σ Γ rtf;; 
  (** if the predicate is not dependent, no restriction is needed and we avoid building the recargs tree. *)
  if negb (rel_range_occurs 1 (length rtf_context) rtf_body) then ret stack 
  else
    (** enter the rtf context *)
    let Γ' := Γ ,,, rtf_context in
    let filter_stack := fix filter_stack Γ t stack : exc (list stack_element) := 
      t' <- whd_all Σ Γ t;;
      match stack, t' with 
      | elem :: stack', tProd na ty t0 => 
        (** the element [elem] in the stack would be applied to what corresponds to the [∀ na : ty, t0] in the rtf *)
        let d := vass na ty in 
        (** decompose the type [ty] of [na] *)
        '(ctx, ty) <- decompose_prod_assum Σ Γ ty;;
        let Γ' := Γ ,,, ctx in
        (** now in the context of the type *)
        whd_ty <- whd_all Σ Γ' ty;;
        (** decompose the rest of the type again and check if the LHS is an inductive *)
        let (ty', ty_args) := decompose_app whd_ty in
        (** compute what is allowed to flow through *)
        elem' <- match ty' with
          | tInd ind univ =>  
              (** it's an inductive *)
              (** inspect the corresponding subterm spec on the stack *)
              spec' <- stack_element_specif Σ ρ elem;;
              sarg <- match spec' with 
                | Not_subterm | Dead_code | Internally_bound_subterm _ => ret spec'
                | Subterm l s path => 
                    (** intersect with an approximation of the unfolded tree for [ind] *)
                    (* TODO : when does get_recargs_approx give something other than identity ? *)
                    recargs <- get_recargs_approx Σ ρ Γ path ind ty_args;;
                    path' <- except (OtherErr "filter_stack_domain" "intersection of trees failed: empty") $ inter_wf_paths path recargs;;
                    (* update the recargs tree to [path'] *)
                    ret (Subterm l s path') 
                end;;
              ret $ SArg sarg

          | _ => 
              (** if not an inductive, the subterm information is not propagated *) 
              ret $ SArg (set_iota_specif nr Not_subterm)
          end;;
        rest <- filter_stack (Γ ,, d) t0 stack';;
        ret (elem' :: rest)
      | _, _ => 
          (** the rest of the stack is restricted to No_subterm, subterm information is not allowed to flow through *)
          ret (List.fold_right (fun _ acc => SArg (set_iota_specif nr Not_subterm) :: acc) [] stack)
      end
    in filter_stack Γ' rtf_body stack.

#[bypass_check(guard)]
Definition find_uniform_parameters (recindxs : list nat) (nargs : nat) (bodies : list term) : nat :=
  let nbodies := List.length bodies in
  let min_indx := fold_left Nat.min recindxs nargs in
  (* We work only on the i-th body but are in the context of n bodies *)
  let fix aux (i k nuniformparams : nat) (c : term) {struct c} : nat :=
    let '(f, l) := decompose_app c in
    match f with
    | tRel n =>
      (* A recursive reference to the i-th body *)
      if n == (nbodies + k - i) then
        fold_left_i (fun j nuniformparams a =>
            match a with
            | tRel m => if m == (k - j) then
              (* a reference to the j-th parameter *)
              nuniformparams else Nat.min j nuniformparams
            | _ =>
              (* not a parameter: this puts a bound on the size of an extrudable prefix of uniform arguments *)
              Nat.min j nuniformparams
            end) l nuniformparams
      else nuniformparams
    | _ => fold_term_with_binders S (aux i) k nuniformparams c
    end
  in
  fold_left_i (fun i => aux i 0) bodies min_indx.

(** Given a fixpoint [fix f x y z n := phi(f x y u t, ..., f x y u' t')] structural recursive on [n],
    with [z] not uniform we build in context [x:A, y:B(x), z:C(x,y)] a term
    [fix f z n := phi(f u t, ..., f u' t')], say [psi], of some type
    [forall (z:C(x,y)) (n:I(x,y,z)), T(x,y,z,n)], so that
    [fun x y z => psi z] is of same type as the original term *)

Definition drop_uniform_parameters (nuniformparams : nat) (bodies : list term) : list term :=
  let nbodies : nat := #|bodies| in
  let fix aux (i k : nat) (c : term) {struct c} : term :=
    let '(f, l) := decompose_app c in
    match f with
    | tRel n =>
      (* A recursive reference to the i-th body *)
      if n == (nbodies + k - i) then
        let new_args := skipn nuniformparams l in
        mkApps f new_args
      else c
    | _ => map_with_binders (B := term) S (aux i) k c
    end
  in mapi (fun i => aux i 0) bodies.


Definition filter_fix_stack_domain (nr decrarg : nat) stack nuniformparams : list stack_element :=
  let fix aux (i nuniformparams : nat) stack :=
    match stack with
    | [] => []
    | a :: stack =>
      let '(uniform, nuniformparams') :=
        if Nat.eqb nuniformparams 0 then (false, 0) else (true, nuniformparams) in
      let a :=
        if uniform || Nat.eqb i decrarg then a
        else
          (* deactivate the status of non-uniform parameters since we
             cannot guarantee that they are preserve in the recursive
             calls *)
          SArg (set_iota_specif nr Not_subterm) in
      a :: aux (S i) nuniformparams' stack
    end
  in aux 0 nuniformparams stack.

Definition pop_argument Σ ρ needreduce G elt stack (x : aname) (a b : term)
  : exc (guard_env * list (stack_element) * term) :=
  match needreduce, elt with
  | NoNeedReduce, SClosure NoNeedReduce _ n c =>
    (* Neither function nor args have rec calls on internally bound variables *)
    spec <- stack_element_specif Σ ρ elt;;
    (* Thus, args do not a priori require to be rechecked, so we push a let *)
    (* maybe the body of the let will have to be locally expanded though, see Rel case *)
    ret (push_let G (x,lift0 n c,a,spec), lift_stack 1 stack, b)
  | _, SClosure _ _ n c =>
    (* Either function or args have rec call on internally bound variables *)
    ret (G, stack, subst10 (lift0 n c) b)
  | _, SArg spec =>
    (* Going down a case branch *)
    ret (push_var G (x,a,spec), lift_stack 1 stack, b)
  end.

(* TODO: typing judgement. probably useless, not sure *)
(* Definition judgment_of_fixpoint (_, types, bodies) :=
  Array.map2 (fun typ body -> { uj_val = body ; uj_type = typ }) types bodies *)

Definition bruijn_print Σ Γ t :=
  print_term Σ (ctx_names Γ) true t.


Unset Guard Checking. (* who checks the checkers? *)
Section CheckFix.
Context (Σ : global_env_ext) (ρ : pathsEnv).
Context (decreasing_args : list nat) (trees : list wf_paths).

(** 
  The main checker descending into the recursive structure of a term.
  Checks if [t] only makes valid recursive calls, with variables (and their subterm information) being tracked in the context [G].

  [stack] is the list of constructor's argument specification and arguments that
  will be applied after reduction.

  For example: for the term [(match .. with |.. => t end) u], [t] will be checked
  with (the subterm information of) [u] on the stack. This is needed as we (of course)
  might not be able to reduce the match, but still want to be able to reason
  about [t] being applied to [u] after reduction.
 
  [trees] is the list of recursive structures for the decreasing arguments of the mutual fixpoints.
  
  [decreasing_args] is the list of the recursive argument position of every mutual fixpoint. 
  [rs] is the stack of redexes traversed w/o having been triggered *)
Fixpoint check_rec_call_stack G (stack : list stack_element) (rs : list fix_check_result) (t : term) {struct t} : exc (list fix_check_result) := 
  (* possible optimisation: precompute [num_fixes] *)
  let num_fixes := #|decreasing_args| in 

  (** if [t] does not make recursive calls, then it is guarded: *)
  (* YJ: checks that no variable in [G.(rel_min_fix), G.(rel_min_fix)+num_fixes[
    is called in [t]. Ie none of fix1, ..., fixk is called in [t] where k = num_fixes *)
  (* if negb(rel_range_occurs G.(rel_min_fix) num_fixes t) then ret tt
  else  *)
  (* t_whd <- whd_βιζ Σ G.(loc_env) t;;
  (* FIXME: the guardedness checker will not be able to determine guardedness of this function since we wrap the match in there; thus l will not be determined as a subterm (as [] isn't) *)
  let (f, l) := decompose_app t_whd in   *)
  (** NOTE : I have annotated some of the cases with conditions on guardedness, but these are partially incomplete as the [stack] of 'virtually applied' arguments complicates verbal descriptions quite a bit. 
    The commented code is likely more informative. *)
  match t with 
  | tApp f args =>
      '(rs', stack') <- fold_right (fun arg rs_stack =>
          '(rs, stack) <- rs_stack ;;
          '(needreduce, rs') <- check_rec_call G rs arg ;;
          let stack' := push_stack_closure G needreduce arg stack in
          ret (rs', stack')) (ret (rs, stack)) args ;;
      check_rec_call_stack G stack' rs' f

  | tRel p =>
      (** check if [p] is a fixpoint (of the block of fixpoints we are currently checking),i.e. we are making a recursive call *)
      if (Nat.leb G.(rel_min_fix) p) && (Nat.ltb p (G.(rel_min_fix) + num_fixes)) then
        let rec_fixp_index := G.(rel_min_fix) + num_fixes - 1 - p in
        decreasing_arg <- except (IndexErr "check_rec_call" "invalid fixpoint index" rec_fixp_index) $ 
          nth_error decreasing_args rec_fixp_index;;
        let z_exc := except
          (IndexErr "check_rec_call" "not enough arguments for recursive fix call" decreasing_arg) $ 
          nth_error stack decreasing_arg
        in
        let g (z : stack_element) : exc (list fix_check_result) :=
          (** get the tree for the recursive argument type *)
          recarg_tree <- except
            (IndexErr "check_rec_call" "no tree for the recursive argument" rec_fixp_index)
            (nth_error trees rec_fixp_index);;
          z_tree <- stack_element_specif Σ ρ z;;
          subterm_spec <- check_is_subterm z_tree recarg_tree;;
          let guard_err : fix_guard_error := illegal_rec_call G decreasing_arg z in
          match subterm_spec with
            | NeedReduceSubterm l => ret (m := fun x => exc x) (set_need_reduce G.(loc_env) l guard_err rs)
            | InvalidSubterm => raise (GuardErr "check_rec_call" "recursion on non-subterm" guard_err)
          end
        in
        catchMap z_exc
          (fun _exc => ret $ set_need_reduce_top G.(loc_env) (NotEnoughArgumentsForFixCall decreasing_arg) rs)
          g
      else
        check_rec_call_state G NoNeedReduce stack rs (fun _ =>
          entry <- except (IndexErr "check_rec_call" "dB index out of range" p) $ nth_error G.(loc_env) p;;
          except (OtherErr "check_rec_call_stack :: tRel" "found assumption instead of definition") $ option_map (fun t => (lift0 p t, [])) entry.(decl_body)
        )
  (** Assume we are checking the fixpoint f. For checking [g a1 ... am] where
  <<
  g := match [discriminant]
      as [rtf.pcontext[0]]
      in [ind_nparams_relev.ci_ind]
      return [rtf.preturn]
    with 
      | C_i [branches[i].bcontext] -> [branches[i].bbody]
    end
  >>
  we need to fulfill the following conditions:
  1. f is guarded wrt the set of subterms S in a1 ... am
  2. f is guarded wrt the set of subterms S in the return-type [rtf]
  3. f is guarded wrt the set of subterms S in [discriminant]
  4. for each branch Ci xi1 ... xin => bi
      where S' := S ∪ { xij | the constructor Ci is recursive in the argument xij }:
    f is guarded with respect to S' in the branch body
    bi (virtually) applied to a1 ... am, where we restrict the subterm information of a1 ... am to 
    what is allowed to flow through the rtf (???)

  then f is guarded with respect to the set of subterms S in [g a1 ... am].
    (YJ: Taken from Eduardo's "Codifying guarded recursions" )
  *)
  | tCase ci ti discriminant branches => 
      '(needreduce_discr, rs) <- check_rec_call G rs discriminant ;;
      rs <- check_inert_subterm_rec_call G rs ti.(preturn) ;;
      (* compute the recarg info for the arguments of each branch *)
      let rs' := NoNeedReduce::rs in
      let nr := redex_level rs' in
      disc_spec <- (subterm_specif Σ ρ G [] discriminant) ;;
      case_spec <- branches_specif Σ G (set_iota_specif nr disc_spec) ci.(ci_ind);;
      stack' <- filter_stack_domain Σ ρ G.(loc_env) nr ti.(preturn) stack ;; 
      rs' <- fold_left_i (fun k rs' br' =>
          (* TODO: quadratic *)
          rs' <- rs' ;;
          spec <- except (IndexErr "check_rec_call_stack :: tCase" "not enough specs" k) $ nth_error case_spec k ;;
          let stack_br := push_stack_args spec stack' in
          check_rec_call_stack G stack_br rs' br') (map bbody branches) (ret rs') ;;
      needreduce_br <- except (IndexErr "check_rec_call_stack :: tCase" "" 0) $ hd rs' ;;
      rs <- except (IndexErr "check_rec_call_stack :: tCase" "" 0) $ tl rs' ;;
      check_rec_call_state G (needreduce_br ||| needreduce_discr) stack rs (fun _ =>
        (* we try hard to reduce the match away by looking for a
            constructor in c_0 (we unfold definitions too) *)
        discriminant <- whd_all Σ G.(loc_env) discriminant ;;
        let '(hd, args) := decompose_app discriminant in
        '(hd, args) <- match hd with
          | tCoFix cf idx =>
              cf' <- contract_cofix cf idx ;;
              hd' <- whd_all Σ G.(loc_env) (tApp cf' args) ;;
              ret $ decompose_app hd'
          | _ => ret (hd, args)
          end ;;
        match hd return exc (term * list stack_element) with
        | tConstruct ind idx _ =>
            c' <- apply_branch ind idx args ci branches ;;
            ret (c', [])
        | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _
        | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ =>
            raise $ OtherErr "check_rec_call_stack :: tCase" "whd_all is broken"
        | tRel _ | tVar _ | tConst _ _ | tApp _ _ | tCase _ _ _ _ | tFix _ _
        | tProj _ _ | tCast _ _ _ | tEvar _ _ =>
            raise NoReductionPossible
        end)


      (* let ind := .(ci_ind) in
      let nparams := ind_nparams_relev.(ci_npar) in
      catchE (
        (** check the arguments [l] it is applied to, the return-type function and the discriminant *)
        _ <- list_iter (check_rec_call' G []) l;;
        _ <- check_rec_call' G [] rtf.(preturn) ;;
        _ <- check_rec_call' G [] discriminant;;
        (** compute the recursive argument info for the binders of each branch by looking at the tree *)
        discriminant_spec <- subterm_specif Σ ρ G [] discriminant;; 
        case_branch_specs <- branches_binders_specif Σ G discriminant_spec ind;; 
        (** push arguments on stack *)
        let stack' := push_stack_closures G stack l in
        (** filter the stack to only contain the subterm info which is allowed to propagate through matches *)
        stack' <- filter_stack_domain Σ ρ G.(loc_env) rtf.(preturn) stack';;
        (** check the branches of the matches *)
        list_iteri (fun i '(mk_branch ctx branch) =>
            branch_spec <- except (IndexErr "check_rec_call" "branch specs too short" i) $ 
              nth_error case_branch_specs i;;
            (** push the rec arg specs for the binders introduced by the branch *)
            let stack_branch := push_stack_args stack' branch_spec in
            (** check the branch *)
            check_rec_call' G stack_branch branch) (* TODO YJ: probably this needs to use push_guard_env G with ctx *)
          branches
      )  
      (fun err => 
        (** if the checking goes wrong, we can still try harder by reducing the match away if possible *)
        discriminant <- whd_all Σ G.(loc_env) discriminant;;
        let '(hd, _) := decompose_app discriminant in
        match hd with 
        | tConstruct _ _ _ => 
            (*just check the whole thing again with the reduced discriminant *)
            check_rec_call_stack' G [] (mkApps (tCase ind_nparams_relev rtf discriminant branches) l)
        | _ => raise err
        end
      ) *)

  (** Assume we are checking the fixpoint f wrt the set of subterms S. 
      The arguments called on g, [l] = l1 ... lm
      This implements the following rule for checking the term [g l1 ... lm]:
      if - g = fix g (y1:T1)...(yp:Tp) {struct yp} := e, then the term
      [g l1 ... lm] is guarded wrt S if:
        1. f is guarded wrt the set of subterms S in l1 ... lm        
        2. f is guarded wrt the set of subterms S in T1 ... Tp        
        YJ: why is condition 3 necessary?
        3. lp, the recursive argument of g, is a sub-term of the recursive argument of f
          and f is guarded wrt the set of subterms S ∪ {yp} in e
          OR
          lp is *not* a sub-term of the recursive argument of f
          and f is guarded with respect to the set of subterms S in e
      then f is guarded with respect to the set of subterms S in (g l1 ... lm). 
      Eduardo 7/9/98 according to Bruno *)
  | tFix mfix_inner fix_ind => 
    (* | Fix ((recindxs,i),(_,typarray,bodies as recdef) as fix) -> *)
    f <- except (IndexErr "check_rec_call_stack" "not enough fixpoints" fix_ind) $ nth_error mfix_inner fix_ind ;;
    let decrArg := f.(rarg) in
    let nbodies := #|mfix_inner| in
    rs' <- fold_left (fun rs t =>
      rs <- rs ;;
      acc <- check_inert_subterm_rec_call G rs t ;;
      ret acc)
      (map dtype mfix_inner) (ret $ NoNeedReduce::rs)  ;;
    let G' := push_fix_guard_env G mfix_inner in
    let bodies := map dbody mfix_inner in
    let nuniformparams := find_uniform_parameters (map rarg mfix_inner) #|stack| bodies in
    let bodies := drop_uniform_parameters nuniformparams bodies in
    let fix_stack := filter_fix_stack_domain (redex_level rs) decrArg stack nuniformparams in
    let fix_stack := if Nat.ltb decrArg (List.length stack) then List.firstn (decrArg+1) fix_stack else fix_stack in
    let stack_this := lift_stack nbodies fix_stack in
    let stack_others := lift_stack nbodies (List.firstn nuniformparams fix_stack) in
    (* Check guard in the expanded fix *)
    rs' <- fold_left2_i (fun j rs' recindx body =>
        rs' <- rs' ;;
        let fix_stack := if fix_ind == j then stack_this else stack_others in
        check_nested_fix_body G' (S recindx) fix_stack rs' body)
      (map rarg mfix_inner) bodies (ret rs') ;;
    needreduce_fix <- except (IndexErr "check_rec_call_stack :: tFix" "" 0) $ hd rs' ;;
    rs <- except (IndexErr "check_rec_call_stack :: tFix" "" 0) $ tl rs' ;;
    let non_absorbed_stack := List.skipn nuniformparams stack in
    check_rec_call_state G needreduce_fix non_absorbed_stack rs (fun _ =>
      (* we try hard to reduce the fix away by looking for a
        constructor in [decrArg] (we unfold definitions too) *)
      if Nat.leb #|stack| decrArg then raise NoReductionPossible else
      decr_stack_elem <- except (IndexErr "check_rec_call_stack :: tFix" "" 0) $ nth_error stack decrArg ;;
      match decr_stack_elem with
      | SArg _ => raise NoReductionPossible (* A match on the way *)
      | SClosure _ _ n recArg =>
        c <- whd_all Σ G.(loc_env) (lift0 n recArg) ;;
        let '(hd, _) := decompose_app c in
        match hd with
        | tConstruct _ _ _ =>
            f' <- contract_fix mfix_inner fix_ind ;;
            ret (f', stack)
        | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _
        | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ =>
            raise $ OtherErr "check_rec_call_stack :: tCase" "whd_all is broken"
        | tRel _ | tVar _ | tConst _ _ | tApp _ _ | tCase _ _ _ _ | tFix _ _
        | tProj _ _ | tCast _ _ _ | tEvar _ _ =>
            raise $ NoReductionPossible
        end
      end)

      (* this_fix <- except (OtherErr "check_rec_call" "tFix: malformed fixpoint") $ nth_error mfix_inner fix_ind;;
      let decreasing_arg := rarg this_fix in 
      trace $ "check_rec_call : tFix :: " ++ (bruijn_print Σ G.(loc_env) t_whd);;
      catchE (
        (** 1. check args *)
        _ <- list_iter (check_rec_call' G []) l;;
        (** 2. check types *)
        _ <- list_iter (check_rec_call' G []) (mfix_types mfix_inner);;
        (** push arguments onto the stack *)
        let stack' := push_stack_closures G stack l in 
        (** update the env with the rec. (YJ: inner, ie g) fixes *)
        let G' := push_fix_guard_env G mfix_inner in 
        list_iteri (fun j body => 
          if (fix_ind == j) && Nat.ltb decreasing_arg (length stack') then
            (** we have subterm information for the decreasing arg on the stack *)
            rec_arg_stackel <- except (ProgrammingErr "check_rec_call" "should be unreachable") $ 
              nth_error stack' decreasing_arg;; 
            (** compute the subterm spec for the recursive argument *)
            rec_arg_spec <- stack_element_specif Σ ρ rec_arg_stackel;;
            (** 3. check the body of the fix after entering under the arguments and adding rec_arg_spec as the specification for [decreasing_arg] *)
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
          | _ => raise err          | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _
        | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ => assert false
        | tRel _ | tVar _ | tConst _ _ | tApp _ _ | tCase _ _ _ _ | tFix _ _
        | tProj _ _ | tCast _ _ _ | tEvar _ _ => None
        end
          end *)

  | tConst _ _ => ret rs
  (* | tConst kname univ => 
      check_rec_call_state G NoNeedReduce stack rs (fun tt =>
        if is_evaluable_const Σ kname then Some (get_const_value G.(loc_env) kname univ, [])
        else None) *)

  | tLambda x ty body =>
      (* let '(needreduce, rs) := check_rec_call G rs ty in *)
      res <- check_rec_call G rs ty ;;
      let '(needreduce, rs) := res in
      match stack with
      | elt :: stack =>
          '(renv, stack, body) <- pop_argument Σ ρ needreduce G elt stack x ty body ;;
          check_rec_call_stack G stack rs body
      | [] => check_rec_call_stack (push_var_guard_env G (redex_level rs) x ty) [] rs body
      end

      (*(** l is empty or reduction is broken *)
      _ <- assert (l == []) (OtherErr "check_rec_call" "tLambda : reduction is broken");;
      (** check the type *)
      check_rec_call' G [] ty;          | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _
        | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ => assert false
        | tRel _ | tVar _ | tConst _ _ | tApp _ _ | tCase _ _ _ _ | tFix _ _
        | tProj _ _ | tCast _ _ _ | tEvar _ _ => None
        end;
      (** we take the subterm spec at the head of the stack (corresponding to the element which will be applied to this lambda), or No_subterm if the stack is empty *)
      '(spec, stack') <- extract_stack_hd Σ ρ stack;;
      (** and check the body in the updated environment with the spec for this applied element *)
      check_rec_call' (push_guard_env G (x, ty, spec)) stack' body*)

  | tProd x ty body => 
      rs' <- check_inert_subterm_rec_call G rs ty ;;
      ret rs'
      (* check_rec_call_stack' (push_var G (redex_level rs) (x, ty)) [] rs' body *)

      (*(** the list [l] should be empty, otherwise the term is ill-typed *)
      _ <- assert (l == []) (OtherErr "check_rec_call" "tProd: input term is ill-typed");;
      (*TODO Coq doesn't like the following check *)
      (*_ <- assert (stack == []) "tProd: stack should be empty";;*)
      (** check the type *)
      check_rec_call' G [] ty;;
      (** check the body: x is not a subterm *)
      check_rec_call' (push_var_nonrec G (x, ty)) [] body*)

  | tCoFix mfix_inner fix_ind => 
      let rs := fold_left
        (fun rs t => rs <- rs ;; check_inert_subterm_rec_call G rs t)
        (map dtype mfix_inner) (ret rs) in
      let G' := push_fix_guard_env G mfix_inner in
      fold_left (fun rs body =>
          rs <- rs ;;
          '(needreduce', rs) <- check_rec_call G' rs body ;;
          check_rec_call_state G needreduce' stack rs (fun _ => raise NoReductionPossible))
        (map dbody mfix_inner) (ret rs)

      (*(** check the arguments *)
      _ <- list_iter (check_rec_call' G []) l;;
      (** check the types of the mfixes *)
      _ <- list_iter (check_rec_call' G []) (map dtype mfix_inner);;
      (** check the bodies *)
      let G' := push_fix_guard_env G mfix_inner in
      list_iter (check_rec_call' G' []) (map dbody mfix_inner)*)

  | tInd _ _ | tConstruct _ _ _ =>
    check_rec_call_state G NoNeedReduce stack rs (fun _ => raise NoReductionPossible)

  | tProj p c =>
      '(needreduce', rs) <- check_rec_call G rs c ;;
      check_rec_call_state G needreduce' stack rs (fun tt =>
        (* if this fails, try to reduce the projection by looking for a constructor in c *)
        c <- whd_all Σ G.(loc_env) c;;
        let '(hd, args) := decompose_app c in 
        '(hd, args) <- match hd with 
        | tCoFix cf idx =>
            cf' <- contract_cofix cf idx ;;
            t <- whd_all Σ G.(loc_env) (tApp cf' args);;
            ret $ decompose_app t
        | _ => ret (hd, args)
        end;;
        match hd with
        | tConstruct _ _ _ =>
            let i := p.(proj_npars) + p.(proj_arg) in
            arg <- except (IndexErr "check_rec_call_stack" "index out of range" i) $ nth_error args i ;;
            ret (arg, [])
        | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _
        | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ =>
            raise $ OtherErr "check_rec_call_stack :: tProj" "whd_all is broken"
        | tRel _ | tVar _ | tConst _ _ | tApp _ _ | tCase _ _ _ _ | tFix _ _
        | tProj _ _ | tCast _ _ _ | tEvar _ _ =>
            raise NoReductionPossible
        end)

      | tVar _ => ret rs
  (* FIXME: do vars work in MC? *)
  (* | tVar id => 
      check_rec_call_state G NoNeedReduce stack rs (fun tt =>
        entry <- except (OtherErr "check_rec_call_stack" "unknown variable") $
          find (fun ctx_decl => ctx_decl.(decl_name) == id) G.(loc_env);;
        match entry.(decl_body) with
        | None => None
        | Some t => Some (t, [])
        end)
    *)
  | tLetIn x c t b =>
      '(needreduce_c, rs) <- check_rec_call G rs c ;;
      '(needreduce_t, rs) <- check_rec_call G rs t ;;
      match needreduce_of_stack stack ||| needreduce_c ||| needreduce_t with
      | NoNeedReduce =>
          (* Stack do not require to beta-reduce; let's look if the body of the let needs *)
          spec <- subterm_specif Σ ρ G [] c ;;
          let stack := lift_stack 1 stack in
          check_rec_call_stack (push_let G (x,c,t,spec)) stack rs b
      | NeedReduce _ _ => check_rec_call_stack G stack rs (subst10 c b)
      end
  
  | tCast c _ t =>
      rs <- check_inert_subterm_rec_call G rs t ;;
      check_rec_call_stack G stack rs c

  | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ => ret rs

  | tEvar _ _ => ret rs
  end

(** Check the body [body] of a nested fixpoint with decreasing argument [decr] (dB index) and subterm spec [sub_spec] for the recursive argument.*)
(** We recursively enter the body of the fix, adding the non-recursive arguments preceding [decr] to the guard env and finally add the decreasing argument with [sub_spec], before continuing to check the rest of the body *)
with check_nested_fix_body G (decr:nat) stack (rs : list fix_check_result) (body:term) {struct decr}: exc (list fix_check_result) := 
  if decr == 0 then check_inert_subterm_rec_call G rs body else 
  (** reduce the body *)
  body_whd <- whd_all Σ G.(loc_env) body;;
  match body_whd with 
  | tLambda x ty body =>
      match stack with
      | elt :: stack =>
          (** push to env as non-recursive variable and continue recursively *)
          rs <- check_inert_subterm_rec_call G rs ty ;;
          '(G', stack', body') <- pop_argument Σ ρ NoNeedReduce G elt stack x ty body ;;
          check_nested_fix_body G' decr stack' rs body'
      | [] =>
          (** we have arrived at the recursive arg *)
          let G' := push_var_guard_env G (redex_level rs) x ty in
          check_nested_fix_body G' decr [] rs body
      end
  | _ => raise $ GuardErr "check_nested_fix_body" "illformed inner fix body" NotEnoughAbstractionInFixBody
  end

with check_rec_call_state G needreduce_of_head stack rs (expand_head : unit -> exc (term * list stack_element)) {struct rs}:=
  (* Test if either the head or the stack of a state
    needs the state to be reduced before continuing checking *)
  let e := needreduce_of_head ||| needreduce_of_stack stack in
  match e with
  | NoNeedReduce => ret rs
  | NeedReduce _ _ =>
      (* Expand if possible, otherwise, last chance, propagate need
        for expansion, in the hope to be eventually erased *)
      catchMap (expand_head tt)
        (fun err => match err with
          | NoReductionPossible =>
              tail <- except (IndexErr "check_rec_call_state" "" 0) $ tl rs ;;
              ret $ e :: tail
          | _ => raise err
          end)
        (fun '(c, stack') => check_rec_call_stack G (stack' ++ stack) rs c)
  end

with check_inert_subterm_rec_call G rs c {struct rs} : exc (list fix_check_result) :=
  '(needreduce, rs) <- check_rec_call G rs c ;;
  check_rec_call_state G needreduce [] rs (fun _ => raise NoReductionPossible)

with check_rec_call G rs c {struct rs} : exc (fix_check_result * list fix_check_result):=
  res <- check_rec_call_stack G [] (NoNeedReduce :: rs) c ;;
  head <- except (IndexErr "check_rec_call" "" 0) $ hd res ;;
  tail <- except (IndexErr "check_rec_call" "" 0) $ tl res ;;
  ret (head, tail).

(* YJ: just a wrapper to check_rec_call. *)
(** Check if [def] is a guarded fixpoint body, with arguments up to (and including)
  the recursive argument being introduced in the context [G]. 
  [G] has been initialized with initial guardedness information on the recursive argument.
  [trees] is a list of recursive structures for the decreasing arguments of the mutual fixpoints.
  [recpos] is a list with the recursive argument indices of the mutually defined fixpoints.
*)
Definition check_one_fix G (def : term) : exc unit := 
  '(needreduce, rs) <- check_rec_call G [] def ;;
  _ <- assert (#|rs| == 0) (OtherErr "check_one_fix" "check_rec_call doesn't clear the redex stack") ;;
  match needreduce with 
  | NeedReduce Γ e => raise (GuardErr "check_one_fix" "" e)
  | NoNeedReduce => ret tt
  end.

End CheckFix.
Set Guard Checking.


(* YJ: This function "chops" an inductive into the recursive part and the rest.
  As an example: [fixp] is a singleton list (non-mutual fixpoint) containing
  <<
  Fixpoint f a (b : List X) c {struct b} := match b with ... end.
  >>
  Then the call (inductive_of_mutfix Σ Γ fixp) returns
  ([List X], [([a, b], [λ c . match b with ... end])]).
  *)
(** Extract the [inductive] that [fixp] is doing recursion over (and check that the recursion is indeed over an inductive).
  Moreover give the body of [fixp] after the recursive argument and the environment (updated from [Γ])
  that contains the arguments up to (and including) the recursive argument (of course also the fixpoints). *)
#[bypass_check(guard)]
Definition inductive_of_mutfix Σ Γ (fixp : mfixpoint term) : exc (list inductive * list (context * term)):= 
  let number_of_fixes := #|fixp| in
  (* YJ: which cannot be an empty list. We extract the name, type, and body *)
  assert (number_of_fixes != 0) (OtherErr "inductive_of_mutfix" "ill-formed fix");;
  let ftypes := map dtype fixp in
  let fnames := map dname fixp in 
  let fbodies := map dbody fixp in
  let nvect := map rarg fixp in 
  (** push fixpoints to local context *)
  let Γ_fix := push_assumptions_context (fnames, ftypes) Γ in

  (* YJ: this function will be iterated onto each fixpoint of [fixp]. *)
  (** Check the i-th definition [fixdef] of the mutual inductive block where k is the recursive argument, 
    making sure that no invalid recursive calls are in the types of the first [k] arguments, 
    make sure that the recursion is over an inductive type, 
    and return that inductive together with the body of [fixdef] after the recursive arguement
    together with its context. *)
  (* YJ: dependent types - the recursive argument might be dependent on previous arguments,
    so we have to check UNTIL the recarg. Every fixpoint can only have a recarg,
    so the rest can be thought of as part of the "body" without recarg. *)
  (* YJ: parameter [i] is unused?? YEP, removing [i] and using [map2] instead
  of [map2_i] works perfectly *)
  let find_ind i k fixdef : exc (inductive * (context * term)):= 
      (** check that a rec call to the fixpoint [fixdef] does not appear in the [k] first abstractions,
        that the recursion is over an inductive, and 
        gives the inductive and the body + environment of [fixdef] after introducing the first [k] arguments *)
      let check_occur := fix check_occur Γ n (def : term) {struct def}: exc (inductive * (context * term)) := 
        (* YJ: this is the main runner. It opens up k [tLambda]s and then run *)
        (** n is the number of lambdas we're under/aka the dB from which the mutual fixes are starting:
          n ... n + number_of_fixes - 1 *)
        def_whd <- whd_all Σ Γ def;;
        match def_whd with 
        | tLambda x t body => 
            assert (negb(rel_range_occurs n number_of_fixes t)) 
              (GuardErr "inductive_of_mutfix" "bad occurrence of recursive call"
                (RecursionOnIllegalTerm n (Γ, def_whd) ([], [])));;
            let Γ' := Γ ,, (vass x t) in
            if n == k then (** becomes true once we have entered [k] inner lambdas*)
              (** so now the rec arg should be at dB 0 and [t] is the type we are doing recursion over *)
              (** get the inductive type of the fixpoint, ensuring that it is an inductive *)
              '((ind, _), _) <- catchE (find_inductive Σ Γ t) (fun _ => raise $ GuardErr "inductive_of_mutfix" "recursion not on inductive" (RecursionNotOnInductiveType t));;
              '(mib, _) <- lookup_mind_specif Σ ind;;
              if mib.(ind_finite) != Finite then (* ensure that it is an inductive *)
                raise $ GuardErr "inductive_of_mutfix" "recursion not on inductive" (RecursionNotOnInductiveType def)
              else
                (** now return the inductive, the env after taking the inductive argument and all arguments before it, and the rest of the fix's body *)
                ret (ind, (Γ', body))
            else check_occur Γ' (S n) body
        | _ => 
            (** not a lambda -> we do not have enough arguments and can't find the recursive one *)
            raise $ GuardErr "inductive_of_mutfix" "not enough abstractions in fix body" NotEnoughAbstractionInFixBody
        end
      in 
      (** check that recursive occurences are nice and extract inductive + fix body *)
      check_occur Γ_fix 0 fixdef
  in 
  (** now iterate this on all the fixpoints of the mutually recursive block *)
  rv <- unwrap $ map2_i find_ind nvect fbodies;;
  (* trace "inductive_of_mutfix : leave";; *)
  (** return the list of inductives as well as the fixpoint bodies in their context *)
  ret (map fst rv : list inductive, map snd rv : list (context * term)).


(* YJ: check_fix is just mapping check_one_fix over the different branches. (I know, I know) *)
(** The entry point for checking fixpoints. 
  [Σ]: the global environment with all definitions used in [mfix]. 
  [ρ]: the global environment of wf_paths (for every inductive in Σ, this should contain the wf_paths).
  [Γ]: the local environment in which the fixpoint is defined.
  [mfix]: the fixpoint to check.
*)
Definition check_fix Σ (ρ : pathsEnv) Γ (mfix : mfixpoint term) : exc unit := 
  (** check that the recursion is over inductives and get those inductives 
    as well as the bodies of the fixpoints *)
  (* trace "enter check_fix";; *)
  '(minds, rec_defs) <- inductive_of_mutfix Σ Γ mfix;;
  (** get the inductive definitions -- note that the mibs should all be the same*)
  (* YJ: the oib is the fixpoint among mib whose name is "exposed". *)
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
  let fix_envs : list context := map fst rec_defs in     
  let fix_bodies : list term := map snd rec_defs in   (** the bodies under the respective [fix_envs] *)
  let rec_args : list nat := map rarg mfix in 

  _ <- unwrap $ mapi (fun i fix_body => 
    fix_env <- except (IndexErr "check_fix" "fix_envs too short" i) $ nth_error fix_envs i;;
    rec_tree <- except (IndexErr "check_fix" "rec_trees too short" i) $ nth_error rec_trees i;;
    rec_arg <- except (IndexErr "check_fix" "rec args too short" i) $ nth_error rec_args i;;
    (** initial guard env *)
    let G := init_guard_env fix_env rec_arg rec_tree in
    (** check the one fixpoint *)
    check_one_fix Σ ρ rec_args rec_trees G fix_body 
    ) fix_bodies;;
  ret tt.
