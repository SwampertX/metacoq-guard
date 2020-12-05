
From MetaCoq.Checker Require Import Checker. 
From MetaCoq.Template Require Import utils BasicAst Ast AstUtils.
From MetaCoq.Template Require Import Universes Environment Reflect LiftSubst. 
From MetaCoq.Template.utils Require Import RTree. 
From MetaCoq.Template Require Import utils.Except.



(* TODO move *)
Definition list_iter {X} (f : X -> exc unit) (l : list X) : exc unit := 
  List.fold_left (fun (acc : exc unit) x => _ <- acc;; f x) l (ret tt).
Definition list_iteri {X} (f : nat -> X -> exc unit) (l : list X) : exc unit := 
  _ <- List.fold_left (fun (acc : exc nat) x => i <- acc;; _ <- f i x;; ret (S i)) l (ret 0);;
  ret tt.
(* TODO:move*)
Definition map2_i { A B C} (f : nat -> A -> B -> C) (a : list A) (b : list B) := 
  let map2' := fix rec a b n := 
     match a, b with
     | a0 :: a, b0 :: b => f n a0 b0 :: rec a b (S n)
     | _, _ => []
     end
  in map2' a b 0.
(* TODO: move *)
Fixpoint update_list {X} (l : list X) index x := 
  match l with 
  | [] => []
  | h :: l => 
      match index with 
      | 0 => x :: l
      | S index => h :: update_list l index x
      end
  end.
(* TODO move *)
Definition assert (b : bool) (err : string) : exc unit := 
  match b with 
  | false => raise err
  | true => ret tt
  end.

(* TODO : move *)
(* catch error and potentially emit another error *)
Definition catchE {X} (a : exc X) (f : string -> exc X) : exc X := 
  match a with 
  | inl a => ret a
  | inr e => f e
  end.

Definition catch {X} (a : exc X) (f : string -> X) : X := 
  match a with 
  | inl a => a
  | inr e => f e
  end.

Definition catchMap {X Y} (e : exc X) (f : string -> Y) (g : X -> Y) :=
  match e with
  | inr e => f e
  | inl a => g a 
  end.



(* TODO move *)
(* head-normalized constructor types so that their conclusion exposes the inductive type -- context contains the arguments (including lets and parameters) *)
Definition ind_ctors_hnf (i : mind_specif) := map (fun t => decompose_let_prod_env t) (ind_user_lc i).

(** ** Compute uniform parameters *)

(** If the conclusion of a constructor is [tApp I app] in a context [ctx] of the constructors arguments where the parameters have the largest dB index, this computes the number of parameters of the inductive which can at most be uniform for the type. *)
Definition constr_result_num_uniform (ctx : context) (num_pars : nat) (app : list term) := 
  let num_args := length ctx in
  let is_param n := 
    (* the parameters are num_args - num_pars .... num_args - 1 *)
    Nat.leb n (num_args - 1) && Nat.leb (num_args - num_pars) n in
  let check_args := fix check_args (l : list term) := 
    match l with 
    | [] => 0 
    | a :: l => 
        match a with 
        | tRel k => if is_param k then S (check_args l) 
                                  else 0
        | _ => 0
        end
    end
  in check_args app.

(* Compute the number of parameters which can at most be uniform for an inductive. *)
Definition one_inductive_num_uniform (i : mind_specif) := 
  let ctors_hnf := ind_ctors_hnf i in
  let num_pars := (fst i).(ind_npars) in
  let one_constr '(ctx, con) := 
    match con with
    | tApp _ app => constr_result_num_uniform ctx num_pars app
    | _ => 0
    end in
  List.fold_left (fun acc c => min acc (one_constr c)) ctors_hnf num_pars. 


(* Computes the number of uniform parameters of the mutual inductive definition [i]. 
  Note: In Coq, for an inductive declaration 
    Inductive I X1 ... Xn : U := ...
  if Xi is non-uniform, then also Xj for j >= i are treated as non-uniform.
  That is, from the number of uniform parameters we can restore which parameters are uniform (from Coq's perspective). 
*)
Definition num_uniform_params (mib : mutual_inductive_body) : nat := 
  List.fold_left (fun acc oib => min acc (one_inductive_num_uniform (mib, oib))) mib.(ind_bodies) mib.(ind_npars). 


(* Kernel representation of lists *)
Definition list_indname : inductive := 
  {|
   inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
   inductive_ind := 0 
  |}.
  
(* NOTE: the constructor arguments in recargs trees are always without lets and without params! *)
Definition list_recargs : wf_paths := 
  Rec 0 [ Node (Mrec list_indname) [ Node Norec []; Node Norec [ Node Norec []; 
                                                                 Param 0 1]
                                   ]
        ].
Eval cbn in (expand (list_recargs)). 

(*Inductive test := *)
  (*| abc : let a := 10 * 10 in nat -> test. *)

(*Eval hnf in let a := 10 * 10 in nat -> test.*)

Print one_inductive_body.
(* I don't really care about universes, just use Set everywhere *)

Definition list_indbody : one_inductive_body := 
  {| 
    ind_name := "list";
    ind_type := tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                      (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.60"))))
                      (tSort (Universe.from_kernel_repr (Level.lSet, false) [(Level.Level "Coq.Init.Datatypes.60", false)]));
    ind_kelim := InType;
    ind_ctors := [("nil", tProd {|
                               binder_name := nNamed "A";
                               binder_relevance := Relevant |}
                             (tSort
                                (Universe.of_levels
                                   (inr
                                      (Level.Level "Coq.Init.Datatypes.60"))))
                             (tApp (tRel 1) [tRel 0]), 0);
                          ("cons",
                          tProd
                            {|
                            binder_name := nNamed "A";
                            binder_relevance := Relevant |}
                            (tSort
                               (Universe.of_levels
                                  (inr
                                     (Level.Level "Coq.Init.Datatypes.60"))))
                            (tProd
                               {|
                               binder_name := nAnon;
                               binder_relevance := Relevant |} 
                               (tRel 0)
                               (tProd
                                  {|
                                  binder_name := nAnon;
                                  binder_relevance := Relevant |}
                                  (tApp (tRel 2) [tRel 1])
                                  (tApp (tRel 3) [tRel 2]))), 2)];
               ind_projs := [];
               ind_relevance := Relevant;
               ind_recargs := list_recargs |}. 



(* I don't care about universes. *)
Definition univdecl := Monomorphic_ctx
                   (LevelSetProp.of_list
                      [Level.Level "Coq.Init.Datatypes.60"],
                   ConstraintSet.empty).


Definition list_param_ctxt := 
[{|
   decl_name := {|
                binder_name := nNamed "A";
                binder_relevance := Relevant |};
   decl_body := None;
   decl_type := tSort
                  (Universe.of_levels
                     (inr (Level.Level "Coq.Init.Datatypes.60"))) |}].
Definition list_mindbody : mutual_inductive_body := 
  {| 
    ind_bodies := [list_indbody];
    ind_finite := Finite;
    ind_npars := 1;
    (*ind_npars_unif := 1;*)
    ind_params := list_param_ctxt;
    ind_universes := univdecl;
    ind_variance := None;
  |}.


Compute (num_uniform_params list_mindbody). 














Notation "a == b" := (eqb a b) (at level 90). 
Notation "a != b" := (negb(a==b)) (at level 90).



(** * WIP : An implementation of the guardedness checker *)

(* dest_subterms *)
Definition wf_paths_constr_args_sizes t : exc (list (list wf_paths)) := 
  destruct_node t (fun ra constrs => 
    assert (match ra with Norec => false | _ => true end) "wf_paths_constr_args_sizes should not be called with Norec";;
    l <- exc_unwrap $ map (fun t => destruct_node t (fun _ args => ret args) (raise "expected node")) constrs;;
    ret l)
  (raise "expected node").


Implicit Types (Σ : global_env) (Γ : context). 
Definition whd_all Σ c t := 
  except "whd_all: out of fuel" $ reduce_opt RedFlags.default Σ c default_fuel t. 

(* β, ι, ζ weak-head reduction *)
Definition whd_βιζ Σ Γ t := 
  let redflags := RedFlags.mk true true true false false false in
  except "whd_βιζ: out of fuel" $ reduce_opt redflags Σ Γ default_fuel t. 

(* no let/ζ reduction *)
Definition whd_all_nolet Σ Γ t := 
  let redflags := RedFlags.mk true true false true true true in
  except "whd_all_nolet: out of fuel" $ reduce_opt redflags Σ Γ default_fuel t. 


Definition lookup_env_const Σ kn : option constant_body := 
  match lookup_env Σ kn with 
  | Some (ConstantDecl const) => Some const
  | _ => None
  end.


(* TODO: what is the MetaCoq invariant here? Is the cst_body really only present when it is a transparent constant? *)
Definition is_evaluable_const Σ kn := 
  match lookup_env_const Σ kn with
  | Some const =>
      match const.(cst_body) with
      | Some _ => true
      | _ => false
      end
  | _ => false
  end.

(* TODO: same as above -- are we really allowed to reduce this?*)
Definition get_const_value Σ kn : option term := 
  match lookup_env_const Σ kn with
  | Some const => const.(cst_body)
  | None => None
  end.

Definition lookup_env_mind Σ kn : option mutual_inductive_body := 
  match lookup_env Σ kn with 
  | Some (InductiveDecl ind) => Some ind
  | _ => None
  end.

Definition lookup_mind_specif Σ (ind : inductive) : exc mind_specif := 
  mib <- except "lookup_mind_specif: could not find inductive" $ 
    lookup_env_mind Σ ind.(inductive_mind) ;;
  ib <- except "lookup_mind_specif: invalid inductive index" $ 
    nth_error mib.(ind_bodies) ind.(inductive_ind) ;;
  ret (mib, ib).


(* if c evaluates to an application (weak-head) and the LHS is an inductive, return it together with the RHS (list) *)
Definition find_rectype Σ Γ t := 
  t <- whd_all Σ Γ t;; 
  let (t, l) := decompose_app t in 
  match t with 
  | tInd i u => ret ((i, u), l)
  | _ => raise "find_rectype"
  end. 


(* the same, but only if the rectype is an inductive or record (bifinite) *)
Definition find_inductive Σ Γ t := 
  '((i, u), l) <- find_rectype Σ Γ t;;
  '(mib, _) <- lookup_mind_specif Σ i;;
  if mib.(ind_finite) != CoFinite then ret ((i, u), l) else raise "find_inductive: is cofinite".

(* only if coinductive *)
Definition find_coinductive Σ Γ t := 
  '((i, u), l) <- find_rectype Σ Γ t;;
  '(mib, _) <- lookup_mind_specif Σ i;;
  if mib.(ind_finite) == CoFinite then ret ((i, u), l) else raise "find_coinductive: is not cofinite".


(* push assumptions to the de Bruijn context *)
Definition push_assumptions_context '(names, types) Γ := 
  (* we use fold_left, so the i-th element that is pushed to the context needs to be lifted by i *)
  let ctxt := map2_i (fun i name type => vass name (lift0 i type)) names types in
  List.fold_left (fun acc assum => acc ,, assum) Γ ctxt. 


Definition mfix_names (fixp : mfixpoint term) := map dname fixp. 
Definition mfix_types (fixp : mfixpoint term) := map dtype fixp.
Definition mfix_bodies (fixp : mfixpoint term) := map dbody fixp.

(* [decompose_lam_assum Σ Γ ty] decomposes [ty] into a context of lambdas/lets and a remaining type, after reducing *)
Unset Guard Checking.
Definition decompose_lam_assum Σ Γ := 
  let lamec_rec := fix lamec_rec Γ Γ0 ty {struct ty} :=
    ty_whd <- whd_all_nolet Σ Γ ty;;
    match ty_whd with 
    | tLambda x ty body =>
        let d := vass x ty in 
        lamec_rec (Γ ,, d) (Γ0 ,, d) body
    | tLetIn x t ty body => 
        let d := vdef x t ty in
        lamec_rec (Γ ,, d) (Γ0 ,, d) body
    | _ => ret (Γ0, ty_whd)
    end
  in lamec_rec Γ [].

(* [decompose_prod_assum Σ Γ ty] decomposes [ty] into a context of prods/lets and a remaining type, after reducing *)
Definition decompose_prod_assum Σ Γ := 
  let prodec_rec := fix prodec_rec Γ Γ0 ty {struct ty} := 
    ty_whd <- whd_all_nolet Σ Γ ty;;
    match ty_whd with
    | tProd x ty body => 
        let d := vass x ty in 
        prodec_rec (Γ ,, d) (Γ0 ,, d) body 
    | tLetIn x t ty body => 
        let d := vdef x t ty in 
        prodec_rec (Γ ,, d) (Γ0 ,, d) body 
    | _ => 
        (* try to reduce *)
        ty_whd' <- whd_all Σ Γ ty_whd;;
        if ty_whd == ty_whd' then ret (Γ0, ty_whd) else prodec_rec Γ Γ0 ty_whd'
    end 
  in prodec_rec Γ []. 

(* [decompose_prod Σ Γ ty] decomposes [ty] into a context of prods and a remaining type, after reducing *)
Definition decompose_prod Σ Γ (t : term) : exc (context * term) := 
  let decrec := fix decrec Γ Γ0 t {struct t} := 
    t_whd <- whd_all Σ Γ t;;
    match t_whd with
    | tProd na ty body => 
        let d := vass na ty in
        decrec (Γ ,, d) (Γ0 ,, d) body
    | _ => ret (Γ0, t)
    end
  in decrec Γ [] t. 

(* TODO: check order of arguments of vdef everywhere *)

(* [decompose_lam_n_assum Σ Γ n t] decomposes [t] into a context of lambdas and lets. 
  We expect [n] lambdas and also take all the lets up to the n-th lambda, but no more lets after the n-th lambda. *)
Definition decompose_lam_n_assum Σ Γ n (t : term) : exc (context * term) := 
  let lamdec_rec := fix lamdec_rec Γ Γ0 n t {struct t} := 
    match n with
    | 0 => ret (Γ0, t)
    | S n => match t with 
             | tLambda x ty body => 
                 let d := vass x ty in
                 lamdec_rec (Γ ,, d) (Γ0 ,, d) n body
             | tLetIn x def ty body => 
                let d := vdef x def ty in 
                lamdec_rec (Γ ,, d) (Γ0 ,, d) (S n) body
             | tCast t _ _ => lamdec_rec Γ Γ0 (S n) t
             | _ => raise "decompose_lam_n_assum: not enough abstractions"
             end
    end
  in lamdec_rec Γ [] n t. 


(** * Guard condition *)


(** Environments annotated with marks on recursive arguments *)

(* proper subterm (strict) or loose subterm (may be equal to the recursive argument, i.e. no proper subterm) *)
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

(* greatest lower bound/infimum *)
Definition size_glb s1 s2 := 
  match s1, s2 with 
  | Strict, Strict => Strict
  | _, _ => Loose
  end.

(* possible specifications for a term:
   - Not_subterm: when the size of a term is not related to the
     recursive argument of the fixpoint
   - Subterm: when the term is a subterm of the recursive argument
     the wf_paths argument specifies which subterms of the term are recursive -- this is just the whole recursive structure of the term's type again, for nested matches (possibly not the trivial recargs tree that could also be looked up in the environment, but for nested inductives, this is instantiated)
   - Dead_code: when the term has been built by elimination over an empty type
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

(* in contrast to the Boolean equality decider we get by eqb, this also checks equivalence if structural equality is failing *)
Definition eq_wf_paths : wf_paths -> wf_paths -> bool := rtree_equal (eqb (A := recarg)). 

(* TODO: where exactly do we need intersections *)
Definition inter_recarg r1 r2 := 
  match r1, r2 with
  | Norec, Norec => Some Norec
  | Mrec i1, Mrec i2
  | Imbr i1, Imbr i2
  | Mrec i1, Imbr i2 => if i1 == i2 then Some r1 else None (* intersection is an Mrec, not an Imbr, if one is an Mrec *)
  | Imbr i1, Mrec i2 => if i1 == i2 then Some r2 else None
  | _, _ => None
  end.

Definition inter_wf_paths := rtree_inter (eqb (A := recarg)) inter_recarg Norec. 
Definition incl_wf_paths := rtree_incl (eqb (A := recarg)) inter_recarg Norec. 
Definition equal_wf_paths := rtree_equal (eqb (A := recarg)). 


Definition mk_norec := mk_node Norec []. 

(* Given a list of lists with the trees for the arguments (excluding parameters) of each constructor, 
  construct the tree for a particular inductive type. 
  (This is not really a fully correct tree, as this is just the tree for one of the mutual inductives.) *)
Definition mk_ind_paths rarg constr_arg_trees : wf_paths := 
  mk_node rarg (map (fun c => mk_node Norec c) constr_arg_trees). 

(* given a tree specifying the recursive structure of a term, generate a subterm spec *)
(* used e.g. when destructing an inductive *)
Definition spec_of_tree t := 
  if eq_wf_paths t mk_norec then Not_subterm else Subterm Strict t. 


(* intersection of subterm specs.
  Dead_code is neutral element and Not_subterm least element. For Subterms, we intersect the recursive paths and the size *)
Definition inter_spec s1 s2 : exc subterm_spec := 
  match s1, s2 with 
  | _, Dead_code => ret s1
  | Dead_code, _ => ret s2
  | Not_subterm, _ => ret s1
  | _, Not_subterm => ret s2
  | Subterm a1 t1, Subterm a2 t2 => 
      inter <- except "inter_spec" $ inter_wf_paths t1 t2;;
      ret $ Subterm (size_glb a1 a2) inter
  end.

(* greatest lower bound of a list of subterm specs *)
Definition subterm_spec_glb (sl : list subterm_spec) : exc subterm_spec := 
  List.fold_left (fun acc s => acc <- acc;; inter_spec acc s) sl (ret Dead_code). 

(** Environment to keep track of guardedness information *)
Record guard_env := 
  { 
    (* the local environment *)
    loc_env : context;
    (* de Bruijn index of the last fixpoint in this block (starting at 0) *)
    (* i.e. in a block of n fixpoints, the dBs of the fixes are:
        rel_min, ..., rel_min + n - 1
    *)
    rel_min_fix : nat;
    (* de Bruijn context containing subterm information *)
    guarded_env : list subterm_spec;
  }.
Implicit Type (G : guard_env). 

(* make an initial guard_env after entering a fixpoint.
  [recarg] is the index of the recursive argument, starting at 0. 
    e.g. for [fix r (n1 : nat) (n2 : nat) {struct n1} := ....] it would be 0.
  [tree] is the recursion tree for the inductive type of the recursive argument 
*)
Definition init_guard_env Γ recarg tree :=
  {| 
    loc_env := Γ;
    (* Rel 0 -> recursive argument, 
       Rel recarg -> first "proper" (non-recursive) argument,
       Rel (S recarg) -> last fixpoint in this block 
    *)
    rel_min_fix := 1 + recarg;
    guarded_env := [Subterm Loose tree]
  |}.

(* push a binder with name [na], type [type] and subterm specification [spec] *)
Definition push_guard_env G '(na, type, spec) := 
  {|
    loc_env := G.(loc_env) ,, vass na type;
    rel_min_fix := S (G.(rel_min_fix));
    guarded_env := spec :: G.(guarded_env);
  |}.

(* update the subterm spec of dB [i] to [new_spec] *)
Definition update_guard_spec G i new_spec := 
  {| 
    loc_env := G.(loc_env);
    rel_min_fix := G.(rel_min_fix);
    guarded_env := update_list G.(guarded_env) i new_spec 
  |}.

(* add a new inner variable which is not a subterm *)
Definition push_nonrec_guard_env G '(na, type) := 
  push_guard_env G (na, type, Not_subterm).

(* lookup subterm information for de Bruijn index [p] *)
Definition lookup_subterm G p := 
  match nth_error G.(guarded_env) p with 
  | Some spec => spec
  | None => Not_subterm
  end.

(* push a local context -- these are not subterms *)
Definition push_context_guard_env G Γ := 
  let n := length Γ in 
  {| 
    loc_env := Γ ++ G.(loc_env);
    rel_min_fix := G.(rel_min_fix) + n;
    guarded_env := Nat.iter n (fun acc => Not_subterm :: acc) G.(guarded_env);
  |}. 

(* push fixes to the guard env -- these are not subterms *)
Definition push_fix_guard_env G (mfix : mfixpoint term) := 
  let n := length mfix in
  {|
    loc_env := push_assumptions_context (mfix_names mfix, mfix_types mfix) G.(loc_env);
    rel_min_fix := G.(rel_min_fix) + n;
    guarded_env := Nat.iter n (fun acc => Not_subterm :: acc) G.(guarded_env);
  |}.


(** ** Stack *)
(* A stack is used to maintain subterm information for elements which are (morally) applied to the term currently under observation, and which would really be applied if we could fully reduce with concrete values. 
  [SClosure] is used for efficiency reasons: we don't want to compute subterm information for everything, so this is done on demand. It thus captures the term and the guardedness environment it's in.
  [SArg] represents subterm information for a term for which we actually have computed that information. *)
Inductive stack_element := 
  | SClosure G (t : term)
  | SArg (s : subterm_spec). 

(* push a list of closures [l] with guard env [G] to the stack *)
Definition push_stack_closures G l stack := 
  List.fold_right (fun h acc => (SClosure G h) :: acc) l stack. 

(* push a list of args [l] to the stack *)
Definition push_stack_args l stack := 
  List.fold_right (fun h acc => SArg h :: acc) l stack. 


(* TODO *)
Definition hd {X} (l : list X) : exc X := 
  match l with 
  | [] => raise "cannot take hd of empty list"
  | x :: l => ret x
  end.

Definition tl {X} (l : list X) : exc list X := 
  match l with 
  | [] => raise "cannot take tl of empty list"
  | x :: l => ret l
  end.


Definition destruct_recarg (t : wf_paths) := destruct_node t (fun r _ => Some r) None. 

Definition match_recarg_inductive (ind : inductive) (r : recarg) := 
  match r with
  | Norec => false
  | Mrec i | Imbr i => i == ind
  end.



(* TODO move *)
(* pseudo-reduction rule:
 * [hnf_prod_app env (Prod(_,B)) r --> B[r]
 * with an HNF on the first argument to produce a product. *)
Definition hnf_prod_app Σ Γ t r : exc term := 
  t_whd <- whd_all Σ Γ t;;
  match t_whd with 
  | tProd _ _ body => ret $ subst10 r t
  | _ => raise "hnf_prod_app: need a product"
  end.
Definition hnf_prod_apps Σ Γ t l : exc term := 
  List.fold_left (fun acc r => acc <- acc;; hnf_prod_app Σ Γ acc r) l (ret t). 


(* Add the types of mutual inductives as assumptions to the local context. 
  The inductive types are instantiated with the (uniform) parameters in [pars]. 
*)
Definition context_push_ind_with_params Σ Γ (mib : mutual_inductive_body) (pars : list term) : exc context := 
  let num_bodies := length mib.(ind_bodies) in
  (* get relevance *)
  fst_body <- except "mutual inductive has no bodies" $ nth_error mib.(ind_bodies) 0;;
  let relev := fst_body.(ind_relevance) in
  (* function: push one inductive to the context *)
  let push_ind := fun (specif : one_inductive_body) Γ =>
    let na := {|binder_name := nAnon; binder_relevance := relev|} in
    (* get the type instantiated with params *)
    ty_inst <- hnf_prod_apps Σ Γ specif.(ind_type) pars;;
    ret $ Γ ,, vass na ty_inst 
  in 
  List.fold_right (fun i acc => acc <- acc;; push_ind i acc) (ret Γ) mib.(ind_bodies).

(* Add the types of mutual inductives to a recargs environment *)
Definition ra_env_push_inner_inductives_with_params ra_env ind_kn ntypes := 
  (* make inner inductive types (Imbr in the tree) with recursive references for the individual types *)
  let rc := rev $ mapi (fun i t => (Imbr (mkInd ind_kn i), t)) 
                       (mk_rec_calls (X := recarg) ntypes) in
  (* lift the existing ra_env *)
  let ra_env := map (fun '(r, t) => (r, rtree_lift ntypes t)) ra_env in
  rc ++ ra_env. 

(* puts lambdas accepting sorts 0.. n-1 (for some dummy sorts) in front of [t] (and lift [t] accordingly)*)
(* we don't care about the exact universe as this is only relevant for checking guardedness -- it only needs to reduce afterwards *)
Definition lam_implicit_lift n t := 
  let anon := mkBindAnn nAnon Relevant in
  let some_sort := tSort (Universe.make (Level.Level "guarded_implicit")) in 
  let lambda_implicit t := tLambda anon some_sort t in 
  Nat.iter n lambda_implicit (lift0 n t). 

(* This removes global parameters of the inductive types in [constrs] (for
   nested inductive types only) *)
(* for instance: if [constrs] is the list of [list] constructors, 
 * then we get back (roughly): [∀ X, (λ X, Rel 2) X;
 *                              ∀ X (x : X) (l : (λ X, Rel 3) X), (λ X, Rel 4) X]
 * i.e. we assume that at index 0 (at the outside) there is [list] instantiated with a parameter 
 * and we ignore the parameter X for the recursive occurrences of [list] in the constructor. *)
(* Note : in the types in [constrs], the dBs 0... ntyps-1 refer to the mutual inductives *)
(* Now we substitute the references to these types *)
(* effectively, this means that we just ignore the parameters and instead assume that at indices 1... ntypes, 
 * there are the inductive types already instantiated with some parameters *)
Definition abstract_params_mind_constrs num_types num_params (constrs : list term) :=
  (* if there are no parameters, there is no abstracting to do *)
  if num_params == 0 then constrs
  else 
    (* make lambdas abstracting over the parameters *)
    let make_abs := tabulate (fun i => lam_implicit_lift num_params (tRel i)) num_types in
    (* substitute the recursive occurences of the inductive types by these abstractions *)

    map (subst0 make_abs) constrs.

(* Move the first [n] prods of [c] into the context as elements of non-recursive type. *)
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
    | _ => raise "ra_env_decompose_prod: not enough prods" 
    end
  end.

(* This code is very
close to check_positive in indtypes.ml, but does no positivity check and does not
compute the number of recursive arguments. *)
Unset Guard Checking. 
(** Build the recargs tree for a term [t]. *)
(* [tree] is used to decide when to traverse nested inductives. *)
(* [ra_env] is used to keep track of the subterm information of dB variables. 
   It need not bind all variables occurring in [t]: to unbound indices, we implicitly assign [Norec].*)
Fixpoint build_recargs Σ Γ (ra_env : list (recarg * wf_paths)) (tree : wf_paths) (t : term) {struct t}: exc wf_paths := 
  t_whd <- whd_all Σ Γ t;;
  let '(x, args) := decompose_app t_whd in
  match x with 
  | tProd na type body => 
      assert (args == []) "reduction is broken";;
      let Γ' := Γ ,, vass na type in
      let ra_env' := (Norec, mk_norec) :: ra_env in
      build_recargs Σ Γ' ra_env' tree body
  | tRel k => 
      (* free variables are allowed and assigned Norec *)
      catchE (k_ra <- except "" $ nth_error ra_env k;; ret (snd k_ra)) 
            (fun _ => ret mk_norec)
  | tInd ind _ => 
    (* if the given tree for [t] allows it (i.e. has an inductive as label at the root), 
      we traverse a nested inductive *)
    match destruct_recarg tree with 
    | None => raise "malformed recargs tree"
    | Some (Imbr ind') | Some (Mrec ind') => 
        if ind == ind' then build_recargs_nested Σ Γ ra_env tree ind args 
                       else ret mk_norec
    | _ => ret mk_norec 
    end
  | _ => ret mk_norec
  end

(* Create the recursive tree for a nested inductive [ind] applied to arguments [args]. *)
(* In particular: starting from the tree [tree], we instantiate parameters suitably, according to [args], to handle nested inductives. *)
(* [tree] is used to decide when to traverse nested inductives. *)
(* [ra_env] is used to keep track of the subterm information of dB variables. 
   It need not bind all variables occurring in [t]: to unbound indices, we implicitly assign [Norec].*)
with build_recargs_nested Σ Γ (ra_env : list (recarg * wf_paths)) (tree : wf_paths) (ind: inductive) (args: list term) {struct args}: exc wf_paths := 
  (* if the tree [tree] already disallows recursion, we don't need to go further *)
  if equal_wf_paths tree mk_norec then ret tree else (
  '(mib, oib) <- lookup_mind_specif Σ ind;;
  (* determine number of (non-) uniform parameters *)
  let num_unif_params := num_uniform_params mib in
  let num_non_unif_params := mib.(ind_npars) - num_unif_params in
  (* get the instantiations for the uniform parameters *)
  (* Note that in Coq, all parameters after the first non-uniform parameter are treated as non-uniform -- thus we can just take a prefix of the list *)
  let inst_unif := firstn num_unif_params args in
  let num_mut_inds := length mib.(ind_bodies) in
  (* extend the environment with the inductive definitions applied to the parameters *)
  Γ' <- context_push_ind_with_params Σ Γ mib inst_unif;;
  (* do the same for the ra environment: recarg is Imbr (for inner inductives), the trees are direct recursive references [Param 0 j] *)
  let ra_env' := ra_env_push_inner_inductives_with_params ra_env ind.(inductive_mind) num_mut_inds in

  (* lift the parameters we instantiate with by the number of types: 
      the dB layout we setup is: 
        [inductive types setup in the nested inductive], [the environment the parameters are assuming]
      Since we insert the inductive types when we use the parameters to instantiate the recargs tree, 
      we thus have to lift them by the number of nested types.
  *)
  let inst_unif_lifted := map (lift0 num_mut_inds) inst_unif in

  (* In case of mutual inductive types, we use the recargs tree which was
    computed statically. This is fine because nested inductive types with
    mutually recursive containers are not supported -- meaning we need not instantiate in that case. 
    In the case that there are no mutual inductives, we use the argument tree [tree].*)
  trees <- (if num_mut_inds == 1 
    then arg_sizes <- wf_paths_constr_args_sizes tree;; ret [arg_sizes]
    else exc_unwrap $ map (fun oib => wf_paths_constr_args_sizes oib.(ind_recargs)) 
      mib.(ind_bodies));;

  (* Make the recargs tree for the [j]-th inductive in the block with body [oib].
   * Essentially, we instantiate the corresponding recargs tree in [trees] with the parameters in [inst_unif]. *)
  let mk_ind_recargs (j : nat) (oib : one_inductive_body) : exc wf_paths :=
    let constrs := map (fun '((_, c), _) => c) oib.(ind_ctors) in
    (* abstract the parameters of the recursive occurrences of the inductive type in the constructor types *)
    (* we assume that at indices 1... auxntyp, the inductive types are instantiated with the parameters *)
    let abstracted_constrs := abstract_params_mind_constrs num_mut_inds num_unif_params constrs in
    (* build the trees for the constructors, instantiated with the uniform parameters [inst_unif] *) 
    paths <- exc_unwrap $ mapi (fun k c => (* [k]-th constructor with abstracted type [c] *)
        (* instantiate the abstracted constructor types with the parameters we are interested in. *)
        c_inst <- hnf_prod_apps Σ Γ' c inst_unif_lifted;;
        (* move non-uniform parameters into the context *) 
        '(Γ', ra_env', c') <- ra_env_decompose_prod Σ Γ' ra_env' num_non_unif_params c_inst;;
        (* first fetch the trees for this constructor  *)
        constr_trees <- except "build_recargs_nested: no tree for inductive" $ nth_error trees j;;
        arg_trees <- except "build_recargs_nested: no tree for constructor" $ nth_error constr_trees k;; 
        (* build the trees for the constructor's arguments *)
        build_recargs_constructors Σ Γ' ra_env' arg_trees c'
      ) abstracted_constrs;;
      (* make the tree for this nested inductive *)
      ret $ mk_ind_paths (Imbr (mkInd ind.(inductive_mind) j)) paths
  in
  (* create the trees for all the bodies *)
  ind_recargs <- exc_unwrap $ mapi mk_ind_recargs mib.(ind_bodies);;
  (* now, given the bodies, make the mutual inductive trees *)
  trees <- except "creating trees failed" $ mk_rec ind_recargs;;
  (* return the tree for our particular inductive type *)
  tree_ind <- except "created trees malformed" $ nth_error trees ind.(inductive_ind);;
  ret tree_ind)
  

(* [build_recargs_constructors Σ Γ ra_env trees c] builds a list of each of the constructor [c]'s argument's recursive structures, instantiating nested inductives suitably.  
  We assume that [c] excludes parameters -- these should already be contained in the environment. 

  [trees] is a list of trees for the constructor's argument types, used to determine when to traverse nested inductive types.

  [ra_env] is used to keep track of the subterm information of dB variables. 
   It need not bind all variables occurring in [t]: to unbound indices, we implicitly assign [Norec].
*)
with build_recargs_constructors Σ Γ (ra_env : list (recarg * wf_paths)) (trees : list wf_paths) (c : term) {struct c}: exc (list wf_paths) := 
  let recargs_constr_rec := fix recargs_constr_rec Γ (ra_env : list (recarg * wf_paths)) (trees : list wf_paths) (lrec :list wf_paths) (c : term) {struct c} : exc (list wf_paths) := 
    c_whd <- whd_all Σ Γ c;;
    let '(x, args) := decompose_app c_whd in
    match x with 
    | tProd na type body => 
        (* the constructor has an argument of type [type] *)
        assert (args == []) "reduction is broken";;
        (* compute the recursive structure of [type] *)
        first_tree <- hd trees;;
        (*rec_tree <- raise "a";;*)
        rec_tree <- build_recargs Σ Γ ra_env first_tree type;;
        (* [na] of type [type] is non-recursive *)
        let Γ' := Γ ,, vass na type in
        let ra_env' := (Norec, mk_norec) :: ra_env in 
        (* process the rest of the constructor type *)
        rest_trees <- tl trees;;
        recargs_constr_rec Γ' ra_env' rest_trees (rec_tree :: lrec) body
    | _ => 
        (* we have processed all the arguments of the constructor -- reverse to get a valid dB-indexed context *)
        ret $ rev lrec  
    end
  in recargs_constr_rec Γ ra_env trees [] c. 


(* [get_recargs_approx env tree ind args] builds an approximation of the recargs
tree for [ind], knowing [args]. The argument [tree] is used to know when candidate
nested types should be traversed, pruning the tree otherwise. *)
Definition get_recargs_approx Σ Γ (tree : wf_paths) (ind : inductive) (args : list term) : exc wf_paths := 
  (* starting with ra_env = [] seems safe because any unbound Rel will be assigned Norec *)
  build_recargs_nested Σ Γ [] tree ind args. 


(** ** Checking fixpoints *)


(* Given a subterm spec for a term to match on, compute the subterm specs for the binders bound by a match in the individual branches. *)
(* In [match c as z in ci y_s return P with |C_i x_s => t end]
   [branches_specif Σ G c_spec ind] returns an array of x_s specs knowing
   c_spec. *)
(* [ind] is the inductive we match on. *)
Definition branches_binders_specif Σ G (discriminant_spec : subterm_spec) (ind : inductive) : exc list (list subterm_spec) := 
  (* get the arities of the constructors (without lets, without parameters) *)
  constr_arities <- (
    '(_, oib) <- lookup_mind_specif Σ ind;;
    ret $ map snd oib.(ind_ctors));;
  exc_unwrap $ mapi (fun i (ar : nat) => 
    match discriminant_spec return exc (list subterm_spec)  with 
    | Subterm _ tree => 
        (* check if the tree refers to the same inductive as we are matching on *)
        recarg_info <- except "malformed tree" $ destruct_recarg tree;;
        if negb (match_recarg_inductive ind recarg_info) then
          (* the tree talks about a different inductive than we are matching on, so all the constructor's arguments cannot be subterms  *)
          ret $ tabulate (fun _ => Not_subterm) ar
        else 
          (* get trees for the arguments of the i-th constructor *)
          constr_args_sizes <- wf_paths_constr_args_sizes tree;;
          args_sizes <- except "" $ nth_error constr_args_sizes i;;
          (* this should hopefully be long enough and agree with the arity of the constructor *)
          assert (length args_sizes == ar) "number of constructor arguments don't agree";;
          (* for each arg of the constructor: generate a strict subterm spec if they are recursive, otherwise Not_subterm. 
            These do also contain the recursive tree for that argument to enable nested matches. *)
          ret $ map spec_of_tree args_sizes 
    | Dead_code => 
        (* just propagate *)
        ret $ tabulate (fun _ => Dead_code) ar
    | Not_subterm => 
        (* just propagate *)
        ret $ tabulate (fun _ => Not_subterm) ar
    end
    ) constr_arities.


(* [fold_term_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions.
   It carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)
Definition fold_term_with_binders {X Y}(g : X -> X) (f : X -> Y -> term -> Y) (n : X) (acc : Y) (t : term) :=
  match t with 
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => acc 
  | tCast c _ t => f n (f n acc c) t
  | tProd _ t c => f (g n) (f n acc t) c
  | tLambda _ t c => f (g n) (f n acc t) c
  | tLetIn _ b t c => f (g n) (f n (f n acc b) t) c
  | tApp c l => List.fold_left (f n) l (f n acc c)
  | tProj _ c => f n acc c
  | tEvar _ l => List.fold_left (f n) l acc
  | tCase _ p c bl => List.fold_left (fun acc '(_, t) => f n acc t) bl (f n (f n acc p) c)
  | tFix mfix nb | tCoFix mfix nb => 
      let n' := Nat.iter (length mfix) g n in (* the length mfix binders for the fixes are introduced *)
      let types_and_bodies := map2 (fun a b => (a, b)) (mfix_types mfix) (mfix_bodies mfix) in 
      List.fold_left (fun acc '(type, body) => f n' (f n acc type) body) types_and_bodies acc
  end.

(* check if a de Bruijn index in range 
    n ... n + num -1 
  occurs in t *)
Unset Guard Checking.
(*FIXME: not strictly structural, just unset guard checking for now *)
(* TODO: might not handle evars/metas/casts correctly *)
Definition rel_range_occurs n num t := 
  let occur_rec := fix occur_rec n t {struct t}:= 
    match t with
    | tRel p => if Nat.leb n p && Nat.ltb p (n + num) then true else false
    | tEvar _ _ => false
    | _ => fold_term_with_binders S (fun n acc t => acc || occur_rec n t) n false t
    end
  in occur_rec n t.
Set Guard Checking.



Unset Guard Checking. 
(* Extract the [inductive] that [fixp] is doing recursion over
   (and check that the recursion is indeed over an inductive).
  Moreover give the body of [fixp] after the recursive argument and the environment (updated from [Γ])
  that contains the arguments up to (and including) the recursive argument (of course also the fixpoints). *)
(* FIXME: is not structurally recursive as we reduce before checking *)
Definition inductive_of_mutfix Σ Γ (fixp : mfixpoint term) : exc (list inductive * list (context * term)):= 
  let number_of_fixes := length fixp in
  assert (number_of_fixes != 0) "ill-formed fix";;
  let ftypes := mfix_types fixp in
  let fnames := mfix_names fixp in 
  let fbodies := mfix_bodies fixp in
  (* push fixpoints to environment *)
  let Γ_fix := push_assumptions_context (fnames, ftypes) Γ in
  let nvect := map rarg fixp in 

  (* Check the i-th definition [fixdef] of the mutual inductive block where k is the recursive argument, 
    making sure that no invalid recursive calls are in the types of the first [k] arguments, 
    make sure that the recursion is over an inductive type, 
    and return that inductive together with the body of [fixdef] after the recursive arguement
    together with its context. *)
  let find_ind i k fixdef : exc (inductive * (context * term)):= 
      (* check that a rec call to the fixpoint [fixdef] does not appear in the [k] first abstractions,
        that the recursion is over an inductive, and 
        gives the inductive and the body + environment of [fixdef] after introducing the first [k] arguments *)
      let check_occur := fix check_occur Γ n (def : term) {struct def}: exc (inductive * (context * term)) := 
        (* n is the number of lambdas we're under/aka the dB from which the mutual fixes are starting:
          n ... n + number_of_fixes - 1 *)
        def_whd <- whd_all Σ Γ def;;
        match def_whd with 
        | tLambda x t body => 
            assert (negb(rel_range_occurs n number_of_fixes t)) "bad occurrence of recursive call";;
            let Γ' := Γ ,, (vass x t) in
            if n == k then (* becomes true once we have entered [k] inner lambdas*)
              (* so now the rec arg should be at dB 0 and [t] is the type we are doing recursion over *)
              (* get the inductive type of the fixpoint, ensuring that it is an inductive *)
              '((ind, _), _) <- catchE (find_inductive Σ Γ t) (fun _ => raise "recursion not on inductive");;
              '(mib, _) <- lookup_mind_specif Σ ind;;
              if mib.(ind_finite) != Finite then (* ensure that it is an inductive *)
                raise "recursion not on inductive"
              else
                (* now return the inductive, the env after taking the inductive argument and all arguments before it, and the rest of the fix's body *)
                ret (ind, (Γ', body))
            else check_occur Γ' (S n) body
        | _ => 
            (* not a lambda -> we do not have enough arguments and can't find the recursive one *)
            raise "not enough abstractions in fix body" 
        end
      in 
      (* check that recursive occurences are nice and extract inductive + fix body *)
      res <- check_occur Γ_fix 0 fixdef;; 
      let '(ind, _) := res in
      '(_, oib) <- lookup_mind_specif Σ ind;;
      (*if oib.(ind_relevance) == Irrelevant && *)
      (* TODO some sprop checking for relevance *)
      ret res
  in 
  (* now iterate this on all the fixpoints of the mutually recursive block *)
  rv <- exc_unwrap $ map2_i find_ind nvect fbodies;;
  (* return the list of inductives as well as the fixpoint bodies in their context *)
  ret (map fst rv : list inductive, map snd rv : list (context * term)).

(* [restrict_spec_for_match Σ Γ spec rtf] restricts the size information in [spec] to what is 
allowed to flow through a match with return-type function [rtf] in environment (Σ, Γ). *)
Definition restrict_spec_for_match Σ Γ spec (rtf : term) : exc subterm_spec := 
  if spec == Not_subterm then ret Not_subterm
  else 
  '(rtf_context, rtf) <- decompose_lam_assum Σ Γ rtf;;
  (* if the return-type function is not dependent, no restriction is needed *)
  if negb(rel_range_occurs 0 (length rtf_context - 1) rtf) then ret spec 
  else
    (* decompose the rtf into context and rest and check if there is an inductive at the head *)
    let Γ' := rtf_context ++ Γ in
    '(rtf_context', rtf') <- decompose_prod_assum Σ Γ rtf;;
    let Γ'' := rtf_context' ++ Γ' in
    rtf'_whd <- whd_all Σ Γ rtf';;
    let '(i, args) := decompose_app rtf'_whd in 
    match i with 
    | tInd ind univ => (* there's an inductive [ind] at the head under the lambdas, prods, and lets *)
        match spec with 
        | Dead_code => ret Dead_code
        | Subterm size tree => 
            (* intersect with approximation obtained by unfolding *)
            recargs <- get_recargs_approx Σ Γ tree ind args;;
            recargs <- except "restrict_spec_for_match: intersection failed" $ inter_wf_paths tree recargs;;
            ret (Subterm size recargs)
        | _ => raise "this should not be reachable" (* TODO why *)
        end
    | _ => ret Not_subterm
    end.

(* check if a (function) type has an inductive co-domain *)
Definition has_inductive_codomain Σ Γ t : exc bool := 
  '(abs_context, t') <- decompose_lam_assum Σ Γ t;;
  let Γ' := abs_context ++ Γ in
  '(context', t'') <- decompose_prod_assum Σ Γ t';;
  let Γ'' := context' ++ Γ' in
  t''_whd <- whd_all Σ Γ'' t'';;
  let '(i, _) := decompose_app t''_whd in
  match i with 
  | tInd _ _ => ret true
  | _ => ret false 
  end.


Definition lookup_ind_subterms Σ (ind : inductive) :=
  '(_, oib) <- lookup_mind_specif Σ ind;;
  ret oib.(ind_recargs).

(* FIXME: is not structurally recursive *)
(* [subterm_specif Σ G stack t] computes the recursive structure of [t] applied to elements with the subterm structures given by the [stack]. 
  [G] collects subterm information about variables which are in scope. 
*)
Fixpoint subterm_specif Σ G (stack : list stack_element) t {struct t}: exc subterm_spec:= 
  t_whd <- whd_all Σ G.(loc_env) t;;
  let '(f, l) := decompose_app t_whd in 
  match f with 
  | tRel k => ret $ lookup_subterm G k
  | tCase ind_relev rtf discriminant branches => 
      let '(ind, relev) := ind_relev in
      (* push l to the stack *)
      let stack' := push_stack_closures G stack l in
      (* get subterm info for the discriminant *)
      discriminant_spec <- subterm_specif Σ G [] discriminant;;
      (* get subterm info for the binders in the branches *)
      branches_binders_specs <- branches_binders_specif Σ G discriminant_spec (fst ind);;
      (* determine subterm info for the full branches *)
      branches_specs <- exc_unwrap $ mapi (fun i branch => 
        binder_specs <- except "" $ nth_error branches_binders_specs i;;
        let stack_br := push_stack_args stack' binder_specs in
        subterm_specif Σ G stack_br branch) (map snd branches);;
      (* take their glb *)
      spec <- subterm_spec_glb branches_specs;;
      (* restrict the subterm info according to the rtf *)
      restrict_spec_for_match Σ G.(loc_env) spec rtf 
  | tFix mfix mfix_ind => 
      cur_fix <- except "invalid fixpoint index" $ nth_error mfix mfix_ind;;
      (* if the co-domain isn't an inductive, this surely can't be a subterm *)
      ind_cod <- (has_inductive_codomain Σ G.(loc_env) cur_fix.(dtype));; 
      if negb ind_cod then ret Not_subterm 
      else 
        '(context, cur_fix_codomain) <- decompose_prod Σ G.(loc_env) cur_fix.(dtype);;
        let Γ' := context ++ G.(loc_env) in 
        (* if we can't find the inductive, it is not a subterm. *)
        (* TODO is there actually a case where this is valid behvaviour? *)
        catchMap (find_inductive Σ Γ' cur_fix_codomain) (fun _ => ret Not_subterm) $ fun '((ind, _), _) => 
        let num_fixes := length mfix in
        (* get the recursive structure for the recursive argument's type *)
        rectree <- lookup_ind_subterms Σ ind;;
        (* push fixpoints to the guard env *)
        let G' := push_fix_guard_env G mfix in
        (* we let the current fixpoint be a strict subterm *)
        (* TODO: is this sound? why is it needed? nested fixes? *)
        let G' := update_guard_spec G' (num_fixes - mfix_ind) (Subterm Strict rectree) in
        let decreasing_arg := cur_fix.(rarg) in
        let body := cur_fix.(dbody) in 
        (* number of abstractions (including the one for the decreasing arg) that the body is under *)
        let num_abstractions := S decreasing_arg in
        (* split into context up to (including) the decreasing arg and the rest of the body *)
        '(context, body') <- decompose_lam_n_assum Σ G'.(loc_env) num_abstractions body;;
        (* add the arguments as Not_subterm *)
        let G'' := push_context_guard_env G' context in 
        (* push the arguments [l] _ in guard env [G] _ *)
        let stack' := push_stack_closures G stack l in

        (* before we go on to check the body: if there are enough arguments on the stack, 
          we can use the subterm information on the stack for the decreasing argument of 
          the nested fixpoint (instead of taking Not_subterm) *)
        (* we check the body with an empty stack *)
        if Nat.ltb (length stack') num_abstractions then subterm_specif Σ G'' [] body' else
          decreasing_arg_stackel <- except "" $ nth_error stack' decreasing_arg;;
          arg_spec <- stack_element_specif Σ decreasing_arg_stackel;;
          let G'' := update_guard_spec G'' 0 arg_spec in 
          subterm_specif Σ G'' [] body'
  | tLambda x ty body => 
     assert (l == []) "reduction is broken";;
     (* get the subterm spec of what the lambda would be applied to *)
     (* TODO: why don't we need to check for emptiness here?*)
     '(spec, stack') <- extract_stack_hd Σ stack;;
     subterm_specif Σ (push_guard_env G (x, ty, spec)) stack' body 
  | tEvar _ _ => 
      (* evars are okay *)
      (* TODO: check handling of Dead_code at other places *)
      ret Dead_code
  | tProj p t => 
      (* compute the spec for t *)
      (* TODO: why do we do this with the stack (instead of the empty stack)?
        shouldn't _the result_ of the projection be applied to the elements of the stack?? *)
      t_spec <- subterm_specif Σ G stack t;;
      match t_spec with 
      | Subterm _ paths => 
          arg_trees <- wf_paths_constr_args_sizes paths;;
          match arg_trees with 
          | [arg_tree] => 
              (* get the tree of the projected argument *)
              let proj_arg := snd p in
              proj_arg_tree <- except "malformed recursive tree" $ nth_error arg_tree proj_arg;;
              (* make a spec out of it *)
              ret (spec_of_tree proj_arg_tree)
          | _ => raise "projection on type having a number of constructors ≠ 1"
          end
      | Dead_code => ret Dead_code
      | Not_subterm => ret Not_subterm
      end
  | _ => ret Not_subterm
  end

(* given a stack element, compute its subterm specification *)
with stack_element_specif Σ stack_el {struct stack_el} : exc subterm_spec := 
  match stack_el with 
  | SClosure G t => subterm_specif Σ G [] t
  | SArg spec => ret spec
  end

(* get the subterm specification for the top stack element together with the rest of the stack*)
with extract_stack_hd Σ stack {struct stack} : exc (subterm_spec * list stack_element) := 
  match stack with 
  | [] => ret (Not_subterm, [])
  | h :: stack => 
      spec <- stack_element_specif Σ h;;
      ret (spec, stack)
  end.

Set Guard Checking.

(* Check that a term [t] with subterm spec [spec] can be applied to a fixpoint whose recursive argument has subterm structure [tree]*)
Definition check_is_subterm spec tree := 
  match spec with 
  | Subterm Strict tree' => 
      (* TODO: find an example where the inclusion checking is needed -- probably with nested inductives? *)
      incl_wf_paths tree tree'
  | Dead_code => true
  | _ => false
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
    intersect it with the subterm tree of xi in the stack. TODO: make this more precise
  All other subterm information is truncated to Not_subterm. 

  TODO: why do we have these constraints given by the rtf? 
*)
Definition filter_stack_domain Σ Γ (rtf : term) (stack : list stack_element) : exc (list stack_element) := 
  '(rtf_context, rtf_body) <- decompose_lam_assum Σ Γ rtf;; 
   (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if negb (rel_range_occurs 0 (length rtf_context -1) rtf_body) then ret stack 
  else
    (* enter the rtf context *)
    let Γ' := rtf_context ++ Γ in
    let filter_stack := fix filter_stack Γ t stack : exc (list stack_element) := 
      t' <- whd_all Σ Γ t;;
      match stack, t' with 
      | elem :: stack', tProd na ty t0 => 
        (* the element elem in the stack would be applied to what corresponds to the ∀ na : ty, t0 in the rtf *)
        let d := vass na ty in 
        (* decompose the type [ty] of [na] *)
        '(ctx, ty) <- decompose_prod_assum Σ Γ ty;;
        let Γ' := ctx ++ Γ in
        (* now in the context of the type *)
        whd_ty <- whd_all Σ Γ' ty;;
        (* decompose the rest of the type again and check if the LHS is an inductive *)
        let (ty', ty_args) := decompose_app whd_ty in
        (* compute what is allowed to flow through *)
        elem' <- match ty' with
          | tInd ind univ =>  
              (* it's an inductive *)
              (* inspect the corresponding subterm spec on the stack *)
              spec' <- stack_element_specif Σ elem;;
              match spec' with 
              | Not_subterm | Dead_code => ret elem (* don't restrict *)
              | Subterm s path => 
                  (* intersect with an approximation of the unfolded tree for [ind] *)
                  recargs <- get_recargs_approx Σ Γ path ind ty_args;;
                  path' <- except "intersection of trees failed" $  inter_wf_paths path recargs;;
                  (* update the recargs tree to [path'] *)
                  ret $ SArg (Subterm s path') 
              end
                 | _ => ret $ SArg Not_subterm (* if not an inductive, the subterm information is not propagated *) 
          end;;
        (* NOTE: the Coq impl goes into recursion with Γ' ,, d. I believe that is wrong and have fixed it here. *)
        rest <- filter_stack (Γ ,, d) t0 stack';;
        ret (elem' :: rest)
      | _, _ => 
          (* the rest of the stack is restricted to No_subterm, subterm information is not allowed to flow through *)
          ret (List.fold_right (fun _ acc => SArg (Not_subterm) :: acc) [] stack)
      end
    in filter_stack Γ' rtf_body stack.

From ReductionEffect Require Import PrintingEffect. 
  (*Fixpoint test (n : nat) := *)
    (*match n with *)
    (*| 0 => 0 *)
    (*| S n => print_id (S (test n))*)
    (*end.*)
  (*Eval cbn in (test 4).*)

Definition print {A} (a : A) : exc A := ret (print_id a). 

(* 
  The main checker descending into the recursive structure of a term.
  Checks if [t] only makes valid recursive calls, with variables (and their subterm information) being tracked in the context [G].

  [stack] is the list of constructor's argument specification and arguments that will be applied after reduction.
  For example: for the term [(match .. with |.. => t end) u], [t] will be checked with (the subterm information of) [u] on the stack. This is needed as we (of course) might not be able to reduce the match, but still want to be able to reason about [t] being applied to [u] after reduction.

  [trees] is the list of recursive structures for the decreasing arguments of the mutual fixpoints.*)
(* FIXME: make structurally recursive *)
Unset Guard Checking. 
Fixpoint check_rec_call (num_fixes : nat) (decreasing_args : list nat) trees
Σ G (stack : list stack_element) (t : term) {struct t} : exc unit := 
  let check_rec_call' := check_rec_call num_fixes decreasing_args trees Σ in 

  (* if [t] does not make recursive calls, then it is guarded: *)
  if negb(rel_range_occurs G.(rel_min_fix) num_fixes t) then ret tt
  else 
    t_whd <- whd_βιζ Σ G.(loc_env) t;;
    (* FIXME: the guardedness checker will not be able to determine guardedness of this function since we wrap the match in there; thus l will not be determined as a subterm (as [] isn't) *)
    let (f, l) := decompose_app t_whd in  
    match f with 
    | tRel p =>
        (* check if [p] is a fixpoint (of the block of fixpoints we are currently checking),i.e. we are making a recursive call *)
        if Nat.leb G.(rel_min_fix) p && Nat.ltb p (G.(rel_min_fix) + num_fixes) then
          (* check calls in the argument list, initialized to an empty stack*)
          _ <- list_iter (check_rec_call' G []) l;;
          (* get the position of the invoked fixpoint in the mutual block *)
          let rec_fixp_index := G.(rel_min_fix) + num_fixes -1 - p in
          (* get the decreasing argument of the recursive call *)
          decreasing_arg <- except "check_rec_call: invalid fixpoint index" $ nth_error decreasing_args rec_fixp_index;;
          (* push the arguments as closures on the stack -- we don't infer their full subterm information yet *)
          (* TODO : we don't really need to construct the updated stack here! *)
          let stack' := push_stack_closures G stack l in 
          (* get the stack entry for the decreasing argument *)
          z <- except "check_rec_call: not enough arguments for recursive fix call" $ nth_error stack' decreasing_arg;;
          (* get the tree for the recursive argument type *)
          recarg_tree <- except "check_rec_call: no tree for the recursive argument" $ nth_error trees rec_fixp_index;;
          (* infer the subterm spec of the applied argument *)
          rec_subterm_spec <- stack_element_specif Σ z;;
          (* verify that it is a subterm *)
          if negb (check_is_subterm rec_subterm_spec recarg_tree) 
          then 
            match z with 
            | SClosure z z' => raise "illegal recursive call (could not ensure that argument is decresasing)"
            | SArg _ => raise "check_rec_call: fix was partially applied"
            end
          else ret tt
        else ret tt

    | tCase ind_nparams_relev rtf discriminant branches => 
        (* match discriminant : ind return rtf with [branches] end *)
        let '((ind, nparams), relev) := ind_nparams_relev in

        catchE (
          (* check the arguments [l] it is applied to, the return-type function and the discriminant *)
          _ <- list_iter (check_rec_call' G []) l;;
          _ <- check_rec_call' G [] rtf;;
          _ <- check_rec_call' G [] discriminant;;
          (* compute the recursive argument info for the arguments of each branch by looking at the tree *)
          discriminant_spec <- subterm_specif Σ G [] discriminant;; 
          case_branch_specs <- branches_binders_specif Σ G discriminant_spec ind;; 
          (* push arguments on stack *)
          let stack' := push_stack_closures G stack l in
          (* filter the stack to only contain the subterm info which is allowed to propagate through matches *)
          stack' <- filter_stack_domain Σ G.(loc_env) rtf stack';;
          (* check the branches of the matches *)
          list_iteri (fun i '(_, branch) =>
              branch_spec <- except "check_rec_call: branch specs too short" $ nth_error case_branch_specs i;;
              (* NOTSURE push the rec arg specs for the variables introduced by the branch *)
              let stack_branch := push_stack_args stack' branch_spec in
              (* check the branch *)
              check_rec_call' G stack_branch branch) 
            branches
        )  
        (fun err => 
          (* if the checking goes wrong, we can still try harder by reducing the match away if possible *)
          discriminant <- whd_all Σ G.(loc_env) discriminant;;
          let '(hd, _) := decompose_app discriminant in
          match hd with 
          | tConstruct _ _ _ => 
              (* just check the whole thing again with the reduced discriminant *)
              check_rec_call' G [] (mkApps (tCase ind_nparams_relev rtf discriminant branches) l)
          | _ => raise err
          end)

    (* Enables to traverse Fixpoint definitions in a more intelligent
       way, ie, the rule :
       if - g = fix g (y1:T1)...(yp:Tp) {struct yp} := e &
          - f is guarded with respect to the set of pattern variables S
            in a1 ... am        &
          - f is guarded with respect to the set of pattern variables S
            in T1 ... Tp        &
          - ap is a sub-term of the formal argument of f &
          - f is guarded with respect to the set of pattern variables
            S+{yp} in e
       then f is guarded with respect to S in (g a1 ... am).
       Eduardo 7/9/98 *)
    | tFix mfix_inner fix_ind => 
        this_fix <- except "malformed fixpoint" $ nth_error mfix_inner fix_ind;;
        let decreasing_arg := rarg this_fix in 
        catchE (
          (* check args *)
          _ <- list_iter (check_rec_call' G []) l;;
          (* check types *)
          _ <- list_iter (check_rec_call' G []) (mfix_types mfix_inner);;
          (* push arguments onto the stack *)
          let stack' := push_stack_closures G stack l in 
          (* update the env with the rec. fixes *)
          let G' := push_fix_guard_env G mfix_inner in 
          list_iteri (fun j body => 
            if (fix_ind == j) && Nat.ltb decreasing_arg (length stack') then
              (* we have subterm information for the decreasing arg on the stack *)
              rec_arg_stackel <- except "should be unreachable" $ nth_error stack' decreasing_arg;; 
              (* compute the subterm spec for the recursive argument *)
              rec_arg_spec <- stack_element_specif Σ rec_arg_stackel;;
              (* check the body of the fix after entering under the arguments and adding rec_arg_spec as the specification for [decreasing_arg] *)
              check_nested_fix_body num_fixes decreasing_args trees Σ G' decreasing_arg rec_arg_spec body
            else 
              (* just check the body with an empty stack *)
              check_rec_call' G' [] body)
            (mfix_bodies mfix_inner))
          $ fun err => 
            (* try to reduce the fix away by looking for a constructor in l[decreasing_arg] *)
            if Nat.leb (length l) decreasing_arg then raise err else
            rec_arg_term <- except "should be unreachable" $ nth_error l decreasing_arg;;
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
          (* check the arguments *)
          catchE (list_iter (check_rec_call' G []) l) $ fun _ => 
          (* an error occurred, maybe it goes better if we apply the arguments reduce the constant? *)
            val <- except "constant lookup failed, this is weird :(" $ get_const_value Σ kname;;
            check_rec_call' G stack (tApp val l)
        else 
          (* just check the arguments without fallback *)
          list_iter (check_rec_call' G []) l

    | tLambda x ty body =>
        (* l is empty or reduction is broken *)
        _ <- assert (l == []) "tLambda : l should be empty";;
        (* check the type *)
        check_rec_call' G [] ty;;
        (* we take the subterm spec at the head of the stack (corresponding to the element which will be applied to this lambda)*)
        '(spec, stack') <- extract_stack_hd Σ stack;;
        (* and check the body in the updated environment with the spec for this applied element *)
        check_rec_call' (push_guard_env G (x, ty, spec)) stack' body


    | tProd x ty body => 
        (* the list [l] should be empty, otherwise reduction is broken *)
        _ <- assert (l == []) "tProd: l should be empty";;
        (* moreover, the stack should be empty: 
          We only ever put elements on the stack when we cannot reduce a match. 
          Arguments which would be applied to a Prod would however not be allowed to flow through a match. 
          TODO: this can't be the real reason: that information would still be on the stack, it would just be
            Not_subterm.
          *) 
        (*TODO Coq doesn't like the following check *)
        (*_ <- assert (stack == []) "tProd: stack should be empty";;*)
        (* check the type *)
        check_rec_call' G [] ty;;
        (* check the body: x is not a subterm *)
        check_rec_call' (push_nonrec_guard_env G (x, ty)) [] body

    | tCoFix mfix_inner fix_ind => 
        (* check the arguments *)
        _ <- list_iter (check_rec_call' G []) l;;
        (* check the types of the mfixes *)
        _ <- list_iter (check_rec_call' G []) (map dtype mfix_inner);;
        (* check the bodies *)
        let G' := push_fix_guard_env G mfix_inner in
        list_iter (check_rec_call' G' []) (map dbody mfix_inner)

    | tInd _ _ | tConstruct _ _ _ => 
        (* just check the arguments *)
        list_iter (check_rec_call' G []) l

    | tProj p c =>
        catchE (
          (* check arguments *)
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
        raise "handling of named variables is unimplemented"

    | tSort _ => 
        (* a sort shouldn't be applied to anything; guardedness is fine of course *)
        assert (l == []) "sorts shouldn't be applied to anything..."

    | tEvar _ _ => 
        (* the RHS [l] is not checked because it is considered as the evar's context *)
        (* TODO : is that really okay? *)
        ret tt
    | tApp _ _ | tLetIn  _ _ _ _ | tCast _ _ _ => raise "beta-zeta-iota reduction is broken"
    end

(* Check the body [body] of a nested fixpoint with decreasing argument [decr] (dB index) and subterm spec [sub_spec] for the recursive argument.*)
(* We recursively enter the body of the fix, adding the non-recursive arguments preceding [decr] to the guard env and finally add the decreasing argument with [sub_spec], before continuing to check the rest of the body *)
with check_nested_fix_body (num_fixes : nat) (decreasing_args : list nat) trees
Σ G (decr : nat) (sub_spec : subterm_spec) (body : term) {struct decr}: exc unit := 
  let check_rec_call' := check_rec_call num_fixes decreasing_args trees Σ in
  (* reduce the body *)
  body_whd <- whd_all Σ G.(loc_env) body;;
  match body with 
  | tLambda x ty body => 
      _ <- check_rec_call' G [] ty;; 
      match decr with 
      | 0 =>
        (* we have arrived at the recursive arg *)
        check_rec_call' (push_guard_env G (x, ty, sub_spec)) [] body 
      | S n => 
        (* push to env as non-recursive variable and continue recursively *)
        let G' := push_nonrec_guard_env G (x, ty) in  
        check_nested_fix_body num_fixes decreasing_args trees Σ G' n sub_spec body
      end
  | _ => raise "illformed inner fix body"
  end.
Set Guard Checking. 

(* Check if [def] is a guarded fixpoint body, with arguments up to (and including)
  the recursive argument being introduced in the context [G]. 
  [G] has been initialized with initial guardedness information on the recursive argument.
  [trees] is a list of recursive structures for the decreasing arguments of the mutual fixpoints.
  [recpos] is a list with the recursive argument indicese of the mutually defined fixpoints.
*)
Definition check_one_fix Σ G (recpos : list nat) (trees : list wf_paths) (def : term) : exc unit := 
  check_rec_call (length recpos) recpos trees Σ G [] def.  


Definition check_fix Σ Γ (mfix : mfixpoint term) : exc unit := 
  (* check that the recursion is over inductives and get those inductives 
    as well as the bodies of the fixpoints *)
  '(minds, rec_defs) <- inductive_of_mutfix Σ Γ mfix;;
  (* get the inductive definitions -- note that the mibs should all be the same*)
  specifs <- exc_unwrap $ map (lookup_mind_specif Σ) minds;;
  let mibs := map fst specifs in
  let oibs := map snd specifs in
  let rec_trees := map (fun oib => oib.(ind_recargs)) oibs in

  (* the environments with arguments introduced by the fix; 
     for fix rec1 a1 ... an := .... with rec2 b1 ... bm := ... 
     the environment for rec1 would be 
      [an, ...., a1, rec2, rec1]
     and the one for rec2
      [bm, ...., b1, rec2, rec1]
  *)
  let fix_envs := map fst rec_defs in     
  let fix_bodies := map snd rec_defs in   (* the bodies under the respective [fix_envs] *)
  let rec_args := map rarg mfix in 

  _ <- exc_unwrap $ mapi (fun i fix_body => 
    fix_env <- except "fix_envs too short" $ nth_error fix_envs i;;
    rec_tree <- except "rec_trees too short" $ nth_error rec_trees i;;
    rec_arg <- except "rec args too short" $ nth_error rec_args i;;
    (* initial guard env *)
    let G := init_guard_env fix_env rec_arg rec_tree in
    (* check the one fixpoint *)
    check_one_fix Σ G rec_args rec_trees fix_body 
    ) fix_bodies;;
  ret tt.

























































From MetaCoq.Template Require Import Environment utils.RTree Ast AstUtils All. 
Open Scope string_scope.
Require Import List String.
Import ListNotations.
Open Scope string_scope.

Module kernel_lists.
(* Kernel representation of lists *)
Definition list_indname : inductive := 
  {|
   inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
   inductive_ind := 0 
  |}.
  
(* NOTE: the constructor arguments in recargs trees are always without lets and without params! *)
Definition list_recargs : wf_paths := 
  Rec 0 [ Node (Mrec list_indname) [ Node Norec []; Node Norec [ Node Norec []; 
                                                                 Param 0 1]
                                   ]
        ].
Eval cbn in (expand (list_recargs)). 

(*Inductive test := *)
  (*| abc : let a := 10 * 10 in nat -> test. *)

(*Eval hnf in let a := 10 * 10 in nat -> test.*)

(*Print one_inductive_body.*)
(* I don't really care about universes, just use Set everywhere *)

Definition list_indbody : one_inductive_body := 
  {| 
    ind_name := "list";
    ind_type := tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                      (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.60"))))
                      (tSort (Universe.from_kernel_repr (Level.lSet, false) [(Level.Level "Coq.Init.Datatypes.60", false)]));
    ind_kelim := InType;
    ind_ctors := [("nil", tProd {|
                               binder_name := nNamed "A";
                               binder_relevance := Relevant |}
                             (tSort
                                (Universe.of_levels
                                   (inr
                                      (Level.Level "Coq.Init.Datatypes.60"))))
                             (tApp (tRel 1) [tRel 0]), 0);
                          ("cons",
                          tProd
                            {|
                            binder_name := nNamed "A";
                            binder_relevance := Relevant |}
                            (tSort
                               (Universe.of_levels
                                  (inr
                                     (Level.Level "Coq.Init.Datatypes.60"))))
                            (tProd
                               {|
                               binder_name := nAnon;
                               binder_relevance := Relevant |} 
                               (tRel 0)
                               (tProd
                                  {|
                                  binder_name := nAnon;
                                  binder_relevance := Relevant |}
                                  (tApp (tRel 2) [tRel 1])
                                  (tApp (tRel 3) [tRel 2]))), 2)];
               ind_projs := [];
               ind_relevance := Relevant;
               ind_recargs := list_recargs |}. 



(* I don't care about universes. *)
Definition univdecl := Monomorphic_ctx
                   (LevelSetProp.of_list
                      [Level.Level "Coq.Init.Datatypes.60"],
                   ConstraintSet.empty).


Definition list_param_ctxt := 
[{|
   decl_name := {|
                binder_name := nNamed "A";
                binder_relevance := Relevant |};
   decl_body := None;
   decl_type := tSort
                  (Universe.of_levels
                     (inr (Level.Level "Coq.Init.Datatypes.60"))) |}].
Definition list_mindbody : mutual_inductive_body := 
  {| 
    ind_bodies := [list_indbody];
    ind_finite := Finite;
    ind_npars := 1;
    (*ind_npars_unif := 1;*)
    ind_params := list_param_ctxt;
    ind_universes := univdecl;
    ind_variance := None;
  |}.


Definition list_entry := (MPfile ["Datatypes"; "Init"; "Coq"], "list", InductiveDecl list_mindbody). 

(*From MetaCoq.Template Require Import Inductives.*)

Require Import List String.
Import MonadNotation.
Import ListNotations.
Open Scope string_scope.

(*Definition list_env. *)
(* explicit instantiation with TemplateMonad as a definition parametric over the monad causes trouble with universe polymorphism *)
Definition list_iter {X} (f : X -> TemplateMonad unit) (l : list X) : TemplateMonad unit := 
  List.fold_left (fun (acc : TemplateMonad unit) x => _ <- acc;; f x) l (ret tt).


(* whoops, I've turned the guardedness checker off *)
Unset Guard Checking.
Fixpoint broken_app {A : Type} (l m : list A) {struct l} := 
  match l with
  | [] => m
  | a :: l' => broken_app l m
  end.

Unset Guard Checking.
(*Set Typeclasses Debug.*)
(*Check (_ : Monad TemplateMonad). *)
Fixpoint check_fix_term (Σ : global_env) (Γ : context) (t : term) {struct t} := 
  match t with 
  | tFix mfix _ => 
      (* TODO: we should first recursively check the body of the fix (in case of nested fixpoints!) *)
      (*tmPrint mfix ;;*)
      (*tmPrint Σ*)
      (*ret tt*)
      (*let Σ := *)
      catchMap (check_fix Σ Γ mfix) 
        (fun s => tmPrint s) (fun _ => tmPrint "success")
  | tCoFix mfix idx =>
      (* TODO *)
      ret tt
  | tLambda na T M => 
      _ <- check_fix_term Σ Γ T;;
      _ <- check_fix_term Σ (Γ ,, vass na T) M;;
      ret tt
  | tApp u v => 
      _ <- check_fix_term Σ Γ u;;
      _ <- list_iter (check_fix_term Σ Γ) v;;
      ret tt
  | tProd na A B => 
      _ <- check_fix_term Σ Γ A;;
      _ <- check_fix_term Σ (Γ ,, vass na A) B;;
      ret tt
  | tCast C kind t => 
      _ <- check_fix_term Σ Γ C;;
      _ <- check_fix_term Σ Γ t;;
      ret tt
  | tLetIn na b t b' => 
      _ <- check_fix_term Σ Γ b;;
      _ <- check_fix_term Σ Γ t;;
      _ <- check_fix_term Σ (Γ ,, vdef na b t) b';;
      ret tt
  | tCase ind rtf discriminant brs =>
    _ <- check_fix_term Σ Γ rtf;;
    _ <- check_fix_term Σ Γ discriminant;;
    _ <- list_iter (fun '(_, b) => check_fix_term Σ Γ b) brs;;
    ret tt
  | tProj _ C => 
      _ <- check_fix_term Σ Γ C;;
      ret tt
  | tConst kn u => 
      match lookup_env_const Σ kn with 
      | Some const => 
          match const.(cst_body) with 
          | Some t => check_fix_term Σ Γ t
          | _ => ret tt
          end
      | None => ret tt
      end
  | _ => ret tt 
      (*tmPrint t;; tmPrint "not a fix" *)
  end.

Definition check_fix Σ t := check_fix_term Σ [] t. 



Definition check_fix_start {A} (a : A) :=
  mlet (Σ, t) <- tmQuoteRec a ;;
  check_fix (list_entry :: Σ) t.
MetaCoq Run (check_fix_start broken_app ). 
MetaCoq Run (check_fix_start app ). 
