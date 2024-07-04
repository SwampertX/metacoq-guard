(* From MetaCoq.Guarded Require Import printers.  *)
From MetaCoq.Template Require Import Checker. 
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst Universes Environment Reflect.
From MetaCoq.Template Require Import Ast AstUtils.
From MetaCoq.Template Require Import LiftSubst Pretty.
From MetaCoq.Guarded Require Import MCRTree. 

From MetaCoq.Guarded Require Export Except util.

(** * Common preliminaries of the positivity and guard checkers *)

(** Exceptions *)
(** most of the code runs in a monad for handling errors/exceptions *)
Declare Scope exc_scope.
Open Scope exc_scope.

Notation loc := string (only parsing).

(** ** Trace-monad based *)
From MetaCoq.Guarded Require Export Trace. 

(** TODO YJ: what do the parameters mean? *)
Inductive fix_guard_error :=
  | NotEnoughAbstractionInFixBody
  | RecursionNotOnInductiveType : term -> fix_guard_error
  | RecursionOnIllegalTerm : nat -> (context * term) -> (list nat * list nat) -> fix_guard_error
  | NotEnoughArgumentsForFixCall : nat -> fix_guard_error
  | FixpointOnIrrelevantInductive.

Inductive guard_exc := 
  | ProgrammingErr (w : loc) (s : string)
  | OtherErr (w : loc) (s : string)
  | EnvErr (w: loc) (kn : kername) (s : string)
  | IndexErr (w : loc) (s : string) (i : nat)
  | GuardErr (w : loc) (s : string) (e : fix_guard_error)
  | PositivityError (w : loc) (s : string)
  | TimeoutErr. 

(*max bind steps *)
Definition max_steps := 500. 
Definition catchE := @catchE max_steps. 
Arguments catchE {_ _}. 
Definition catchMap := @catchMap max_steps _ TimeoutErr. 
Arguments catchMap {_ _}. 
  
Instance: Monad (@TraceM guard_exc) := @trace_monad max_steps guard_exc TimeoutErr. 
Notation "'exc' A" := (@TraceM guard_exc A) (at level 100) : exc_scope. 
Definition unwrap := @trc_unwrap.
Arguments unwrap { _ _ _ _}. 

Instance: TrcUnwrap list := list_trc_unwrap max_steps TimeoutErr.

Notation "a == b" := (eqb a b) (at level 70) : exc_scope. 
Notation "a != b" := (negb(a==b)) (at level 90) : exc_scope.

(** As the guardedness checker reduces terms at many places before reducing, the key functions are not structurally recursive. 
  We therefore disable the guardedness checker for this file. *)
(* Unset Guard Checking.  *)


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

Definition mind_specif := mutual_inductive_body * one_inductive_body.

(* In Coq kernel speak, an arity is the type of an inductive without the parameters (i.e. what comes after the colon when writing down the inductive) *)
Record inductive_arity := {
    ind_user_arity : term; (* the full arity *)
    ind_sort : sort        (* just the sort *)
  }.

Fixpoint ind_get_sort (arity : term) : sort := 
  match arity with 
  | tSort s => s
  | tLetIn _ _ _ t => ind_get_sort t
  | tProd _ _ t => ind_get_sort t
  | _ => sProp
  end.

(* decompose a term prefixed by prods/lets into the context given by the declarations and the remaining term *)
Definition decompose_let_prod_env (t : term) : context * term := 
  let decomp := fix decomp (t : term) (acc : context) := 
      match t with 
      | tProd na ty t => 
          decomp t (mkdecl na None ty :: acc)
      | tLetIn na def ty t => 
          decomp t (mkdecl na (Some def) ty :: acc)
      | _ => (acc, t)
      end
  in decomp t []. 


Fixpoint decompose_prod_n (t : term) (n : nat) : (list aname * list term) * term := 
  match n with 
  | 0 => ([], [], t)
  | S n => 
      match t with 
      | tProd na A B => let (nAs, B) := decompose_prod_n B n in
                        let (ns, As) := nAs in
                        (na :: ns, A :: As, B)
      | _ => ([],[], t)
      end
  end.
(* decompose the type of an inductive into the parameter context (parameters) and the arity *)
Definition decompose_arity (t : term) (nparams : nat) : context * inductive_arity.
  pose (typ := decompose_prod_n t nparams).
  destruct typ as [[names types] ar].
  apply (List.firstn nparams) in names.
  apply (List.firstn nparams) in types.
  split.
  refine (List.rev (map (fun '(x, ty) => vass x ty) (combine names types))). 
  constructor.
  exact ar. exact (ind_get_sort ar). 
Defined.

(** Arity sort and original user arity Ui*)
Definition ind_arity (i : mind_specif) := 
  let (mib, oib) := i in 
  snd (decompose_arity (oib.(ind_type)) mib.(ind_npars)). 
Definition param_ctxt (i : mind_specif) := 
  let (mib, oib) := i in 
  fst (decompose_arity (oib.(ind_type)) mib.(ind_npars)). 

Definition user_arity_ctxt (user_arity : term) := 
  fst (decompose_let_prod_env user_arity).

(** Arity context of [Ii] with parameters: [forall params, Ui] *)
(* NOTE: does also contain lets and indices! *)
Definition ind_arity_ctxt (i : mind_specif) := 
  let (mib, oib) := i in 
  let (param_ctx, ar) := (decompose_arity oib.(ind_type) mib.(ind_npars)) in
  (user_arity_ctxt (ar.(ind_user_arity))) ++ param_ctx. 

(** Names of the constructors: [cij] *)
Definition ind_consnames (i : mind_specif) := 
  map cstr_name (snd i).(ind_ctors). 

(** Types of the constructors with parameters:  [forall params, Tij],
     where the Ik are replaced by de Bruijn index in the
     context I1:forall params, U1 ..  In:forall params, Un *)
Definition ind_user_lc (i : mind_specif) : list term := 
  map cstr_type (snd i).(ind_ctors).


Definition ind_ctors_hnf (i : mind_specif) := map (fun t => decompose_let_prod_env t) (ind_user_lc i).

(** Compute the number of parameters which can at most be uniform for an inductive. *)
Definition one_inductive_num_uniform (i : mind_specif) :=
  let ctors_hnf := ind_ctors_hnf i in
  let num_pars := (fst i).(ind_npars) in
  let one_constr '(ctx, con) :=
    match con with
    | tApp _ app => constr_result_num_uniform ctx num_pars app
    | _ => 0
    end in
  List.fold_left (fun acc c => min acc (one_constr c)) ctors_hnf num_pars.


(** Computes the number of uniform parameters of the mutual inductive definition [i]. 
  Note: In Coq, for an inductive declaration 
    Inductive I X1 ... Xn : U := ...
  if Xi is non-uniform, then also Xj for j >= i are treated as non-uniform.
  That is, from the number of uniform parameters we can restore which parameters are uniform (from Coq's perspective). 
*)
Definition num_uniform_params (mib : mutual_inductive_body) : nat := 
  List.fold_left (fun acc oib => min acc (one_inductive_num_uniform (mib, oib))) mib.(ind_bodies) mib.(ind_npars). 



Implicit Types (Σ : global_env_ext) (Γ : context). 
Implicit Types (kn : kername) (c: term).

Open Scope bs.

Definition ctx_names Γ : list ident := [].

(** ** Reduction and Environment Handling *)
Definition whd_all Σ Γ t : exc term := 
  except (OtherErr "whd_all" ("reduction error or out of fuel " ++ print_term Σ (ctx_names Γ) true t)) $ reduce_stack_term RedFlags.default Σ Γ default_fuel t. 

(** β, ι, ζ weak-head reduction *)
Definition whd_βιζ Σ Γ t : exc term := 
  let redflags := RedFlags.mk true true true false false false in
  except (OtherErr "whd_βιζ" "reduction error or out of fuel") $ reduce_stack_term redflags Σ Γ default_fuel t. 

(** no let/ζ reduction *)
Definition whd_all_nolet Σ Γ t : exc term := 
  let redflags := RedFlags.mk true true false true true true in
  except (OtherErr "whd_all_nolet" "reduction error or out of fuel") $ reduce_stack_term redflags Σ Γ default_fuel t. 

Definition lookup_env_const Σ kn : option constant_body := 
  match lookup_env Σ kn with 
  | Some (ConstantDecl const) => Some const
  | _ => None
  end.

(* NOTE: this does not accurately model the intended behaviour as MetaCoq ignores opaqueness *)
Definition is_evaluable_const Σ kn := 
  match lookup_env_const Σ kn with
  | Some const =>
      match const.(cst_body) with
      | Some _ => true
      | _ => false
      end
  | _ => false
  end.

(* NOTE: same as above -- are we really allowed to reduce this?*)
Definition get_const_value Σ kn : option term := 
  match lookup_env_const Σ kn with
  | Some const => const.(cst_body)
  | None => None
  end.

(** lookup a mutual inductive *)
Definition lookup_mib Σ kn : exc mutual_inductive_body := 
  match lookup_env Σ kn with 
  | Some (InductiveDecl ind) => ret ind
  | _ => raise $ EnvErr "lookup_mib" kn "could not find inductive in global env"
  end.

(** lookup an inductive *)
Definition lookup_mind_specif Σ (ind : inductive) : exc mind_specif := 
  mib <- lookup_mib Σ ind.(inductive_mind) ;;
  ib <- except (IndexErr "lookup_mind_specif" "invalid inductive index" ind.(inductive_ind)) $ 
    nth_error mib.(ind_bodies) ind.(inductive_ind);;
  ret (mib, ib).


(** if [t] evaluates to an application (weak-head) and the LHS is an inductive, return it together with the RHS (list) *)
Definition find_rectype Σ Γ t : exc inductive * Instance.t * list term:= 
  t <- whd_all Σ Γ t;; 
  let (t, l) := decompose_app t in 
  match t with 
  | tInd i u => ret ((i, u), l)
  | _ => raise $ OtherErr "find_rectype" "head is not an inductive"
  end. 


(** the same, but only if the rectype is an inductive or record (bifinite) *)
Definition find_inductive Σ Γ t := 
  '((i, u), l) <- find_rectype Σ Γ t;;
  '(mib, _) <- lookup_mind_specif Σ i;;
  if mib.(ind_finite) != CoFinite then ret ((i, u), l) 
    else raise $ OtherErr "find_inductive" "inductive is cofinite".

(** only if coinductive *)
Definition find_coinductive Σ Γ t := 
  '((i, u), l) <- find_rectype Σ Γ t;;
  '(mib, _) <- lookup_mind_specif Σ i;;
  if mib.(ind_finite) == CoFinite then ret ((i, u), l) 
    else raise $ OtherErr "find_coinductive" "inductive is not cofinite".

(** push assumptions to the de Bruijn context *)
Definition push_assumptions_context '(names, types) Γ := 
  (* we use fold_left, so the i-th element that is pushed to the context needs to be lifted by i *)
  let ctxt := map2_i (fun i name type => vass name (lift0 i type)) names types in
  List.fold_left (fun acc assum => acc ,, assum) ctxt Γ. 

Unset Guard Checking. 
(** [decompose_lam_assum Σ Γ ty] decomposes [ty] into a context of lambdas/lets and a remaining type, after reducing *)
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

(** [decompose_prod_assum Σ Γ ty] decomposes [ty] into a context of prods/lets and a remaining type, after reducing *)
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
        (** try to reduce *)

        (** TODO: commented reduction because this is ****ing slow /diverges *)
        (** precisely: while the whd_all is fast due to laziness, the equality test takes forever (stopped after a few minutes) due to reducing the wrong redexes *)
        (** this does already happen when e.g. ty = [tInd nat] (i.e., the whd_all could terminate in very few steps if the reduction strategy would pick the right redexes) *)
        
        (*ty_whd' <- whd_all Σ Γ ty_whd;;*)
        (*if ty_whd == ty_whd' then ret (Γ0, ty_whd) else prodec_rec Γ Γ0 ty_whd'*)
        ret (Γ0, ty)
    end 
  in prodec_rec Γ []. 

(** [decompose_prod Σ Γ ty] decomposes [ty] into a context of prods and a remaining type, after reducing *)
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

Set Guard Checking. 
(** [decompose_lam_n_assum Σ Γ n t] decomposes [t] into a context of lambdas and lets. 
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
             | tCast t _ _ => lamdec_rec Γ Γ0 n t
             | _ => raise $ OtherErr "decompose_lam_n_assum" "not enough abstractions"
             end
    end
  in lamdec_rec Γ [] n t. 

(* [decompose_prod_n_assum Σ Γ n t] decomposes [t] into a context of prods and lets. 
  We expect [n] prods and also take all the lets up to the n-th prod, but no more lets after the n-th prod. *)
Definition decompose_prod_n_assum Σ Γ n (t : term) : exc (context * term) := 
    let prodec_rec := fix prodec_rec Γ Γ0 n t {struct t} := 
    match n with
    | 0 => ret (Γ0, t)
    | S n => match t with 
             | tProd x ty body => 
                 let d := vass x ty in
                 prodec_rec (Γ ,, d) (Γ0 ,, d) n body
             | tLetIn x def ty body => 
                let d := vdef x def ty in 
                prodec_rec (Γ ,, d) (Γ0 ,, d) (S n) body
             | tCast t _ _ => prodec_rec Γ Γ0 n t
             | _ => raise $ OtherErr "decompose_prod_n_assum" "not enough prods"
             end
    end
  in prodec_rec Γ [] n t. 


(** pseudo-reduction rule:
  [hnf_prod_app env (Prod(_,B)) r] --> [B[r]]
  with a HNF on [t] to produce a product. *)
Definition hnf_prod_app Σ Γ t r : exc term := 
  t_whd <- whd_all Σ Γ t;;
  match t_whd with 
  | tProd _ _ body => ret $ subst10 r body
  | _ => raise $ OtherErr "hnf_prod_app" "need a product"
  end.
(** use the previous reduction to apply a list of arguments [l] to [t]. *)
Definition hnf_prod_apps Σ Γ t l : exc term := 
  List.fold_left (fun acc r => acc <- acc;; hnf_prod_app Σ Γ acc r) l (ret t). 


Definition mfix_names (fixp : mfixpoint term) := map dname fixp. 
Definition mfix_types (fixp : mfixpoint term) := map dtype fixp.
Definition mfix_bodies (fixp : mfixpoint term) := map dbody fixp.

(** [fold_term_with_binders g f n acc c] folds [f n] on the immediate
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
  | tCase _ p c bl => List.fold_left (fun acc '(mk_branch _ t) => f n acc t) bl (f n (f n acc p.(preturn)) c)
  | tFix mfix nb | tCoFix mfix nb => 
      let n' := Nat.iter (length mfix) g n in (* the length mfix binders for the fixes are introduced *)
      let types_and_bodies := map2 (fun a b => (a, b)) (mfix_types mfix) (mfix_bodies mfix) in 
      List.fold_left (fun acc '(type, body) => f n' (f n acc type) body) types_and_bodies acc
  | tInt _ | tFloat _ | tArray _ _ _ _ => acc (* primitives *)
  end.

(** check if a de Bruijn index in range 
    n ... n + num -1 
  occurs in t *)
(* TODO: might not handle evars/metas/casts correctly *)
#[bypass_check(guard)]
Definition rel_range_occurs n num t := 
  let occur_rec := fix occur_rec n t {struct t}:= 
    match t with
    | tRel p => if Nat.leb n p && Nat.ltb p (n + num) then true else false
    | tEvar _ _ => false
    | _ => fold_term_with_binders S (fun n acc t => acc || occur_rec n t) n false t
    end
  in occur_rec n t.

(** check if a (function) type has an inductive co-domain *)
(** Counterpart: [check_inductive_codomain] *)
Definition has_inductive_codomain Σ Γ t : exc bool := 
  '(abs_context, t') <- decompose_lam_assum Σ Γ t;;
  let Γ' := Γ ,,, abs_context in
  '(context', t'') <- decompose_prod_assum Σ Γ t';;
  let Γ'' :=  Γ' ,,, context' in
  t''_whd <- whd_all Σ Γ'' t'';;
  let '(i, _) := decompose_app t''_whd in
  match i with 
  | tInd _ _ => ret true
  | _ => ret false 
  end.



(** ** Tools for wf_paths *)

Inductive recarg_type :=
  (* "internal" recursion on (one of) the (mutual) inductive(s). *)
  | RecArgInd (i : inductive) 
  (* "external" recursion on inductives outside the currently-defined mutual group.
    has nothing to do with nested induction, since nesting is eventually inlined (TODO: find proof) *)
  | RecArgPrim (c : kername). 

Definition eqb_recarg_type (rt1 rt2 : recarg_type) :=
  match rt1, rt2 with
    | RecArgInd i1, RecArgInd i2 => eqb i1 i2
    | RecArgPrim c1, RecArgPrim c2 => eqb c1 c2
    | _, _ => false
  end.
Instance reflect_recarg_type : ReflectEq recarg_type.
Proof.
  refine {| eqb := eqb_recarg_type |}. 
  intros [] []; unfold eqb_recarg_type; finish_reflect. 
Defined.

(* Recursive argument labels for representing the recursive structure of constructors of inductive types. *)
Inductive recarg := 
  | Norec                   (* Non-recursive argument *)
  | Mrec (i : recarg_type). (* Recursive argument of type [i] *)

Definition wf_paths := rtree recarg.

Instance reflect_rtree (X : Type) (H: ReflectEq X): ReflectEq (rtree X).
Proof. 
  refine {| eqb := rtree_eqb eqb |}.  
  intros [] []; unfold rtree_eqb; simpl.
  all: try solve [constructor ; discriminate].

  - destruct (eqb_spec tree_index tree_index0);
    destruct (eqb_spec ind_index ind_index0);
    try subst; simpl.
Admitted.  (* FIXME *)

Definition eqb_recarg (x y : recarg) := 
  match x, y with 
  | Norec, Norec => true
  | Mrec i, Mrec i' => eqb i i'
  | _, _ => false
  end.
Instance reflect_recarg : ReflectEq recarg. 
Proof. 
  refine {| eqb := eqb_recarg |}. 
  intros [] []; unfold eqb_recarg; finish_reflect. 
Defined.




(** wf_paths env *)
(** Since the MC representation of inductives does not include wf_paths, we infer them using the positivity checker and keep an additional paths_env. *)
Definition pathsEnv := list (kername * list wf_paths).
Implicit Type (ρ : pathsEnv).

(** Lookup the wf_paths for an inductive [i]. *)
Definition lookup_paths ρ (i : inductive) := 
  match lookup eqb i.(inductive_mind) ρ with
  | Some paths => nth_error paths i.(inductive_ind) 
  | None => None
  end.

Definition lookup_paths_all ρ (i : inductive) := 
  lookup eqb i.(inductive_mind) ρ.


(** In contrast to the Boolean equality decider we get by eqb, this also checks equivalence if structural equality is failing by unfolding the recursive trees. *)
Definition eq_wf_paths a b := rtree_equal (eqb (A := recarg)) a b.

(** Join the recarg info if compatible. *)
Definition inter_recarg r1 r2 := 
  if (eqb (A := recarg)) r1 r2 then Some r1 else None.
  (* match r1, r2 with
  | Norec, Norec => Some Norec
  | Mrec i1, Mrec i2
  | Imbr i1, Imbr i2
  | Mrec i1, Imbr i2 => if i1 == i2 then Some r1 else None (* intersection is an Mrec, not an Imbr, if one is an Mrec *)
  | Imbr i1, Mrec i2 => if i1 == i2 then Some r2 else None
  | _, _ => None
  end. *)

(** *** Operations on recursive arguments trees *)

(** Intersection and equality test on [wf_paths]. Needed to restrict subterm information flowing through dependent matches.*)
Definition inter_wf_paths a b := 
  rtree_inter (eqb (A := recarg)) inter_recarg Norec a b.
Definition incl_wf_paths a b := 
  rtree_incl (eqb (A := recarg)) inter_recarg Norec a b.
Definition equal_wf_paths a b := 
  rtree_equal (eqb (A := recarg)) a b.

Definition mk_norec := mk_node Norec []. 

(** Given a recargs tree [t] representing an inductive type,
  returns a list of trees corresponding to the i-th constructor of [t]. *)
(** Complexity: Linear in number of constructors. *)
Definition wf_paths_constr_args_sizes t i : exc (list wf_paths) := 
  let fn_name := "wf_paths_constr_args_sizes" in
  (** By destructing the tree, we get the root and its constructors. *)
  destruct_node t (fun ra constrs =>
    (** Of which the root should not be Norec *)
    assert (match ra with Norec => false | _ => true end) $ ProgrammingErr fn_name "should not be called with Norec";;
    constr <- except (ProgrammingErr fn_name "index i of constructor out of bound") (nth_error constrs i);;
    l <- destruct_node constr (fun _ args => ret args) (raise $ ProgrammingErr "wf_paths_constr_args_sizes" "expected node");;
    ret l)
  (raise $ ProgrammingErr fn_name "expected node").

(** Given a recargs tree [t] representing an inductive type, returns a list of
list of trees. Each inner list corresponds to a constructor of [t], and has
a tree for every argument of the constructor. (edit: clarity) *)
Definition wf_paths_all_constr_args_sizes t : exc (list (list wf_paths)) := 
  destruct_node t (fun ra constrs => (** YJ: constrs = constructors not constraints :sweat_smile: *)
    assert (match ra with Norec => false | _ => true end) $ ProgrammingErr "wf_paths_constr_args_sizes" "should not be called with Norec";;
    l <- unwrap $ map (fun t => destruct_node t (fun _ args => ret args) (raise $ ProgrammingErr "wf_paths_all_constr_args_sizes" "expected node")) 
      constrs;;
    ret l)
  (raise $ ProgrammingErr "wf_paths_constr_args_sizes" "expected node").


(** Given a list of lists with the trees for the arguments (excluding parameters) of each constructor, 
  construct the tree for a particular inductive type. 
  (This is not really a fully correct tree, as this is just the tree for one of the mutual inductives.) *)
Definition mk_ind_paths rarg constr_arg_trees : wf_paths := 
  mk_node rarg (map (fun l => mk_node Norec l) constr_arg_trees). 


(** Puts lambdas accepting sorts [0].. [n-1] (for some dummy sorts) in front of [t] (and lift [t] accordingly)*)
(** We don't care about the exact universe as this is only relevant for checking guardedness -- it only needs to reduce afterwards *)
Definition lam_implicit_lift n t := 
  let anon := mkBindAnn nAnon Relevant in
  let some_sort := tSort (sType (Universe.make (Level.level "guarded_implicit", 0))) in 
  let lambda_implicit t := tLambda anon some_sort t in 
  Nat.iter n lambda_implicit (lift0 n t). 

(** This removes global parameters of the inductive types in [constrs] (for nested inductive types only). *)
(** for instance: if [constrs] is the list of [list] constructors, 
  then we get back (roughly): [∀ X, (λ X, Rel 2) X;
                               ∀ X (x : X) (l : (λ X, Rel 3) X), (λ X, Rel 4) X]
  i.e. we assume that at index 0 (at the outside) there is [list] instantiated with a parameter 
  and we ignore the parameter X for the recursive occurrences of [list] in the constructor. *)
(** Note : in the types in [constrs], the dBs 0... ntyps-1 refer to the mutual inductives. *)
(** Now we substitute the references to these types. *)
(** Effectively, this means that we just ignore the parameters and instead assume that at indices [0]... [ntypes-1], there are the inductive types already instantiated with some parameters. *)
Definition abstract_params_mind_constrs num_types num_params (constrs : list term) :=
  (* if there are no parameters, there is no abstracting to do *)
  if num_params == 0 then constrs
  else 
    (* make lambdas abstracting over the parameters *)
    let make_abs := tabulate (fun i => lam_implicit_lift num_params (tRel i)) num_types in
    (* substitute the recursive occurences of the inductive types by these abstractions *)

    map (subst0 make_abs) constrs.

