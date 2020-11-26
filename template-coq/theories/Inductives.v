
From MetaCoq.Checker Require Import Checker. 
From MetaCoq.Template Require Import utils BasicAst Ast AstUtils.
From MetaCoq.Template Require Import Universes Environment Reflect LiftSubst. 
From MetaCoq.Template.utils Require Import RTree. 
From MetaCoq.Template Require Import utils.Except.



Notation "a == b" := (eqb a b) (at level 90). 
Notation "a != b" := (negb(a==b)) (at level 90).



(** * WIP : An implementation of the guardedness checker *)

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




(* head-normalized constructor types so that their conclusion exposes the inductive type -- context contains the parameters *)
(* TODO : similar to ind_user_lc, this might not reflect the actual Coq definition *)
Definition ind_ctors_hnf (i : mind_specif) : exc (list (context * term)) := 
  let (mib, oib) := i in
  let npars := mib.(ind_npars) in 
  let without_params := map (fun t => snd (decompose_prod_n t npars)) (ind_user_lc (mib, oib)) in 
  let params := param_ctxt (mib, oib) in
  hnfed <- exc_unwrap $ map (whd_all [] params) without_params;;
  ret (map (fun t => (params, t)) hnfed).


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


(* TODO:move*)
Definition map2_i { A B C} (f : nat -> A -> B -> C) (a : list A) (b : list B) := 
  let map2' := fix rec a b n := 
     match a, b with
     | a0 :: a, b0 :: b => f n a0 b0 :: rec a b (S n)
     | _, _ => []
     end
  in map2' a b 0.

(* push assumptions to the de Bruijn context *)
Definition push_assumptions_context '(names, types) Γ := 
  (* we use fold_left, so the i-th element that is pushed to the context needs to be lifted by i *)
  let ctxt := map2_i (fun i name type => vass name (lift0 i type)) names types in
  List.fold_left (fun acc assum => acc ,, assum) Γ ctxt. 


Definition mfix_names (fixp : mfixpoint term) := map dname fixp. 
Definition mfix_types (fixp : mfixpoint term) := map dtype fixp.
Definition mfix_bodies (fixp : mfixpoint term) := map dbody fixp.

(* [decompose_lam_assum Γ ty] decomposes [ty] into a context of lambdas/lets and a remaining type, after reducing *)
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

(* [decompose_prod_assum Γ ty] decomposes [ty] into a context of prods/lets and a remaining type, after reducing *)
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


Definition mk_norec := mk_node Norec []. 

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
(* TODO: figure out the role of SArg *)
Inductive stack_element := 
  | SClosure G (t : term)
  | SArg (s : subterm_spec). 

(* push a list of closures [l] with guard env [G] to the stack *)
Definition push_stack_closures G l stack := 
  List.fold_right (fun h acc => (SClosure G h) :: acc) l stack. 

(* push a list of args [l] to the stack *)
Definition push_stack_args l stack := 
  List.fold_right (fun h acc => SArg h :: acc) l stack. 



(* This code is very
close to check_positive in indtypes.ml, but does no positivity check and does not
compute the number of recursive arguments. *)
Fixpoint build_recargs Σ Γ (ra_env : list (recarg * wf_paths)) (tree : wf_paths) (t : term) : exc wf_paths := 
  (* TODO *)
  ret (Node Norec [])

with build_recargs_nested Σ Γ (ra_env : list (recarg * wf_paths)) (tree : wf_paths) (ind_args : (inductive * Instance.t) * list term) : exc wf_paths := 
  (* TODO *)
    ret (Node Norec [])

with build_recargs_constructors Σ Γ (ra_env : list (recarg * wf_paths)) (trees : list wf_paths) (t : term) : exc (list wf_paths) := 
  (* TODO *)
  ret [].    


(* [get_recargs_approx env tree ind args] builds an approximation of the recargs
tree for [ind], knowing [args]. The argument [tree] is used to know when candidate
nested types should be traversed, pruning the tree otherwise. *)
Definition get_recargs_approx Σ Γ (tree : wf_paths) (ind : inductive * Instance.t) (args : list term) : exc wf_paths := 
  (* starting with ra_env = [] seems safe because any unbound Rel will be assigned Norec *)
  build_recargs_nested Σ Γ [] tree (ind, args). 


(** ** Checking fixpoints *)

(* TODO move *)
Definition assert (b : bool) (err : string) : exc unit := 
  match b with 
  | false => raise err
  | true => ret tt
  end.

(* Given a subterm spec for a term to match on, compute the subterm specs for the binders bound by a match in the individual branches. *)
(* In {match c as z in ci y_s return P with |C_i x_s => t end}
   [branches_specif renv c_spec ci] returns an array of x_s specs knowing
   c_spec. *)
Definition branches_specif Σ G (discriminant_spec : subterm_spec) : exc list (list subterm_spec) := 
  (* TODO *)
  ret [].



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
            recargs <- get_recargs_approx Σ Γ tree (ind, univ) args;;
            recargs <- except "restrict_spec_for_match: intersection failed" $ inter_wf_paths tree recargs;;
            ret (Subterm size recargs)
        | _ => raise "this should not be reachable" (* TODO why *)
        end
    | _ => ret Not_subterm
    end.

(* FIXME: is not structurally recursive *)
Fixpoint subterm_specif Σ G (stack : list stack_element) t {struct t}: exc subterm_spec:= 
  (* TODO *)
  ret Not_subterm

(* given a stack element, compute its subterm specification *)
with stack_element_specif Σ stack_el {struct stack_el} : exc subterm_spec := 
  match stack_el with 
  | SClosure G t => subterm_specif Σ G [] t
  | SArg spec => ret spec
  end

(* get the subterm specification for the top stack element together with the rest of the stack*)
with extract_stack Σ stack {struct stack} : exc (subterm_spec * list stack_element) := 
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


(* TODO move *)
Definition list_iter {X} (f : X -> exc unit) (l : list X) : exc unit := 
  List.fold_left (fun (acc : exc unit) x => _ <- acc;; f x) l (ret tt).
Definition list_iteri {X} (f : nat -> X -> exc unit) (l : list X) : exc unit := 
  _ <- List.fold_left (fun (acc : exc nat) x => i <- acc;; _ <- f i x;; ret (S i)) l (ret 0);;
  ret tt.

 

(* TODO understand *)
Definition filter_stack_domain Σ Γ (rtf : term) (stack : list stack_element) : exc (list stack_element) := 
  '(rtf_context, rtf_body) <- decompose_lam_assum Σ Γ rtf;; 
   (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if negb (rel_range_occurs 0 (length rtf_context -1) rtf_body) then ret stack 
  else
    let Γ' := rtf_context ++ Γ in
    let filter_stack Γ rtf stack : exc (list stack_element) := 
      (* TODO *)
      ret stack
    in filter_stack Γ' rtf_body stack.

(*
  Check if [t] only makes valid recursive calls, with variables (and their subterm information) being tracked in the context [G].
  [stack] is the list of constructor's argument specification and arguments that will be applied after reduction.
  TODO    example: u in t where we have (match .. with |.. => t end) u
  [trees] is a list of recursive structures for the decreasing arguments of the mutual fixpoints.*)
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
        (* check if [p] is a fixpoint, i.e. we are making a recursive call *)
        if Nat.leb G.(rel_min_fix) p && Nat.ltb p (G.(rel_min_fix) + num_fixes) then
          (* check calls in the argument list, initialized to an empty stack*)
          _ <- list_iter (check_rec_call' G []) l;;
          (* get the position of the invoked fixpoint in the mutual block *)
          let rec_fixp_index := G.(rel_min_fix) + num_fixes - p in
          (* get the decreasing argument of the recursive call *)
          decreasing_arg <- except "check_rec_call: invalid fixpoint index" $ nth_error decreasing_args rec_fixp_index;;
          (* push the arguments as closures on the stack *)
          let stack' := push_stack_closures G stack l in 
          (* get the stack entry for the decreasing argument *)
          z <- except "check_rec_call: not enough arguments for recursive fix call" $ nth_error stack' decreasing_arg;;
          (* get the tree for the recursive argument type *)
          recarg_tree <- except "check_rec_call: no tree for the recursive argument" $ nth_error trees decreasing_arg;;
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
          case_branch_specs <- branches_specif Σ G discriminant_spec;; (* TODO: function will need access to match info *)
          (* push arguments on stack *)
          let stack' := push_stack_closures G stack l in
          (* filter the stack to only contain the things which are allowed to propagate through matches *)
          stack' <- filter_stack_domain Σ G.(loc_env) rtf stack';;
          (* check the branches of the matches *)
          list_iter (fun '(i, branch) =>
              branch_spec <- except "check_rec_call: branch specs too short" $ nth_error case_branch_specs i;;
              (* NOTSURE push the rec arg specs for the variables introduced by the branch *)
              let stack_branch := push_stack_args stack' branch_spec in
              (* check the branch *)
              check_rec_call' G stack_branch branch) 
            branches
        )  
        (fun err => 
          (* if the checking goes wrong, we can still try harder by reducing the match away if possible *)
          (* TODO *)
          raise err)

    | tFix mfix_inner fix_ind => ret tt (* TODO *)

    | tConst kname univ => ret tt (* TODO *)

    | tLambda x ty body => ret tt (* TODO *)

    | tProd x ty body => ret tt (* TODO *)

    | tCoFix mfix_inner fix_ind => ret tt (* TODO *)

    | tInd _ _ | tConstruct _ _ _ =>  ret tt (* TODO *)

    | tProj p c => ret tt (* TODO *)

    | tVar id => ret tt (* TODO *)

    | tSort _ => ret tt (* TODO *)

    | tEvar _ _ => 
        (* the RHS [l] is not checked because it is considered as the evar's context *)
        (* TODO : is that really okay? *)
        ret tt
    | tApp _ _ | tLetIn  _ _ _ _ | tCast _ _ _ => raise "beta-zeta-iota reduction is broken"
    end

(* TODO: doc *)
with check_nested_fix_body Σ G (decr : nat) (sub_spec : subterm_spec) (body : term) {struct decr}: exc unit := 
  ret tt. 
Set Guard Checking. 

(* Check if [def] is a guarded fixpoint body, with arguments up to (and including)
  the recursive argument being introduced in the context [G]. 
  [G] has been initialized with initial guardedness information on the recursive argument.
  [trees] is a list of recursive structures for the decreasing arguments of the mutual fixpoints.
*)
Definition check_one_fix G (recpos : list nat) (trees : list wf_paths) (def : term) : exc unit := 
  check_rec_call (length recpos) G [] def.  


Definition check_fix Σ (mfix : mfixpoint term) : exc unit := 
  (* check that the recursion is over inductives and get those inductives 
    as well as the bodies of the fixpoints *)
  '(minds, rec_defs) <- inductive_of_mutfix Σ [] mfix;;
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

  exc_unwrap $ mapi (fun i fix_body => 
    fix_env <- except "fix_envs too short" $ nth_error fix_envs i;;
    rec_tree <- except "rec_trees too short" $ nth_error rec_trees i;;
    rec_arg <- except "rec args too short" $ nth_error rec_args i;;
    (* initial guard env *)
    let G := init_guard_env fix_env rec_arg rec_tree in
    (* check the one fixpoint *)
    check_one_fix G rec_args rec_trees fix_body 
    ) fix_bodies.
