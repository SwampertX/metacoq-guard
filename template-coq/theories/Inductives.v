
From MetaCoq.Checker Require Import Checker. 
From MetaCoq.Template Require Import utils BasicAst Ast AstUtils.
From MetaCoq.Template Require Import Universes Environment Declarations Reflect. 
From MetaCoq.Template.utils Require Import RTree. 


(* we work in the sum monad to handle all the error stuff *)
Import MonadNotation.

Instance sum_exc : MonadExc string (fun m => (m + string)%type)  :=
  {| 
    raise := fun T e => @inr T string e;
    catch := fun T x f => 
      match x with 
      | inl x => inl x 
      | inr y => f y
      end
  |}. 

Instance sum_monad {Y}: Monad (fun X => X + Y)%type := 
  {| 
    ret := fun T t => inl t;
    bind := fun T U x f => 
      match x with 
      | inl x => f x
      | inr y => inr y
      end
  |}. 

Definition except {X Y: Type} (def : Y) (x : option X) : X + Y := 
  match x with 
  | Some x => inl x
  | None => inr def
  end.
Definition raise {X Y : Type} (def : Y) : X + Y := inr def. 
Notation "'exc' A" := ((A + string)%type) (at level 100). 

Notation "f '$' a" := (f (a)) (at level 99, only parsing). 


Notation "a == b" := (eqb a b) (at level 90). 
Notation "a != b" := (negb(a==b)) (at level 90).


Class ExcUnwrap (Xl : Type -> Type) := exc_unwrap X : Xl (exc X) -> exc (Xl X).
Arguments exc_unwrap {_ _ _}. 

Fixpoint list_unwrap {X : Type} (l : list (exc X)) : exc (list X) := 
  match l with 
  | [] => ret []
  | x :: l => 
      x <- x ;;
      l <- list_unwrap l;;
      ret (x :: l)
  end.
Instance: ExcUnwrap list := @list_unwrap. 


(** WIP : An implementation of the guardedness checker *)

Implicit Types (Σ : global_env) (c : context). 
Definition whd_all Σ c t := 
  except "whd_all: out of fuel" $ reduce_opt RedFlags.default Σ c default_fuel t. 

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
Definition find_rectype Σ c t := 
  t <- whd_all Σ c t;; 
  let (t, l) := decompose_app t in 
  match t with 
  | tInd i u => ret ((i, u), l)
  | _ => raise "find_rectype"
  end. 


(* the same, but only if the rectype is an inductive or record (bifinite) *)
Definition find_inductive Σ c t := 
  '((i, u), l) <- find_rectype Σ c t;;
  '(mib, _) <- lookup_mind_specif Σ i;;
  if mib.(ind_finite) != CoFinite then ret ((i, u), l) else raise "find_inductive: is cofinite".

(* only if coinductive *)
Definition find_coinductive Σ c t := 
  '((i, u), l) <- find_rectype Σ c t;;
  '(mib, _) <- lookup_mind_specif Σ i;;
  if mib.(ind_finite) == CoFinite then ret ((i, u), l) else raise "find_coinductive: is not cofinite".


