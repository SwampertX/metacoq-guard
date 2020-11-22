From MetaCoq.Template Require Import utils BasicAst.
From MetaCoq.Template Require Import Universes Environment Declarations.
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
Notation "'exc' A" := ((A + string)%type) (at level 100). 

Notation "f '$' a" := (f (a)) (at level 99). 


(** WIP : An implementation of the guardedness checker *)

Module Guarded (T : Term) (D : DeclarationsSig T). 
  Import T D. 

  Definition mind_definition := mutual_inductive_body * one_inductive_body. 
  
  Definition lookup_mind_definition Σ (ind : inductive) := 
    mib <- except "lookup_mind_definition: could not find inductive" $ 
      lookup_env_mind Σ ind.(inductive_mind) ;;
    ib <- except "lookup_mind_definition: invalid inductive index" $ 
      nth_error mib.(ind_bodies) ind.(inductive_ind) ;;
    ret (mib, ib).


End Guarded.



Import Environment.
Check Environment.mutual_inductive_body.
