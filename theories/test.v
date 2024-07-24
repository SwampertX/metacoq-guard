From MetaCoq.Guarded Require Import plugin.
From MetaCoq Require Import Utils.bytestring.

Open Scope bs.



(** Vectors *)
Set Implicit Arguments.
Set Asymmetric Patterns.
Require Coq.Vectors.Vector.

(* #[bypass_check(guard)]
Fixpoint abc_bad (n : nat) := 
  match n with 
  | 0 => 0
  | S m => abc_bad (match m with O => m | S k => m end)
  end. *)

(* MetaCoq Run (check_fix_ci true abc_bad).  *)

(* Fixpoint add m n :=
  match m with
  | O => n
  | S m' => add m' (S n)
  end. *)

(* MetaCoq Run (check_fix_ci true add).  *)

(** Taken from  https://github.com/coq/coq/issues/4320 *)

(* Unset Guard Checking. *)
Section ilist.

(* Lists of elements whose types depend on an indexing set (CPDT's hlists).
These lists are a convenient way to implement finite maps
whose elements depend on their keys. The data structures used
by our ADT notations uses these to implement notation-friendly
method lookups. *)

Import Coq.Vectors.VectorDef.VectorNotations.

(* MetaCoq Run (check_fix_ci true plus). *)

MetaCoq Run (check_fix_ci true (@Vector.nth)).


Context {A : Type}. (* The indexing type. *)
Context {B : A -> Type}. (* The type of indexed elements. *)

Fixpoint ilist {n} (l : Vector.t A n) : Type :=
match l with
| [] => unit
| a :: l => (B a) * (ilist l)
end.

MetaCoq Run (check_fix_ci true (@ilist)).

Definition icons (a : A) {n} {l : Vector.t A n} (b : B a) (il : ilist l) : ilist (a :: l) := pair b il.

Definition ilist_hd : forall {n} {As : Vector.t A n} (il : ilist As),
match As return ilist As -> Type with
| a :: As' => fun il => B a
| [] => fun _ => unit
end il.
intros. destruct As. exact tt. cbn in il. apply il.
Defined.

Definition ilist_tl : forall {n} {As : Vector.t A n} (il : ilist As),
match As return ilist As -> Type with
| a :: As' => fun il => ilist As'
| [] => fun _ => unit
end il.
intros. destruct As. exact tt. cbn in il. apply il.
Defined.

Axiom ass : forall {n}, B n.

Definition ith_body 
    (ith : forall {m : nat} {As : Vector.t A m} (il : ilist As) (n : Fin.t m), B (Vector.nth As n))
    {m : nat}
    {As : Vector.t A m}
    (il : ilist As)
    (n : Fin.t m)
  : B (Vector.nth As n)
:= Eval cbv beta iota zeta delta [Vector.caseS] in ass.

(* note that guard checking is turned off before the section *)
Fixpoint ith {m : nat} {As : Vector.t A m} (il : ilist As) (n : Fin.t m) {struct n} : B (Vector.nth As n) := 
  @ ith_body (@ ith) m As il n.

(* FIXME: (failure of tree intersection) *)

MetaCoq Run (check_fix_ci false (@ith)).
End ilist.
Set Guard Checking.
