From MetaCoq.Template Require Import Environment utils.MCRTree Ast AstUtils All. 
Open Scope string_scope.
Require Import List String.
Import ListNotations.
Open Scope string_scope.
From MetaCoq.Guarded Require Import Inductives Except Trace.


(* explicit instantiation with TemplateMonad as a definition parametric over the monad causes trouble with universe polymorphism *)
Definition list_iter {X} (f : X -> TemplateMonad unit) (l : list X) : TemplateMonad unit := 
  List.fold_left (fun (acc : TemplateMonad unit) x => _ <- acc;; f x) l (ret tt).



(* whoops, I've turned the guardedness checker off *)
Unset Guard Checking.


Fixpoint check_fix_term (Σ : global_env) (Γ : context) (t : term) {struct t} := 
  match t with 
  | tFix mfix _ => 
      (* TODO: we should first recursively check the body of the fix (in case of nested fixpoints!) *)
      (*tmPrint mfix ;;*)
      (*tmPrint Σ*)
      (*ret tt*)
      (*let Σ := *)
      match (check_fix Σ Γ mfix) with
      | (_, trace, inr e) => 
          trace <- tmEval cbn trace;;
          tmPrint trace;; tmPrint e
      | _ => tmPrint "success"
      end
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
  end.

Set Guard Checking. 

Definition check_fix {A} (a : A) :=
  mlet (Σ, t) <- tmQuoteRec a ;;
  (*tmPrint Σ;;*)
  check_fix_term Σ [] t.



(** * Some tests *)
Unset Guard Checking.

Require Import List String.
Import MonadNotation.
Import ListNotations.
Open Scope string_scope.

Fixpoint broken_app {A : Type} (l m : list A) {struct l} := 
  match l with
  | [] => m
  | a :: l' => broken_app l m
  end.

(*Set Printing All. *)
MetaCoq Run (check_fix broken_app ). 
MetaCoq Run (check_fix app ). 
MetaCoq Run (check_fix rev).
MetaCoq Run (check_fix Nat.div).



(** Rosetrees *)
Inductive rtree (X : Type) := 
  | rnode (children : list (rtree X)). 

Fixpoint sumn (l : list nat) := List.fold_left (fun a b => a + b) l 0. 
MetaCoq Run (check_fix sumn). 

Fixpoint rtree_size {X} (t : rtree X) := 
  match t with
  | rnode l => sumn (map rtree_size l)
  end.

MetaCoq Run (check_fix rtree_size). 









(** Vectors *)
Set Implicit Arguments.
Set Asymmetric Patterns.
Require Coq.Vectors.Vector.

Section ilist.

(* Lists of elements whose types depend on an indexing set (CPDT's hlists).
These lists are a convenient way to implement finite maps
whose elements depend on their keys. The data structures used
by our ADT notations uses these to implement notation-friendly
method lookups. *)

Import Coq.Vectors.VectorDef.VectorNotations.

Context {A : Type}. (* The indexing type. *)
Context {B : A -> Type}. (* The type of indexed elements. *)

Fixpoint ilist {n} (l : Vector.t A n) : Type :=
match l with
| [] => unit
| a :: l => (B a) * (ilist l)
end.

MetaCoq Run (check_fix_start ilist).

Definition icons (a : A) {n} {l : Vector.t A n} (b : B a) (il : ilist l) : ilist (a :: l) := pair b il.

Axiom ilist_hd : forall {n} {As : Vector.t A n} (il : ilist As),
match As return ilist As -> Type with
| a :: As' => fun il => B a
| [] => fun _ => unit
end il.

Axiom ilist_tl : forall {n} {As : Vector.t A n} (il : ilist As),
match As return ilist As -> Type with
| a :: As' => fun il => ilist As'
| [] => fun _ => unit
end il.

Definition ith_body 
    (ith : forall {m : nat} {As : Vector.t A m} (il : ilist As) (n : Fin.t m), B (Vector.nth As n))
    {m : nat}
    {As : Vector.t A m}
    (il : ilist As)
    (n : Fin.t m)
  : B (Vector.nth As n)
:= Eval cbv beta iota zeta delta [Vector.caseS] in
  match n in Fin.t m return forall (As : Vector.t A m), ilist As -> B (Vector.nth As n) with
  | Fin.F1 k =>
    fun As =>
      Vector.caseS (fun n As => ilist As -> B (Vector.nth As (@ Fin.F1 n)))
      (fun h n t => ilist_hd) As
  | Fin.FS k n' =>
    fun As =>
      Vector.caseS (fun n As => forall n', ilist As -> B (Vector.nth As (@ Fin.FS n n')))
        (fun h n t m il => @ ith _ _ (ilist_tl il) m)
        As n'
  end As il.

Fixpoint ith {m : nat} {As : Vector.t A m} (il : ilist As) (n : Fin.t m) {struct n} : B (Vector.nth As n) := 
  @ ith_body (@ ith) m As il n.

(* TODO: diverges *)
(*MetaCoq Run (check_fix_start ith).*)


