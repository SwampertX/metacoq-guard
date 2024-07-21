From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Guarded Require Export Trace.

(** Exceptions *)
(** most of the code runs in a monad for handling errors/exceptions *)
Declare Scope exc_scope.
Open Scope exc_scope.

Notation loc := string (only parsing).

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
  | TimeoutErr
  | NoReductionPossible. 

(*max bind steps *)
Definition max_steps := 1000. 
Definition catchE := @catchE max_steps. 
Arguments catchE {_ _}. 
Definition catchMap := @catchMap max_steps _ TimeoutErr. 
Arguments catchMap {_ _}. 
  
Instance trace_monad : Monad (@TraceM guard_exc).
apply trace_monad. exact max_steps. exact TimeoutErr.
Defined.

(* Notation "'exc' A" := (excOn guard_exc A) (at level 100) : exc_scope.  *)
Notation "'exc' A" := (@TraceM guard_exc A) (at level 100) : exc_scope. 
(* Definition unwrap := @exc_unwrap. *)
Definition unwrap := @trc_unwrap.
Arguments unwrap { _ _ _ _}. 

Instance: TrcUnwrap list := list_trc_unwrap max_steps TimeoutErr.