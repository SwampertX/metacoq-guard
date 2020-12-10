From MetaCoq.Template Require Export monad_utils.
From MetaCoq.Template Require Import utils.
Export MonadNotation.
Require Import MetaCoq.Guarded.Except. 


Section trace. 
  Context (max_steps : nat).
  Context {Y : Type}.
  Context (timeout : Y). 

  Definition trace_info := string. 
  Definition TraceM A := nat (* number of steps on the clock *)
                        * list trace_info (* trace *)
                        * excOn Y A. (* error monad *)

  (* max steps handling is not totally accurate as we cannot pass the current number of steps into the function in bind, but anyways *)
  Instance trace_monad : Monad TraceM := 
    {| 
      ret := fun T t => (0, [], ret t);
      bind := fun T U x f => 
        match x with 
        | (s, t, e) => 
            match e with 
            | inl e => 
                match f e with 
                | (s', t', e') => 
                    let s'' := 1 + s' + s in
                    if Nat.leb max_steps s'' then (s'', t' ++ t, raise timeout) 
                      else (s'', t' ++ t, e')
                end
            | inr err => (s, t, inr err)
            end
        end
    |}. 

  (* emit a trace element *)
  Definition trace (i : trace_info) : TraceM unit := (0, [i], ret tt). 
  Definition step : TraceM unit := (1, [], ret tt). 


  (** Lifting of the primitive operations on the except monad *)
  Notation "'trc' A" := (@TraceM A) (at level 100).

  Definition raise {X} (y : Y) : trc X := (0, [], Except.raise y).  
  Definition except {X} (y: Y) (a : option X) : trc X := (0, [], Except.except y a). 

  Class TrcUnwrap (Xl : Type -> Type) := trc_unwrap X : Xl (trc X) -> trc (Xl X).
  Arguments trc_unwrap {_ _ _}. 

  Fixpoint list_unwrap {X : Type} (l : list (trc X)) : trc (list X) := 
    match l with 
    | [] => ret []
    | x :: l => 
        x <- x;;
        l <- list_unwrap l;;
        ret (x :: l)
    end.
  Instance list_trc_unwrap: TrcUnwrap list := @list_unwrap. 

  Definition lift_exc {X} (a : excOn Y X) : trc X := (0, [], a).
  Definition add_trace {Z} steps trace (a : trc Z) := 
    match a with 
    | (steps', trace', z) => (steps + steps', trace' ++ trace, z)
    end.

  Definition assert (b : bool) (err : Y) : trc unit := 
    lift_exc (Except.assert b err). 

  Definition catchE {X} (a : trc X) (f : Y -> trc X) : trc X := 
    match a with 
    | (steps, trace, e) => 
        match e with 
        | inl a => (steps, trace, e)
        | inr e => 
            add_trace steps trace (f e)
        end
    end.

  Definition catch {X} (a : trc X) (f : Y -> X) : X := 
    match a with 
    | (_, _, inr e) => f e
    | (_, _, inl e) => e
    end.

  Definition catchMap {X Z} (e : trc X) (f : Y -> trc Z) (g : X -> trc Z) : trc Z :=
    match e with
    | (steps, trace, inr e) => 
        add_trace steps trace (f e)
    | (steps, trace, inl a) => 
        add_trace steps trace (g a)
    end.
End trace.

Arguments trc_unwrap {_ _ _ _}. 

Module example. 
  Inductive err := 
  | TimeoutErr
  | OtherErr (s : string). 

  Definition max_steps := 2. 
  
  Instance: Monad (@TraceM err) := @trace_monad max_steps err TimeoutErr. 
  Notation "'trc' A" := (@TraceM err A) (at level 100). 

  Definition test : trc unit := 
    trace "test";; 
    raise $ OtherErr "s".

  Definition test' : trc unit := 
    catchE test (fun _ => step;; raise $ OtherErr "sss"). 
  (*Eval cbn in test'.*)
End example.
