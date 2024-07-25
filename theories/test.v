From MetaCoq.Guarded Require Import plugin.
From MetaCoq Require Import Utils.bytestring.

Open Scope bs.

Fixpoint add n m :=
  match m with
  | O => n
  | S m' => add (S n) m'
  end.

MetaCoq Run (check_fix_ci true add). 
