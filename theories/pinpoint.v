From MetaCoq.Guarded Require Import plugin.
From MetaCoq Require Import Utils.bytestring.
Open Scope bs.

(** * Instructive examples of the guard checker.
  The examples listed below aims to explain, from simple to complicated, the inner workings of the guard checker.
  - [add] for how a term is deemed as a "Strict subterm" as the recarg.
  - TODO: one example to show the power of wf_paths compared to naive set representation.
    probably a simple mutual inductive type.
  - [combine_branches_spec] shows how a [tCase] term is given its subterm_specif.
*)

(* Passes since m' is a strict subterm of m.
  Strictness follows from the recursive structure of nat. *)
Fixpoint add (m n : nat) {struct m} : nat :=
  match m with O => n | S m' => add m' (S n) end.

MetaCoq Run (check_fix_ci true add).

(* Swapping the arguments preserves guardedness, although the local context is slightly different.
  Behaviour of the steps in typechecking are the same.
*)
Fixpoint add' (m n : nat) {struct n} : nat :=
  match n with O => m | S n' => add' (S m) n' end.

MetaCoq Run (check_fix_ci true add').


(* A bad version of [add], fails because the argument [m] to [add_typo] is a [Large] subterm.
  Determining the size of [m] is simply done by looking up in the [guarded_env]. *)
Fail Fixpoint add_typo (m n : nat) {struct m} : nat :=
  match m with O => n | S unused => add_typo m (S n) end.

#[bypass_check(guard)]
Fixpoint add_typo (m n : nat) {struct m} : nat :=
  match m with O => n | S unused => add_typo m (S n) end.

MetaCoq Run (check_fix_ci false add_typo).

(* Let's try to obfuscate [m] and see if the guard checker labels the size of the argument [id m] correctly. *)
Fail Fixpoint add_typo_obf (m n : nat) {struct m} : nat :=
  match m with O => n | S unused => add_typo_obf (id m) (S n) end.

#[bypass_check(guard)]
Fixpoint add_typo_obf (m n : nat) {struct m} : nat :=
  match m with O => n | S unused => add_typo_obf (id m) (S n) end.

(* apparently, it doesn't even try to lookup the definition of id.
  instead, when determining if [(id m)] is a strict subterm, we do a weak head reduction!
  this results in [m] which is clearly a Large subterm, as seen in [G.(guarded_env)]. *)
MetaCoq Run (check_fix_ci false add_typo_obf).

(* as a positive example, similarly the whd_all reduces away the [id]. *)
Fixpoint add_obf (m n : nat) {struct m} : nat :=
  match m with O => n | S m' => add_obf (id m') (S n) end.

MetaCoq Run (check_fix_ci true add_obf).

(* Just to be clear, running weak head reduction is really powerful. *)
Fixpoint add_obf' (m n : nat) {struct m} : nat :=
  match m with O => n | S m' => add_obf' (pred (S m')) (min (S n) (S (S n))) end.

MetaCoq Run (check_fix_ci true add_obf').

(* what about obfuscating the head instead of arguments? *)
Fixpoint add_obf_head (m n : nat) {struct m} : nat :=
  match m with O => n | S m' => (id add_obf_head) m' (S n) end.

(* Now the head is expanded to its definition. Leading to it are:
  - The 1-st branch in full is [(fun m' => id (nat->nat->nat) add_obf_head m' (S n))].
  - When checking the body of the branch, the tApp [id (nat->nat->nat) add_obf_head m' (S n))],
    the argument [add_obf_head] requests for reduction since its stack is empty.
  - Thus in the last step of tApp, the head is expanded, and we unwrap the tLambdas until it works.
  Note that the tApp is NOT reduced away.
*)
MetaCoq Run (check_fix_ci true add_obf_head).

(* What if the obfuscation is not just a tConst? *)
Fixpoint add_obf_head' (m n : nat) {struct m} : nat :=
  match m with O => n | S m' => (fun a b => pred (S (add_obf_head' a b))) m' (S n) end.

(* Subterm spec flows from m', n into a, b respectively.
  Therefore there is no difference. *)
MetaCoq Run (check_fix_ci true add_obf_head').

Fixpoint combine_branches_spec (x : nat) :=
  match x as x_match with | O => O
  | S y => match y as y_match with | O => O
    | S z => combine_branches_spec (match z as z_match with | O => y | S unused => z end)
    end
  end.

MetaCoq Run (check_fix_ci true f).

Fail Fixpoint combine_branches_spec' (x : nat) :=
  match x as x_match with | O => O
  | S y => match y as y_match with | O => O
    | S z => combine_branches_spec' (match z as z_match with | O => x | S unused => z end)
    end
  end.

#[bypass_check(guard)]
Fixpoint combine_branches_spec' (x : nat) :=
  match x as x_match with | O => O
  | S y => match y as y_match with | O => O
    | S z => combine_branches_spec' (match z as z_match with | O => x | S unused => z end)
    end
  end.
MetaCoq Run (check_fix_ci false f').