From MetaCoq.Guarded Require Import plugin.
From MetaCoq Require Import Utils.bytestring.
Open Scope bs.

Fixpoint f (n:nat) :=
  match n with
  | O => O
  | S n' => let m := id n' in f m
  end.

MetaCoq Run (check_fix_ci true f).

#[bypass_check(guard)]
Fixpoint erasable_zeta (x : bool) : bool :=
let _ := erasable_zeta x in true.
MetaCoq Run (check_fix_ci false erasable_zeta).

Eval lazy in (erasable_zeta true).

From Equations Require Import Equations.
Require Import Vector.

Equations map2 {A B C} (f:A->B->C) (n:nat) (v1:t A n) (v2:t B n) : t C n :=
map2 f 0 nil nil := nil C;
map2 f (S n) (cons h1 n t1) (cons h2 n t2) := cons C (f h1 h2) n (map2 f n t1 t2).

Print map2.

MetaCoq Run (check_fix_ci true (@map2)).

#[bypass_check(guard)]
Fixpoint f (a : nat) := match a with O => O | S b => f a end.
MetaCoq Run (check_fix_ci false f).
(* #[bypass_check(guard)] *)
Fixpoint f (x : nat) := (fun y:bool => match x with O => O | S n => f n y end).
MetaCoq Run (check_fix_ci true f).

#[bypass_check(guard)]
Fixpoint foo n :=
  match n with
  | 0 => 0
  | S n => (fun n => match n with
          | 0 => foo n
          | S n => foo n
          end) (S n)
  end.

MetaCoq Run (check_fix_ci false foo).


Fixpoint minus (n m:nat) {struct n} : nat :=
  match (n, m) with
  | (O , _) => O
  | (S _ , O) => n
  | (S n', S m') => minus n' m'
  end.

MetaCoq Run (check_fix_ci true minus).


Unset Guard Checking.

(* A few examples of non strongly normalizing fixpoints *)
Fixpoint beta_erase (v:bool) := (fun x y => x) 0 (beta_erase v).

Require Import VectorDef.
Print rectS.

Set Guard Checking.
Fixpoint iter2 a b :=
  match a, b with
  | 0, 0 => 0
  | S n, S m => iter2 n m
  | S n, _ => n
  | _, S n => n
  end.
Print iter2.
Fail Fixpoint zeta_erase (v:bool) := let _ := zeta_erase v in 0.

Fail Fixpoint iota_case_erase (v:bool) :=
  match true with
  | true => 0
  | false => iota_case_erase v
  end.

Fail Fixpoint iota_fix_erase (v:bool) :=
  let g1 := fix g1 (x : nat) := x
            with g2 (x : nat) := iota_fix_erase v
            for g1
  in
  g1 0.

Fail Fixpoint f (x : bool) :=
  let y := f x in
  match true with
  | true => true
  | false => y
  end.
#[bypass_check(guard)]
Fixpoint f (x : bool) : bool := let _ := f x in true.

MetaCoq Run (check_fix_ci false f).


Module PropExt0.
Unset Guard Checking.
Section func_unit_discr.
Hypothesis Heq : (False -> False) = True.

Fixpoint contradiction (u : True) : False :=
match u with
| I => contradiction (
        match Heq in (_ = T) return T with
        | eq_refl => fun f:False => match f with end
        end)
end.

MetaCoq Run (check_fix_ci true contradiction).

Section func_unit_discr.

Inductive rtree :=
| rnode : list rtree -> rtree.

Definition rtree_rec' (P: rtree -> Set) (Q: list rtree -> Set)
  (Qnil : Q nil) (Qcons : forall (t: rtree) (ts: list rtree), P t -> Q ts -> Q (cons t ts))
  (Prnode : forall (children: list rtree), Q children -> P (rnode children)) :=
  let fix prec (t : rtree) : P t :=
    let fix qrec (ts : list rtree) : Q ts :=
      match ts with nil => Qnil | cons t ts => Qcons t ts (prec t) (qrec ts) end
    in match t with
    | rnode l => Prnode l (qrec l)
    end
  in prec.
