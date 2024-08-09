From MetaCoq.Guarded Require Import plugin.

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
