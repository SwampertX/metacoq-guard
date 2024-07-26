From MetaCoq.Guarded Require Import plugin.
From MetaCoq Require Import Utils.bytestring.

Open Scope bs.

Set Printing Depth 200.
Set Printing Width 200.

Inductive rtree := rnode (l : list rtree).

Fixpoint rtree_size (t : rtree) :=
  let map_id :=
    (fix map (l : list (rtree)) : list (rtree) := match l with
                                                   | nil => nil
                                                   | cons a t => cons (rtree_size a) nil
                                                   end) in
  match t with
  | rnode l => rnode (map_id l)
  end.
(* MetaCoq Run (check_fix_ci true (@rtree_size)). *)
 
