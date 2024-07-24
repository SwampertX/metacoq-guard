From MetaCoq.Guarded Require Import plugin.
From MetaCoq Require Import Utils.bytestring.

Open Scope bs.

Inductive rtree (X : Type) := rnode (l : list (rtree X)).

Fixpoint rtree_size {X} (t : rtree X) := 
  match t with
  | rnode l => rnode X ((fix map (l : list (rtree X)) : list (rtree X) := match l with
                                                                          | nil => nil
                                                                          | cons a t => cons (rtree_size a) (map t)
                                                                          end) l)
  end.
MetaCoq Run (check_fix_ci true (@rtree_size)). 
