From MetaCoq.Template Require Import utils.
Require Import MetaCoq.Guarded.Except.

Definition map2_i { A B C} (f : nat -> A -> B -> C) (a : list A) (b : list B) := 
  let map2' := fix rec a b n := 
     match a, b with
     | a0 :: a, b0 :: b => f n a0 b0 :: rec a b (S n)
     | _, _ => []
     end
  in map2' a b 0.
Fixpoint update_list {X} (l : list X) index x := 
  match l with 
  | [] => []
  | h :: l => 
      match index with 
      | 0 => x :: l
      | S index => h :: update_list l index x
      end
  end.

Section Except. 
  Context { Y : Type}. 
  (*Notation "'exc' X" := (excOn Y X) (at level 100). *)
  Context {M : Type -> Type} {M_monad : Monad M}. 

  Definition list_iter {X} (f : X -> M unit) (l : list X) : M unit := 
    List.fold_left (fun (acc : M unit) x => _ <- acc;; f x) l (ret tt).
  Definition list_iteri {X} (f : nat -> X -> M unit) (l : list X) : M unit := 
    _ <- List.fold_left (fun (acc : M nat) x => i <- acc;; _ <- f i x;; ret (S i)) l (ret 0);;
    ret tt.


End Except.

Definition hd {X} (l : list X) : option X := 
  match l with 
  | [] => None
  | x :: l => Some x
  end.

Definition tl {X} (l : list X) : option(list X) := 
  match l with 
  | [] => None
  | x :: l => Some l
  end.

