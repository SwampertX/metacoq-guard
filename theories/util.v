From MetaCoq.Utils Require Import utils.
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

Definition is_none {X: Type} (a : option X) :=
  match a with
  | None => true
  | _ => false
  end.

Fixpoint tabulate {X : Type} (f : nat -> X) n :=
  match n with
  | 0 => []
  | S n => tabulate f n ++ [f n]
  end.

Definition repeat {X} (x : X) n := tabulate (fun _ => x) n.

Definition lookup {X Y: Type} (eqb : X -> X -> bool) (x : X) := fix rec (l : list (X * Y)) : option Y :=
  match l with
  | [] => None
  | (x', y') :: l => if eqb x x' then Some y' else rec l
  end.

Definition list_eqb {X : Type} (eqbX : X -> X -> bool) := fix rec l l' :=
  match l, l' with
  | nil, nil => true
  | cons x l0, cons x' l0' => eqbX x x' && rec l0 l0'
  | _, _ => false
  end.

Definition forallb2 {X : Type} (f : X -> X -> bool) := fix rec l l' :=
  match l, l' with
  | nil, nil => true
  | x :: l0, x' :: l0' => f x x' && rec l0 l0'
  | _, _ => false
  end.

Definition set_memb {X : Type} (eqbX : X -> X -> bool) := fix rec x s :=
  match s with
  | [] => false
  | x' :: s' =>  eqbX x x' || rec x s'
  end.

Definition map2 {X Y Z: Type} (f : X -> Y -> Z) := fix rec l1 l2 :=
  match l1, l2 with
  | [], [] => []
  | x :: l1, y :: l2 => f x y :: rec l1 l2
  | _, _ => []
  end.

Definition pair_eqb {X : Type} (eqb : X -> X -> bool) '(t, u) '(t', u') := eqb t t' && eqb u u'.

Definition option_lift {X Y Z} (f : X -> Y -> Z) (a : option X) (b : option Y) : option Z:=
  match a, b with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.
Fixpoint list_lift_option {X} (l : list (option X)) : option (list X) :=
  match l with
  | [] => Some []
  | x :: l => option_lift (@cons X) x (list_lift_option l)
  end.

Infix "<?" := Nat.ltb (at level 70).
Infix "=?" := Nat.eqb (at level 70).


(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

From MetaCoq.Template Require Import Ast.

Fixpoint iterate {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
match n with O => x | S n' => iterate f n' (f x) end.

(* Counterpart: [Constr.fold_constr_with_binders] *)
Definition fold_term_with_binders {A B : Type} (g : A -> A)
  (f : A -> B -> term -> B) (n : A) (acc : B) (c : term) :=
  match c with
  | (tRel _ | tVar _   | tSort _ | tConst _ _ | tInd _ _
    | tConstruct _ _ _ | tInt _ | tFloat _) => acc
  | tCast c _ t => f n (f n acc c) t
  | tProd _na t c => f (g n) (f n acc t) c
  | tLambda  _na t c => f (g n) (f n acc t) c
  | tLetIn _na b t c => f (g n) (f n (f n acc b) t) c
  | tApp c l => fold_left (f n) l (f n acc c)
  | tProj _p c => f n acc c
  | tEvar _ l => fold_left (f n) l acc
  (* | Case (_,_,pms,(p,_),iv,c,bl) -> *)
  | tCase _ci ti c bl => (* TODO: should p include the context? *)
    let pms : list term := ti.(pparams) in
    let nas : list aname := ti.(pcontext) in
    let p : term := ti.(preturn) in
    let fold_ctx n (acc : B) (nas_c : list aname * term) : B :=
      let '(nas, c) := nas_c in
      f (iterate g (length nas) n) acc c
    in
    let a : B := fold_ctx n (fold_left (f n) pms acc) (nas, p) in
    fold_left (fun acc br => fold_ctx n acc (br.(bcontext),br.(bbody))) bl (f n a c)
  (* | Fix (_,(_,tl,bl)) => *)
  | tFix fixpt _ | tCoFix fixpt _ =>
      let tl : list term := map dtype fixpt in
      let bl : list term := map dbody fixpt in
      let n' : A := iterate g (length tl) n in
      let fd : list (term * term) := map2 (fun t b => (t,b)) tl bl in
      fold_left (fun acc '(t,b) => f n' (f n acc t) b) fd acc
  | tArray _u t def ty  =>
    f n (f n (fold_left (f n) t acc) def) ty
  end.
