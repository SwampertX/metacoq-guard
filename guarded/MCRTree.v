
(* Type of regular trees:
   - Param denotes tree variables (like de Bruijn indices)
     the first int is the depth of the occurrence, and the second int
     is the index in the array of trees introduced at that depth.
     ==============================================================================    Warning: Param's indices both start at 0!!!
   - Node denotes the usual tree node, labelled with 'a
   - Rec(j,v1..vn) introduces an infinite tree. It denotes
     v(j+1) with parameters 0..n-1 replaced by
     Rec(0,v1..vn)..Rec(n-1,v1..vn) respectively.
 *)
Definition fuel := 10000. 

Inductive rtree (X : Type) := 
  | Param (tree_index : nat) (ind_index : nat)
  | Node (l : X) (children : list (rtree X))
  | Rec (index : nat) (children : list (rtree X)). 

Arguments Param {_}. 
Arguments Node {_}. 
Arguments Rec {_}. 

Require Import List. 
Import ListNotations. 
Require Import Coq.Lists.ListSet. 
Require Import Coq.Arith.PeanoNat. 
From MetaCoq.Template Require Import utils.MCList. 

Open Scope bool_scope. 

(* TODO move *)
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

Definition forallb2_option {X : Type} (f : X -> X -> option bool) := fix rec l l' := 
  match l, l' with 
  | nil, nil => Some true
  | x :: l0, x' :: l0' => 
      match f x x', rec l0 l0' with 
      | Some b, Some b' => Some (b && b')
      | _, _ => None
      end
  | _, _ => Some false
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


Section trees.
Context {X : Type}.
Implicit Types (t : rtree X). 

Definition default_tree := Param (X:=X) 0 0. (* bogus tree used as default value*)

(* Building trees *)
(* array of "references" to mutual inductives of innermostly introduced (by Rec) inductive *)
Definition mk_rec_calls i := tabulate (fun j => Param (X := X) 0 j) i. 

Definition mk_node label children := Node (X := X) label children.

(* The usual lift operation *)
(* lift unbound references >= depth to inductive types by n *)
Fixpoint lift_rtree_rec depth n (t : rtree X) := 
  match t with
  | Param i j => 
      (* lift all but the innermost depth types by n *)
      if i <? depth then t else Param (i+n) j
  | Node l children => Node l (map (lift_rtree_rec depth n) children)
  | Rec j defs => Rec j (map (lift_rtree_rec (S depth) n) defs)
  end.

(* lift all unbound references by n *)
Definition rtree_lift n t := if n =? 0 then t else lift_rtree_rec 0 n t. 


(* The usual subst operation *)
(* substitute the depth -th unbound type by sub *)
Fixpoint subst_rtree_rec depth sub t := 
  match t with 
  | Param i j as t => 
      if i <? depth then t 
      else if i =? depth then  (* we refer to the inductive, depth, we want to substitute *)
        rtree_lift depth (Rec j sub) (* substitute in and lift references in sub by depth in order to avoid capture *)
      else Param (i-1) j
  | Node l children => Node l (map (subst_rtree_rec depth sub) children)
  | Rec j defs => Rec j (map (subst_rtree_rec (S depth) sub) defs)
  end.

(* substitute the innermost unbound by sub *)
Definition subst_rtree sub t := subst_rtree_rec 0 sub t.

(* To avoid looping, we must check that every body introduces a node
   or a parameter *)
Fixpoint expand' fuel t := 
  match fuel with 
  | 0 => None
  | S n =>
    match t with 
    | Rec j defs => 
        (* substitute by the j-th inductive type declared here *)
        expand' n (subst_rtree defs (nth j defs default_tree)) 
    | t => Some t
    end
  end. 
Definition expand := expand' fuel. 
(* loops on some inputs:*)
(*Compute(expand (Rec 0 [(Param 0 0)])). *)
  

(* Given a vector of n bodies, builds the n mutual recursive trees.
   Recursive calls are made with parameters (0,0) to (0,n-1). We check
   the bodies actually build something by checking it is not
   directly one of the parameters of depth 0. Some care is taken to
   accept definitions like  rec X=Y and Y=f(X,Y) *)                                   
(* TODO: well, does it actually check that?? expanding first does not seem to be smart, see example from before *)
Definition mk_rec defs := 
  let check := fix rec fuel (histo : set nat) d {struct fuel} := 
    match fuel with 
    | 0 => None
    | S n => 
      match expand d with 
      | Some (Param 0 j) => 
          if set_mem (Nat.eq_dec) j histo 
          then None (* invalid recursive call *)
          else 
            match nth_error defs j with 
            | Some e => rec n (set_add (Nat.eq_dec) j histo) e
            | None => None (* invalid tree *)
            end
      | Some _ => Some tt
      | None => None
      end
    end
  in 
    if existsb is_none (mapi (fun i d => check fuel (set_add (Nat.eq_dec) i (empty_set _)) d) defs)
    then None
    else Some (mapi (fun i d => Rec i defs) defs).

(* Tree destructors, expanding loops when necessary *)
Definition destruct_param {Y} t (f : nat -> nat -> Y) y := 
  match expand t with 
  | Some (Param i j) => f i j
  | _ => y 
  end.
Definition destruct_node {Y} t (f : X -> list (rtree X) -> Y) y := 
  match expand t with 
  | Some (Node l children) => f l children
  | _ => y
  end.
Definition is_node t := 
  match expand t with 
  | Some (Node _ _) => true
  | _ => false
  end.

Fixpoint map_rtree {Y} (f : X -> Y) t := 
  match t with 
  | Param i j => Param i j
  | Node a children => Node (f a) (map (map_rtree f) children)
  | Rec j defs => Rec j (map (map_rtree f) defs)
  end.

(** Structural equality test, parametrized by an equality on elements *)
Definition rtree_eqb (eqbX : X -> X -> bool) := fix rec t t' := 
  match t, t' with 
  | Param i j, Param i' j' => Nat.eqb i i' && Nat.eqb j j'
  | Node x c, Node x' c' => eqbX x x' && list_eqb rec c c'
  | Rec i a, Rec i' a' => Nat.eqb i i' && list_eqb rec a a'
  | _, _ => false
  end.

Fixpoint unwrap_option {X} (l : list (option X)) : option (list X) := 
  match l with
  | [] => Some []
  | Some a :: l => match unwrap_option l with 
                   | Some l => Some (a :: l)
                   | None => None
                   end
  | None :: l => None
  end.

(** Equivalence test on expanded trees. It is parametrized by two
    equalities on elements:
    - [cmp] is used when checking for already seen trees
    - [cmp'] is used when comparing node labels. *)
Definition rtree_equiv (cmp : X -> X -> bool) (cmp' : X -> X -> bool) :=
  let compare := fix rec fuel histo t t' : option bool := 
    if set_memb (pair_eqb (rtree_eqb cmp)) (t, t') histo then Some true else 
    match fuel with 
    | 0 => None 
    | S n => 
        match expand t, expand t' with 
        | Some (Node x v), Some (Node x' v') => 
            if cmp' x x' then forallb2_option (rec n ((t, t') :: histo)) v v' else Some false
        | Some _, Some _ => Some false
        | _, _ => None
        end
    end
  in compare fuel []. 

(** The main comparison on rtree tries first structural equality, then the logical equivalence *)
Definition rtree_equal eqb t t' : option bool := 
  if rtree_eqb eqb t t' then Some true
  else rtree_equiv eqb eqb t t'.

(** Intersection of rtrees of same arity *)
(* Returns either:
   - None if it ran out of fuel
   - Some None if the trees don't intersect
   - Some Some t if t is the intersection
*)
Definition rtree_inter' (eqb : X -> X -> bool) (interlbl : X -> X -> option X) def := 
  fix rec fuel n (histo : list ((rtree X * rtree X) * (nat * nat))) t t' {struct fuel} : option (option (rtree X)) :=
  match fuel with 
  | 0 => None
  | S fuel =>
    match lookup (pair_eqb (rtree_eqb eqb)) (t, t') histo with 
    | Some (i, j) => Some (Some (Param (n - i - 1) j))
    | None => 
        match t, t' with 
        | Param i j, Param i' j' => 
            if Nat.eqb i i' && Nat.eqb j j' then Some (Some t) else Some None
        | Node x a, Node x' a' => 
            match interlbl x x' with 
            | None => Some (Some (mk_node def []))  (* cannot intersect labels, make node with default labels *)
            | Some x'' => 
                match list_lift_option (map2 (rec fuel n histo) a a') with 
                | None => (* out of fuel *) None
                | Some l => Some (option_map (Node x'') (list_lift_option l))
                end
            end 
        | Rec i v, Rec i' v' => 
            (* if possible, we preserve the shape of input trees *)
            if Nat.eqb i i' && Nat.eqb (length v) (length v') then
              let histo := ((t, t'), (n, i)) :: histo in 
                match list_lift_option (map2 (rec fuel (S n) histo) v v') with
                | None => None (* out of fuel *)
                | Some l => Some (option_map (Rec i) (list_lift_option l))
                end
            else (* otherwise, mutually recursive trees are transformed into nested trees *)
              let histo := ((t, t'), (n, 0)) :: histo in 
                match expand t, expand t' with
                | Some t0, Some t0' => 
                  match rec fuel (S n) histo t0 t0' with
                  | None => None
                  | Some r => Some (option_map (fun s => Rec 0 [s]) r)
                  end
                | _, _ => None
                end
          | Rec _ _, _ => 
              match expand t with
              | Some t0 => rec fuel n histo t0 t' 
              | _ => None
              end
          | _, Rec _ _ => 
              match expand t' with 
              | Some t0' => rec fuel n histo t t0' 
              | _ => None
              end
          | _, _ => Some None
        end
    end
  end.
Definition rtree_inter eqb interlbl def t t' := rtree_inter' eqb interlbl def fuel 0 [] t t'.

(** Inclusion of rtrees. *)
Definition rtree_incl (eqb : X -> X -> bool) interlbl def t t' : option bool := 
  match (rtree_inter eqb interlbl def t t') with 
  | Some (Some t'') => rtree_equal eqb t t''
  | Some None => Some false
  | None => None
  end.

(** Tests if a given tree is infinite, i.e. has a branch of infinite length.
   This corresponds to a cycle when visiting the expanded tree.
   We use a specific comparison to detect already seen trees. *)
(* LG: sadly it diverges on some infinite trees.... *)
(*Definition rtree_is_infinite eqb t := *)
  (*let is_inf := fix rec histo t := *)
    (*set_memb (rtree_eqb eqb) t histo *)
    (*|| match expand t with *)
       (*| Node _ v => existsb (rec (t :: histo)) v*)
       (*| _ => false*)
       (*end*)
  (*in is_inf [] t. *)
End trees.
