Require Import MetaCoq.Guarded.plugin. 

Require Import List String.
Import ListNotations.
Open Scope string_scope.


Print Nat.sub.
Fixpoint div (n m : nat) := 
  match n with 
  | 0 => 0
  | S n => if Nat.ltb (S n) (S m) then 0 else S (div (n - m) m)
  end.  
Compute (div 6 2).
(** NOTE: broken. at least the calls to ltb and sub are properly checked...*)
(** spent a lot of time debugging, but proper debugging is effectively impossible due to slowness *)
(** might also be because I uncommented some reduction stuff because of slowness? who knows *)

MetaCoq Run (check_fix div). 
 
(** * Some examples + explanations *)
(** The guardedness checker works by recursively traversing terms and checking recursive guardedness syntactically.
  The main data structure it works off are regular trees/recursive trees.
  These are computed for every inductive type by the Coq kernel's positivity checker. 
  Essentially, they capture the recursive structure of inductive types. 
  (more precisely, they describe all "well-founded paths", i.e. all paths of how an inhabitant of the inductive type can be constructed -- the positivity checker makes sure that there are no infinite "unguarded" paths)
*)

(** Example : lists *)
(** 
<<
                Rec 0 
                 | 
              (* list *)
          Node (Mrec list_ind)
        /                           \
    (* nil *)                     (* cons *)
    Node Norec                   Node Norec
                            /             \
                        (* x : X *)   (*l : list X *)
                        Node Norec    Param 0 0
  >>

  A recursive tree always contains the trees for a whole mutual inductive block (to account for recursive occurrences).
  The top-level node is a [Rec n], having children for each of the mutually defined types, and describing the recursive structure for the [n]-th type (starting at 0) of this block.

  For lists, there is exactly one mutually inductive block.

  Each of the node for the mutually defined types is annotated with the name of the inductive and has children for each of the constructors.
  The nodes for the constructors are not annotated with anything useful, the Norec does not mean anything. 

  Each of the nodes for the constructors has children for each of the non-parametric arguments. 
  The [nil] constructor obviously has no children. 
  The [cons] constructor has two children. 
    
  The nodes for the arguments are [Norec] if their type does not involve one of the mutually defined types.
  They are [Param i j] for recursive occurrences of types.
  The index [i] refers to the number of [Rec]s up in the tree this refers to (in de Bruijn style). 
    (this can only be non-zero with nested inductives) 
  The index [j] refers to the index of the inductive type in the corresponding block of mutual inductives. 
*)
  

(** Nested inductives need special attention: to correctly handle matches (and subterms) on elements of a nested inductive type we are doing recursion over, the inner inductive type's parameters need to be properly instantiated with the outer inductive type. This is in particular the case for the recursive arguments tree. *)
(** Example: rose trees
   [Inductive rtree (X : Type) := rnode (l : list (rtree X)).]
   When we check a fixpoint which is structural over [r : rtree X] and (after matching) [r] ≃ [rnode l], 
    we want to be able to do recursive calls with elements of [l]. 
   In order to obtain this subterm information when matching on [l], the recargs tree for the [list] type is instantiated with [rtree] beforehand. 

<<
                Rec 0 
                 | 
            Node (Mrec list_ind)
        /                           \
    Node Norec                   Node Norec
                                /             \
                            Node Norec    Param 0 0
  >>

  is turned into

<<
                Rec 0 
                 | 
            Node (Imbr list_ind)
        /                           \
    Node Norec                   Node Norec
                                /             \
                          (* r : rtree *)     (* l : list rtree *)
                            Param 1 0      Param 0 0

  >>
  where the Param 1 0 references the node for [rtree] on the outside (we have to skip over the [Rec] for the inner list type).
  The full tree for [rtree] is then:

<<
              Rec 0
                |
        Node (Mrec rtree_ind)
                | 
            Node Norec
                | 
  [the instantiated tree for list] 
  >>
    
*)


(** When matching on a (loose) subterm of the recursive argument of a fixpoint, we can look in the recursive tree whether a
  particular binder introduced by a match branch is a subterm. *)

(** There are many more complicated behaviours in relation to matches: *)
(** - Matches can be subterms if all branches are subterms. 
    However, this is restricted for dependent matches, depending on the return-type function/match predicate.*)
Fail Fixpoint abc (n : nat) := 
  match n with 
  | 0 => 0
  | S n => abc (match n with | 0 => n | S n => S n end)
  end.
Fixpoint abc (n : nat) := 
  match n with 
  | 0 => 0
  | S n => abc (match n with | 0 => n | S n' => n end)
  end.

MetaCoq Run (check_fix abc). 

(** - If matches are applied to some arguments, we "virtually" apply those arguments to the branches (technically, the checker maintains a stack of such virtual arguments). 
    
    The subterm information of these which is allowed to flow into branches of the match is restricted, too, for dependent matches. *)


(** If we encounter nested fixpoints and apply this nested fixpoint to a subterm of the outer fixpoint (at the position of the recursive argument), we may assume in the body of the inner fixpoint that the recursive argument is a subterm of the outer fixpoint. 
  In this way, we can make recursive calls to the outer fixpoint in the inner fixpoint (see the rosetree example below). 
*)

(** Notably, the guardedness checker reduces at MANY intermediate points: *)
Fixpoint haha_this_is_ridiculous (n : nat) := 
  let _ := haha_this_is_ridiculous n in 0. 
MetaCoq Run (check_fix haha_this_is_ridiculous). 


(** For more details, we refer to the comments in the implementation. *)


(** * Some tests *)

(* to check broken fixpoints *)
Unset Guard Checking.

Definition broken_app  {A : Type} := fix broken_app (l m : list A) {struct l} := 
  match l with
  | [] => m
  | a :: l' => broken_app l m
  end.

(*MetaCoq Run (check_fix broken_app ). *)
(* NOTE: as we only unfold constants at the very top, we need to remove maximally inserted implicits (as the lead to an implicit app, thus preventing broken_app from being unfolded*)
MetaCoq Run (check_fix (@broken_app) ). 


Fixpoint weird_length {X} (l :list X) {struct l} := 
  match l with
  | nil => 0
  | cons x l' => 
      match l with 
      | nil => 1
      | cons y l'' => S (S (weird_length l''))
      end
  end.
MetaCoq Run (check_fix (@weird_length)). 

MetaCoq Run (check_fix app ). 
MetaCoq Run (check_fix rev).
MetaCoq Run (check_fix (@Nat.div)).




(* some attempt at coming up with mutual inductives *)
Inductive even : nat -> Type := 
  | even0 : even 0
  | evenS n : odd n -> even (S n)
  | evenSS n : even n -> even (S (S n))
with odd : nat -> Type := 
  | oddS n : even n -> odd (S n).

Fixpoint count_cons_even n (e : even n) : nat := 
  match e with 
  | even0 => 1
  | evenS n' o => 1 + count_cons_odd n' o 
  | evenSS n e => 1 + count_cons_even n e
  end
with count_cons_odd n (o : odd n) : nat := 
  match o with 
  | oddS n e => 1 + count_cons_even n e
  end.

MetaCoq Run (check_fix count_cons_odd). 
MetaCoq Run (check_fix count_cons_even). 




(** Rosetrees *)
Inductive rtree (X : Type) := 
  | rnode (children : list (rtree X)). 

Fixpoint sumn (l : list nat) := List.fold_left (fun a b => a + b) l 0. 
MetaCoq Run (check_fix sumn). 


Fixpoint rtree_size {X} (t : rtree X) := 
  match t with
  | rnode l => sumn (map rtree_size l)
  end.
MetaCoq Run (check_inductive rtree). 
MetaCoq Run (check_fix rtree_size). 

Unset Guard Checking.
(* I feel a little bad about lying to Coq about the structural argument, but whatever *)
Fixpoint rtree_size_broken {X} (t : rtree X) {struct t} := 
  match t with
  | rnode l => sumn (map (fun _ => rtree_size_broken t) l)
  end.
MetaCoq Run (check_fix rtree_size_broken). 

Fixpoint test (l : list nat) := 
  match l with
  | [] => 0
  | n :: l => sumn l +  test l
  end.
MetaCoq Run (check_fix test). 



Section wo.
  Variable p: nat -> Prop.
  Variable p_dec: forall n, (p n) + ~(p n).

  Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Definition W' : forall n, T n -> { k | p k } :=
    fix F n (a : T n) := 
      let (Φ) := a in 
      match p_dec n with 
      | inl H => exist p n H
      | inr H => F (S n) (Φ H)
      end.

  MetaCoq Run (check_fix W').
End wo.




(** Vectors *)
Set Implicit Arguments.
Set Asymmetric Patterns.
Require Coq.Vectors.Vector.

(** Taken from  https://github.com/coq/coq/issues/4320 *)

Section ilist.

(* Lists of elements whose types depend on an indexing set (CPDT's hlists).
These lists are a convenient way to implement finite maps
whose elements depend on their keys. The data structures used
by our ADT notations uses these to implement notation-friendly
method lookups. *)

Import Coq.Vectors.VectorDef.VectorNotations.

Context {A : Type}. (* The indexing type. *)
Context {B : A -> Type}. (* The type of indexed elements. *)

Fixpoint ilist {n} (l : Vector.t A n) : Type :=
match l with
| [] => unit
| a :: l => (B a) * (ilist l)
end.

MetaCoq Run (check_fix ilist).

Definition icons (a : A) {n} {l : Vector.t A n} (b : B a) (il : ilist l) : ilist (a :: l) := pair b il.

Axiom ilist_hd : forall {n} {As : Vector.t A n} (il : ilist As),
match As return ilist As -> Type with
| a :: As' => fun il => B a
| [] => fun _ => unit
end il.

Axiom ilist_tl : forall {n} {As : Vector.t A n} (il : ilist As),
match As return ilist As -> Type with
| a :: As' => fun il => ilist As'
| [] => fun _ => unit
end il.

Definition ith_body 
    (ith : forall {m : nat} {As : Vector.t A m} (il : ilist As) (n : Fin.t m), B (Vector.nth As n))
    {m : nat}
    {As : Vector.t A m}
    (il : ilist As)
    (n : Fin.t m)
  : B (Vector.nth As n)
:= Eval cbv beta iota zeta delta [Vector.caseS] in
  match n in Fin.t m return forall (As : Vector.t A m), ilist As -> B (Vector.nth As n) with
  | Fin.F1 k =>
    fun As =>
      Vector.caseS (fun n As => ilist As -> B (Vector.nth As (@ Fin.F1 n)))
      (fun h n t => ilist_hd) As
  | Fin.FS k n' =>
    fun As =>
      Vector.caseS (fun n As => forall n', ilist As -> B (Vector.nth As (@ Fin.FS n n')))
        (fun h n t m il => @ ith _ _ (ilist_tl il) m)
        As n'
  end As il.

Fixpoint ith {m : nat} {As : Vector.t A m} (il : ilist As) (n : Fin.t m) {struct n} : B (Vector.nth As n) := 
  @ ith_body (@ ith) m As il n.

(* TODO: broken *)
MetaCoq Run (check_fix ith).

End ilist.


(** * Positivity examples *)

Inductive even : nat -> Prop := 
  | evenO : even O
  | evenSS n: odd n -> even ((S n))
with odd : nat -> Prop := 
  | oddSS n : odd n -> odd (S (S n)). 

Unset Positivity Checking.
Inductive nonpos := 
  | nonposC (f : nonpos -> nat) : nonpos. 

MetaCoq Run (check_inductive nonpos).
