(** * "Pretty" printers for terms and contexts. *)
(** De facto not usable for debugging in MetaCoq due to slow reduction. :( *)
(** Adapted from  https://github.com/NeuralCoder3/metacoq/blob/unary-param/translations/de_bruijn_print.v *)



(*

Pretty print for terms with bruijn indices
(it might be easier to go the other way
and print coq terms with indices)
For a complete pretty print with names
unquote and use Coqs Print Command
It is useful as debugging if a term does not type
 *)

Require Import MetaCoq.Template.All.

Require Import List String.
Require Import Ascii.
Require Import Program Arith Lia PeanoNat.
Import ListNotations MonadNotation Nat.

Definition ascii_to_string (a:ascii) : string := String a (EmptyString).
Definition natToChar (n:nat) : ascii := ascii_of_nat(48+n).

Program Fixpoint natToString (n:nat) {measure n} : string :=
  match leb n 9 with
    true =>
    ascii_to_string (natToChar n)
  | false =>
    append (natToString (Nat.div n 10)) (ascii_to_string(natToChar(Nat.modulo n 10)))
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply leb_complete_conv in Heq_anonymous.
  pose proof (divmod_spec n 9 0 9).
  destruct divmod.
  destruct H;trivial.
  cbn. lia.
Qed.

Infix ":s" := String (at level 73).
Infix "+s" := append (at level 72).
Definition linebreak := ascii_to_string(ascii_of_nat 10).

Definition join (xs:list string) : string :=
  fold_left append xs EmptyString.

Require Import String.
Open Scope string_scope.

(* needed for mutual inductive types *)
Definition getInductiveName Σ (ind:kername) (indIndex:nat) : string :=
  match lookup_env Σ ind with 
  | Some (InductiveDecl ind) => 
      match nth_error ind.(ind_bodies) indIndex with 
      | None => "[ind not found]"
      | Some b => b.(ind_name)
      end
  | _ => "[ind not found]"
  end.


Definition getConstructName Σ (ind:kername) (indIndex:nat) (consIndex:nat) : string :=
  match lookup_env Σ ind with 
  | Some (InductiveDecl ind) => 
      match nth_error ind.(ind_bodies) indIndex with 
      | None => "[ctor not found]"
      | Some b => match nth_error b.(ind_ctors) consIndex with
                  | None => "[ctor not found]"
                  | Some (s, _, _) => s
                  end
      end
  | _ => "[ctor not found]"
  end.

Definition nameToString (s:name) : string :=
  match s with
    nAnon => "_"
  | nNamed s => s
  end.

Definition concatString (xs:list string) : string :=
  fold_left (fun a b => a +s b) xs "".

(* Print kername.
Print ident.
Print tmQuoteInductive. *)

Definition lookup_ctx Γ n := 
  match nth_error Γ n with
  | Some decl => nameToString(decl.(decl_name).(binder_name))
  | None => "u" :s (natToString n)
  end.

Definition bruijn_print Σ := fix bruijn_print_aux Γ (t:term) : string :=
  match t with
  | tRel n => 
      ((lookup_ctx Γ n))
  | tVar ident => (ident)
  | tEvar n xs => "TODO:EVAR"
  | tSort univ => 
    "tSort ?"
  | tProd n t t2 => match n.(binder_name) with
                   | nAnon => let s1 := bruijn_print_aux Γ t in
                              let s2 := bruijn_print_aux (Γ ,, vass n t) t2 in
                             ("(":s append s1 (append ") -> " s2))
                   | nNamed s => let s1 := bruijn_print_aux Γ t in
                                 let s2 := bruijn_print_aux (Γ ,, vass n t) t2 in
                                ("∀ (" +s s +s (" : "+s s1) +s "), " +s s2)
                   end
  | tLambda s t t2 => let s1 := bruijn_print_aux Γ t in
                      let s2 := bruijn_print_aux (Γ ,, vass s t) t2 in
                    ("λ ("+s match s.(binder_name) with
                        nAnon => "_"
                      | nNamed s => s
                      end
                     +s " : "+s s1+s"). "+s s2)
  | tLetIn name t1 t2 t3 =>
    let s1 := bruijn_print_aux Γ t1 in 
    let s2 := bruijn_print_aux Γ t2 in 
    let s3 := bruijn_print_aux (Γ ,, vdef name t1 t2) t3 in
    ("let "+s (nameToString name.(binder_name)) +s " := "+s s1 +s " : " +s s2 +s " in "+s linebreak +s s3)
  | tApp t1 t2 =>
    let s1 := bruijn_print_aux Γ t1 in
    let s2 := List.fold_left (fun s t => let s2 := bruijn_print_aux Γ t in (s +s s2 +s ";")) t2 "" in
    ("((" +s s1 +s ") [" +s s2 +s "])")
  | tConst kn ui => let (_,name) := kn in name
  | tInd ind ui => getInductiveName Σ ind.(inductive_mind) ind.(inductive_ind)
  | tConstruct ind n ui => getConstructName Σ ind.(inductive_mind) ind.(inductive_ind) n
  | tCase ((ind,n), _) p c brs =>
    let sc := bruijn_print_aux Γ c in
    let sp := bruijn_print_aux Γ p in
    let sb := fold_left (fun sa x => match x with (n,t) => 
        let st := bruijn_print_aux Γ t in 
          (sa +s " | ("+s(natToString n)+s") " +s st +s linebreak) end) brs "" 
    in 
    (linebreak +s "match (P:" +s (natToString n) +s ") "+s sc +s " return " +s sp +s " with" +s linebreak +s
            sb +s
             "end")
  | tProj p t => "TODO:Proj"
  | tFix mf n =>
    let fix_ctx := Γ ,,, (map (fun d => vdef d.(dname) d.(dbody) d.(dtype)) mf) in
    (fix f xs := match xs with
                  nil => ""
                | mfb::xs =>
                  let sr := f xs in
          let stype := bruijn_print_aux Γ (mfb.(dtype)) in 
          let sbody := bruijn_print_aux fix_ctx (mfb.(dbody)) in
          (linebreak +s "(fix "+s (nameToString mfb.(dname).(binder_name)) +s " : " +s stype +s " := " +s linebreak +s sbody +s ") "+s sr)
                end
    ) mf
  | _ => "TODO"
  end.


Definition print_context Σ Γ := 
  let print_ctx := fix print_ctx Γ := 
    match Γ with
    | [] => ""
    | decl :: Γ' =>
        let na := nameToString (decl.(decl_name).(binder_name)) in
        let ty := bruijn_print Σ Γ' decl.(decl_type) in
        let bod := match decl.(decl_body) with | None => "[?]" | Some t => bruijn_print Σ Γ' t end in
        "((" +s na +s " : " +s ty +s " := " +s bod +s "))" +s print_ctx Γ'
    end
  in "[[" +s print_ctx Γ +s "]]".
        

(*Definition printTest := *)
  (*(forall (P:nat->Prop) (H0:P 0) (HS: forall n, P n -> P (S n)) (n:nat), P n).*)

(*Definition test : TemplateMonad unit := *)
  (*mlet (Σ, t) <- tmQuoteRec printTest;;*)
  (*s <- tmEval cbn (bruijn_print Σ [] t);;*)
  (*tmPrint  s. *)
(*MetaCoq Run test. *)
