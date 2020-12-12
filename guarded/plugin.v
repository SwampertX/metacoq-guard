From MetaCoq.Template Require Import Environment utils.MCRTree Ast AstUtils All. 
Open Scope string_scope.
Require Import List String.
Import ListNotations.
Open Scope string_scope.
From MetaCoq.Guarded Require Import Inductives Except Trace.


(* explicit instantiation with TemplateMonad as a definition parametric over the monad causes trouble with universe polymorphism *)
Definition list_iter {X} (f : X -> TemplateMonad unit) (l : list X) : TemplateMonad unit := 
  List.fold_left (fun (acc : TemplateMonad unit) x => _ <- acc;; f x) l (ret tt).


(** recursively traverse term and check fixpoints *)
(* needed for the const unfolding case for demonstrational purposes *)
Unset Guard Checking. 
Fixpoint check_fix_term (Σ : global_env) (Γ : context) (t : term) {struct t} := 
  match t with 
  | tFix mfix _ => 
      (** we should first recursively check the body of the fix (in case of nested fixpoints!) *)
      let mfix_ctx := push_assumptions_context (mfix_names mfix, mfix_types mfix) Γ in
      list_iter (fun b => check_fix_term Σ mfix_ctx b.(dbody)) mfix;;

      (*tmPrint Σ*)
      (*tmPrint Γ;;*)

      (* NOTE : uncomment if using trace monad *)
      (*match (check_fix Σ Γ mfix) with*)
      (*| (_, trace, inr e) => *)
          (*trace <- tmEval cbn trace;;*)
          (*e <- tmEval lazy e;;*)
          (*tmPrint trace;;*)
          (*tmPrint e*)
      (*| _ => tmPrint "success"*)
      (*end*)

      (* NOTE : uncomment if using exc monad *)
      match (check_fix Σ Γ mfix) with
      | inr e => 
          e <- tmEval lazy e;;
          tmPrint e
      | _ => tmPrint "success"
      end

  | tCoFix mfix idx =>
      tmPrint "co-fixpoint checking is currently not implemented"
  | tLambda na T M => 
      _ <- check_fix_term Σ Γ T;;
      _ <- check_fix_term Σ (Γ ,, vass na T) M;;
      ret tt
  | tApp u v => 
      _ <- check_fix_term Σ Γ u;;
      _ <- list_iter (check_fix_term Σ Γ) v;;
      ret tt
  | tProd na A B => 
      _ <- check_fix_term Σ Γ A;;
      _ <- check_fix_term Σ (Γ ,, vass na A) B;;
      ret tt
  | tCast C kind t => 
      _ <- check_fix_term Σ Γ C;;
      _ <- check_fix_term Σ Γ t;;
      ret tt
  | tLetIn na b t b' => 
      _ <- check_fix_term Σ Γ b;;
      _ <- check_fix_term Σ Γ t;;
      _ <- check_fix_term Σ (Γ ,, vdef na b t) b';;
      ret tt
  | tCase ind rtf discriminant brs =>
    _ <- check_fix_term Σ Γ rtf;;
    _ <- check_fix_term Σ Γ discriminant;;
    _ <- list_iter (fun '(_, b) => check_fix_term Σ Γ b) brs;;
    ret tt
  | tProj _ C => 
      _ <- check_fix_term Σ Γ C;;
      ret tt
  | tConst kn u => 
      (* NOTE: this is just done for demonstrational purposes for things we have to extract from the global env. 
      Normally, we would not check things which are already in the global env, as they should already have been checked. *)
      match lookup_env_const Σ kn with 
      | Some const => 
          match const.(cst_body) with 
          | Some t => check_fix_term Σ Γ t
          | _ => ret tt
          end
      | None => ret tt
      end


      (* do not unfold nested consts *)
      (*ret tt *)
  | _ => ret tt 
  end.


Set Guard Checking.

Definition check_fix {A} (a : A) :=
  mlet (Σ, t) <- tmQuoteRec a ;;
  t <- match t with 
       | tConst kn u => 
          match lookup_env_const Σ kn with 
          | Some const => 
              match const.(cst_body) with 
              | Some t => ret t
              | _ => ret t
              end
          | None => ret t
          end
        | _ => ret t
       end;;
  (*tmPrint t;;*)
  check_fix_term Σ [] t.

