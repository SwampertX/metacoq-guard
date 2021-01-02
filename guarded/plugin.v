From MetaCoq.Template Require Import Environment utils.MCRTree Ast AstUtils All. 
Open Scope string_scope.
Require Import List String.
Import ListNotations.
Open Scope string_scope.
From MetaCoq.Guarded Require Import Inductives guardchecker positivitychecker Except Trace.


(* explicit instantiation with TemplateMonad as a definition parametric over the monad causes trouble with universe polymorphism *)
Definition list_iter {X} (f : X -> TemplateMonad unit) (l : list X) : TemplateMonad unit := 
  List.fold_left (fun (acc : TemplateMonad unit) x => _ <- acc;; f x) l (ret tt).


(** Compute the wf_paths for the bodies of a mutual inductive (returns a list for the mutually defined types). *)
Definition check_inductive_mib (Σ:global_env) (kn : kername) (mib : mutual_inductive_body) : TemplateMonad (option (list wf_paths)) := 
  let cons_names := map (fun oib => map (fun '(name, _, _) => name) oib.(ind_ctors)) mib.(ind_bodies) in
  let cons_types := map (fun oib => map (fun '(_, type, _) => type) oib.(ind_ctors)) mib.(ind_bodies) in

  match mib.(ind_bodies) with 
  | oib :: _ => 
    let '(param_context, _) := decompose_arity oib.(ind_type) mib.(ind_npars) in

    cons_names <- tmEval cbn cons_names;;
    cons_types <- tmEval cbn cons_types;;
    param_conext <- tmEval cbn param_context;;

    (* [Γ] should contain the parameters (at the head) and the inductives (for recursive usage; after the parameters). *)
    (* the first type should be last in the list *)
    let Γ := List.fold_right (fun oib acc => acc ,, vass (mkBindAnn nAnon oib.(ind_relevance)) oib.(ind_type)) [] mib.(ind_bodies) in
    (* add parameters *)
    let Γ := Γ ,,, param_context in

    match check_positivity_mind true kn cons_names Σ Γ param_context mib.(ind_finite) cons_types with
    | (_, _, _, inl l) => 
        l <- tmEval cbn l;;
        ret (Some l)
    | (_, _, _, inr e) => 
        e <- tmEval cbn e;; 
        tmPrint e;; ret None
    end
  | _ => ret None
  end.

(** Positivity checker *)
Definition check_inductive {A} (a : A) := 
  mlet (Σ, t) <- tmQuoteRec a;;
  match t with
  | tInd ind _ => 
      match lookup_mind_specif Σ ind with 
      | (_, _, _, inl (mib, oib)) => 
          num_unif <- tmEval cbn (num_uniform_params mib);;
          tmPrint num_unif;;
          l <- check_inductive_mib Σ ind.(inductive_mind) mib;;
          match l with 
          | None => ret tt
          | Some l => 
              (*tmPrint l;;*)
              tmPrint "passed positivity check"
          end
      | _ => ret tt
      end
  | _ => ret tt
  end.


(** Compute paths_env *)
(** Since the MC inductives representation does not include wf_paths, we first compute them via the positivity checker. The trees are carried around in an additional paths_env. *)
Fixpoint compute_paths_env Σ0 Σ := 
  match Σ with
  | [] => ret []
  | (kn, InductiveDecl mib) :: Σ' => 
      l <- check_inductive_mib Σ0 kn mib;;
      match l with 
      | None => compute_paths_env Σ0 Σ'
      | Some l => 
          r <- compute_paths_env Σ0 Σ';;
          ret ((kn, l) :: r)
      end 
  | _ :: Σ' => compute_paths_env Σ0 Σ'
  end.


(** recursively traverse term and check fixpoints *)
(* needed for the const unfolding case for demonstrational purposes *)
Unset Guard Checking. 
Fixpoint check_fix_term (Σ : global_env) ρ (Γ : context) (t : term) {struct t} := 
  match t with 
  | tFix mfix _ => 
      (** we should first recursively check the body of the fix (in case of nested fixpoints!) *)
      let mfix_ctx := push_assumptions_context (mfix_names mfix, mfix_types mfix) Γ in
      list_iter (fun b => check_fix_term Σ ρ mfix_ctx b.(dbody)) mfix;;

      (*tmPrint Σ*)
      (*tmPrint Γ;;*)

      (* NOTE : uncomment if using trace monad *)
      match (check_fix Σ ρ Γ mfix) with
      | (_, trace, inr e) => 
          (*trace <- tmEval cbn trace;;*)
          e <- tmEval cbn e;;
          (*tmPrint trace;;*)
          tmPrint e
      | _ => tmPrint "success"
      end

      (* NOTE : uncomment if using exc monad *)
      (*match (check_fix Σ Γ mfix) with*)
      (*| inr e => *)
          (*e <- tmEval cbn e;;*)
          (*tmPrint e*)
      (*| _ => tmPrint "success"*)
      (*end*)

  | tCoFix mfix idx =>
      tmPrint "co-fixpoint checking is currently not implemented"
  | tLambda na T M => 
      _ <- check_fix_term Σ ρ Γ T;;
      _ <- check_fix_term Σ ρ (Γ ,, vass na T) M;;
      ret tt
  | tApp u v => 
      _ <- check_fix_term Σ ρ Γ u;;
      _ <- list_iter (check_fix_term Σ ρ Γ) v;;
      ret tt
  | tProd na A B => 
      _ <- check_fix_term Σ ρ Γ A;;
      _ <- check_fix_term Σ ρ (Γ ,, vass na A) B;;
      ret tt
  | tCast C kind t => 
      _ <- check_fix_term Σ ρ Γ C;;
      _ <- check_fix_term Σ ρ Γ t;;
      ret tt
  | tLetIn na b t b' => 
      _ <- check_fix_term Σ ρ Γ b;;
      _ <- check_fix_term Σ ρ Γ t;;
      _ <- check_fix_term Σ ρ (Γ ,, vdef na b t) b';;
      ret tt
  | tCase ind rtf discriminant brs =>
    _ <- check_fix_term Σ ρ Γ rtf;;
    _ <- check_fix_term Σ ρ Γ discriminant;;
    _ <- list_iter (fun '(_, b) => check_fix_term Σ ρ Γ b) brs;;
    ret tt
  | tProj _ C => 
      _ <- check_fix_term Σ ρ Γ C;;
      ret tt
  | tConst kn u => 
      (* NOTE: this is just done for demonstrational purposes for things we have to extract from the global env. 
      Normally, we would not check things which are already in the global env, as they should already have been checked. *)
      match lookup_env_const Σ kn with 
      | Some const => 
          match const.(cst_body) with 
          | Some t => check_fix_term Σ ρ Γ t
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
  paths_env <- compute_paths_env Σ Σ;;
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
  check_fix_term Σ paths_env [] t.

