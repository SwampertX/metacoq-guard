
Fixpoint check_rec_call_stack G (stack : list stack_element) (rs : list redex_stack_element) (t : term) {struct t} : exc (list redex_stack_element) := 
  let num_fixes := #|decreasing_args| in 
  match t with 
  | tApp f args =>
      (* check_rec_call on every arg, which updates rs and stack iteratively *)
      (* check_rec_call_stack on f *)
      '(rs', stack') <- fold_right (fun arg rs_stack =>
          '(rs, stack) <- rs_stack ;;
          '(needreduce, rs') <- check_rec_call G rs arg ;;
          let stack' := push_stack_closure G needreduce arg stack in
          ret (rs', stack')) (ret (rs, stack)) args ;;
      check_rec_call_stack G stack' rs' f

  | tRel p =>
      (** IF [p] is a fixpoint (of the block of fixpoints we are currently checking), i.e. we are making a recursive call,
          THEN IF stack can supply subterm information for recarg
               THEN 1. stack_elem_specif recarg
                    2. check_is_subterm ind_tree recarg -> check_subterm_result
                    3. IF NeedReduce redexes
                        THEN set_need_reduce rs redexes -> rs
                        ELSE (Invalid subterm) GUARD_ERROR
               ELSE set_need_reduce_top rs -> rs
          ELSE check_rec_call_state NoNeed (retrieve the term from context, suitably lifted)*)
      if (Nat.leb G.(rel_min_fix) p) && (Nat.ltb p (G.(rel_min_fix) + num_fixes)) then
        let rec_fixp_index := G.(rel_min_fix) + num_fixes - 1 - p in
        decreasing_arg <- except (IndexErr "check_rec_call_stack" "invalid fixpoint index" rec_fixp_index) $ 
          nth_error decreasing_args rec_fixp_index;;
        let z_exc := except
          (IndexErr "check_rec_call_stack" "not enough arguments for recursive fix call" decreasing_arg) $ 
          nth_error stack decreasing_arg
        in
        catchMap z_exc
          (* recursive call doesn't have enough arguments. usually because obfuscated or eta-expanded. *)
          (fun _exc => trace "getting wf_paths for recarg on stack failed. setting needreduce for top of rs" ;;
            ret $ set_need_reduce_top G.(loc_env) (NotEnoughArgumentsForFixCall decreasing_arg) rs)
          (* recursive call has enough arguments. key check: if recarg is subterm, possibly needreduce *)
          (fun (z : stack_element) : exc (list redex_stack_element) =>
            (** get the tree for the recursive argument type *)
            recarg_tree <- except
              (IndexErr "check_rec_call_stack" "no tree for the recursive argument" rec_fixp_index)
              (nth_error trees rec_fixp_index);;
            z_tree <- stack_element_specif Σ ρ z;;
            result <- check_is_subterm z_tree recarg_tree;;
            let guard_err : fix_guard_error := illegal_rec_call G decreasing_arg z in
            match result with
              | NeedReduceSubterm l => 
                  trace $ if #|l| == 0 then "is a subterm" else "possibly a subterm, need to reduce at "^(string_of_nat #|l|)^" redexes" ;;
                  ret (m := fun x => exc x) (set_need_reduce G.(loc_env) l guard_err rs)
              | InvalidSubterm => raise (GuardErr "check_rec_call_stack" "invalid subterm" guard_err)
            end)
      else
        check_rec_call_state G NoNeedReduce stack rs (fun _ =>
          entry <- except (IndexErr "check_rec_call" ("dB index out of range"^print_context Σ G.(loc_env))p) $ nth_error G.(loc_env) p;;
          except (OtherErr "check_rec_call_stack :: tRel" "found assumption instead of definition") $ option_map (fun t => (lift0 p t, [])) entry.(decl_body)
        )

  (** Assume we are checking the fixpoint f. For checking [g a1 ... am] where
  <<
  g := match [discriminant]
      as [rtf.pcontext[0]]
      in [ind_nparams_relev.ci_ind]
      return [rtf.preturn]
    with 
      | C_i [branches[i].bcontext] -> [branches[i].bbody]
    end
  >>
  we need to fulfill the following conditions:
  1. f is guarded wrt the set of subterms S in a1 ... am
  2. f is guarded wrt the set of subterms S in the return-type [rtf]
  3. f is guarded wrt the set of subterms S in [discriminant]
  4. for each branch Ci xi1 ... xin => bi
      where S' := S ∪ { xij | the constructor Ci is recursive in the argument xij }exc (list redex_stack_element) :
    f is guarded with respect to S' in the branch body
    bi (virtually) applied to a1 ... am, where we restrict the subterm information of a1 ... am to 
    what is allowed to flow through the rtf (???)

  then f is guarded with respect to the set of subterms S in [g a1 ... am].
    (YJ: Taken from Eduardo's "Codifying guarded recursions" )
  *)
  | tCase ci ti discriminant branches => 
    (* 1. Expand branches (make them into lambda form)
       2. check_rec_call discriminant rs -> needred_discriminant, rs
       3. check_inert_subterm_rec_call return_type rs -> rs
       4. specify_branches -> branches_specif (set_iota_specif disc_spec default:IB(#|rs|))
       5. filter_stack_domain stack -> stack
       6. rs := NoNeed:rs
          for each branch 0..n, check_rec_call_stack branches[i] branches_specif[i] rs -> rs
       7. needred := needred_discriminant or rs[top]
          check_rec_call_state needred rs.tail (
          - whd_all discriminant -> hd, args
          - hd := IF tCoFix THEN whd_all (contract_cofix hd) ELSE hd
          - IF hd = tConstruct THEN apply_branch hd args ELSE whd_handle_rest *)
      trace "expand branches" ;;
      '(p, branches) <- expand_case Σ ci ti branches ;;
      list_iteri (fun i br => trace $ "expanded "^(string_of_nat i)^"-th branch: "^(print_term Σ G.(loc_env) br)) branches ;;
      trace "checking discriminant" ;;
      '(needreduce_discr, rs) <- check_rec_call G rs discriminant ;;
      trace "checking return type " ;;
      rs <- check_inert_subterm_rec_call G rs p ;;
      (* compute the recarg info for the arguments of each branch *)
      trace "checking branches " ;;
      let rs' := NoNeedReduce::rs in
      let nr := redex_level rs' in
      trace "subterm_specif of the discriminant: " ;;
      disc_spec <- (subterm_specif Σ ρ G [] discriminant) ;;
      trace "subterm_specif of the branches: " ;;
      case_spec <- branches_specif Σ G (set_iota_specif nr disc_spec) ci.(ci_ind);;
      trace "filter stack" ;;
      let result := filter_stack_domain Σ ρ G.(loc_env) nr p stack in
      stack' <- result ;; 
      rs' <- fold_left_i (fun k rs' br' =>
          (* TODO: quadratic *)
          rs' <- rs' ;;
          spec <- except (IndexErr "check_rec_call_stack :: tCase" "not enough specs" k) $ nth_error case_spec k ;;
          trace $ "checking the "^(string_of_nat k)^"-th branch" ;;
          let stack_br := push_stack_args spec stack' in
          check_rec_call_stack G stack_br rs' br') branches (ret rs') ;;
      needreduce_br <- except (IndexErr "check_rec_call_stack :: tCase" "" 0) $ hd rs' ;;
      rs <- except (IndexErr "check_rec_call_stack :: tCase" "" 0) $ tl rs' ;;
      res <- check_rec_call_state G (needreduce_br ||| needreduce_discr) stack rs (fun _ =>
        (* we try hard to reduce the match away by looking for a
            constructor in c_0 (we unfold definitions too) *)
        trace "whd_all on discriminant" ;;
        trace $ print_term Σ G.(loc_env) discriminant ;;
        discriminant <- whd_all Σ G.(loc_env) discriminant ;;
        trace "into" ;;
        trace $ print_term Σ G.(loc_env) discriminant ;;
        let '(hd, args) := decompose_app discriminant in
        '(hd, args) <- match hd with
          | tCoFix cf idx =>
              cf' <- contract_cofix cf idx ;;
              trace "whd_all on cofix head in tApp" ;;
              hd' <- whd_all Σ G.(loc_env) (tApp cf' args) ;;
              ret $ decompose_app hd'
          | _ => ret (hd, args)
          end ;;
        match hd return exc (term * list stack_element) with
        | tConstruct ind idx _ =>
            c' <- apply_branch Σ G.(loc_env) ind idx args ci branches ;;
            ret (c', [])
        | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _
        | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ =>
            raise $ OtherErr "check_rec_call_stack :: tCase" "whd_all is broken"
        | tRel _ | tVar _ | tConst _ _ | tApp _ _ | tCase _ _ _ _ | tFix _ _
        | tProj _ _ | tCast _ _ _ | tEvar _ _ =>
            raise NoReductionPossible
        end) ;;
        trace "done checking case" ;;
        ret res


  (** Assume we are checking the fixpoint f wrt the set of subterms S.ft_i (fun k rs' br' =>
      The arguments called on g, [l] = l1 ... lm
      This implements the following rule for checking the term [g l1 ... lm]:
      if - g = fix g (y1:T1)...(yp:Tp) {struct yp} := e, then the term
      [g l1 ... lm] is guarded wrt S if:
        1. f is guarded wrt the set of subterms S in l1 ... lm        
        2. f is guarded wrt the set of subterms S in T1 ... Tp        
        YJ: why is condition 3 necessary?
        3. lp, the recursive argument of g, is a sub-term of the recursive argument of f
          and f is guarded wrt the set of subterms S ∪ {yp} in e
          OR
          lp is *not* a sub-term of the recursive argument of f
          and f is guarded with respect to the set of subterms S in e
      then f is guarded with respect to the set of subterms S in (g l1 ... lm). 
      Eduardo 7/9/98 according to Bruno *)
  | tFix mfix_inner fix_ind => 
      (* 1. NoNeed::rs -> rs
            for every mutual fix, check_inert_subterm_rec_call return_type rs -> rs
         2. push all mutual fixes into the context, as NotSubterm
         2. drop_uniform_parameters bodies -> bodies
         3. filter_fix_stack_domain #|rs| stack num_unif_params -> fix_stack
            firstn (min #|stack| (decr_arg + 1)) fix_stack -> fix_stack
         4. fix_stack -> stack_this
            firstn num_unif_params fix_stack -> stack_others
         5. for b in bodies:
              check_nested_fix_body (IF correct fix THEN stack_this ELSE stack_others (why?)) b -> rs
         6. check_rec_call_state rs[0] rs.tail (skipn num_unif_params stack) (
            - IF stack[recarg] = SArg THEN raise NoReductionPossible ELSE whd_all recarg -> recarg
            - recarg -> (hd, args)
            - IF hd = tConstruct THEN contract_fix fix hd args ELSE whd_handle_rest)*)
      trace "check_rec_call_stack :: tFix" ;;
      (* | Fix ((recindxs,i),(_,typarray,bodies as recdef) as fix) -> *)
      f <- except (IndexErr "check_rec_call_stack" "not enough fixpoints" fix_ind) $ nth_error mfix_inner fix_ind ;;
      let decrArg := f.(rarg) in
      let nbodies := #|mfix_inner| in
      rs' <- fold_left (fun rs t =>
        rs <- rs ;;
        acc <- check_inert_subterm_rec_call G rs t ;;
        ret acc)
        (map dtype mfix_inner) (ret $ NoNeedReduce::rs)  ;;
      let G' := push_fix_guard_env G mfix_inner in
      let bodies := map dbody mfix_inner in
      let nuniformparams := find_uniform_parameters (map rarg mfix_inner) #|stack| bodies in
      let bodies := drop_uniform_parameters nuniformparams bodies in
      let fix_stack := filter_fix_stack_domain (redex_level rs) decrArg stack nuniformparams in
      let fix_stack := if decrArg <? (List.length stack) then List.firstn (decrArg+1) fix_stack else fix_stack in
      let stack_this := lift_stack nbodies fix_stack in
      let stack_others := lift_stack nbodies (List.firstn nuniformparams fix_stack) in
      (* Check guard in the expanded fix *)
      rs' <- fold_left2_i (fun j rs' recindx body =>
          rs' <- rs' ;;
          let fix_stack := if fix_ind == j then stack_this else stack_others in
          (* FIXME: possible db error *)
          check_nested_fix_body G' recindx fix_stack rs' body)
        (map rarg mfix_inner) bodies (ret rs') ;;
      needreduce_fix <- except (IndexErr "check_rec_call_stack :: tFix" "" 0) $ hd rs' ;;
      rs <- except (IndexErr "check_rec_call_stack :: tFix" "" 0) $ tl rs' ;;
      let non_absorbed_stack := List.skipn nuniformparams stack in
      check_rec_call_state G needreduce_fix non_absorbed_stack rs (fun _ =>
        (* we try hard to reduce the fix away by looking for a
          constructor in [decrArg] (we unfold definitions too) *)
        if Nat.leb #|stack| decrArg then raise NoReductionPossible else
        decr_stack_elem <- except (IndexErr "check_rec_call_stack :: tFix" "" 0) $ nth_error stack decrArg ;;
        match decr_stack_elem with
        | SArg _ => raise NoReductionPossible (* A match on the way *)
        | SClosure _ _ n recArg =>
          trace "whd_all on recursive argument" ;;
          let recarg_lifted := lift0 n recArg in
          trace $ print_term Σ G.(loc_env) recarg_lifted ;;
          c <- whd_all Σ G.(loc_env) recarg_lifted ;;
          trace "into" ;;
          trace $ print_term Σ G.(loc_env) c ;;
          let '(hd, _) := decompose_app c in
          match hd with
          | tConstruct _ _ _ =>
              f' <- contract_fix mfix_inner fix_ind ;;
              ret (f', stack)
          | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _
          | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ =>
              raise $ OtherErr "check_rec_call_stack :: tCase" "whd_all is broken"
          | tRel _ | tVar _ | tConst _ _ | tApp _ _ | tCase _ _ _ _ | tFix _ _
          | tProj _ _ | tCast _ _ _ | tEvar _ _ =>
              raise $ NoReductionPossible
          end
        end)

    (* check_rec_call_state NoNeed (lookup_cst(kn).body)*)
  | tConst kn u =>
      check_rec_call_state G NoNeedReduce stack rs (fun _ =>
        match lookup_constant Σ kn with
        | Some {| cst_body := Some b |} =>
            trace $ "found const with body "^(print_term Σ G.(loc_env) b) ;;
            ret (subst_instance u b, [])
        | _ => raise (EnvErr "constant" kn "not found")
        end
        )

    (* 1. check_rec_call ty
       2. IF stack is not empty
          THEN pop the stack, push binder into env with the specs from the stack, check_rec_call body
          ELSE push binder into env as internally bound subterm { #|rs| }, or NotSubterm if rs is empty
       3. check_rec_call_stack body *)
   | tLambda x ty body =>
      trace "check_rec_call_stack :: tLambda" ;;
      res <- check_rec_call G rs ty ;;
      let '(needreduce, rs) := res in
      match stack with
      | elt :: stack =>
          trace "popping the bound variable (and its spec from the stack) into the guard env" ;;
          trace ("  Γ:"^print_context Σ G.(loc_env)) ;;
          trace ("  Γg:"^print_guarded_env Σ G.(guarded_env)) ;;
          trace ("  stack("^(string_of_nat #|stack|)^"): "^print_stack Σ stack) ;;
          trace ("  rs("^(string_of_nat #|rs|)^"): "^print_rs Σ rs) ;;
          '(G, stack, body) <- pop_argument Σ ρ needreduce G elt stack x ty body ;;
          trace "after pop_argument" ;;
          trace ("  Γ:"^print_context Σ G.(loc_env)) ;;
          trace ("  Γg:"^print_guarded_env Σ G.(guarded_env)) ;;
          trace ("  stack("^(string_of_nat #|stack|)^"): "^print_stack Σ stack) ;;
          trace ("  rs("^(string_of_nat #|rs|)^"): "^print_rs Σ rs) ;;
          check_rec_call_stack G stack rs body
      | [] =>
          (* we don't have specs from the arguments to infer from *)
          trace "pushing the bound variable into the context as internally bound subterm" ;;
          check_rec_call_stack (push_var_guard_env G (redex_level rs) x ty) [] rs body
      end

    (* Same as tLambda, but stack is always irrelevant.
       1. check_rec_call ty
       2. push binder into env as internally bound subterm { #|rs| }, or NotSubterm if rs is empty *)
  | tProd x ty body => 
      rs' <- check_inert_subterm_rec_call G rs ty ;;
      check_rec_call_stack (push_var_guard_env G (redex_level rs) x ty) [] rs' body

    (* 1. for every mutual cofix, check_inert_subterm_rec_call return_type rs -> rs
       2. push all mutual cofixes into guard_env as NotSubterm
       3. for every mutual cofix,
          check_rec_call rs body -> needreduce, rs
          check_rec_call_state needreduce rs (raise NoRedPossible) -> rs *)
  | tCoFix mfix_inner fix_ind => 
      let rs := fold_left
        (fun rs t => rs <- rs ;; check_inert_subterm_rec_call G rs t)
        (map dtype mfix_inner) (ret rs) in
      let G' := push_fix_guard_env G mfix_inner in
      fold_left (fun rs body =>
          rs <- rs ;;
          '(needreduce', rs) <- check_rec_call G' rs body ;;
          check_rec_call_state G needreduce' stack rs (fun _ => raise NoReductionPossible))
        (map dbody mfix_inner) (ret rs)

    (* check_rec_call_state NoNeed (raise NoRedPossible) *)
  | tInd _ _ | tConstruct _ _ _ =>
    check_rec_call_state G NoNeedReduce stack rs (fun _ => raise NoReductionPossible)

    (* 1. check_rec_call c -> needreduce, rs
       2. check_rec_call_state needreduce rs (
            - whd_all c -> hd, args
            - IF hd is tCoFix THEN whd_all (contract_cofix (hd, args)) ELSE hd, args -> hd, args)
            - IF hd is tConstruct THEN args[p.npars + p.arg] ELSE whd_handle_rest *)
  | tProj p c => (* c.(p) *)
      '(needreduce', rs) <- check_rec_call G rs c ;;
      check_rec_call_state G needreduce' stack rs (fun tt =>
        (* if this fails, try to reduce the projection by looking for a constructor in c *)
        trace "TODO: whd_all on projection" ;;
        c <- whd_all Σ G.(loc_env) c;;
        let '(hd, args) := decompose_app c in 
        '(hd, args) <- match hd with 
        | tCoFix cf idx =>
            cf' <- contract_cofix cf idx ;;
            t <- whd_all Σ G.(loc_env) (tApp cf' args);;
            ret $ decompose_app t
        | _ => ret (hd, args)
        end;;
        match hd with
        | tConstruct _ _ _ =>
            let i := p.(proj_npars) + p.(proj_arg) in
            arg <- except (IndexErr "check_rec_call_stack" "index out of range" i) $ nth_error args i ;;
            ret (arg, [])
        | tCoFix _ _ | tInd _ _ | tLambda _ _ _ | tProd _ _ _ | tLetIn _ _ _ _
        | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ =>
            raise $ OtherErr "check_rec_call_stack :: tProj" "whd_all is broken"
        | tRel _ | tVar _ | tConst _ _ | tApp _ _ | tCase _ _ _ _ | tFix _ _
        | tProj _ _ | tCast _ _ _ | tEvar _ _ =>
            raise NoReductionPossible
        end)

    (* check_rec_call_state NoNeedReduce (get from context, otherwise raise Error)*)
  | tVar _ => ret rs
  (* FIXME: do vars work in MC? *)
  (* | tVar id => 
      check_rec_call_state G NoNeedReduce stack rs (fun tt =>
        entry <- except (OtherErr "check_rec_call_stack" "unknown variable") $
          find (fun ctx_decl => ctx_decl.(decl_name) == id) G.(loc_env);;
        match entry.(decl_body) with
        | None => None
        | Some t => Some (t, [])
        end) *)
   
    (* 1. check_rec_call rs bound_term -> needred_c, rs
       2. check_rec_call rs type -> needred_t, rs
       3. IF needred_stack || needred_c || needred_t
          THEN check_rec_call_stack (b[x<-c])
          ELSE check_rec_call_stack ((x:t=c, subterm_specif(c))::G) b *)
  | tLetIn x c t b => (* let x : t := c in b*)
      '(needreduce_c, rs) <- check_rec_call G rs c ;;
      '(needreduce_t, rs) <- check_rec_call G rs t ;;
      match needreduce_of_stack stack ||| needreduce_c ||| needreduce_t with
      | NoNeedReduce =>
          (* Stack do not require to beta-reduce; let's look if the body of the let needs *)
          spec <- subterm_specif Σ ρ G [] c ;;
          let stack := lift_stack 1 stack in
          check_rec_call_stack (push_let G (x,c,t,spec)) stack rs b
      | NeedReduce _ _ => check_rec_call_stack G stack rs (subst10 c b)
      end
  
    (* self-explanatory: check type then check term *)
  | tCast c _ t => 
      rs <- check_inert_subterm_rec_call G rs t ;;
      check_rec_call_stack G stack rs c

    (* primitive data types are guarded. 
       sorts are guarded. *)
  | tSort _ | tInt _ | tFloat _ | tArray _ _ _ _ => ret rs

    (* evars are guarded. *)
  | tEvar _ _ => ret rs
  end

(** Check the body [body] of a nested fixpoint with decreasing argument [decr] (dB index) and subterm spec [sub_spec] for the recursive argument.*)
(** We recursively enter the body of the fix, adding the non-recursive arguments preceding [decr] to the guard env and finally add the decreasing argument with [sub_spec], before continuing to check the rest of the body *)
(* while decr > 0 :
  1. whd_all body -> body
  2. IF body is tLambda x ty body
     THEN (push all arguments up till (incl, since decr := recpos + 1) recarg into G)
          IF stack is not empty
          THEN check_inert_subterm_rec_call ty, pop_argument into G, loop (decr -= 1)
          ELSE (? where is the check type) push into G as Not Subterm (or internally bounded), loop (decr -= 1)
  decr == 0 means there are already (recpos + 1) entries in G as expected.
  check_inert_subterm_rec_call rs body
*)
(* this is probably a duplicate of [inductive_of_mutfix] and could be abstracted out.] *)
with check_nested_fix_body G (decr:nat) stack (rs : list redex_stack_element) (body:term) {struct decr}: exc (list redex_stack_element) := 
  trace ("check_nested_fix_body :: "^print_term Σ G.(loc_env) body) ;;
  trace ("  Γ:"^print_context Σ G.(loc_env)) ;;
  trace ("  Γg:"^print_guarded_env Σ G.(guarded_env)) ;;
  trace ("  rs("^(string_of_nat #|rs|)^"): "^print_rs Σ rs) ;;
  if decr == 0 then check_inert_subterm_rec_call G rs body else 
  (** reduce the body *)
  body_whd <- whd_all Σ G.(loc_env) body;;
  match body_whd with 
  | tLambda x ty body =>
      match stack with
      | elt :: stack =>
          rs <- check_inert_subterm_rec_call G rs ty ;;
          '(G', stack', body') <- pop_argument Σ ρ NoNeedReduce G elt stack x ty body ;;
          check_nested_fix_body G' (pred decr) stack' rs body'
      | [] => (* ran out of stack, not subterm by default *)
          let G' := push_var_guard_env G (redex_level rs) x ty in
          check_nested_fix_body G' (pred decr) [] rs body
      end
  | _ => raise $ GuardErr "check_nested_fix_body" "illformed inner fix body" NotEnoughAbstractionInFixBody
  end

(* IF needreduce head || needreduce stack -> e
   THEN expand_head -> t', stack';
        IF NoReductionPossible THEN rs := e :: tail rs
        ELSE IF Other error THEN RAISE
        ELSE check_rec_call_stack (stack' ++ stack) t'
   ELSE return rs *)
with check_rec_call_state G needreduce_of_head stack rs (expand_head : unit -> exc (term * list stack_element)) {struct rs}:=
  (* Test if either the head or the stack of a state
    needs the state to be reduced before continuing checking *)
  trace ("check_rec_call_state") ;;
  trace ("  Γ:"^print_context Σ G.(loc_env)) ;;
  trace ("  Γg:"^print_guarded_env Σ G.(guarded_env)) ;;
  trace ("  rs("^(string_of_nat #|rs|)^"): "^print_rs Σ rs) ;;
  trace ("  stack("^(string_of_nat #|stack|)^"): "^print_stack Σ stack) ;;
  let e := needreduce_of_head ||| needreduce_of_stack stack in
  match e with
  | NoNeedReduce =>
      trace $ "no need to reduce, returning " ^ print_rs Σ rs ;;
      ret rs
  | NeedReduce _ _ =>
      trace $ "need to reduce, trying to expand head " ;;
      (* Expand if possible, otherwise, last chance, propagate need
        for expansion, in the hope to be eventually erased *)
      catchMap (expand_head tt)
        (fun err => trace "expand head failed, propagating need for expansion" ;; match err with
          | NoReductionPossible =>
              tail <- except (IndexErr "check_rec_call_state" "" 0) $ tl rs ;;
              ret $ e :: tail
          | _ => raise err
          end)
        (fun '(c, stack') => trace "expand head succeeded" ;; check_rec_call_stack G (stack' ++ stack) rs c)
  end

with check_inert_subterm_rec_call G rs c {struct rs} : exc (list redex_stack_element) :=
  trace ("check_inert_subterm_rec_call :: "^print_term Σ G.(loc_env) c) ;;
  trace ("  Γ:"^print_context Σ G.(loc_env)) ;;
  trace ("  Γg:"^print_guarded_env Σ G.(guarded_env)) ;;
  trace ("  rs("^(string_of_nat #|rs|)^"): "^print_rs Σ rs) ;;
  '(needreduce, rs) <- check_rec_call G rs c ;;
  check_rec_call_state G needreduce [] rs (fun _ => raise NoReductionPossible)

with check_rec_call G rs c {struct rs} : exc (redex_stack_element * list redex_stack_element):=
  let str := print_term Σ G.(loc_env) c in 
  trace ("check_rec_call :: ("^ string_of_nat (String.length str) ^ ") " ^ str ) ;;
  trace ("  Γ:"^print_context Σ G.(loc_env)) ;;
  trace ("  Γg:"^print_guarded_env Σ G.(guarded_env)) ;;
  trace ("  rs("^(string_of_nat #|rs|)^"): "^print_rs Σ rs) ;;
  res <- check_rec_call_stack G [] (NoNeedReduce :: rs) c ;;
  head <- except (IndexErr "check_rec_call" "" 0) $ hd res ;;
  tail <- except (IndexErr "check_rec_call" "" 0) $ tl res ;;
  trace ("check_rec_call done ::  ("^ string_of_nat (String.length str) ^ ")") ;;
  ret (head, tail).