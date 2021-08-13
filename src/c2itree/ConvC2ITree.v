From compcert Require Import
     AST Maps Globalenvs Memory Values Linking.
From compcert Require Import
     Ctypes Clight.
From ITree Require Import ITree.

Require Import sflib.
Require Import StdlibExt IntegersExt.
Require Import SystemProgs.

Require Import SysSem.
Require Import SyncSysModel.
Require Import RTSysEnv.
Require Import OSNodes.
(* Require Import VerifProgBase. *)
Require Import CProgEventSem.
Require Import CProgSimLemmas.

Require Import ZArith String List Lia.

Import ITreeNotations.

Definition id_list_norepet_c: list ident -> bool :=
  fun ids => if Coqlib.list_norepet_dec (ident_eq) ids then true else false.

Definition id_list_disjoint_c: list ident -> list ident -> bool :=
  fun ids1 ids2 =>
    if (Coqlib.list_disjoint_dec ident_eq ids1 ids2)
    then true else false.

Fixpoint alloc_variables_c (ge: genv) (e: env)
         (m: mem) (vars: list (ident * type))
  : env * mem :=
  match vars with
  | [] => (e, m)
  | (id, ty) :: vars' =>
    let (m1, b1) := Mem.alloc m 0 (sizeof ge ty) in
    alloc_variables_c ge (PTree.set id (b1, ty) e) m1 vars'
  end.

Definition function_entry_c
           (ge: genv) (f: function) (vargs: list val) (m: mem)
  : (env * temp_env * mem)? :=
  if (id_list_norepet_c (var_names (fn_vars f)) &&
      id_list_norepet_c (var_names (fn_params f)) &&
      id_list_disjoint_c (var_names (fn_params f))
                         (var_names (fn_temps f)))%bool
  then
    let (e, m') := alloc_variables_c
                     ge empty_env m (fn_vars f) in
    match
      bind_parameter_temps (fn_params f) vargs
                            (create_undef_temps
                               (fn_temps f))
    with
    | None => None
    | Some le => Some (e, le, m')
    end
  else None.

(* Kcall optid _ _ _ k' -> return (k', optid, mem, v) *)
Inductive scallE : Type -> Type :=
| SCallEvent (b: block) (fd: fundef) (vargs: list val)
             (* (k: cont) *)
             (m: mem)
  : scallE ((* cont * ident? * *) mem * val)
.

(* Notation call_data := (block * fundef * list val * mem)%type. *)

(* Definition SCallEvent *)
(*            (b: block) (fd:fundef) *)
(*            (vargs: list val) (m: mem) *)
(*   : callE call_data (mem * val) _ := *)
(*   Call (b, fd, vargs, m). *)


(* Notation ditrE := (callE call_data (mem * val) +' errE). *)
Notation ditrE := (scallE +' errE).

Section DECOMP.

  Notation itr_t :=
    (itree ditrE (env * temp_env * mem *
                  bool? (*break/continue*) * val?)).

  Variable ge: genv.

  Definition _sassign_c e le m a1 a2 :=
    match eval_lvalue_c ge e le m a1 with
    | Some (loc, ofs) =>
      match eval_expr_c ge e le m a2 with
      | Some v2 =>
        match Cop.sem_cast v2 (typeof a2) (typeof a1) m with
        | Some v =>
          assign_loc_c ge (typeof a1) m loc ofs v
        | None => None
        end
      | None => None
      end
    | None => None
    end.

  Definition _scall_c e le m a al
    : (block * fundef * list val)? :=
    match Cop.classify_fun (typeof a) with
    | Cop.fun_case_f tyargs tyres cconv =>
      match eval_expr_c ge e le m a with
      | Some vf =>
        match eval_exprlist_c ge e le m al tyargs with
        | Some vargs =>
          match Globalenvs.Genv.find_funct ge vf with
          | Some fd =>
            if type_eq (type_of_fundef fd)
                       (Tfunction tyargs tyres cconv)
            then
              match vf with
              | Vptr b ofs => Some (b, fd, vargs)
              | _ => None (* unreachable *)
              end
            else None
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | _ => None
    end.

  Definition _site_c
             (e: env) (le: temp_env) (m: mem) (a: expr)
    : bool? :=
    match eval_expr_c ge e le m a with
    | Some v1 =>
      Cop.bool_val v1 (typeof a) m
    | None => None
    end.


  Definition sloop_iter_body_one
             (itr: itr_t)
    : itree ditrE (env * temp_env * mem * (val? ?)) :=
    '(e', le', m', obc, v) <- itr;;
    match v with
    | Some retv =>
      (* return *)
      Ret (e', le', m', Some (Some retv))
    | None =>
      if (* is_break *)
        match obc with
        | None => false
        | Some bc => bc
        end
      then
        (* break, not return *)
        Ret (e', le', m', Some None)
      else
        (* continue *)
        Ret (e', le', m', None)
    end.

  Definition sloop_iter_body
             (itr1 itr2: env -> temp_env -> mem -> itr_t)
             (i: env * temp_env * mem)
    : itree ditrE
            (env * temp_env * mem +
             env * temp_env * mem * val?) :=
    let '(e, le, m) := i in
    (* '(e1, le1, m1, obc1, v1) <- itr1 e le m ;; *)
    '(e1, le1, m1, ov1) <- sloop_iter_body_one (itr1 e le m) ;;
    match ov1 with
    | Some v1 =>
      (* break or return *)
      Ret (inr (e1, le1, m1, v1))
    | None =>
      (* run loop2 *)
      '(e2, le2, m2, ov2) <- sloop_iter_body_one (itr2 e1 le1 m1);;
      match ov2 with
      | Some v2 =>
        Ret (inr (e2, le2, m2, v2))
      | None =>
        Ret (inl (e2, le2, m2))
      end
    end.

  Definition _sloop_itree
             (e: env) (le: temp_env) (m: mem)
             (itr1 itr2: env -> temp_env -> mem -> itr_t)
    : itr_t :=
    '(e', le', m', v) <-
    ITree.iter (sloop_iter_body itr1 itr2) (e, le, m) ;;
    Ret (e', le', m', None, v).

  Definition _sreturn_c
             (retty: type)
             (e: env) (le: temp_env) (m: mem)
             (oa: expr?)
    : (mem * val)? :=
    match Mem.free_list m (blocks_of_env ge e) with
    | Some m' =>
      match oa with
      | None => Some (m', Vundef)
      | Some a =>
        match eval_expr_c ge e le m a with
        | None => None
        | Some v =>
          match Cop.sem_cast v (typeof a) retty m with
          | Some v' => Some (m', v')
          | None => None
          end
        end
      end
    | None => None
    end.

  Fixpoint decomp_stmt
           (retty: type)
           (stmt: statement) (* (k: cont) *)
           (e: env) (le: temp_env) (m: mem)
    : itr_t :=
    match stmt with
    | Sskip =>
      Ret ((* k, *) e, le, m, None, None)
    | Sassign a1 a2 =>
      match _sassign_c e le m a1 a2 with
      | Some m' =>
        Ret (e, le, m', None, None)
      | None =>
        trigger ErrorEvent;;
        Ret (e, le, m, None, None)
      end
    | Sset id a =>
      match eval_expr_c ge e le m a with
      | Some v =>
        let le' := PTree.set id v le in
        Ret (e, le', m, None, None)
      | None =>
        trigger ErrorEvent;;
        Ret (e, le, m, None, None)
      end
    | Scall optid a al =>
      match _scall_c e le m a al with
      | Some (b, fd, vargs) =>
        '(m', v) <- trigger (SCallEvent b fd vargs m);;
        Ret (e, (set_opttemp optid v le), m', None, None)
      | None =>
        trigger ErrorEvent;;
        Ret (e, le, m, None, None)
      end
    | Sbuiltin _ _ _ _ =>
      trigger ErrorEvent;;
      Ret (e, le, m, None, None)
    | Ssequence s1 s2 =>
      '(e', le', m', bc, v) <- decomp_stmt retty s1 e le m ;;
      match v with
      | Some retval =>
        Ret (e', le', m', None, v)
      | None =>
        match bc with
        | None =>
          decomp_stmt retty s2 e' le' m'
        | Some _ =>
          Ret (e', le', m', bc, None)
        end
      end
    | Sifthenelse a s1 s2 =>
      match _site_c e le m a with
      | Some b =>
        if b then (decomp_stmt retty s1 e le m)
        else (decomp_stmt retty s2 e le m)
      | None =>
        trigger ErrorEvent;;
        Ret (e, le, m, None, None)
      end
    | Sloop s1 s2 =>
      let itr1 := decomp_stmt retty s1 in
      let itr2 := decomp_stmt retty s2 in
      _sloop_itree e le m itr1 itr2
    (* '(e, le, m, bc, v) <- itr ;; *)

    | Sbreak =>
      Ret (e, le, m, Some true, None)
    | Scontinue =>
      Ret (e, le, m, Some false, None)
    | Sreturn oa =>
      match _sreturn_c retty e le m oa with
      | Some (m', v) =>
        Ret (e, le, m', None, Some v)
      | None =>
        trigger ErrorEvent;;
        Ret (e, le, m, None, None)
      end
    | _ =>
      (* not supported *)
      trigger ErrorEvent;;
      Ret (e, le, m, None, None)
    end.

  Fixpoint decomp_func
           (f: Clight.function)
           (vargs: list val) (m: mem)
    : itree ditrE (mem * val) :=
    match function_entry_c ge f vargs m with
    | None =>
      trigger ErrorEvent ;; Ret (m, Vundef)
    | Some (e, le, m1) =>
      '(_, _, m2, _, ov) <- decomp_stmt (fn_return f) (fn_body f) e le m1 ;;
      let v := match ov with
               | None => Vundef
               | Some v => v
               end
      in
      Ret (m2, v)
    end.

End DECOMP.


Notation appE := ((* @abst_sendE bytes +'  *)obsE +' bsendE).

Notation call_data := (block * (* fundef * *) list val * mem)%type.


Section DECOMP_PROG.

  Context `{SystemEnv}.

  Variable cprog_app: Clight.program.
  Variable max_num_tasks: nat.
  (* Variable max_msg_size: Z. *)
  Variable msg_size_k: Z.
  Variable msg_size: Z.

  Let max_msg_size: Z := (msg_size_k * 8 + 7)%Z.
  Let ge: genv := Clight.globalenv cprog_app.

  Fixpoint decomp_fundefs
           (defs: list (ident * globdef Clight.fundef type))
    : list (block * ident * (list val -> mem -> itree ditrE (mem * val))) :=
    match defs with
    | [] => []
    | (id, gdef) :: defs' =>
      match gdef with
      | Gvar _ => decomp_fundefs defs'
      | Gfun fd =>
        match fd with
        | Internal f =>
          match Genv.find_symbol ge id with
          | Some b =>
            (b, id, decomp_func ge f) :: decomp_fundefs defs'
          | None => decomp_fundefs defs'
          end
        | _ => decomp_fundefs defs'
        end
      end
    end.

  Section MERGE.
    Variable itrs: list (block * ident *
                         (list val -> mem ->
                          itree ditrE (mem * val))).

    Definition _handle_ditrE
      : forall T (e: ditrE T), itree (callE call_data (mem * val) +' appE) T :=
      fun T e =>
        match e return itree _ T with
        | inl1 sce =>
          match sce with
          | SCallEvent b fd vargs m =>
            match Genv.find_funct_ptr ge b with
            | Some (Internal f) =>
              call (b, vargs, m)
              (* match Genv.invert_symbol ge b with *)
              (* | None => *)
              (*   Tau (trigger ErrorEvent);; *)
              (*   Ret (m, Vundef) *)
              (* | Some fid => *)
              (*   call (b, vargs, m) *)
              (* end *)
            | Some (External ef _ retty _) =>
              match ef with
              | EF_external fname _ =>
                if String.eqb fname "pals_send" then
                  match vargs with
                  | Vint tid_i :: Vptr blk ofs :: [] =>
                    let obs: bytes? :=
                        match Mem.loadbytes m blk (Ptrofs.unsigned ofs) msg_size with
                        | None => None
                        | Some mvs => proj_bytes mvs
                        end
                    in
                    let tid_z := Int.signed tid_i in
                    if (tid_z <? 0)%Z then
                      Ret (m, Vundef)
                    else
                      match obs with
                      | None =>
                        Tau (trigger ErrorEvent);;
                        Ret (m, Vundef)
                      | Some bs =>
                        trigger (AbstSendEvent (Z.to_nat tid_z) bs);;
                        Ret (m, Vundef)
                      end
                  | _ =>
                    Tau (trigger ErrorEvent);;
                    Ret (m, Vundef)
                  end
                else
                  if type_eq retty Tvoid then
                    trigger (ExtcallEvent_Void fname vargs) ;;
                    Ret (m, Vundef)
                  else
                    rint <- trigger (ExtcallEvent_Int fname vargs);;
                    Ret (m, Vint rint)
              | _ =>
                Tau (trigger ErrorEvent);;
                Ret (m, Vundef)
              end
            | None =>
              Tau (trigger ErrorEvent);;
              Ret (m, Vundef)
            end
          end
        | inr1 erre =>
          match erre with
          | ErrorEvent =>
            Tau (trigger ErrorEvent);;
            Ret tt
          end
        end.

    Definition interp_ditrE
               (itr_cur: itree ditrE (mem * val))
      : itree (callE call_data (mem * val) +' appE)
              (mem * val) :=
      interp (_handle_ditrE) itr_cur.

    Definition merge_itree
               (d: block * list val * mem)
      : itree appE (mem * val) :=
      rec (fun d: block * list val * mem =>
             let '(b, vargs, m) := d in
             match List.find
                     (fun itr => Pos.eqb (fst (fst itr)) b)
                     itrs with
             | Some (_, fid, itr) =>
               interp_ditrE (itr vargs m)
             | None =>
               Tau (trigger ErrorEvent);;
               Ret (m, Vundef)
             end)
          d.

    (* assume |bs| = msg_size if ent = Some bs *)
    Definition ent_to_memvals (ent: bytes?): list memval :=
      match ent with
      | None => repeat (Byte Byte.zero) (S (Z.to_nat msg_size))
      | Some bs => (Byte Byte.one) :: inj_bytes bs
      end.

    Fixpoint store_inbox
             (m: mem) (b: block)
             (n: nat) (inbox: list (bytes?))
      : mem? :=
      match inbox with
      | [] => Some m
      | ent :: inbox' =>
        let bs: list memval := ent_to_memvals ent in
        let ofs: Z := (Z.of_nat n * (1 + max_msg_size))%Z in
        match Mem.storebytes m b ofs bs with
        | None => None
        | Some m' =>
          store_inbox m' b (S n) inbox'
        end
      end.

    Definition job (b_inbox: block) (sytm: Z) (inbox: list (bytes?))
      : mem -> itree appE mem :=
      fun m0: mem =>
        match Genv.find_symbol ge main_prm._job with
        | Some b_job =>
          match store_inbox m0 b_inbox O inbox with
          | None => trigger ErrorEvent;; Ret m0
          | Some m1 =>
            '(m, _) <- merge_itree (b_job, [Vlong (Int64.repr sytm);
                                          Vptr b_inbox Ptrofs.zero], m1);;
            Ret m
          end
        | _ => trigger ErrorEvent;; Ret m0
        end.

  End MERGE.

  (* main_prm.inbox_sz msg_size_k max_num_tasks *)

  Definition gvar_mstore: globvar type :=
    let sz: Z := (main_prm.inbox_sz msg_size_k (Z.of_nat max_num_tasks)) in
    mkglobvar (Tstruct main_prm._inbox_t noattr)
              [Init_space sz] false false.

  Definition alloc_inbox (m: mem): (mem * block)? :=
    let v := gvar_mstore in
    let init := gvar_init v in
    let sz := init_data_list_size init in
    let (m1, b) := Mem.alloc m 0 sz in
    match store_zeros m1 b 0 sz with
    | Some m2 =>
      match Genv.store_init_data_list ge m2 b 0 init with
      | Some m3 =>
        option_map (fun m => (m, b))
                   (Mem.drop_perm m3 b 0 sz (Genv.perm_globvar v))
      | None => None
      end
    | None => None
    end.

  Definition decomp_cprog
    (* : (mem * (block * list val * mem -> *)
    (*           itree appE (mem * val)))? := *)
    : (mem * (Z -> list (bytes?) -> mem ->
              itree appE mem))? :=
    (* match Genv.init_mem cprog_tot with *)
    match Genv.init_mem cprog_app with
    | None => None
    | Some mem_init =>
      match alloc_inbox mem_init  with
      | Some (m, b_inb) =>
        let itrs := decomp_fundefs (prog_defs cprog_app) in
        (* Some (m, merge_itree itrs) *)
        Some (m, job itrs b_inb)
      | None => None
      end
    end.

  Definition cprog2app
    : option (@AppMod.t obsE bytes) :=
    match decomp_cprog with
    | None => None
    | Some (mem_init, job_itree) =>
      Some (AppMod.mk _ _ _ job_itree mem_init)
    end.

End DECOMP_PROG.
