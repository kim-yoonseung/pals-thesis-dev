From ITree Require Import ITree.
From compcert Require Import Maps AST Values Memory Globalenvs Ctypes.
From compcert Require Coqlib Clight Clightdefs.
From Paco Require Import paco.

Require Import sflib.
Require Import Axioms StdlibExt IntegersExt.

Require Import SysSem.
Require Import IPModel DiscreteTimeModel IntByteModel.
Require Import OSModel OSNodes.
Require Import ProgSem.
Require Import ProgSim.

(* Require Import SystemParams. *)
(* Require Import CEventSem. *)

Require Import Arith ZArith Bool.
Require Import String List Lia.

(* Import Params. *)
Import Clight Clightdefs.
Import ITreeNotations.

Set Nested Proofs Allowed.

Definition divide_c (n m: Z): bool :=
  let x := Z.div m n in
  (x * n =? m)%Z.

Lemma divide_comput (n m: Z)
  : divide_c n m = true <-> (n | m)%Z.
Proof.
  split.
  - unfold divide_c. intro COMP.
    exists (m/n)%Z.
    destruct (Z.eqb_spec (m / n * n) m); ss.
  - intro DIV. r in DIV. des.
    unfold divide_c. subst m.
    apply Z.eqb_eq.
    destruct (Z.eqb_spec n 0).
    2: { rewrite Z_div_mult_full by nia. ss. }
    subst.
    do 2 rewrite Z.mul_0_r. ss.
Qed.


Section EXPR_STRONG_IND.

  Fixpoint expr_measure (e: expr): nat :=
    match e with
    | Econst_int _ _ => 0
    | Econst_float _ _ => 0
    | Econst_single _ _ => 0
    | Econst_long _ _ => 0
    | Evar _ _ => 0
    | Etempvar _ _ => 0
    | Ederef e _ => S (expr_measure e)
    | Eaddrof e _ => S (expr_measure e)
    | Eunop _ e _ => S (expr_measure e)
    | Ebinop _ e1 e2 _ =>
      S (expr_measure e1 + expr_measure e2)
    | Ecast e _ => S (expr_measure e)
    | Efield e _ _ => S (expr_measure e)
    | Esizeof _ _ => 0
    | Ealignof _ _ => 0
    end.

  Variable P: expr -> Prop.
  Hypothesis IND_CASE: forall e (IH: forall e', expr_measure e' < expr_measure e -> P e'), P e.

  Lemma expr_str_ind
    : forall e, P e.
  Proof.
    intro e.
    remember (expr_measure e) as m eqn: M'.
    assert (M: expr_measure e <= m) by nia.
    clear M'.
    depgen e.

    induction m as [| m' IH].
    { i. eapply IND_CASE. i. nia. }

    i. eapply IND_CASE.
    i. eapply IH. nia.
  Qed.

End EXPR_STRONG_IND.


(** ** Deterministic behavior of Clight *)

Definition deref_loc_c (ty: type) (m:mem)
           (b:block) (ofs: ptrofs): val? :=
  match access_mode ty with
  | By_value chunk =>
    Mem.loadv chunk m (Vptr b ofs)
  | By_reference => Some (Vptr b ofs)
  | By_copy => Some (Vptr b ofs)
  | By_nothing => None
  end.

Lemma deref_loc_comput
      ty m' b ofs v
  : Clight.deref_loc ty m' b ofs v <->
    deref_loc_c ty m' b ofs = Some v.
Proof.
  split.
  - intro PROP.
    unfold deref_loc_c.
    inv PROP; desf.
  - intro COMP.
    unfold deref_loc_c in COMP.
    desf.
    + econs 1; eauto.
    + econs 2; eauto.
    + econs 3; eauto.
Qed.

Definition assign_loc_c (ce: composite_env)
           (ty: type) (m: mem) (b: block) (ofs: ptrofs)
           (v: val): mem? :=
  match access_mode ty with
  | By_value chunk =>
    Mem.storev chunk m (Vptr b ofs) v
  | By_copy =>
    match v with
    | Vptr b' ofs' =>
      let chk1 :=
          if (0 <? sizeof ce ty) then
            andb (divide_c
                    (alignof_blockcopy ce ty)
                    (Ptrofs.unsigned ofs'))
                 (divide_c
                    (alignof_blockcopy ce ty)
                    (Ptrofs.unsigned ofs))
          else true in
      if negb chk1 then None else
        let chk2 :=
            (orb (negb (b' =? b))%positive
                 (orb (Ptrofs.unsigned ofs' =? Ptrofs.unsigned ofs)
                      (orb (Ptrofs.unsigned ofs' + sizeof ce ty <=? Ptrofs.unsigned ofs)
                           (Ptrofs.unsigned ofs + sizeof ce ty <=? Ptrofs.unsigned ofs'))))%Z
        in
        if negb chk2 then None else
          match Mem.loadbytes
                  m b' (Ptrofs.unsigned ofs')
                  (sizeof ce ty) with
          | None => None
          | Some bytes =>
            Mem.storebytes m b (Ptrofs.unsigned ofs) bytes
          end
    | _ => None
    end
  | By_reference => None
  | By_nothing => None
  end%Z.

Lemma assign_loc_comput
      ce ty m b ofs v m'
  : Clight.assign_loc ce ty m b ofs v m' <->
    assign_loc_c ce ty m b ofs v = Some m'.
Proof.
  split; intro AUX.
  - inv AUX.
    + unfold assign_loc_c. desf.
    + renames H H0 H1 into ACC_MODE DIV1 DIV2.
      renames H2 H3 H4 into PTR LBS SBS.

      unfold assign_loc_c.
      replace (access_mode ty) with By_copy.
      match goal with
      | |- (if negb ?e then _ else _) = _ =>
        replace e with true
      end.
      2: {
        clear - DIV1 DIV2.
        desf.
        symmetry. apply andb_true_iff.
        destruct (Z.ltb_spec 0 (sizeof ce ty)); ss.
        split.
        - apply divide_comput.
          apply DIV1. nia.
        - apply divide_comput.
          apply DIV2. nia.
      }
      ss.
      clear DIV1 DIV2.
      match goal with
      | |- (if negb ?e then _ else _) = _ =>
        replace e with true
      end.
      2: {
        symmetry.
        do 3 rewrite orb_true_iff.
        clear - PTR. des.
        - left. destruct (Pos.eqb_spec b' b); ss.
        - right. left.
          rewrite PTR. apply Z.eqb_refl.
        - right. right. left.
          apply Zle_imp_le_bool. auto.
        - do 3 right.
          apply Zle_imp_le_bool. auto.
      }
      ss.
      desf.

  - unfold assign_loc_c in AUX.
    destruct (access_mode ty) eqn: ACC_MODE; ss.
    + econs 1; eauto.
    + destruct v as [ | | | | | b' ofs']; ss.
      match type of AUX with
      | (if negb ?e then None else _) = _ =>
        assert (CHK1: e = true); [by destruct e; ss|]
      end.
      rewrite CHK1 in AUX. ss.

      match type of AUX with
      | (if negb ?e then None else _) = _ =>
        assert (CHK2: e = true); [by destruct e; ss|]
      end.
      rewrite CHK2 in AUX. ss.

      match type of AUX with
      | match ?e with _ => _ end = _ =>
        destruct e eqn: LBS
      end; ss.

      econs 2; eauto.
      * clear AUX.
        destruct (Z.ltb_spec 0 (sizeof ce ty)); ss.
        apply Bool.andb_true_iff in CHK1. des.
        intro SIZE_POS.
        apply divide_comput. eauto.
      * clear AUX.
        destruct (Z.ltb_spec 0 (sizeof ce ty)); ss.
        apply Bool.andb_true_iff in CHK1. des.
        intro SIZE_POS.
        apply divide_comput. eauto.
      * clear CHK1 AUX.
        rewrite orb_true_iff in CHK2. des.
        { left. destruct (Pos.eqb_spec b' b); ss. }
        right. rewrite orb_true_iff in CHK2. des.
        { left.
          destruct (Z.eqb_spec (Ptrofs.unsigned ofs')
                               (Ptrofs.unsigned ofs)); ss. }
        right. rewrite orb_true_iff in CHK2. des.
        { left.
          destruct (Z.leb_spec (Ptrofs.unsigned ofs' + sizeof ce ty) (Ptrofs.unsigned ofs)); ss.
        }
        { right.
          destruct (Z.leb_spec (Ptrofs.unsigned ofs + sizeof ce ty) (Ptrofs.unsigned ofs')); ss.
        }
Qed.


Section EVAL_EXPR_COMP.

  Variable ge: Clight.genv.
  Variable e: Clight.env.
  Variable le: Clight.temp_env.
  Variable m: mem.

  Section EVAL_LVALUE.
    Variable _eval_expr_c: expr -> val?.

    Fixpoint _eval_lvalue_c (a: expr)
      : (block * ptrofs)? :=
      match a with
      | Evar id ty =>
        match e ! id with
        | Some (l, ty') =>
          if type_eq ty ty' then Some (l, Ptrofs.zero)
          else None
        | None =>
          match Genv.find_symbol
                  (Clight.genv_genv ge) id with
          | Some l => Some (l, Ptrofs.zero)
          | None => None
          end
        end
      | Ederef a ty =>
        match _eval_expr_c a with
        | Some (Vptr l ofs) => Some (l, ofs)
        | _ => None
        end
      | Efield a i ty =>
        match _eval_expr_c a with
        | Some (Vptr l ofs) =>
          match Clight.typeof a with
          | Tstruct id att =>
            match (Clight.genv_cenv ge) ! id with
            | Some co =>
              match field_offset (Clight.genv_cenv ge)
                                 i (co_members co) with
              | Errors.OK delta =>
                Some (l, (Ptrofs.add ofs (Ptrofs.repr delta)))
              | _ => None
              end
            | _ => None
            end
          | Tunion id att =>
            match (Clight.genv_cenv ge) ! id with
            | Some _ => Some (l, ofs)
            | None => None
            end
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end.

  End EVAL_LVALUE.

  Fixpoint eval_expr_c (expr: Clight.expr): val? :=
    match expr with
    | Econst_int i ty => Some (Vint i)
    | Econst_float f ty => Some (Vfloat f)
    | Econst_single f ty => Some (Vsingle f)
    | Econst_long i ty => Some (Vlong i)
    | Etempvar id ty => (le ! id)
    | Eaddrof a ty =>
      match _eval_lvalue_c eval_expr_c a with
      | None => None (*??*)
      | Some (loc, ofs) => Some (Vptr loc ofs)
      end
    | Eunop op a ty =>
      match eval_expr_c a with
      | None => None
      | Some v1 =>
        Cop.sem_unary_operation
          op v1 (Clight.typeof a) m
      end
    | Ebinop op a1 a2 ty =>
      match eval_expr_c a1, eval_expr_c a2 with
      | Some v1, Some v2 =>
        Cop.sem_binary_operation
          (Clight.genv_cenv ge) op
          v1 (Clight.typeof a1)
          v2 (Clight.typeof a2) m
      | _, _ => None
      end
    | Ecast a ty =>
      match eval_expr_c a with
      | None => None
      | Some v1 =>
        Cop.sem_cast v1 (Clight.typeof a) ty m
      end
    | Esizeof ty1 ty =>
      Some (Vptrofs (Ptrofs.repr (sizeof (Clight.genv_cenv ge) ty1)))
    | Ealignof ty1 ty =>
      Some (Vptrofs (Ptrofs.repr (alignof (Clight.genv_cenv ge) ty1)))
    | a =>
      match _eval_lvalue_c eval_expr_c a with
      | None => None
      | Some (loc, ofs) =>
        deref_loc_c (Clight.typeof a) m loc ofs
      end
    end.

  Definition eval_lvalue_c
    : expr -> (block * ptrofs)? :=
    _eval_lvalue_c eval_expr_c.

  Ltac inv_eval_lvalue :=
    match goal with
    | H: eval_lvalue _ _ _ _ _ _ _ |- _ => inv H
    end.

  Lemma _eval_lvalue_comput
        _eval_expr_c a b ofs
        (EVAL_EXPR: forall a' v,
            expr_measure a' < expr_measure a ->
            eval_expr ge e le m a' v <->
            _eval_expr_c a' = Some v)
    : eval_lvalue ge e le m a b ofs <->
      _eval_lvalue_c _eval_expr_c a = Some (b, ofs).
  Proof.
    destruct a; ss;
      try by split; i; ss; inv_eval_lvalue.
    - split; intro AUX; ss.
      + inv AUX; desf.
      + desf.
        * eapply eval_Evar_local; ss.
        * eapply eval_Evar_global; ss.
    - split; intro AUX; ss.
      + inv AUX.
        rewrite EVAL_EXPR in * by nia.
        desf.
      + desf. econs.
        eapply EVAL_EXPR; eauto.
    - split; intro AUX; ss.
      + inv AUX.
        * hexploit (EVAL_EXPR a); ss.
          intros [AUX1 _].
          hexploit AUX1; eauto.
          intro R. rewrite R.
          desf.
        * hexploit (EVAL_EXPR a); ss.
          intros [AUX1 _].
          hexploit AUX1; eauto.
          intro R. rewrite R.
          desf.
      + desf.
        * eapply eval_Efield_struct; eauto.
          apply EVAL_EXPR; eauto.
        * eapply eval_Efield_union; eauto.
          apply EVAL_EXPR; eauto.
  Qed.

  Lemma eval_expr_comput a v
    : eval_expr ge e le m a v <->
      eval_expr_c a = Some v.
  Proof.
    depgen v.
    pattern a. revert a.
    apply expr_str_ind.

    intros a IH.
    destruct a; i;
      try by split; intro AUX; ss; clarify;
        [inv AUX; ss; inv_eval_lvalue | econs].
    (* 7 *)
    - split; intro AUX; ss.
      + inv AUX; ss.
        inv_eval_lvalue.
        * desf. apply deref_loc_comput; auto.
        * desf. apply deref_loc_comput; auto.
      + desf.
        * eapply eval_Elvalue.
          -- apply eval_Evar_local; eauto.
          -- apply deref_loc_comput; eauto.
        * eapply eval_Elvalue.
          -- apply eval_Evar_global; eauto.
          -- apply deref_loc_comput; eauto.
    - split; intro AUX; ss.
      + inv AUX; ss.
        inv_eval_lvalue.
        rewrite IH in * by nia.
        desf. eapply deref_loc_comput; auto.
      + desf.
        eapply eval_Elvalue.
        * eapply _eval_lvalue_comput with
              (_eval_expr_c := eval_expr_c).
          { i. rewrite <- IH; ss. }
          ss. desf.
        * eapply deref_loc_comput; auto.
    - split; intro AUX; ss.
      + inv AUX.
        * hexploit (_eval_lvalue_comput eval_expr_c a).
          { i. rewrite <- IH by nia. ss. }
          intros [R _]. rewrite R; eauto.
        * inv_eval_lvalue.
      + desf. econs.
        destruct a; ss.
        * desf.
          -- eapply eval_Evar_local; ss.
          -- eapply eval_Evar_global; ss.
        * desf.
          rewrite <- IH in * by nia.
          econs. eauto.
        * desf.
          -- eapply eval_Efield_struct; eauto.
             eapply IH; eauto.
          -- eapply eval_Efield_union; eauto.
             eapply IH; eauto.
    - split; intro AUX; ss.
      + inv AUX.
        * hexploit IH; eauto.
          intros [R _]. rewrite R; eauto.
        * inv_eval_lvalue.
      + desf. econs; eauto.
        eapply IH; eauto.
    - split; intro AUX; ss.
      + inv AUX.
        2: { inv_eval_lvalue. }

        hexploit (IH a1); eauto.
        { nia. }
        intros [R1 _]. rewrite R1; eauto.
        hexploit (IH a2); eauto.
        { nia. }
        intros [R2 _]. rewrite R2; eauto.
      + desf. econs; eauto.
        * eapply IH; eauto. nia.
        * eapply IH; eauto. nia.

    - split; intro AUX; ss.
      + inv AUX.
        * hexploit IH; eauto.
          intros [R _]. rewrite R; eauto.
        * inv_eval_lvalue.
      + desf. econs; eauto.
        eapply IH; eauto.
    - split; intro AUX; ss.
      + inv AUX.
        inv_eval_lvalue.
        * hexploit IH; eauto.
          intros [R _]. rewrite R; eauto.
          desf.
          apply deref_loc_comput. auto.
        * hexploit IH; eauto.
          intros [R _]. rewrite R; eauto.
          desf.
          apply deref_loc_comput. auto.
      + desf.
        * eapply eval_Elvalue.
          2: { apply deref_loc_comput; eauto. }
          eapply eval_Efield_struct; eauto.
          eapply IH; eauto.
        * eapply eval_Elvalue.
          2: { apply deref_loc_comput; eauto. }
          eapply eval_Efield_union; eauto.
          eapply IH; eauto.
  Qed.

  Lemma eval_lvalue_comput
    : forall a blk ofs,
      eval_lvalue ge e le m a blk ofs <->
      eval_lvalue_c a = Some (blk, ofs).
  Proof.
    i. apply _eval_lvalue_comput.
    i. apply eval_expr_comput.
  Qed.

  Fixpoint eval_exprlist_c
           (es: list expr) (ts: typelist)
    : (list val)? :=
    match es, ts with
    | [], Tnil => Some []
    | e::es', Tcons ty ts' =>
      match eval_expr_c e, eval_exprlist_c es' ts' with
      | Some v1, Some vs =>
        match Cop.sem_cast v1 (typeof e) ty m with
        | Some v2 => Some (v2::vs)
        | None => None
        end
      | _, _ => None
      end
    | _, _ => None
    end.

  Lemma eval_exprlist_comput
        es ts vs
    : eval_exprlist ge e le m es ts vs <->
      eval_exprlist_c es ts = Some vs.
  Proof.
    revert ts vs.
    induction es as [| a es' IH]; i; ss.
    { split; intro AUX; ss.
      - inv AUX. ss.
      - desf. econs.
    }
    split; intro AUX.
    - inv AUX.
      rewrite eval_expr_comput in *.
      rewrite IH in *.
      desf.
    - desf.
      econs; eauto.
      + apply eval_expr_comput. eauto.
      + apply IH. ss.
  Qed.

End EVAL_EXPR_COMP.

Section CLIGHT_STEP_DET.
  Variable ge: genv.

  Lemma alloc_variables_det
        e0 m fvars e1 m1 e2 m2
        (ALLOC1: alloc_variables
                   ge e0 m fvars e1 m1)
        (ALLOC2: alloc_variables
                   ge e0 m fvars e2 m2)
    : e1 = e2 /\ m1 = m2.
  Proof.
    depgen e2.
    induction ALLOC1; i; ss.
    { inv ALLOC2. ss. }

    inv ALLOC2. ss.
    match goal with
    | H1: Mem.alloc _ _ _ = _,
          H2: Mem.alloc _ _ _ = _ |- _ =>
      rewrite H2 in H1; clarify
    end.

    hexploit IHALLOC1; eauto.
  Qed.

  Lemma function_entry2_det
        f vargs m
        e1 le1 m1 e2 le2 m2
        (ENTRY1: function_entry2 ge f vargs m e1 le1 m1)
        (ENTRY2: function_entry2 ge f vargs m e2 le2 m2)
    : e1 = e2 /\ le1 = le2 /\ m1 = m2.
  Proof.
    inv ENTRY1. inv ENTRY2.
    match goal with
    | A1: alloc_variables _ _ _ _ _ _,
          A2: alloc_variables _ _ _ _ _ _ |- _ =>
      eapply alloc_variables_det in A1; try apply A2
    end.
    des. clarify.
  Qed.

  Lemma clight_silent_step_det
        st st1 st2
        (STEP1: Clight.step2 ge st [] st1)
        (STEP2: Clight.step2 ge st [] st2)
    : st1 = st2.
  Proof.
    inv STEP1; inv STEP2; ss; try by des; ss.
    (* 12 goals *)
    - f_equal.
      rewrite eval_lvalue_comput in *. clarify.
      rewrite eval_expr_comput in *. clarify.
      rewrite assign_loc_comput in *. clarify.
    - do 2 f_equal.
      rewrite eval_expr_comput in *. clarify.
    - rewrite eval_expr_comput in *. clarify.
      match goal with
      | H1: Cop.classify_fun _ = _,
            H2: Cop.classify_fun _ = _ |- _ =>
        rewrite H2 in H1; inv H1
      end.
      rewrite eval_exprlist_comput in *. clarify.
    - rewrite eval_exprlist_comput in *. clarify.

      assert (vres = vres0 /\ m' = m'0).
      { eapply Events.external_call_deterministic; eauto. }
      des. subst. ss.
    - rewrite eval_expr_comput in *. clarify.
    - clarify.
    - rewrite eval_expr_comput in *. clarify.
    - clarify.
    - rewrite eval_expr_comput in *. clarify.
    - clarify.
    - match goal with
      | H1: function_entry2 _ _ _ _ _ _ _,
            H2: function_entry2 _ _ _ _ _ _ _ |- _ =>
        eapply function_entry2_det in H1; try apply H2
      end.
      des. clarify.
    - assert (vres = vres0 /\ m' = m'0).
      { eapply Events.external_call_deterministic; eauto. }
      des. subst. ss.
  Qed.

End CLIGHT_STEP_DET.



(* Arguments PTree.get : simpl nomatch. *)
(* Arguments PTree.set: simpl nomatch. *)
(* Arguments Nat.sub: simpl nomatch. *)


(** ** lenv_equiv. *)

(* Definition lenv_equiv (le: PTree.t val) *)
(*            (l: list (ident * val)) : Prop := *)
(*   forall i, le ! i = find_ilist i l. *)

Definition ptree_equiv {A} (tr: PTree.t A)
           (l: list (ident * A)): Prop :=
  forall i, tr ! i = find_ilist i l.

Notation lenv_equiv := (@ptree_equiv val).
Notation env_equiv := (@ptree_equiv (block * type)).

(* Record lenv_state (le: PTree.t val) *)
(*        (l: list (ident * val)) : Prop := *)
(*   LenvState *)
(*     { lenv_equiv: forall i, le ! i = find_ilist i l ; }. *)

Lemma update_lenv_equiv
      i v
      (le le': PTree.t val) l l'
      (LENV: lenv_equiv le l)
      (UPD: le' = PTree.set i v le)
      (UPD_L: l' = update_ilist i v l)
  : lenv_equiv le' l'.
Proof.
  subst. rr.
  intros i'.
  rewrite update_ilist_find. ss.
  rewrite PTree.gsspec.
  erewrite <- LENV; eauto.
  destruct (Pos.eqb_spec i i').
  - subst i'.
    rewrite Coqlib.peq_true. ss.
  - rewrite Coqlib.peq_false; eauto.
Qed.


Lemma lenv_finit_temps
      (temps: list (ident * type)) le1
      (TEMP_NOREPET: Coqlib.list_norepet
                       (Clight.var_names temps))
      (LE: Clight.create_undef_temps temps = le1)
  : lenv_equiv le1 (List.map (fun x => (x, Vundef))
                             (Clight.var_names temps)).
Proof.
  depgen le1.
  induction temps as [| [id ty] temps' IH]; i; ss.
  { rr. subst.
    i. rewrite PTree.gempty. ss. }

  inv TEMP_NOREPET.
  hexploit IH; eauto.
  intro IH'. clear IH.
  eapply (update_lenv_equiv id Vundef) in IH';
    try reflexivity.

  erewrite update_ilist_new_id in IH'; ss.
  eapply find_ilist_None.
  apply Forall_forall.
  intros [id' v'] IN ID_EQ.
  ss. subst.
  eapply Coqlib.list_in_map_inv in IN.
  des. clarify.
Qed.

Lemma lenv_finit_params
      params args
      le lst le'
      (NOREPET: Coqlib.list_norepet
                  (Clight.var_names params))
      (LENV_EQUIV: lenv_equiv le lst)
      (DISJ: Coqlib.list_disjoint
               (Clight.var_names params)
               (map fst lst))
      (LE: Clight.bind_parameter_temps
             params args le = Some le')
  : lenv_equiv le' (rev (combine (Clight.var_names params) args) ++ lst).
Proof.
  depgen le. revert args lst DISJ.
  induction params as [| [id_h ?] tp IH]; i; ss.
  { destruct args; ss.
    clarify. }

  inv NOREPET.
  destruct args as [| ha ta]; ss.
  rewrite <- app_assoc. ss.
  cut (lenv_equiv (PTree.set id_h ha le)
                  ((id_h, ha):: lst)).
  { intro LE'. eapply IH in LE'; eauto.
    ii. subst. eapply DISJ; eauto.
    - right. eauto.
    - ss. des; ss.
      subst. congruence.
  }

  clear LE IH.
  cut ((id_h, ha)::lst = update_ilist id_h ha lst).
  { intro RW. rewrite RW.
    eapply update_lenv_equiv; eauto. }

  rewrite update_ilist_new_id; ss.
  apply find_ilist_None.
  apply Forall_forall.
  intros [id' x'] IN. ss.
  hexploit (DISJ id_h id'); ss; eauto.
  apply in_map with (f:=fst) in IN. ss.
Qed.

Lemma lenv_finit
      (params temps: list (ident * type))
      (args: list val)
      le
      (TEMPS_NOREPET: Coqlib.list_norepet
                        (Clight.var_names temps))
      (PARAMS_NOREPET: Coqlib.list_norepet
                         (Clight.var_names params))
      (DISJ: Coqlib.list_disjoint
               (Clight.var_names params)
               (Clight.var_names temps))

      (LE: Clight.bind_parameter_temps
             params args
             (Clight.create_undef_temps temps) =
           Some le)
  : lenv_equiv
      le (rev (combine (Clight.var_names params) args) ++
              (List.map (fun x => (x, Vundef))
                        (Clight.var_names temps))).
Proof.
  eapply lenv_finit_params; eauto.
  2: {
    rewrite map_map. ss.
    rewrite map_id. ss.
  }
  eapply lenv_finit_temps; eauto.
Qed.


Lemma alloc_variables_mem_unch
      ge m vars e m'
      (ALLOC: alloc_variables
                (* (Clight.globalenv cprog) *)
                ge
                empty_env m vars e m')
  : Mem.unchanged_on (fun _ _ => True) m m'.
Proof.
  induction ALLOC; ss.
  { apply Mem.unchanged_on_refl. }
  eapply Mem.unchanged_on_trans; eauto.
  eapply Mem.alloc_unchanged_on; eauto.
Qed.

Lemma clight_function_entry
      ge f args k m
      e m'
      (NREP_VARS: Coqlib.list_norepet
                    (var_names (fn_vars f)))
      (NREP_PARAMS: Coqlib.list_norepet
                      (var_names (fn_params f)))
      (NREP_TEMPS: Coqlib.list_norepet
                      (var_names (fn_temps f)))
      (DISJ_PT: Coqlib.list_disjoint
                  (var_names (fn_params f))
                  (var_names (fn_temps f)))
      (ENV: alloc_variables
              (* (Clight.globalenv cprog) *)
              ge
              empty_env m (fn_vars f) e m')
      (LENV: Clight.bind_parameter_temps
               (fn_params f) args
               (create_undef_temps (fn_temps f)) <> None)
  : exists le,
    <<STEP_ENTRY:
      Clight.step2
        (* (Clight.globalenv cprog) *)
        ge
        (Callstate (Internal f) args k m) []
        (State f (fn_body f) k e le m')>> /\
    (* <<UNCH: Mem.unchanged_on (fun _ _ => True) m m'>> /\ *)
    <<LENV_EQUIV:
      lenv_equiv le
        (rev (combine (var_names (fn_params f)) args)
             ++ (List.map (fun x => (x, Vundef))
                          (var_names (fn_temps f))))>>.
Proof.
  eapply Some_not_None in LENV.
  destruct LENV as [le LENV].
  exists le. esplits.
  - econs; ss.
  (* - eapply alloc_variables_mem_unch; eauto. *)
  - eapply lenv_finit; eauto.
Qed.


Section CPROG_SIM_LEMMAS.
  Context `{sysE: Type -> Type}.
  Context `{errE -< sysE}.
  (* Context `{event_conds sysE}. *)
  Let progE : Type -> Type := osE +' sysE.

  (* Instance progE_conds: event_conds progE. *)
  (* Proof. *)
  (*   unfold progE. *)
  (*   typeclasses eauto. *)
  (* Defined. *)

  Context `{@cprog_event progE}.

  Variable cprog: Clight.program.
  Let prog: @Prog.t progE := prog_of_clight cprog.

  Hypothesis wf_prog: Prog.wf prog.

  Let ge := globalenv cprog.
  Let itree_t: Type := itree progE unit.
  Let state: Type := Prog.state prog.

  (* Variable r: nat -> itree progE unit -> Clight.state -> Prop. *)
  Notation sim := (paco3 (_sim_itree prog)).

  Lemma sim_itree_clight_silent
        (r: nat -> itree _ _ -> Clight.state -> Prop)
        idx itr pst pst'
        (IDX_POS: 0 < idx)
        (SILENT_STEP1: Prog.step _ pst pst')
        (SIM: upaco3 (_sim_itree prog) r
                     (idx - 1) itr pst')
    : sim r idx itr pst.
  Proof.
    des.
    pfold. econs 2.
    { esplits; eauto. }
    inv SILENT_STEP1.
    rename STEP into STEP1.
    i. ss.
    inv PROG_SILENT_STEP.
    rename STEP into STEP2.
    hexploit clight_silent_step_det.
    { apply STEP2. }
    { apply STEP1. }
    i. subst.
    exists (idx - 1).
    esplits.
    { left. splits.
      - econs 1.
      - nia.
    }
    eauto.
  Qed.

  Lemma sim_itree_clight_silent_tau
        (r: nat -> itree _ _ -> Clight.state -> Prop)
        idx idx_n itr itr' pst pst'
        (SILENT_STEP1: Prog.step _ pst pst')
        (OBS_TAU: observe itr = TauF itr')
        (SIM: upaco3 (_sim_itree prog) r
                     idx_n itr' pst')
    : sim r idx itr pst.
  Proof.
    des.
    pfold. econs 2.
    { esplits; eauto. }
    inv SILENT_STEP1.
    rename STEP into STEP1.
    i. ss.
    inv PROG_SILENT_STEP.
    rename STEP into STEP2.
    hexploit clight_silent_step_det.
    { apply STEP2. }
    { apply STEP1. }
    i. subst.
    exists idx_n.
    esplits.
    { right. r.
      esplits; eauto.
      econs 1.
    }
    eauto.
  Qed.


  (** *** loop *)

  Definition for_loop_stmt
             (id_i: ident) (stmt_body: statement)
    (* (i_max: nat) *)
             (e_max: expr)
    : statement :=
    Sloop
      (Ssequence
         (Sifthenelse
            (Ebinop Cop.Olt (Etempvar id_i tint)
                    (* (Econst_int (Int.repr (Z.of_nat i_max)) tint) *)
                    e_max tint)
            Sskip Sbreak)
         stmt_body)
      (Sset id_i (Ebinop Cop.Oadd (Etempvar id_i tint) (Econst_int (Int.repr 1) tint) tint))
  .

  Lemma simple_for_loop_gen
        (r: nat -> itree _ _ -> Clight.state -> Prop)
        (f: Clight.function)
        (id_i: ident)
        (i_min i_max: nat) (e_max: expr)
        (idx0 idx idx_each: nat)
        (stmt_body: statement) k env
        itr le m
        (loop_inv: nat -> itree progE unit ->
                   PTree.t val -> mem -> Prop)
        (LINV_BEGIN: loop_inv i_min itr le m)
        (* (I_VAL_ZERO: le ! id_i = Some (Vint Int.zero)) *)
        (RANGE_I_MIN: i_min <= i_max)
        (RANGE_I_MAX: IntRange.sint i_max)
        (IDX_BIG: (idx0 + (i_max - i_min) * idx_each < idx)%nat)
        (* (E_MAX_CONST: *)
        (*    forall m, eval_expr_c ge env le m e_max = *)
        (*         Some (Vint (IntNat.of_nat i_max))) *)
        (LOOP_BODY_PROOF:
           forall (i: nat)
             idx1 itr1 le1 m1
             (IDX_BIG: idx0 + idx_each < idx1)
             (RANGE_I: (i_min <= i < i_max)%nat)
             (* (I_VAL: le1 ! id_i = Some (Vint (IntNat.of_nat i))) *)
             (LINV: loop_inv i itr1 le1 m1)
             (SIM_NEXT:
                forall itr2 le2 m2
                  (* (I_VAL': le2 ! id_i = Some (Vint (IntNat.of_nat (S i)))) *)
                  (LINV': loop_inv (S i) itr2 le2 m2),
                  sim r (idx1 - idx_each) itr2
                      (State f (for_loop_stmt
                                  id_i stmt_body e_max)
                             k env le2 m2)),
             sim r idx1 itr1
                 (State f (for_loop_stmt
                             id_i stmt_body e_max)
                        k env le1 m1))
        (LOOP_END_PROOF:
           forall itr_e le_e m_e
             (* (I_VAL: le_e ! id_i = Some (Vint (IntNat.of_nat i_max))) *)
             (LINV_END: loop_inv i_max itr_e le_e m_e),
             sim r (idx - (i_max - i_min) * idx_each) itr_e
                 (State f (for_loop_stmt
                             id_i stmt_body e_max)
                        k env le_e m_e))
    : sim r idx itr
          (State f (for_loop_stmt
                      id_i stmt_body e_max)
                 k env le m)
  .
  Proof.
    pose (stmt_lp := for_loop_stmt id_i stmt_body e_max).
    fold stmt_lp.
    fold stmt_lp in LOOP_BODY_PROOF.
    fold stmt_lp in LOOP_END_PROOF.

    assert (MID_AUX:
              forall i_m
                (RANGE_I_M: 0 <= i_m <= i_max - i_min)
                (AFTER: forall itr_m le_m m_m
                          (* (I_VAL: le_m ! id_i = *)
                          (*         Some (Vint (IntNat.of_nat i_m))) *)
                          (LINV: loop_inv (i_min + i_m) itr_m le_m m_m),
                    sim r (idx - i_m * idx_each) itr_m
                        (State f stmt_lp k env le_m m_m)),
                sim r idx itr
                    (State f stmt_lp k env le m)).
    { clear LOOP_END_PROOF.
      intro i_m.
      induction i_m as [| i_m' IH]; i; ss.
      { rewrite Nat.sub_0_r in AFTER.
        rewrite Nat.add_0_r in AFTER.
        eapply AFTER; ss. }

      eapply IH; ss.
      { nia. }
      i.

      eapply (LOOP_BODY_PROOF (i_min + i_m')); eauto.
      { nia. }
      { nia. }

      i.
      replace (idx - i_m' * idx_each - idx_each)
        with (idx - (idx_each + i_m' * idx_each)) by nia.
      eapply AFTER; eauto.
      rewrite plus_n_Sm in LINV'. ss.
    }

    apply MID_AUX with (i_m := i_max - i_min).
    - nia.
    - rewrite le_plus_minus_r by nia.
      eauto.
  Qed.

  Lemma simple_for_loop
        (r: nat -> itree _ _ -> Clight.state -> Prop)
        (f: Clight.function)
        (id_i: ident)
        (i_max: nat) (e_max: expr)
        (idx0 idx idx_each: nat)
        (stmt_body: statement) k env
        itr le m
        (loop_inv: nat -> itree progE unit ->
                   PTree.t val -> mem -> Prop)
        (LINV_BEGIN: loop_inv 0 itr le m)
        (* (I_VAL_ZERO: le ! id_i = Some (Vint Int.zero)) *)
        (RANGE_I_MAX: IntRange.sint i_max)
        (IDX_BIG: (idx0 + i_max * idx_each < idx)%nat)
        (* (E_MAX_CONST: *)
        (*    forall m, eval_expr_c ge env le m e_max = *)
        (*         Some (Vint (IntNat.of_nat i_max))) *)
        (LOOP_BODY_PROOF:
           forall (i: nat)
             idx1 itr1 le1 m1
             (IDX_BIG: idx0 + idx_each < idx1)
             (RANGE_I: (i < i_max)%nat)
             (* (I_VAL: le1 ! id_i = Some (Vint (IntNat.of_nat i))) *)
             (LINV: loop_inv i itr1 le1 m1)
             (SIM_NEXT:
                forall itr2 le2 m2
                  (* (I_VAL': le2 ! id_i = Some (Vint (IntNat.of_nat (S i)))) *)
                  (LINV': loop_inv (S i) itr2 le2 m2),
                  sim r (idx1 - idx_each) itr2
                      (State f (for_loop_stmt
                                  id_i stmt_body e_max)
                             k env le2 m2)),
             sim r idx1 itr1
                 (State f (for_loop_stmt
                             id_i stmt_body e_max)
                        k env le1 m1))
        (LOOP_END_PROOF:
           forall itr_e le_e m_e
             (* (I_VAL: le_e ! id_i = Some (Vint (IntNat.of_nat i_max))) *)
             (LINV_END: loop_inv i_max itr_e le_e m_e),
             sim r (idx - i_max * idx_each) itr_e
                 (State f (for_loop_stmt
                             id_i stmt_body e_max)
                        k env le_e m_e))
    : sim r idx itr
          (State f (for_loop_stmt
                      id_i stmt_body e_max)
                 k env le m)
  .
  Proof.
    eapply simple_for_loop_gen with
        (i_min := 0) (i_max := i_max); eauto.
    - nia.
    - rewrite Nat.sub_0_r. apply IDX_BIG.
    - i. eapply LOOP_BODY_PROOF; eauto.
      nia.
    - i. rewrite Nat.sub_0_r.
      apply LOOP_END_PROOF. eauto.
  Qed.


  Definition KWhile1 e s :=
    Kloop1 (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

  Definition KWhile2 e s :=
    Kloop2 (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

  Ltac fold_KWhile1 :=
    match goal with
    | |- context [Kloop1 (Ssequence (Sifthenelse ?e _ _) ?s) _ ?k] =>
      fold (KWhile1 e s k)
    end.

  Ltac fold_KWhile2 :=
    match goal with
    | |- context [Kloop2 (Ssequence (Sifthenelse ?e _ _) ?s) _ ?k] =>
      fold (KWhile2 e s k)
    end.

  Lemma sim_while
        (r: nat -> itree _ _ -> Clight.state -> Prop)
        (linv: itree progE unit ->
               PTree.t val -> mem -> Prop)
        idx itr f expr_c s k e le m

        (INIT_LOOP_INV: linv itr le m)
        (LINV_EXPR_COMPUTABLE:
           forall itr' le' m' (LINV: linv itr' le' m'),
             exists v1 b,
             eval_expr_c ge e le' m' expr_c = Some v1 /\
             Cop.bool_val v1 (typeof expr_c) m' = Some b)
        (LOOP_BODY_PROOF:
           forall r' itr_c le_c m_c v1
             (R_INCL: r <3= r')
             (LOOP_INV: linv itr_c le_c m_c)
             (EVAL_EXPR: eval_expr_c ge e le_c m_c expr_c = Some v1)
             (COND_TRUE: Cop.bool_val v1 (typeof expr_c) m_c = Some true)
             (CIH: forall itr_n le_n m_n
                     (LOOP_INV: linv itr_n le_n m_n),
                 r' (idx + 5) itr_n
                   (State f (Swhile expr_c s)
                          k e le_n m_n))
           ,
             sim r' idx itr_c (State f s (KWhile1 expr_c s k) e le_c m_c))
        (LOOP_FINAL:
           forall r' itr_f le_f m_f v1
             (R_INCL: r <3= r')
             (LOOP_INV: linv itr_f le_f m_f)
             (EVAL_EXPR: eval_expr_c ge e le_f m_f expr_c = Some v1)
             (COND_FALSE: Cop.bool_val v1 (typeof expr_c) m_f = Some false),
             sim r' idx itr_f (State f Sskip k e le_f m_f))
    : sim r (idx + 5) itr (State f (Swhile expr_c s) k e le m).
  Proof.
    revert itr le m INIT_LOOP_INV.
    pcofix CIH. i.

    eapply sim_itree_clight_silent; [nia| |left].
    { ss. econs; ss. econs. }
    eapply sim_itree_clight_silent; [nia| |left].
    { ss. econs; ss. econs. }

    hexploit LINV_EXPR_COMPUTABLE; eauto.
    intros (v1 & b & EVAL_EXPR_C & BOOL_VAL_C).
    destruct b.
    - (* true *)
      eapply sim_itree_red_idx with (idx_small:=idx + 2).
      { nia. }
      eapply sim_itree_clight_silent; [nia| |left].
      { ss. econs; ss. econs.
        - eapply eval_expr_comput; eauto.
        - eauto.
      }
      ss.
      eapply sim_itree_clight_silent; [nia| |left].
      { ss. econs; ss. econs. }
      eapply sim_itree_red_idx with (idx_small:=idx).
      { nia. }

      fold_KWhile1.
      eapply LOOP_BODY_PROOF; eauto.

    - (* false *)
      eapply sim_itree_clight_silent; [nia| |left].
      { ss. econs; ss. econs.
        - eapply eval_expr_comput; eauto.
        - eauto.
      }
      ss.
      eapply sim_itree_clight_silent; [nia| |left].
      { ss. econs; ss. econs. }
      eapply sim_itree_clight_silent; [nia| |left].
      { ss. econs; ss. eapply step_break_loop1. }
      eapply sim_itree_red_idx with (idx_small:=idx).
      { nia. }
      eauto.
  Qed.

End CPROG_SIM_LEMMAS.


Ltac fold_for_loop i :=
  match goal with
  | |- context [ Sloop (Ssequence ?s1 ?stmt) ?b ] =>
    match s1 with
    | Sifthenelse
        (Ebinop Cop.Olt (Etempvar i tint) ?e_max tint)
        Sskip Sbreak =>
      replace (Sloop (Ssequence s1 stmt) b)
        with (for_loop_stmt i stmt e_max); [| by ss]
    end
  end.
