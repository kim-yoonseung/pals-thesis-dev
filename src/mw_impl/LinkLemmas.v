From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.

From compcert Require Import Maps Linking.
Require Import Axioms.
Require Import sflib.

Local Transparent Linker_prog.

Lemma link_build_composite_env_eq
      cdefs1 cdefs2 cdefs
      cenv1 cenv2
      eq1 eq2 eq3 cenv pf
      (CENV_OK: build_composite_env' cdefs pf = cenv)
  : exists EQ, link_build_composite_env
            cdefs1 cdefs2 cdefs
            cenv1 cenv2 eq1 eq2 eq3 = exist _ (proj1_sig cenv) EQ.
Proof.
  assert (CENV': exists cenv',
             build_composite_env cdefs = Errors.OK cenv' /\
             cenv' = proj1_sig cenv).
  { destruct cenv as [cenv CENV_PF]. ss.
    esplits; eauto. }

  destruct CENV' as [cenv' [BUILD_EQ CENV']].
  rewrite <- CENV'.
  clear CENV_OK CENV'.

  destruct (link_build_composite_env
              cdefs1 cdefs2 cdefs cenv1 cenv2
              eq1 eq2 eq3).
  des.
  assert (REW: x = cenv') by congruence.
  rewrite <- REW.
  esplits; eauto.
Qed.


Lemma link_program_eq
      (p1 p2 p: Clight.program)
      (LINK_AST_PROGS:
         link_prog (program_of_program p1)
                   (program_of_program p2) =
         Some (program_of_program p))
      (LINK_COMPS: link_composite_defs
                     (prog_types p1)
                     (prog_types p2) =
                   Some (prog_types p))
      (WF_COMP: wf_composites (prog_types p))
  : link_program p1 p2 = Some p.
Proof.
  unfold link_program. unfold link.
  unfold Linker_prog.
  rewrite LINK_AST_PROGS.
  unfold Linker_composite_defs.

  match goal with
  | |- match ?x with _ => _ end = _ =>
    destruct x as [DEFS | DEFS]
  end.
  2: { rewrite LINK_COMPS in *. ss. }

  assert (COMP_EQ: proj1_sig DEFS = prog_types p).
  { destruct DEFS as [defs PF]. ss. clarify. }
  destruct DEFS as [comp LINK_COMPS'].
  clarify.

  match goal with
  | |- context[link_build_composite_env
                ?c1 ?c2 ?c3 ?ce1 ?ce2
                ?cep1 ?cep2 ?lpf] =>
    hexploit (link_build_composite_env_eq
                c1 c2 c3 ce1 ce2 cep1 cep2 lpf)
  end.
  { instantiate (2:= WF_COMP). reflexivity. }

  intros [EQ_ENVS EQ_LINK].
  rewrite EQ_LINK. des.

  destruct p. ss.
  f_equal.

  destruct (build_composite_env' prog_types WF_COMP).
  ss. clear.

  assert (x = prog_comp_env) by congruence.
  subst x.
  f_equal.
  apply proof_irrelevance.
Qed.


Section LINKED_PROG.
  Variable p1 p2 p: Clight.program.
  Hypothesis LINKED: link_program p1 p2 = Some p.

  Lemma def_in_defmap1
        i (gd: globdef Clight.fundef type)
        (IN_P1: (prog_defmap p1) ! i = Some gd)
        (IN_P2': match (prog_defmap p2) ! i with
                 | None => True
                 | Some gd' => link gd gd' = Some gd
                 end)
    : (prog_defmap p) ! i = Some gd.
  Proof.
    replace (prog_defmap p) with
        (PTree_Properties.of_list (PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)))).
    2: {
      unfold prog_defmap. ss. f_equal.
      unfold link_program in LINKED. ss.
      unfold link_prog in LINKED.
      desf.
    }

    rewrite PTree_Properties.of_list_elements.
    rewrite PTree.gcombine by ss.

    unfold link_prog_merge. rewrite IN_P1.
    desf.
  Qed.

  Lemma def_in_defmap2
        i (gd: globdef Clight.fundef type)
        (IN_P2: (prog_defmap p2) ! i = Some gd)
        (IN_P1': match (prog_defmap p1) ! i with
                 | None => True
                 | Some gd' => link gd' gd = Some gd
                 end)
    : (prog_defmap p) ! i = Some gd.
  Proof.
    replace (prog_defmap p) with
        (PTree_Properties.of_list (PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)))).
    2: {
      unfold prog_defmap. ss. f_equal.
      unfold link_program in LINKED. ss.
      unfold link_prog in LINKED.
      desf.
    }

    rewrite PTree_Properties.of_list_elements.
    rewrite PTree.gcombine by ss.

    unfold link_prog_merge. rewrite IN_P2.
    desf.
  Qed.

  Lemma cd_in_either_prog_types
        cd
        (IN_EITHER: In cd (prog_types p1) \/
                    In cd (prog_types p2))
    : In cd (prog_types p).
  Proof.
    unfold link_program in LINKED.
    unfold link in LINKED. ss.
    guardH IN_EITHER.
    desf; ss.

    hexploit link_composite_def_inv; eauto.
    intros [_ [_ AUX]].
    eapply AUX. eauto.
  Qed.

  Lemma co_in_either_composites
        i co
        (IN_EITHER: (prog_comp_env p1) ! i = Some co \/
                    (prog_comp_env p2) ! i = Some co)
    : (prog_comp_env p) ! i = Some co.
  Proof.
    unfold link_program in LINKED.
    unfold link in LINKED. ss.
    guardH IN_EITHER.
    desf; ss.
    des.
    unguard. des; eauto.
  Qed.

End LINKED_PROG.



Lemma in_dec_app A
      (D: forall x y:A, {x = y} + {x <> y})
      a l1 l2
  : Coqlib.proj_sumbool (in_dec D a (l1 ++ l2)) =
    orb (Coqlib.proj_sumbool (in_dec D a l1))
        (Coqlib.proj_sumbool (in_dec D a l2)).
Proof.
  induction l1 as [| h t IH]; ss.
  desf.
Qed.


Lemma linked_prog_public
      (p1 p2 p_l: Clight.program)
      (LINK_PROGRAM_OK: link_program p1 p2 = Some p_l)
  : prog_public p_l = prog_public p1 ++ prog_public p2.
Proof.
  Local Transparent Linker_prog.
  unfold link_program in LINK_PROGRAM_OK. desf.
  ss.
  hexploit (link_prog_inv p1 p2); eauto.
  i. des. ss. clarify.
  Local Opaque Linker_prog.
Qed.


Lemma linked_prog_defs
      (p1 p2 p_l: Clight.program)
      (LINK_PROGRAM_OK: link_program p1 p2 = Some p_l)
  : prog_defs p_l = PTree.elements (PTree.combine
                                      link_prog_merge
                                      (prog_defmap p1) (prog_defmap p2)).
Proof.
  Local Transparent Linker_prog.
  unfold link_program in LINK_PROGRAM_OK. desf.
  ss.
  hexploit (link_prog_inv p1 p2); eauto.
  i. des. ss. clarify.
  Local Opaque Linker_prog.
Qed.


Lemma program_impl_prog_defs
      (p: Clight.program)
  : AST.prog_defs p = prog_defs p.
 (* /\ *)
 (*    AST.prog_public p = prog_public p /\ *)
 (*    AST.prog_main p = prog_main p. *)
Proof. ss. Qed.

Local Transparent Linker_def Linker_fundef Ctypes.Linker_fundef.

Lemma link_same_gfun_ext
      (gd1 gd2: globdef fundef type)
      ef ts t c
      (GDEF1: gd1 = Gfun (External ef ts t c))
      (GDEF2: gd2 = Gfun (External ef ts t c))
  : link gd1 gd2 = Some gd1.
Proof.
  subst. ss.
  unfold link.
  desf.
  exfalso.
  destruct (external_function_eq ef ef); ss.
  destruct (typelist_eq ts ts); ss.
  destruct (type_eq t t); ss.
  destruct (calling_convention_eq c c); ss.
Qed.

Lemma link_prog_merge_same_link
      (ogd1 ogd2: option (globdef fundef type)) gd
      ef ts t c
      (OGD1: ogd1 = Some (Gfun (External ef ts t c)))
      (OGD2: ogd2 = Some (Gfun (External ef ts t c)))
      (LINK_PROG_MERGE: link_prog_merge ogd1 ogd2 = Some gd)
  : link gd (Gfun (External ef ts t c)) = Some (Gfun (External ef ts t c)).
Proof.
  unfold link_prog_merge in LINK_PROG_MERGE.
  subst.
  erewrite link_same_gfun_ext in LINK_PROG_MERGE; eauto.
  erewrite link_same_gfun_ext; eauto.
  clarify.
Qed.




Lemma program_impl_prog_public
      (p: Clight.program)
  : AST.prog_public p = prog_public p.
 (* /\ *)
 (*    AST.prog_public p = prog_public p /\ *)
 (*    AST.prog_main p = prog_main p. *)
Proof. ss. Qed.





Lemma link_prog_merge_exts_aux
      (ogd1 ogd2: option (globdef fundef type))
      gd fd ef ts t c
      (EF_EQ: fd = External ef ts t c)
      (LINK_PM: link_prog_merge ogd1 ogd2 = Some gd)
      (EF1: ogd1 = Some (Gfun fd))
      (EF2: ogd2 = Some (Gfun fd))
  : link gd (Gfun fd) <> None.
Proof.
  subst.
  erewrite link_same_gfun_ext; eauto.
  { ss. }
  unfold link_prog_merge in LINK_PM.
  erewrite link_same_gfun_ext in LINK_PM; eauto.
  clarify.
Qed.


Section LINKING3_LEMMAS.
  Variable p1 p2 p3 p_l: Clight.program.
  Hypothesis LINK_PROGRAM_OK: link_program p1 p2 = Some p_l.

  Let dm1 := prog_defmap p1.
  Let dm2 := prog_defmap p2.
  Let dm_l := prog_defmap p_l.
  Let dm3 := prog_defmap p3.

  Local Transparent Linker_def.

  Lemma link_prog_check_lemma
        (CHECK_EACH:
           forall id gd
             (IN_DEFS3: In (id, gd) (prog_defs p3)),
             Coqlib.proj_sumbool (in_dec Coqlib.peq id (AST.prog_public p3)) /\
             (forall dm_x (DM_L_ID: link_prog_merge (dm1 ! id) (dm2 ! id) = Some dm_x),
                 (Coqlib.proj_sumbool (in_dec Coqlib.peq id (AST.prog_public p1)) \/
                  Coqlib.proj_sumbool (in_dec Coqlib.peq id (AST.prog_public p2))) /\
                 link_def dm_x gd <> None))
             (* (((* all externals *) *)
             (*     Coqlib.proj_sumbool (in_dec Coqlib.peq id (AST.prog_public p1)) /\ *)
             (*     exists ef ts t c, *)
             (*       <<GD: gd = Gfun (External ef ts t c)>> /\ *)
             (*       <<DM1_I: dm1 ! id = Some gd>> /\ *)
             (*       <<DM2_I:dm2 ! id = Some gd>>) \/ *)
             (*  ((* p3-only *) *)
             (*    (* exists ef, *) *)
             (*    (*   <<GD: gd = >> /\ *) *)
             (*    <<DM1_I: dm1 ! id = None>> /\ *)
             (*    <<DM2_I: dm2 ! id = None>>) \/ *)
             (*  ((* p3 has def *) *)
             (*    Coqlib.proj_sumbool (in_dec Coqlib.peq id (AST.prog_public p1)) /\ *)
             (*    exists gd1, *)
             (*      <<DM1_I: dm1 ! id = Some gd1>> /\ *)
             (*      <<DM2_I: dm2 ! id = None>> /\ *)
             (*      <<GD_LINK_OK: link_def gd1 gd <> None>>))) *)
    : PTree_Properties.for_all
        dm_l (link_prog_check p_l p3) = true.
  Proof.
    apply PTree_Properties.for_all_correct.
    intros i gd DEF_L.

    unfold link_prog_check.

    destruct ((prog_defmap p3) ! i) eqn: DEFMAP3.
    2: { ss. }

    unfold prog_defmap in DEFMAP3.
    apply PTree_Properties.in_of_list in DEFMAP3.

    hexploit (linked_prog_defs p1 p2 p_l).
    { apply LINK_PROGRAM_OK. }
    intros DEF_LIST_L.

    unfold dm_l in DEF_L.
    unfold prog_defmap in DEF_L.
    rewrite program_impl_prog_defs in DEF_L.

    rewrite DEF_LIST_L in DEF_L.
    rewrite PTree_Properties.of_list_elements in DEF_L.
    rewrite PTree.gcombine in DEF_L by ss.
    fold dm1 dm2 in DEF_L.

    hexploit CHECK_EACH.
    { apply DEFMAP3. }
    intros (PUB3 & DEF12).

    hexploit DEF12.
    { apply DEF_L. }
    intros (PUB12 & LINK_DEF_OK).

    apply andb_true_iff.
    split.
    { apply andb_true_iff.
      split; ss.
      rewrite (linked_prog_public p1 p2) by ss.
      rewrite in_dec_app.
      apply orb_true_iff. ss.
    }
    ss.
    desf.
  Qed.

  Local Opaque Linker_def.
End LINKING3_LEMMAS.




Lemma get_linked_prog_defs
      (p1 p2 p: Clight.program) id
      (LINKED: link_program p1 p2 = Some p)
  : (prog_defmap p) ! id =
    link_prog_merge ((prog_defmap p1) ! id) ((prog_defmap p2) ! id).
Proof.
  unfold prog_defmap at 1.
  rewrite program_impl_prog_defs.
  erewrite linked_prog_defs; eauto.
  rewrite PTree_Properties.of_list_elements.
  rewrite PTree.gcombine by ss.
  ss.
Qed.


Lemma link_def_gfun_gvar_absurd_aux
      (gd1 gd2: globdef fundef type) v
      (LINK: link gd1 gd2 = Some (Gvar v))
      (GFUN: exists f, gd1 = Gfun f \/ gd2 = Gfun f)
  : False.
Proof.
  des; subst; ss; desf.
  unfold link_def in *. desf.
Qed.
