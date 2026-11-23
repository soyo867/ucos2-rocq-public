Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.mutex Require Import del_full_goal.
From Ucos2Verify.VC.code.mutex Require Import del_full_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_del_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Local Open Scope sac.

Lemma proof_of_OSMutexDel_FirstSet8_return_wit_1 : OSMutexDel_FirstSet8_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst bits_in.
  unfold mutex_del_first_set8.
  rewrite PreH7, PreH6, PreH5, PreH4, PreH3, PreH2, PreH1.
  simpl.
  repeat apply ucos2_rules_lib.UCOS2_C_Rules._derivable1_andp_intros.
  all: try (apply derivable1s_coq_prop_r; lia).
  all: unfold ucos2_rules_lib.UCOS2_C_Rules.derivable1,
              ucos2_rules_lib.UCOS2_C_Rules.emp,
              ucos2_rules_lib.UCOS2_C_Rules.is_unit,
              ConAssertion.state_empty;
       intros s Hemp;
       first [ exact (proj1 Hemp)
             | exact (proj1 (proj2 Hemp))
             | exact (proj2 (proj2 Hemp)) ].
Qed.

Lemma proof_of_OSMutexDel_FirstSet8_return_wit_2 : OSMutexDel_FirstSet8_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst bits_in.
  assert (Hbit : Z.eqb (Z.land bits_pre 64) 0 = false).
  { apply Z.eqb_neq. exact PreH1. }
  unfold mutex_del_first_set8.
  rewrite PreH7, PreH6, PreH5, PreH4, PreH3, PreH2, Hbit.
  simpl.
  repeat apply ucos2_rules_lib.UCOS2_C_Rules._derivable1_andp_intros.
  all: try (apply derivable1s_coq_prop_r; lia).
  all: unfold ucos2_rules_lib.UCOS2_C_Rules.derivable1,
              ucos2_rules_lib.UCOS2_C_Rules.emp,
              ucos2_rules_lib.UCOS2_C_Rules.is_unit,
              ConAssertion.state_empty;
       intros s Hemp;
       first [ exact (proj1 Hemp)
             | exact (proj1 (proj2 Hemp))
             | exact (proj2 (proj2 Hemp)) ].
Qed.

Lemma proof_of_OSMutexDel_FirstSet8_return_wit_3 : OSMutexDel_FirstSet8_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst bits_in.
  assert (Hbit : Z.eqb (Z.land bits_pre 32) 0 = false).
  { apply Z.eqb_neq. exact PreH1. }
  unfold mutex_del_first_set8.
  rewrite PreH6, PreH5, PreH4, PreH3, PreH2, Hbit.
  simpl.
  repeat apply ucos2_rules_lib.UCOS2_C_Rules._derivable1_andp_intros.
  all: try (apply derivable1s_coq_prop_r; lia).
  all: unfold ucos2_rules_lib.UCOS2_C_Rules.derivable1,
              ucos2_rules_lib.UCOS2_C_Rules.emp,
              ucos2_rules_lib.UCOS2_C_Rules.is_unit,
              ConAssertion.state_empty;
       intros s Hemp;
       first [ exact (proj1 Hemp)
             | exact (proj1 (proj2 Hemp))
             | exact (proj2 (proj2 Hemp)) ].
Qed.

Lemma proof_of_OSMutexDel_FirstSet8_return_wit_4 : OSMutexDel_FirstSet8_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst bits_in.
  assert (Hbit : Z.eqb (Z.land bits_pre 16) 0 = false).
  { apply Z.eqb_neq. exact PreH1. }
  unfold mutex_del_first_set8.
  rewrite PreH5, PreH4, PreH3, PreH2, Hbit.
  simpl.
  repeat apply ucos2_rules_lib.UCOS2_C_Rules._derivable1_andp_intros.
  all: try (apply derivable1s_coq_prop_r; lia).
  all: unfold ucos2_rules_lib.UCOS2_C_Rules.derivable1,
              ucos2_rules_lib.UCOS2_C_Rules.emp,
              ucos2_rules_lib.UCOS2_C_Rules.is_unit,
              ConAssertion.state_empty;
       intros s Hemp;
       first [ exact (proj1 Hemp)
             | exact (proj1 (proj2 Hemp))
             | exact (proj2 (proj2 Hemp)) ].
Qed.

Lemma proof_of_OSMutexDel_FirstSet8_return_wit_5 : OSMutexDel_FirstSet8_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst bits_in.
  assert (Hbit : Z.eqb (Z.land bits_pre 8) 0 = false).
  { apply Z.eqb_neq. exact PreH1. }
  unfold mutex_del_first_set8.
  rewrite PreH4, PreH3, PreH2, Hbit.
  simpl.
  repeat apply ucos2_rules_lib.UCOS2_C_Rules._derivable1_andp_intros.
  all: try (apply derivable1s_coq_prop_r; lia).
  all: unfold ucos2_rules_lib.UCOS2_C_Rules.derivable1,
              ucos2_rules_lib.UCOS2_C_Rules.emp,
              ucos2_rules_lib.UCOS2_C_Rules.is_unit,
              ConAssertion.state_empty;
       intros s Hemp;
       first [ exact (proj1 Hemp)
             | exact (proj1 (proj2 Hemp))
             | exact (proj2 (proj2 Hemp)) ].
Qed.

Lemma proof_of_OSMutexDel_FirstSet8_return_wit_6 : OSMutexDel_FirstSet8_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst bits_in.
  assert (Hbit : Z.eqb (Z.land bits_pre 4) 0 = false).
  { apply Z.eqb_neq. exact PreH1. }
  unfold mutex_del_first_set8.
  rewrite PreH3, PreH2, Hbit.
  simpl.
  repeat apply ucos2_rules_lib.UCOS2_C_Rules._derivable1_andp_intros.
  all: try (apply derivable1s_coq_prop_r; lia).
  all: unfold ucos2_rules_lib.UCOS2_C_Rules.derivable1,
              ucos2_rules_lib.UCOS2_C_Rules.emp,
              ucos2_rules_lib.UCOS2_C_Rules.is_unit,
              ConAssertion.state_empty;
       intros s Hemp;
       first [ exact (proj1 Hemp)
             | exact (proj1 (proj2 Hemp))
             | exact (proj2 (proj2 Hemp)) ].
Qed.

Lemma proof_of_OSMutexDel_FirstSet8_return_wit_7 : OSMutexDel_FirstSet8_return_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst bits_in.
  assert (Hbit : Z.eqb (Z.land bits_pre 2) 0 = false).
  { apply Z.eqb_neq. exact PreH1. }
  unfold mutex_del_first_set8.
  rewrite PreH2, Hbit.
  simpl.
  repeat apply ucos2_rules_lib.UCOS2_C_Rules._derivable1_andp_intros.
  all: try (apply derivable1s_coq_prop_r; lia).
  all: unfold ucos2_rules_lib.UCOS2_C_Rules.derivable1,
              ucos2_rules_lib.UCOS2_C_Rules.emp,
              ucos2_rules_lib.UCOS2_C_Rules.is_unit,
              ConAssertion.state_empty;
       intros s Hemp;
       first [ exact (proj1 Hemp)
             | exact (proj1 (proj2 Hemp))
             | exact (proj2 (proj2 Hemp)) ].
Qed.

Lemma proof_of_OSMutexDel_FirstSet8_return_wit_8 : OSMutexDel_FirstSet8_return_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst bits_in.
  assert (Hbit : Z.eqb (Z.land bits_pre 1) 0 = false).
  { apply Z.eqb_neq. exact PreH1. }
  unfold mutex_del_first_set8.
  rewrite Hbit.
  simpl.
  repeat apply ucos2_rules_lib.UCOS2_C_Rules._derivable1_andp_intros.
  all: try (apply derivable1s_coq_prop_r; lia).
  all: unfold ucos2_rules_lib.UCOS2_C_Rules.derivable1,
              ucos2_rules_lib.UCOS2_C_Rules.emp,
              ucos2_rules_lib.UCOS2_C_Rules.is_unit,
              ConAssertion.state_empty;
       intros s Hemp;
       first [ exact (proj1 Hemp)
             | exact (proj1 (proj2 Hemp))
             | exact (proj2 (proj2 Hemp)) ].
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_2_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_uchar_range
       (( &( "OSRdyGrp" ) )) (mutex_del_refresh_grp_value post)).
  Intros_p Hgrp_range.
  change (0 <= mutex_del_refresh_grp_value post <= 255) in Hgrp_range.
  rewrite unsigned_last_nbits_eq in PreH1 by (cbn; lia).
  apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
  exact PreH1.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_5_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_uchar_range
       (( &( "OSRdyGrp" ) )) (mutex_del_refresh_grp_value post)).
  Intros_p Hgrp_range.
  change (0 <= mutex_del_refresh_grp_value post <= 255) in Hgrp_range.
  split_pures.
  - apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
    reflexivity.
  - apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
    exact (proj2 Hgrp_range).
  - apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
    exact (proj1 Hgrp_range).
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst retval.
  assert (Hindex :
    osrdytbl_index_in_range
      (mutex_del_first_set8 (mutex_del_refresh_grp_value post))) by
    (unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE; lia).
  prop_apply_p
    (store_osrdytbl_Znth_uchar_range__g01_scan_snapshot
      sg (mutex_del_refresh_ready_tbl_values post)
      (mutex_del_first_set8 (mutex_del_refresh_grp_value post)) Hindex).
  Intros_p Hrow_range.
  change
    (0 <=
       Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
         (mutex_del_refresh_ready_tbl_values post) 0 <= 255)
    in Hrow_range.
  split_pures.
  - apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
    reflexivity.
  - apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
    exact (proj1 Hrow_range).
  - apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
    exact (proj2 Hrow_range).
  - apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
    exact (proj2 Hrow_range).
  - apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
    exact (proj1 Hrow_range).
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_partial_solve_wit_11_pure : OSMutexDel_RefreshHighReady_partial_solve_wit_11_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_uchar_range
       (( &( "OSRdyGrp" ) )) (mutex_del_refresh_grp_value post)).
  Intros_p Hgrp_range.
  change (0 <= mutex_del_refresh_grp_value post <= 255) in Hgrp_range.
  rewrite unsigned_last_nbits_eq in PreH7 by (cbn; lia).
  apply ucos2_rules_lib.UCOS2_C_Rules.derivable1s_coq_prop_r.
  exact PreH7.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_1 : OSMutexDel_RefreshHighReady_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof H as Hcontext.
  unfold mutex_del_refresh_context_prop,
    mutex_del_refresh_layout_prop in Hcontext.
  destruct Hcontext as
    [Hstable [Hrdy_grp [Hrdy_tbl [Hprio_high [Htcb_high Hprio_tbl]]]]].
  sep_apply_l_atomic
    (mutex_del_transition_raw_stage_validity__g02_refresh_close sg entry post).
  pureIntros.
  pose proof
    (mutex_del_refresh_snapshot_from_validity__g02_refresh_close
      sg post Hstable H0) as Hsnapshot.
  sep_apply_l_atomic
    (mutex_del_raw_stage_refresh_expose__g02_refresh_close
      sg entry post H0).
  Intros old_high_tcb old_high_prio.
  Exists old_high_tcb old_high_prio.
  rewrite Hrdy_grp, Hrdy_tbl, Hprio_high, Htcb_high, Hprio_tbl.
  rewrite Hrdy_grp, Hrdy_tbl, Hprio_high, Htcb_high, Hprio_tbl in H.
  andp_cancel.
  sepcon_assoc_change.
  repeat progress cancel.
  apply sepcon_cancel_end.
  - apply derivable1_truep_intros.
  - apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_2 : OSMutexDel_RefreshHighReady_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_l.
  intros Hsnapshot.
  apply derivable1s_coq_prop_r.
  unfold mutex_del_refresh_snapshot_prop in Hsnapshot.
  destruct Hsnapshot as [_ [_ [_ Hready]]].
  destruct post.(SchedState).(readyList) as [| head tail] eqn:Hlist.
  - simpl in Hready.
    destruct Hready as [_ [Hprio Htid]].
    unfold mutex_del_refresh_choice_prop.
    rewrite Hprio, Htid.
    split; reflexivity.
  - simpl in Hready.
    destruct Hready as [head_t [_ [_ [Hnonzero _]]]].
    exfalso. apply Hnonzero. exact PreH1.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_3 : OSMutexDel_RefreshHighReady_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof H as Hcontext.
  unfold mutex_del_refresh_context_prop,
    mutex_del_refresh_layout_prop in Hcontext.
  destruct Hcontext as
    [Hstable [Hrdy_grp [Hrdy_tbl [Hprio_high [Htcb_high Hprio_tbl]]]]].
  unfold mutex_del_refresh_choice_prop in H1.
  destruct H1 as [Hchoice_prio Hchoice_tcb].
  rewrite Hrdy_grp, Hrdy_tbl, Hprio_high, Htcb_high, Hprio_tbl.
  rewrite Hrdy_grp, Hrdy_tbl, Hprio_high, Htcb_high, Hprio_tbl in H.
  rewrite Hchoice_prio; try rewrite Hchoice_tcb.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - unfold mutex_del_refresh_prio_tbl_values.
    repeat progress cancel.
    sepcon_assoc_change.
    apply mutex_del_refresh_spatial_framed_closed__g02_refresh_close.
    exact H0.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_4 : OSMutexDel_RefreshHighReady_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_restore_rep.
  apply mutex_del_refresh_closed_full.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_5 : OSMutexDel_RefreshHighReady_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof H as Hcontext.
  unfold mutex_del_refresh_context_prop,
    mutex_del_refresh_layout_prop in Hcontext.
  destruct Hcontext as
    [Hstable [Hrdy_grp [Hrdy_tbl [Hprio_high [Htcb_high Hprio_tbl]]]]].
  subst y.
  rewrite Hrdy_tbl.
  rewrite Hrdy_tbl in H.
  sep_apply_l_atomic
    (store_osrdytbl_split
      sg (mutex_del_refresh_ready_tbl_values post)
      (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
      ltac:(unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE;
        apply mutex_del_first_set8_range__g02_refresh_close)
      ltac:(unfold mutex_del_refresh_ready_tbl_values,
        OS_RDY_TBL_SIZE, Zlength; reflexivity)).
  unfold osrdytbl_element_store, sizeof_OS_PRIO.
  repeat progress cancel.
  replace (sizeof(UCHAR)) with 1 by reflexivity.
  andp_cancel.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_6 : OSMutexDel_RefreshHighReady_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof H as Hcontext.
  unfold mutex_del_refresh_context_prop,
    mutex_del_refresh_layout_prop in Hcontext.
  destruct Hcontext as
    [Hstable [Hrdy_grp [Hrdy_tbl [Hprio_high [Htcb_high Hprio_tbl]]]]].
  subst y.
  subst row.
  rewrite Hrdy_tbl.
  rewrite Hrdy_tbl in H.
  replace (sizeof(UCHAR)) with 1 by reflexivity.
  fold (osrdytbl_element_store
    (g_OSRdyTbl sg)
    (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
    (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
      (mutex_del_refresh_ready_tbl_values post) 0)).
  andp_cancel.
  change
    (osrdytbl_element_store (g_OSRdyTbl sg)
       (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
       (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
         (mutex_del_refresh_ready_tbl_values post) 0) **
     store_osrdytbl_missing_i sg
       (mutex_del_refresh_ready_tbl_values post)
       (mutex_del_first_set8 (mutex_del_refresh_grp_value post)) |--
     store_osrdytbl sg (mutex_del_refresh_ready_tbl_values post)).
  sep_apply_l_atomic
    (store_osrdytbl_merge
      sg (mutex_del_refresh_ready_tbl_values post)
      (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
      (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
        (mutex_del_refresh_ready_tbl_values post) 0)
      ltac:(unfold osrdytbl_index_in_range, OS_RDY_TBL_SIZE;
        apply mutex_del_first_set8_range__g02_refresh_close)
      ltac:(unfold mutex_del_refresh_ready_tbl_values,
        OS_RDY_TBL_SIZE, Zlength; reflexivity)).
  rewrite replace_Znth_Znth.
  intros h Hh. exact Hh.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_7 : OSMutexDel_RefreshHighReady_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof H as Hcontext.
  unfold mutex_del_refresh_context_prop,
    mutex_del_refresh_layout_prop in Hcontext.
  destruct Hcontext as
    [Hstable [Hrdy_grp [Hrdy_tbl [Hprio_high [Htcb_high Hprio_tbl]]]]].
  subst high_prio.
  rewrite Hprio_tbl.
  rewrite Hprio_tbl in H.
  sep_apply_l_atomic
    (store_priotbl_list_split
      sg (mutex_del_refresh_prio_tbl_values sg post)
      (mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
       mutex_del_first_set8
         (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
           (mutex_del_refresh_ready_tbl_values post) 0))
      ltac:(
        pose proof
          (mutex_del_first_set8_range__g02_refresh_close
            (mutex_del_refresh_grp_value post)) as Hrow_range;
        pose proof
          (mutex_del_first_set8_range__g02_refresh_close
            (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
              (mutex_del_refresh_ready_tbl_values post) 0)) as Hcol_range;
        unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia)
      ltac:(unfold mutex_del_refresh_prio_tbl_values;
        apply mutex_del_prioTbl_to_addrs_Zlength)).
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  repeat progress cancel.
  replace (sizeof(PTR)) with 4 by reflexivity.
  andp_cancel.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_8 : OSMutexDel_RefreshHighReady_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof H as Hcontext.
  unfold mutex_del_refresh_context_prop,
    mutex_del_refresh_layout_prop in Hcontext.
  destruct Hcontext as
    [Hstable [Hrdy_grp [Hrdy_tbl [Hprio_high [Htcb_high Hprio_tbl]]]]].
  subst high_prio.
  subst high_tcb.
  rewrite Hprio_tbl.
  rewrite Hprio_tbl in H.
  replace (sizeof(PTR)) with 4 by reflexivity.
  fold (priotbl_element_store
    (g_OSTCBPrioTbl sg)
    (mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
     mutex_del_first_set8
       (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
         (mutex_del_refresh_ready_tbl_values post) 0))
    (Znth
      (mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
       mutex_del_first_set8
         (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
           (mutex_del_refresh_ready_tbl_values post) 0))
      (mutex_del_refresh_prio_tbl_values sg post) 0)).
  andp_cancel.
  change
    (priotbl_element_store (g_OSTCBPrioTbl sg)
       (mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
        mutex_del_first_set8
          (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
            (mutex_del_refresh_ready_tbl_values post) 0))
       (Znth
         (mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
          mutex_del_first_set8
            (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
              (mutex_del_refresh_ready_tbl_values post) 0))
         (mutex_del_refresh_prio_tbl_values sg post) 0) **
     store_priotbl_list_missing_i sg
       (mutex_del_refresh_prio_tbl_values sg post)
       (mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
        mutex_del_first_set8
          (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
            (mutex_del_refresh_ready_tbl_values post) 0)) |--
     store_priotbl_list sg (mutex_del_refresh_prio_tbl_values sg post)).
  sep_apply_l_atomic
    (store_priotbl_list_merge
      sg (mutex_del_refresh_prio_tbl_values sg post)
      (mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
       mutex_del_first_set8
         (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
           (mutex_del_refresh_ready_tbl_values post) 0))
      (Znth
        (mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
         mutex_del_first_set8
           (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
             (mutex_del_refresh_ready_tbl_values post) 0))
        (mutex_del_refresh_prio_tbl_values sg post) 0)
      ltac:(
        pose proof
          (mutex_del_first_set8_range__g02_refresh_close
            (mutex_del_refresh_grp_value post)) as Hrow_range;
        pose proof
          (mutex_del_first_set8_range__g02_refresh_close
            (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
              (mutex_del_refresh_ready_tbl_values post) 0)) as Hcol_range;
        unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia)
      ltac:(unfold mutex_del_refresh_prio_tbl_values;
        apply mutex_del_prioTbl_to_addrs_Zlength)).
  rewrite replace_Znth_Znth.
  intros h Hh. exact Hh.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_9 : OSMutexDel_RefreshHighReady_which_implies_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply derivable1s_coq_prop_l.
  intros Hsnapshot.
  apply derivable1s_coq_prop_r.
  unfold mutex_del_refresh_snapshot_prop in Hsnapshot.
  destruct Hsnapshot as [Hrdy_grp [Hrdy_tbl [Hprio_tbl Hready]]].
  destruct post.(SchedState).(readyList) as [| head tail] eqn:Hlist.
  - simpl in Hready.
    destruct Hready as [Hzero _].
    exfalso. apply PreH1. exact Hzero.
  - simpl in Hready.
    destruct Hready as
      [head_t [Hlookup [Hrange [Hnonzero [Hrow [Hrow_nonzero
        [Hcol [Hprio_addr [Hhigh_prio Hhigh_tid]]]]]]]]].
    assert (Hprio_value :
      mutex_del_first_set8 (mutex_del_refresh_grp_value post) * 8 +
      mutex_del_first_set8
        (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
          (mutex_del_refresh_ready_tbl_values post) 0) =
      head_t.(curPrio)).
    { rewrite Hcol, Hrow.
      pose proof (Z.div_mod head_t.(curPrio) 8 ltac:(lia)).
      lia. }
    unfold mutex_del_refresh_choice_prop.
    rewrite Hhigh_prio, Hhigh_tid, Hprio_value, Hprio_addr.
    split; reflexivity.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_10 : OSMutexDel_RefreshHighReady_which_implies_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof H as Hcontext.
  unfold mutex_del_refresh_context_prop,
    mutex_del_refresh_layout_prop in Hcontext.
  destruct Hcontext as
    [Hstable [Hrdy_grp [Hrdy_tbl [Hprio_high [Htcb_high Hprio_tbl]]]]].
  unfold mutex_del_refresh_choice_prop in H1.
  destruct H1 as [Hchoice_prio Hchoice_tcb].
  rewrite Hrdy_grp, Hrdy_tbl, Hprio_high, Htcb_high, Hprio_tbl.
  rewrite Hrdy_grp, Hrdy_tbl, Hprio_high, Htcb_high, Hprio_tbl in H.
  rewrite Hchoice_tcb, Hchoice_prio.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - unfold mutex_del_refresh_prio_tbl_values.
    repeat progress cancel.
    sepcon_assoc_change.
    apply mutex_del_refresh_spatial_framed_closed__g02_refresh_close.
    exact H0.
Qed.

Lemma proof_of_OSMutexDel_RefreshHighReady_which_implies_wit_11 : OSMutexDel_RefreshHighReady_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_restore_rep.
  apply mutex_del_refresh_closed_full.
Qed.

Lemma proof_of_OSMutexDel_full_safety_wit_3 : OSMutexDel_full_safety_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_ushort_range
       (&((pevent) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros_p Hecnt.
  split_pures.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_OSMutexDel_full_safety_wit_7 : OSMutexDel_full_safety_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_ushort_range
       (&((pevent) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros_p Hecnt.
  split_pures.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_OSMutexDel_full_safety_wit_10 : OSMutexDel_full_safety_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_ushort_range
       (&((pevent) # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  Intros_p Hecnt.
  split_pures.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_1 : OSMutexDel_full_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst etype pevent_pre pd opt_pre.
  pose proof
    (mutex_del_owner_lineage_decode__g03_owner_entry
       e ecnt_in pcp_idx owner_orig H8) as Hdecode.
  destruct Hdecode as [Hpcp [Howner_orig Hcanonical]].
  unfold mutex_del_return_lineage_prop.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel.
    unfold derivable1.
    intros.
    exact I.
  - split_pures.
    all: dump_pre_spatial;
      repeat first [assumption | reflexivity | split].
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_2_1 : OSMutexDel_full_entail_wit_2_1.
Proof.
  unfold OSMutexDel_full_entail_wit_2_1.
  left; intros.
  unfold mutex_del_event_focus_inv,
    mutex_del_event_inv_no_eid_no_free_head.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_uchar_range
       (&((pe) # "os_event" ->ₛ "OSEventGrp")) egrp_in).
  Intros_p Hegrp_range.
  pose proof
    (mutex_del_owner_lineage_decode__g03_owner_entry
       e ecnt_in pcp_idx owner_orig H3) as Hdecode.
  destruct Hdecode as [Hpcp [Howner_orig Hcanonical]].
  assert (Hsource : mutex_del_source_entry_prop sg e ls0 eid pe 1).
  {
    eapply
      mutex_del_source_entry_from_focus_facts__g03_owner_entry.
    - exact H15.
    - exact H11.
    - exact PreH6.
    - exact H5.
    - lia.
    - reflexivity.
    - exact H3.
    - right. split; [exact PreH1 | reflexivity].
    - change (0 <= egrp_in <= 255) in Hegrp_range.
      exact Hegrp_range.
  }
  subst etype.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel.
    unfold derivable1.
    intros.
    exact I.
  - split_pures.
    all: dump_pre_spatial;
      repeat first [assumption | reflexivity | split].
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_2_2 : OSMutexDel_full_entail_wit_2_2.
Proof.
  unfold OSMutexDel_full_entail_wit_2_2.
  left; intros.
  unfold mutex_del_event_focus_inv,
    mutex_del_event_inv_no_eid_no_free_head.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_uchar_range
       (&((pe) # "os_event" ->ₛ "OSEventGrp")) egrp_in).
  Intros_p Hegrp_range.
  pose proof
    (mutex_del_owner_lineage_decode__g03_owner_entry
       e ecnt_in pcp_idx owner_orig H3) as Hdecode.
  destruct Hdecode as [Hpcp [Howner_orig Hcanonical]].
  assert (Hsource : mutex_del_source_entry_prop sg e ls0 eid pe 0).
  {
    eapply
      mutex_del_source_entry_from_focus_facts__g03_owner_entry.
    - exact H15.
    - exact H11.
    - exact PreH6.
    - exact H5.
    - lia.
    - reflexivity.
    - exact H3.
    - left. split; [exact PreH1 | reflexivity].
    - change (0 <= egrp_in <= 255) in Hegrp_range.
      exact Hegrp_range.
  }
  subst etype.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel.
    unfold derivable1.
    intros.
    exact I.
  - split_pures.
    all: dump_pre_spatial;
      repeat first [assumption | reflexivity | split].
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_3_1 : OSMutexDel_full_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstage :
    mutex_del_rdyatprio_stage_prop sg e ls0 ls_rdy).
  {
    eapply mutex_del_owner_call_snapshot_refines_owner_stage
      with
        (owner_ptr := eptr_in)
        (owner_tid := owner_tid)
        (owner_t := owner_t)
        (owner_prio := owner_prio)
        (prio_addr := &((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
        (ecnt := ecnt_in)
        (pcp := unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
        (owner_orig := Z.land ecnt_in 255);
      eauto.
  }
  pose proof
    (mutex_del_no_pend_zero_facts__g03_owner_entry
       sg e ls0 eid pevent tasks_v ecnt_in eptr_in egrp_in evtL_in
       opt_in opt_abs H5 H8 PreH10 H0 PreH18) as Hzero.
  destruct Hzero as [Hegrp [Hsnapshot0 [Hsuccess Hno_pend]]].
  subst egrp_in.
  unfold mutex_del_owner_stage_focus.
  Exists ls_rdy.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (InsideCritical sg ls_rdy).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls_rdy eid).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventPtr") # Ptr |-> eptr_in).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventGrp") # UChar |-> 0).
    cancel (used_event_wait_table_storage (ls0.(TskState)) pevent e).
    cancel ((&("OSEventFreeList")) # Ptr |-> freelist_in).
    cancel (perr # UChar |-> perr_in).
    cancel.
    unfold derivable1.
    intros.
    exact I.
  - split_pures.
    all: dump_pre_spatial;
      repeat first [assumption | reflexivity | split].
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_3_2 : OSMutexDel_full_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstage :
    mutex_del_rdyatprio_stage_prop sg e ls0 ls0).
  {
    eapply mutex_del_owner_mismatch_refines_owner_stage
      with
        (owner_ptr := eptr_in)
        (owner_tid := owner_tid)
        (owner_t := owner_t)
        (owner_prio := owner_prio)
        (prio_addr := &((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
        (ecnt := ecnt_in)
        (pcp := unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
        (owner_orig := Z.land ecnt_in 255);
      eauto.
  }
  pose proof
    (mutex_del_owner_snapshot_nonnull_components
       sg ls0 e eptr_in owner_tid owner_t owner_prio
       (&((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio")) PreH3 H14)
    as [Hsnapshot_owner Hlayout_owner].
  sep_apply_l_atomic
    (mutex_del_event_owner_open_merge_physical__g03_owner_entry
       sg ls0 eid owner_tid owner_t eptr_in owner_prio
       (&((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
       Hsnapshot_owner Hlayout_owner).
  sep_apply_l_atomic
    (mutex_del_event_focus_to_ready_identity__g03_owner_entry
       sg ls0 eid).
  pose proof
    (mutex_del_no_pend_zero_facts__g03_owner_entry
       sg e ls0 eid pevent tasks_v ecnt_in eptr_in egrp_in evtL_in
       opt_in opt_abs H6 H9 PreH5 H0 PreH13) as Hzero.
  destruct Hzero as [Hegrp [Hsnapshot0 [Hsuccess Hno_pend]]].
  subst egrp_in.
  unfold mutex_del_owner_stage_focus.
  Exists ls0.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (InsideCritical sg ls0).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls0 eid).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventPtr") # Ptr |-> eptr_in).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventGrp") # UChar |-> 0).
    cancel (used_event_wait_table_storage (ls0.(TskState)) pevent e).
    cancel ((&("OSEventFreeList")) # Ptr |-> freelist_in).
    cancel (perr # UChar |-> perr_in).
    cancel.
    unfold derivable1.
    intros.
    exact I.
  - split_pures.
    all: dump_pre_spatial;
      repeat first [assumption | reflexivity | split].
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_3_3 : OSMutexDel_full_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstage :
    mutex_del_rdyatprio_stage_prop sg e ls0 ls0).
  {
    rewrite PreH1 in H6.
    eapply mutex_del_owner_null_refines_owner_stage
      with
        (owner_tid := owner_tid)
        (owner_t := owner_t)
        (owner_prio := owner_prio)
        (prio_addr := &((0) # "os_tcb" ->ₛ "OSTCBPrio"));
      exact H6.
  }
  sep_apply_l_atomic
    (mutex_del_event_focus_to_ready_identity__g03_owner_entry
       sg ls0 eid).
  pose proof
    (mutex_del_no_pend_zero_facts__g03_owner_entry
       sg e ls0 eid pevent tasks_v ecnt_in eptr_in egrp_in evtL_in
       opt_in opt_abs H7 H10 PreH3 H0 PreH11) as Hzero.
  destruct Hzero as [Hegrp [Hsnapshot0 [Hsuccess Hno_pend]]].
  subst egrp_in.
  unfold mutex_del_owner_stage_focus.
  Exists ls0.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (InsideCritical sg ls0).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls0 eid).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventPtr") # Ptr |-> eptr_in).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventGrp") # UChar |-> 0).
    cancel (used_event_wait_table_storage (ls0.(TskState)) pevent e).
    cancel ((&("OSEventFreeList")) # Ptr |-> freelist_in).
    cancel (perr # UChar |-> perr_in).
    cancel.
    unfold derivable1.
    intros.
    exact I.
  - split_pures.
    all: dump_pre_spatial;
      repeat first [assumption | reflexivity | split].
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_4_1 : OSMutexDel_full_entail_wit_4_1.
Proof.
  unfold OSMutexDel_full_entail_wit_4_1.
  left; intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pureIntros.
  match goal with
  | Hx : mutex_del_source_entry_prop
      sg e ls0 eid pevent tasks_v |- _ => pose proof Hx as Hsource0
  end.
  match goal with
  | Hx : mutex_del_no_pend_mode_prop opt_abs tasks_v |- _ =>
      pose proof Hx as Hno_pend0
  end.
  match goal with
  | Hx : mutex_del_rdyatprio_stage_prop sg e ls0 owner_post |- _ =>
      pose proof Hx as Hstage
  end.
  match goal with
  | Hx : event_snapshot_of_prop
      sg ls0.(TskState) ls0.(EventState) eid e
      4 ecnt_in eptr_in 0 evtL_in |- _ =>
      pose proof Hx as Hsnapshot_entry
  end.
  match goal with
  | Hx : event_free_list_head_prop
      sg ls0.(EventState) freelist_in |- _ => pose proof Hx as Hhead_entry
  end.
  match goal with
  | Hx : mutex_del_owner_value_lineage_prop
      e ecnt_in pcp_v prio_v |- _ => pose proof Hx as Hlineage0
  end.
  match goal with
  | Hx : mutex_del_refresh_context_prop sg _ _ _ _ _ |- _ =>
      pose proof Hx as Hrefresh0
  end.
  match goal with
  | Hx : os_tcb_prio_tbl_addr sg ?prio_tbl_addr |- _ =>
      pose proof Hx as Hprio_tbl_addr
  end.
  match goal with
  | Hx : event_core_fields_layout_prop sg eid ?type_addr ?ptr_addr ?cnt_addr |- _ =>
      pose proof Hx as Hcore_layout
  end.
  unfold event_core_fields_layout_prop in Hcore_layout.
  destruct Hcore_layout as [Htype_addr [Hptr_addr Hcnt_addr]].
  rewrite <- PreH2 in Htype_addr, Hptr_addr.
  pose proof Hsource0 as Hsource_shape.
  unfold mutex_del_source_entry_prop in Hsource_shape.
  destruct Hsource_shape as
    [_ [_ [_ [_ [_ [_ [Htasks_shape _]]]]]]].
  unfold mutex_del_no_pend_mode_prop in Hno_pend0.
  destruct Hno_pend0 as [_ Htasks0].
  unfold mutex_del_tasks_waiting_prop in Htasks_shape.
  destruct Htasks_shape as [[_ Hempty] | [Htasks1 _]]; [|lia].
  pose proof Hsnapshot_entry as Hsnapshot_fields.
  unfold event_snapshot_of_prop in Hsnapshot_fields.
  destruct Hsnapshot_fields as
    [Hused [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  pose proof
    (mutex_del_owner_stage_empty_event_noninterference__g03_owner_entry
       sg e ls0 owner_post eid Hused Hempty Hstage) as Hnoninterference.
  pose proof
    (mutex_del_selected_event_snapshot_transport
       sg eid ls0 owner_post e 4 ecnt_in eptr_in 0 evtL_in
       Hnoninterference Hsnapshot_entry) as Hsnapshot_post.
  pose proof
    (mutex_del_selected_event_wait_table_storage_eq
       eid ls0 owner_post e pevent Hnoninterference Hused)
    as Hstorage.
  assert (Hhead_post :
    event_free_list_head_prop sg owner_post.(EventState) freelist_in).
  {
    eapply mutex_del_owner_wake_free_head_transport
      with (eid := eid) (owner_post := owner_post) (current := owner_post).
    - exact Hhead_entry.
    - exact Hstage.
    - constructor.
  }
  pose proof
    (mutex_del_owner_lineage_decode__g03_owner_entry
       e ecnt_in pcp_v prio_v Hlineage0) as Hdecode.
  destruct Hdecode as [Hpcp [_ _]].
  unfold mutex_del_refresh_context_prop in Hrefresh0.
  destruct Hrefresh0 as [Hvalid _].
  unfold valid_stable_glob_vars in Hvalid.
  do 8 (destruct Hvalid as [_ Hvalid]).
  destruct Hvalid as [Hceil _].
  assert (Hrelease : Z.eqb pcp_v sg.(osPrioMutexCeilDis) = false).
  { apply Z.eqb_neq. rewrite Hceil. exact PreH1. }
  unfold os_tcb_prio_tbl_addr in Hprio_tbl_addr.
  unfold mutex_del_no_pend_pcp_release_residual.
  Exists owner_post e evtL_in.
  unfold mutex_del_pcp_release_focus.
  rewrite Hrelease.
  unfold priotbl_element_store.
  rewrite <- Hprio_tbl_addr.
  rewrite Hstorage.
  rewrite <- Htype.
  rewrite Htype_addr, Hptr_addr.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (InsideCritical sg owner_post).
    cancel (mutex_del_event_missing_priotbl_focus
      sg ls0 owner_post eid pcp_v).
    cancel (((&("OSTCBPrioTbl")) + pcp_v * sizeof(PTR)) # Ptr |-> 0).
    cancel ((pevent + OSEventType_off) # UChar |-> 4).
    cancel ((pevent + OSEventPtr_off) # Ptr |-> eptr_in).
    sep_apply_l_atomic
      (store_uchar_undef_store_uchar (&("prio")) prio_v).
    sep_apply_l_atomic
      (store_ptr_undef_store_ptr (&("ptcb")) ptcb_v).
    cancel (perr # UChar |-> perr_in).
    cancel ((&("OSEventFreeList")) # Ptr |-> freelist_in).
    cancel (used_event_wait_table_storage (ls0.(TskState)) pevent e).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventGrp") # UChar |-> 0).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel.
    unfold derivable1. intros. exact I.
  - split_pures.
    all: dump_pre_spatial;
      repeat first [assumption | reflexivity | split].
    all: now rewrite PreH2.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_4_2 : OSMutexDel_full_entail_wit_4_2.
Proof.
  unfold OSMutexDel_full_entail_wit_4_2.
  left; intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pureIntros.
  match goal with
  | Hx : mutex_del_source_entry_prop
      sg e ls0 eid pevent tasks_v |- _ => pose proof Hx as Hsource0
  end.
  match goal with
  | Hx : event_snapshot_of_prop
      sg ls0.(TskState) ls0.(EventState) eid e
      4 ecnt_in eptr_in egrp_in evtL_in |- _ =>
      pose proof Hx as Hsnapshot_entry
  end.
  match goal with
  | Hx : mutex_del_option_decode_prop opt_in opt_abs |- _ =>
      pose proof Hx as Hdecode0
  end.
  match goal with
  | Hx : mutex_del_owner_snapshot_prop
      sg ls0 e eptr_in owner_tid owner_t owner_prio _ |- _ =>
      pose proof Hx as Howner0
  end.
  match goal with
  | Hx : mutex_del_owner_value_lineage_prop
      e ecnt_in (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
        (Z.land ecnt_in 255) |- _ =>
      pose proof Hx as Hlineage0
  end.
  match goal with
  | Hx : event_core_fields_layout_prop sg eid ?type_addr ?ptr_addr ?cnt_addr |- _ =>
      pose proof Hx as Hcore_layout
  end.
  unfold event_core_fields_layout_prop in Hcore_layout.
  destruct Hcore_layout as [Htype_addr [Hptr_addr Hcnt_addr]].
  rewrite <- PreH6 in Htype_addr, Hptr_addr.
  pose proof
    (mutex_del_no_pend_zero_facts__g03_owner_entry
       sg e ls0 eid pevent tasks_v ecnt_in eptr_in egrp_in evtL_in
       opt_in opt_abs Hsource0 Hsnapshot_entry PreH2 Hdecode0 PreH10)
    as Hzero.
  destruct Hzero as [Hegrp [Hsnapshot0 [Hsuccess Hno_pend]]].
  subst egrp_in.
  assert (Hstage : mutex_del_rdyatprio_stage_prop sg e ls0 ls0).
  {
    eapply mutex_del_owner_disabled_snapshot_identity
      with
        (owner_ptr := eptr_in)
        (owner_tid := owner_tid)
        (owner_t := owner_t)
        (owner_prio := owner_prio)
        (prio_addr := &((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
        (ecnt := ecnt_in)
        (pcp := unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
        (owner_orig := Z.land ecnt_in 255);
      assumption.
  }
  pose proof Howner0 as Howner_ceil.
  unfold mutex_del_owner_snapshot_prop in Howner_ceil.
  destruct Howner_ceil as [Hceil _].
  assert (Hrelease :
    Z.eqb (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8)
      sg.(osPrioMutexCeilDis) = true).
  { apply Z.eqb_eq. rewrite Hceil. exact PreH1. }
  pose proof Hsnapshot0 as Hsnapshot_fields.
  unfold event_snapshot_of_prop in Hsnapshot_fields.
  destruct Hsnapshot_fields as
    [Hused [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  sep_apply_l_atomic
    (mutex_del_event_focus_to_ready_identity__g03_owner_entry
       sg ls0 eid).
  unfold mutex_del_no_pend_pcp_release_residual.
  Exists ls0 e evtL_in.
  unfold mutex_del_pcp_release_focus.
  rewrite Hrelease.
  rewrite <- Htype.
  rewrite Htype_addr, Hptr_addr.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (InsideCritical sg ls0).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls0 eid).
    cancel ((pevent + OSEventType_off) # UChar |-> 4).
    cancel ((pevent + OSEventPtr_off) # Ptr |-> eptr_in).
    cancel (used_event_wait_table_storage (ls0.(TskState)) pevent e).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&((pevent) # "os_event" ->ₛ "OSEventGrp") # UChar |-> 0).
    cancel ((&("OSEventFreeList")) # Ptr |-> freelist_in).
    cancel (perr # UChar |-> perr_in).
    cancel.
    unfold derivable1. intros. exact I.
  - split_pures.
    all: dump_pre_spatial;
      repeat first [assumption | reflexivity | split].
    all: now rewrite PreH6.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_5 : OSMutexDel_full_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sepcon_lift
    (mutex_del_pcp_release_focus sg ls0 owner_post eid pcp_v).
  prop_apply
    (mutex_del_pcp_release_focus_validity__g04_no_pend_errors
       sg ls0 owner_post eid pcp_v).
  Intros_p Hvalidity.
  pose proof H1 as Hreturn.
  unfold mutex_del_return_lineage_prop in Hreturn.
  repeat lazymatch type of Hreturn with
    | _ /\ _ => destruct Hreturn as [_ Hreturn]
    end.
  unfold mutex_del_owner_value_lineage_prop in Hreturn.
  destruct Hreturn as
    (m & Hmtype & Hmfields & Hdecode & Howner_decode & Hmpcp & Hshape).
  pose proof H8 as Hsource.
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as
    (Hbase & Hvalid_eid & Hentry & Hstype & [m0 Hsfields] &
     Hintr & Hwaiting & Hentry_owner).
  rewrite Hmfields in Hsfields. inversion Hsfields; subst m0.
  pose proof H9 as Hsnapshot.
  unfold event_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as
    (Hcurrent & Hold_type & Hcnt & Hptr & Hgrp & Htbl).
  destruct
    (mutex_del_owner_stage_preserves_selected_mutex_fields__g04_no_pend_errors
       sg e ls0 owner_post eid m Hentry Hstype Hmfields H11)
    as (epost & Hpost & Hcurrent_type & Hcurrent_fields).
  rewrite Hcurrent in Hpost. inversion Hpost; subst epost.
  pose proof Hvalidity as Hvalid_parts.
  unfold UCOS2_validity_bundle in Hvalid_parts.
  destruct Hvalid_parts as (Htask & Hsched & Hevent & Hcross).
  assert (Hcanonical :
    Ucos2Verify.lib.event_wait.event_waitList_canonical
      sg owner_post.(TskState) current_event.(waitList)).
  {
    unfold event_vaild_cond_prop, valid_GlobEventAbstractState,
      event_in_range in Hevent.
    destruct Hevent as (_ & _ & _ & _ & _ & _ & _ & Hentries).
    exact (proj1 (Hentries eid current_event Hcurrent)).
  }
  assert (Hempty : current_event.(waitList) = nil).
  {
    apply
      (proj1
        (mutex_del_wait_grp_zero_iff_empty__g04_no_pend_errors
           sg owner_post.(TskState) current_event.(waitList) Hcanonical)).
    symmetry. exact Hgrp.
  }
  assert (Hmpcp_pcp : m.(mfPCP) = pcp_v) by congruence.
  assert (Hno_live :
    no_live_task_at_priority owner_post.(TskState) pcp_v).
  {
    rewrite <- Hmpcp_pcp.
    exact
      (mutex_del_owner_stage_no_live_total__g04_no_pend_errors
         sg e ls0 owner_post eid current_event m
         Hcurrent Hcurrent_type Hcurrent_fields Hstype Hmfields
         Hentry_owner H11 Hvalidity).
  }
  set (commit :=
    mutex_del_free_commit_after__g04_no_pend_errors
      sg eid pcp_v owner_post).
  assert (Hcommit_valid : UCOS2_validity_bundle sg commit).
  {
    unfold commit.
    rewrite <- Hmpcp_pcp.
    apply
      (mutex_del_owner_stage_commit_validity__g04_no_pend_errors
         sg e ls0 owner_post eid current_event m
         Hstype Hmfields Hcurrent Hcurrent_type Hcurrent_fields
         Hentry_owner H11 Hempty).
    - rewrite Hmpcp_pcp. exact Hno_live.
    - exact Hvalidity.
  }
  destruct
    (mutex_del_prepare_and_free_stage__g04_no_pend_errors
       sg owner_post eid current_event m
       Hcurrent Hcurrent_type Hcurrent_fields Hempty)
    as (prepare & Hprepare & Hfree).
  assert (Hfree_commit :
    mutex_del_free_stage_prop sg eid prepare commit).
  {
    unfold commit. rewrite <- Hmpcp_pcp. exact Hfree.
  }
  unfold mutex_del_no_pend_mode_prop in H7.
  destruct H7 as [Hopt Htasks]. subst opt_abs.
  assert (Hanchor :
    mutex_del_success_commit_anchor_prop
      sg e ls0 eid MutexDelNoPend owner_post commit).
  {
    unfold mutex_del_success_commit_anchor_prop.
    exists owner_post, prepare.
    split; [exact H11|].
    split.
    - unfold mutex_del_mode_wake_prop. reflexivity.
    - split; assumption.
  }
  assert (Hlineage :
    mutex_del_owner_value_lineage_prop
      e ecnt_in pcp_v (decode_OwnerPrio_from_cnt ecnt_in)).
  {
    unfold mutex_del_owner_value_lineage_prop.
    exists m.
    split; [exact Hmtype|].
    split; [exact Hmfields|].
    split; [exact PreH1|].
    split; [reflexivity|].
    split; [exact Hmpcp_pcp|].
    exact Hshape.
  }
  assert (Hrange :
    Z.eqb pcp_v sg.(osPrioMutexCeilDis) = false ->
    priotbl_index_in_range pcp_v).
  {
    intro Henabled.
    assert (Hneq255 : pcp_v <> 255).
    {
      pose proof H3 as Hr.
      unfold mutex_del_refresh_context_prop in Hr.
      destruct Hr as [Hstable _].
      unfold valid_stable_glob_vars in Hstable.
      destruct Hstable as
        (_ & _ & _ & _ & _ & _ & _ & _ & Hdisabled & _).
      apply Z.eqb_neq in Henabled.
      rewrite Hdisabled in Henabled.
      exact Henabled.
    }
    assert (Hrng : 0 <= pcp_v /\ pcp_v < 64).
    {
      eapply
        mutex_del_owner_stage_enabled_pcp_range__g04_no_pend_errors.
      - exact H3.
      - exact H8.
      - exact Hlineage.
      - exact H11.
      - exact Hcross.
      - exact Hneq255.
    }
    unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE.
    exact Hrng.
  }
  pose proof H10 as Hfree_head.
  unfold event_free_list_head_prop in Hfree_head.
  unfold os_event_free_list_addr in H4.
  rewrite H4.
  sep_apply_l_atomic
    (mutex_del_pcp_release_freed_raw_ready_fold__g04_no_pend_errors
       sg ls0 owner_post eid pcp_v current_event pevent
       (&((pevent) # "os_event" ->ₛ "OSEventType"))
       (&((pevent) # "os_event" ->ₛ "OSEventPtr"))
       (&((pevent) # "os_event" ->ₛ "OSEventCnt"))
       (&((pevent) # "os_event" ->ₛ "OSEventGrp"))
       (&((pevent) # "os_event" ->ₛ "OSEventTbl"))
       freelist_in Hvalidity Hrange Hbase H6 H5 Hfree_head).
  fold commit.
  assert (Htransition :
    UCOS2_raw_ready_prio_stage sg ls0 commit |--
    mutex_del_transition_rep sg ls0 commit).
  {
    unfold mutex_del_transition_rep.
    Right.
    apply _derivable1_andp_intros.
    - Right.
      cancel (UCOS2_raw_ready_prio_stage sg ls0 commit).
    - apply derivable1s_coq_prop_r. exact Hcommit_valid.
  }
  sep_apply_l_atomic Htransition.
  assert (Hsuccess_mode :
    mutex_del_success_mode_prop MutexDelNoPend tasks_v).
  { unfold mutex_del_success_mode_prop. exact Htasks. }
  assert (Hno_pend_mode :
    mutex_del_no_pend_mode_prop MutexDelNoPend tasks_v).
  {
    unfold mutex_del_no_pend_mode_prop.
    split; [reflexivity|exact Htasks].
  }
  unfold mutex_del_success_commit_inv.
  Exists owner_post commit.
  split_pure_spatial.
  - cancel (InsideCritical sg owner_post).
    cancel (mutex_del_transition_rep sg ls0 commit).
    cancel (perr # UChar |-> perr_in).
    andp_cancel.
    apply derivable1_truep_intros.
  - split_pures.
    all: dump_pre_spatial.
    all: try (first
      [ exact H1
      | exact H3
      | exact Hanchor
      | exact H8
      | exact Hsuccess_mode
      | exact H2
      | exact PreH2
      | exact Hno_pend_mode ]).
    split; [exact Hanchor|].
    split; [exact H8|].
    split; [exact Hsuccess_mode|].
    exact H2.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_6 : OSMutexDel_full_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists perr_in.
  unfold mutex_del_no_pend_exit_inv.
  Exists critical_anchor ls_commit ls2.
  unfold mutex_del_restore_rep; simpl.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls2).
    cancel (UCOS2_Verify_inv sg ls2).
    cancel (perr # UChar |-> perr_in).
    andp_cancel.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial.
      exact
        (conj H4
          (conj H3
            (conj H
              (conj H6 (conj (proj1 H5) H1))))).
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_7 : OSMutexDel_full_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_unchanged_inside_inv.
  split_pure_spatial.
  - sep_apply_l_atomic
      (mutex_del_event_focus_merge
         sg ls0 eid e pevent
         (&((pevent) # "os_event" ->ₛ "OSEventType"))
         (&((pevent) # "os_event" ->ₛ "OSEventPtr"))
         (&((pevent) # "os_event" ->ₛ "OSEventCnt"))
         (&((pevent) # "os_event" ->ₛ "OSEventGrp"))
         (&((pevent) # "os_event" ->ₛ "OSEventTbl"))
         (&("OSEventFreeList"))
         4 ecnt_in eptr_in egrp_in evtL_in freelist_in
         H10 H9 H8 H3 H2 PreH5).
    cancel (InsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    cancel (perr # UChar |-> perr_in).
    andp_cancel.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial. exact H14.
    + dump_pre_spatial.
      split.
      * exact H7.
      * split.
        -- unfold mutex_del_error_mode_prop.
           left.
           split.
           ++ unfold mutex_del_option_decode_prop in H0.
              intuition subst; congruence.
           ++ split.
              ** unfold mutex_del_source_entry_prop in H7.
                 unfold mutex_del_tasks_waiting_prop in H7.
                 intuition subst; try int_auto.
              ** reflexivity.
        -- exact PreH2.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_8 : OSMutexDel_full_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists perr_in.
  unfold mutex_del_unchanged_exit_inv.
  Exists ls2.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls2).
    cancel (mutex_del_restore_rep false sg ls0 ls2).
    cancel (perr # UChar |-> perr_in).
    andp_cancel.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial.
      split; [exact H2 |].
      split; [exact H1 |].
      split; [exact H3 | exact H0].
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_9_1 : OSMutexDel_full_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstage :
    mutex_del_rdyatprio_stage_prop sg e ls0 ls_rdy).
  {
    eapply mutex_del_owner_call_snapshot_refines_owner_stage;
      eauto.
  }
  assert (Hfree :
    event_free_list_head_prop sg ls_rdy.(EventState) freelist_in).
  {
    unfold event_free_list_head_prop in H2 |- *.
    rewrite
      (mutex_del_rdyatprio_stage_preserves_unused_events
         sg e ls0 ls_rdy Hstage).
    exact H2.
  }
  assert (Hsnapshot :
    event_snapshot_of_prop sg ls_rdy.(TskState) ls_rdy.(EventState)
      eid e 4 ecnt_in eptr_in egrp_in evtL_in).
  {
    eapply mutex_del_selected_event_snapshot_transport;
      eauto.
  }
  pose proof H8 as Hsnapshot0.
  unfold event_snapshot_of_prop in Hsnapshot0.
  destruct Hsnapshot0 as [Hused _].
  pose proof
    (mutex_del_selected_event_wait_table_storage_eq
       eid ls0 ls_rdy e pevent H13 Hused) as Hstorage.
  assert (Hsuccess : mutex_del_success_mode_prop opt_abs tasks_v).
  {
    pose proof H0 as Hdecode.
    unfold mutex_del_option_decode_prop in Hdecode.
    destruct Hdecode as [[Hin Hopt] | [[Hin Hopt] | [Hin [Hne Hopt]]]];
      try lia.
    subst opt_abs.
    pose proof H5 as Hsource.
    unfold mutex_del_source_entry_prop in Hsource.
    destruct Hsource as [_ [_ [_ [_ [_ [_ [Hwaiting _]]]]]]].
    unfold mutex_del_tasks_waiting_prop in Hwaiting.
    unfold mutex_del_success_mode_prop.
    destruct Hwaiting as [[-> _] | [-> _]]; auto.
  }
  assert (Hopt_always : opt_abs = MutexDelAlways).
  {
    pose proof H0 as Hdecode.
    unfold mutex_del_option_decode_prop in Hdecode.
    destruct Hdecode as
      [[Hin Hopt] | [[Hin Hopt] | [Hin [Hne Hopt]]]].
    - lia.
    - exact Hopt.
    - lia.
  }
  assert (Halways : mutex_del_always_mode_prop opt_abs tasks_v).
  {
    unfold mutex_del_always_mode_prop.
    split; [exact Hopt_always|].
    rewrite Hopt_always in Hsuccess.
    unfold mutex_del_success_mode_prop in Hsuccess.
    exact Hsuccess.
  }
  Exists e evtL_in ls_rdy ls_rdy.
  rewrite Hstorage.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_uchar_undef_store_uchar
         (&( "prio" )) (Z.land ecnt_in 255)).
    sep_apply_l_atomic
      (store_ptr_undef_store_ptr (&( "ptcb" )) eptr_in).
    cancel (used_event_wait_table_storage
      ls0.(TskState) pevent e).
    cancel (&( "prio" ) # UChar |->_).
    cancel (&( "ptcb" ) # Ptr |->_).
    cancel (InsideCritical sg ls_rdy).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls_rdy eid).
    cancel (&( pevent # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&( pevent # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventPtr") # Ptr |-> eptr_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> egrp_in).
    cancel (perr # UChar |-> perr_in).
    cancel (&( "OSEventFreeList" ) # Ptr |-> freelist_in).
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - split_pures;
      dump_pre_spatial;
      try assumption.
    apply mutex_del_wake_steps_refl.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_9_2 : OSMutexDel_full_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstage : mutex_del_rdyatprio_stage_prop sg e ls0 ls0).
  {
    eapply mutex_del_owner_mismatch_refines_owner_stage.
    - exact PreH3.
    - exact H14.
    - exact H4.
    - exact PreH1.
  }
  assert (Hfree :
    event_free_list_head_prop sg ls0.(EventState) freelist_in).
  { exact H2. }
  assert (Hsuccess : mutex_del_success_mode_prop opt_abs tasks_v).
  {
    pose proof H0 as Hdecode.
    unfold mutex_del_option_decode_prop in Hdecode.
    destruct Hdecode as [[Hin Hopt] | [[Hin Hopt] | [Hin [Hne Hopt]]]];
      try lia.
    subst opt_abs.
    pose proof H6 as Hsource.
    unfold mutex_del_source_entry_prop in Hsource.
    destruct Hsource as [_ [_ [_ [_ [_ [_ [Hwaiting _]]]]]]].
    unfold mutex_del_tasks_waiting_prop in Hwaiting.
    unfold mutex_del_success_mode_prop.
    destruct Hwaiting as [[-> _] | [-> _]]; auto.
  }
  assert (Hopt_always : opt_abs = MutexDelAlways).
  {
    pose proof H0 as Hdecode.
    unfold mutex_del_option_decode_prop in Hdecode.
    destruct Hdecode as
      [[Hin Hopt] | [[Hin Hopt] | [Hin [Hne Hopt]]]].
    - lia.
    - exact Hopt.
    - lia.
  }
  assert (Halways : mutex_del_always_mode_prop opt_abs tasks_v).
  {
    unfold mutex_del_always_mode_prop.
    split; [exact Hopt_always|].
    rewrite Hopt_always in Hsuccess.
    unfold mutex_del_success_mode_prop in Hsuccess.
    exact Hsuccess.
  }
  sep_apply_l_atomic
    (mutex_del_event_owner_open_merge_pure__g05_always_loop
       sg ls0 eid e eptr_in owner_tid owner_t owner_prio
       (&( eptr_in # "os_tcb" ->ₛ "OSTCBPrio")) PreH3 H14).
  sep_apply_l_atomic
    (mutex_del_event_focus_to_ready_focus__g05_always_loop sg ls0 eid).
  Exists e evtL_in ls0 ls0.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_uchar_undef_store_uchar
         (&( "prio" )) (Z.land ecnt_in 255)).
    sep_apply_l_atomic
      (store_ptr_undef_store_ptr (&( "ptcb" )) eptr_in).
    cancel (used_event_wait_table_storage ls0.(TskState) pevent e).
    cancel (&( "prio" ) # UChar |->_).
    cancel (&( "ptcb" ) # Ptr |->_).
    cancel (InsideCritical sg ls0).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls0 eid).
    cancel (&( pevent # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&( pevent # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventPtr") # Ptr |-> eptr_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> egrp_in).
    cancel (perr # UChar |-> perr_in).
    cancel (&( "OSEventFreeList" ) # Ptr |-> freelist_in).
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - split_pures;
      dump_pre_spatial;
      try assumption.
    apply mutex_del_wake_steps_refl.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_9_3 : OSMutexDel_full_entail_wit_9_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst eptr_in.
  assert (Hstage : mutex_del_rdyatprio_stage_prop sg e ls0 ls0).
  {
    eapply mutex_del_owner_null_refines_owner_stage;
      eauto.
  }
  assert (Hfree :
    event_free_list_head_prop sg ls0.(EventState) freelist_in).
  { exact H2. }
  assert (Hsuccess : mutex_del_success_mode_prop opt_abs tasks_v).
  {
    match goal with
    | Hdecode : mutex_del_option_decode_prop _ opt_abs,
      Hsource : mutex_del_source_entry_prop sg e ls0 eid pevent tasks_v |- _ =>
        pose proof Hdecode as Hd;
        unfold mutex_del_option_decode_prop in Hd;
        destruct Hd as [[Hin Hopt] | [[Hin Hopt] | [Hin [Hne Hopt]]]];
          try lia;
        subst opt_abs;
        pose proof Hsource as Hs;
        unfold mutex_del_source_entry_prop in Hs;
        destruct Hs as [_ [_ [_ [_ [_ [_ [Hwaiting _]]]]]]];
        unfold mutex_del_tasks_waiting_prop in Hwaiting;
        unfold mutex_del_success_mode_prop;
        destruct Hwaiting as [[-> _] | [-> _]]; auto
    end.
  }
  assert (Hopt_always : opt_abs = MutexDelAlways).
  {
    match goal with
    | Hdecode : mutex_del_option_decode_prop _ opt_abs |- _ =>
        pose proof Hdecode as Hd;
        unfold mutex_del_option_decode_prop in Hd;
        destruct Hd as
          [[Hin Hopt] | [[Hin Hopt] | [Hin [Hne Hopt]]]];
        [lia | exact Hopt | lia]
    end.
  }
  assert (Halways : mutex_del_always_mode_prop opt_abs tasks_v).
  {
    unfold mutex_del_always_mode_prop.
    split; [exact Hopt_always|].
    rewrite Hopt_always in Hsuccess.
    unfold mutex_del_success_mode_prop in Hsuccess.
    exact Hsuccess.
  }
  sep_apply_l_atomic
    (mutex_del_event_focus_to_ready_focus__g05_always_loop sg ls0 eid).
  Exists e evtL_in ls0 ls0.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_uchar_undef_store_uchar
         (&( "prio" )) (Z.land ecnt_in 255)).
    sep_apply_l_atomic
      (store_ptr_undef_store_ptr (&( "ptcb" )) 0).
    cancel (used_event_wait_table_storage ls0.(TskState) pevent e).
    cancel (&( "prio" ) # UChar |->_).
    cancel (&( "ptcb" ) # Ptr |->_).
    cancel (InsideCritical sg ls0).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls0 eid).
    cancel (&( pevent # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&( pevent # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventPtr") # Ptr |-> 0).
    cancel (&( pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> egrp_in).
    cancel (perr # UChar |-> perr_in).
    cancel (&( "OSEventFreeList" ) # Ptr |-> freelist_in).
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - split_pures;
      dump_pre_spatial;
      try assumption.
    apply mutex_del_wake_steps_refl.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_9_4 : OSMutexDel_full_entail_wit_9_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstage : mutex_del_rdyatprio_stage_prop sg e ls0 ls0).
  {
    match goal with
    | Hsnapshot : mutex_del_owner_snapshot_prop
        sg ls0 e eptr_in owner_tid owner_t owner_prio ?prio_addr,
      Hlineage : mutex_del_owner_value_lineage_prop
        e ecnt_in ?pcp ?owner_orig |- _ =>
        eapply
          (mutex_del_owner_disabled_snapshot_identity
             sg ls0 e eptr_in owner_tid owner_t owner_prio prio_addr
             ecnt_in pcp owner_orig);
        [ exact Hsnapshot | exact Hlineage | lia ]
    end.
  }
  assert (Hfree :
    event_free_list_head_prop sg ls0.(EventState) freelist_in).
  { exact H2. }
  assert (Hsuccess : mutex_del_success_mode_prop opt_abs tasks_v).
  {
    match goal with
    | Hdecode : mutex_del_option_decode_prop _ opt_abs,
      Hsource : mutex_del_source_entry_prop sg e ls0 eid pevent tasks_v |- _ =>
        pose proof Hdecode as Hd;
        unfold mutex_del_option_decode_prop in Hd;
        destruct Hd as [[Hin Hopt] | [[Hin Hopt] | [Hin [Hne Hopt]]]];
          try lia;
        subst opt_abs;
        pose proof Hsource as Hs;
        unfold mutex_del_source_entry_prop in Hs;
        destruct Hs as [_ [_ [_ [_ [_ [_ [Hwaiting _]]]]]]];
        unfold mutex_del_tasks_waiting_prop in Hwaiting;
        unfold mutex_del_success_mode_prop;
        destruct Hwaiting as [[-> _] | [-> _]]; auto
    end.
  }
  assert (Hopt_always : opt_abs = MutexDelAlways).
  {
    match goal with
    | Hdecode : mutex_del_option_decode_prop _ opt_abs |- _ =>
        pose proof Hdecode as Hd;
        unfold mutex_del_option_decode_prop in Hd;
        destruct Hd as
          [[Hin Hopt] | [[Hin Hopt] | [Hin [Hne Hopt]]]];
        [lia | exact Hopt | lia]
    end.
  }
  assert (Halways : mutex_del_always_mode_prop opt_abs tasks_v).
  {
    unfold mutex_del_always_mode_prop.
    split; [exact Hopt_always|].
    rewrite Hopt_always in Hsuccess.
    unfold mutex_del_success_mode_prop in Hsuccess.
    exact Hsuccess.
  }
  sep_apply_l_atomic
    (mutex_del_event_focus_to_ready_focus__g05_always_loop sg ls0 eid).
  Exists e evtL_in ls0 ls0.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (used_event_wait_table_storage ls0.(TskState) pevent e).
    cancel (InsideCritical sg ls0).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls0 eid).
    cancel (&( pevent # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&( pevent # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventPtr") # Ptr |-> eptr_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> egrp_in).
    cancel (perr # UChar |-> perr_in).
    cancel (&( "OSEventFreeList" ) # Ptr |-> freelist_in).
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - split_pures;
      dump_pre_spatial;
      try assumption.
    apply mutex_del_wake_steps_refl.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_11 : OSMutexDel_full_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsteps :
    mutex_del_wake_steps sg eid ls_owner_cur_2 ls_r).
  {
    eapply mutex_del_wake_steps_snoc;
      eauto.
  }
  assert (Hfree :
    event_free_list_head_prop sg ls_r.(EventState) freelist_in).
  {
    match goal with
    | Hhead : event_free_list_head_prop
        sg ls_loop_2.(EventState) freelist_in,
      Hstep : mutex_del_wake_step sg eid ls_loop_2 ls_r |- _ =>
        unfold event_free_list_head_prop in Hhead |- *;
        rewrite (mutex_del_wake_step_preserves_unused_events
                   sg eid ls_loop_2 ls_r Hstep);
        exact Hhead
    end.
  }
  Exists e_r egrp_out evtL_out ls_owner_cur_2 ls_r.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (InsideCritical sg ls_r).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls_r eid).
    cancel (&( pevent # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&( pevent # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventPtr") # Ptr |-> eptr_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> egrp_out).
    cancel (used_event_wait_table_storage ls_r.(TskState) pevent e_r).
    cancel (perr # UChar |-> perr_in).
    cancel (&( "OSEventFreeList" ) # Ptr |-> freelist_in).
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - split_pures;
      dump_pre_spatial;
      try assumption.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_12 : OSMutexDel_full_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_uchar_range
       (&( pevent # "os_event" ->ₛ "OSEventGrp")) egrp_loop).
  Intros_p Hegrp_range.
  change (0 <= egrp_loop <= 255) in Hegrp_range.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= egrp_loop < 4294967296); lia).
  subst egrp_loop.
  assert (Hetype : encode_event_type e_loop.(eventType) = 4).
  {
    match goal with
    | Hsnapshot : event_snapshot_of_prop
        sg ls_loop.(TskState) ls_loop.(EventState) eid e_loop
        4 ecnt_in eptr_in 0 evtL_loop |- _ =>
        pose proof Hsnapshot as Hsnapshot0;
        unfold event_snapshot_of_prop in Hsnapshot0;
        destruct Hsnapshot0 as [_ [Htype _]];
        symmetry;
        exact Htype
    end.
  }
  match goal with
  | Hsnapshot : event_snapshot_of_prop
      sg ls_loop.(TskState) ls_loop.(EventState) eid e_loop
      4 ecnt_in eptr_in 0 evtL_loop |- _ =>
      pose proof Hsnapshot as Hsnapshot_parts
  end.
  unfold event_snapshot_of_prop in Hsnapshot_parts.
  destruct Hsnapshot_parts as
    [Hused [Htype_part [Hcnt_part [Hptr_part [Hgrp_part Htbl_part]]]]].
  match goal with
  | Hcore : event_core_fields_layout_prop sg eid ?ta ?pa ?ca |- _ =>
      pose proof Hcore as Hcore0
  end.
  unfold event_core_fields_layout_prop in Hcore0.
  destruct Hcore0 as [Htype_addr [Hptr_addr Hcnt_addr]].
  rewrite <- PreH2 in Htype_addr, Hptr_addr, Hcnt_addr.
  unfold mutex_del_abort_loop_residual.
  Exists ls_owner_cur ls_loop e_loop evtL_loop.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (InsideCritical sg ls_loop).
    cancel (mutex_del_event_ready_focus_inv sg ls0 ls_loop eid).
    rewrite <- Htype_addr, <- Hptr_addr.
    rewrite Hetype.
    cancel (&( pevent # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    cancel (&( pevent # "os_event" ->ₛ "OSEventPtr") # Ptr |-> eptr_in).
    cancel (used_event_wait_table_storage ls_loop.(TskState) pevent e_loop).
    cancel (&( pevent # "os_event" ->ₛ "OSEventCnt") # UShort |-> ecnt_in).
    cancel (&( pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> 0).
    cancel (perr # UChar |-> perr_in).
    cancel (&( "OSEventFreeList" ) # Ptr |-> freelist_in).
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - split_pures;
      dump_pre_spatial;
      try assumption;
      try (rewrite Hetype; assumption).
    repeat split; try assumption.
    all: try (rewrite Hetype; assumption).
    all: try reflexivity.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_13_1 : OSMutexDel_full_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hvalid : valid_stable_glob_vars sg).
  {
    match goal with
    | Hrefresh : mutex_del_refresh_context_prop sg _ _ _ _ _ |- _ =>
        unfold mutex_del_refresh_context_prop in Hrefresh;
        tauto
    end.
  }
  assert (Hceil : sg.(osPrioMutexCeilDis) = 255).
  {
    unfold valid_stable_glob_vars in Hvalid;
    tauto.
  }
  match goal with
  | Htbl : os_tcb_prio_tbl_addr sg ?p |- _ =>
      pose proof Htbl as Htbl_addr
  end.
  unfold os_tcb_prio_tbl_addr in Htbl_addr.
  unfold mutex_del_abort_loop_pcp_release_residual.
  rewrite Hceil.
  assert (Hneqb :
    Z.eqb (unsigned_last_nbits (Z.shiftr ecnt_in 8) 8) 255 = false).
  { apply Z.eqb_neq. exact PreH1. }
  rewrite Hneqb.
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  rewrite <- Htbl_addr.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_13_2 : OSMutexDel_full_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hvalid : valid_stable_glob_vars sg).
  {
    match goal with
    | Hrefresh : mutex_del_refresh_context_prop sg _ _ _ _ _ |- _ =>
        unfold mutex_del_refresh_context_prop in Hrefresh;
        tauto
    end.
  }
  assert (Hceil : sg.(osPrioMutexCeilDis) = 255).
  {
    unfold valid_stable_glob_vars in Hvalid;
    tauto.
  }
  unfold mutex_del_abort_loop_pcp_release_residual.
  rewrite Hceil, PreH1, Z.eqb_refl.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_14 : OSMutexDel_full_entail_wit_14.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (mutex_del_pcp_release_focus_expose_validity__g05_always_loop
      sg ls0 current eid pcp_v).
  pureIntros.
  match goal with
  | H : UCOS2_validity_bundle sg current |- _ =>
      rename H into Hvalid
  end.
  match goal with
  | H : mutex_del_rdyatprio_stage_prop sg e ls0 owner_post |- _ =>
      rename H into Howner_stage
  end.
  match goal with
  | H : mutex_del_wake_steps sg eid owner_post current |- _ =>
      rename H into Hwake_steps
  end.
  match goal with
  | H : event_snapshot_of_prop
      sg current.(TskState) current.(EventState) eid current_event
      old_type ecnt_in eptr_in 0 current_tbl |- _ =>
      rename H into Hsnapshot
  end.
  match goal with
  | H : mutex_del_source_entry_prop
      sg e ls0 eid pevent tasks_v |- _ =>
      rename H into Hsource
  end.
  match goal with
  | H : mutex_del_success_mode_prop opt_abs tasks_v |- _ =>
      rename H into Hmode
  end.
  match goal with
  | H : mutex_del_always_mode_prop opt_abs tasks_v |- _ =>
      rename H into Halways
  end.
  match goal with
  | H : event_core_fields_layout_prop
      sg eid _ _ _ |- _ =>
      rename H into Hcore_layout
  end.
  match goal with
  | H : event_wait_fields_layout_prop
      sg eid _ _ |- _ =>
      rename H into Hwait_layout
  end.
  match goal with
  | H : os_event_free_list_addr sg _ |- _ =>
      rename H into Hfree_addr
  end.
  match goal with
  | H : event_free_list_head_prop
      sg current.(EventState) freelist_in |- _ =>
      rename H into Hfree_head
  end.
  match goal with
  | H : mutex_del_refresh_context_prop sg _ _ _ _ _ |- _ =>
      rename H into Hrefresh
  end.
  match goal with
  | H : mutex_del_return_lineage_prop
      sg e ls0 eid pe pd pevent perr pevent_pre perr_pre
      etype isr opt_in opt_abs ecnt_in eptr_in egrp_in evtL_in |- _ =>
      rename H into Hlineage
  end.
  assert (Hstable : valid_stable_glob_vars sg).
  {
    unfold mutex_del_refresh_context_prop in Hrefresh.
    tauto.
  }
  pose proof Hsource as Hsource0.
  unfold mutex_del_source_entry_prop in Hsource0.
  destruct Hsource0 as
    (Hbase & Heid_valid & Hentry_lookup & Hinitial_type &
     (m & Hinitial_fields) & Hnesting & Hwaiting & Howner_entry).
  destruct
    (mutex_del_owner_stage_preserves_event_core__g05_always_loop
       sg e ls0 owner_post eid Hentry_lookup Howner_stage) as
    (owner_event & Howner_lookup & Howner_type & Howner_fields).
  destruct
    (mutex_del_wake_steps_preserve_event_core__g05_always_loop
       sg eid owner_post current owner_event
       Howner_lookup Hwake_steps) as
    (selected & Hselected_lookup & Hselected_type & Hselected_fields).
  pose proof Hsnapshot as Hsnapshot0.
  unfold event_snapshot_of_prop in Hsnapshot0.
  destruct Hsnapshot0 as
    (Hsnapshot_lookup & Hsnapshot_type & Hsnapshot_cnt &
     Hsnapshot_ptr & Hsnapshot_grp & Hsnapshot_tbl).
  rewrite Hsnapshot_lookup in Hselected_lookup.
  inversion Hselected_lookup; subst selected.
  assert (Hcurrent_type :
    current_event.(eventType) = OS_EVENT_TYPE_MUTEX) by congruence.
  assert (Hcurrent_fields :
    current_event.(mutexFields) = Some m) by congruence.
  pose proof Hlineage as Hlineage0.
  unfold mutex_del_return_lineage_prop in Hlineage0.
  destruct Hlineage0 as
    (Hpe & Hpevent & Hpd & Hperr & Hnonzero & Hetype & Hisr &
     Hisr_nonpos & Hopt & Hentry_snapshot & Howner_lineage).
  unfold mutex_del_owner_value_lineage_prop in Howner_lineage.
  destruct Howner_lineage as
    (m0 & Hlineage_type & Hlineage_fields & Hdecoded_pcp &
     Hdecoded_owner & Hm0_pcp & Howner_shape).
  rewrite Hinitial_fields in Hlineage_fields.
  inversion Hlineage_fields; subst m0.
  assert (Hm_pcp : m.(mfPCP) = pcp_v) by congruence.
  pose proof Hvalid as Hvalid0.
  unfold UCOS2_validity_bundle in Hvalid0.
  destruct Hvalid0 as
    (Htask_valid & Hsched_valid & Hevent_valid & Hcross_valid).
  pose proof Hevent_valid as Hevent_valid0.
  unfold event_vaild_cond_prop, valid_GlobEventAbstractState,
    event_in_range in Hevent_valid0.
  destruct Hevent_valid0 as
    (_ & _ & _ & _ & _ & _ & _ & Hwait_entries).
  specialize (Hwait_entries eid current_event Hsnapshot_lookup).
  unfold Ucos2Verify.lib.event_wait.event_wait_entry_consistency
    in Hwait_entries.
  destruct Hwait_entries as (Hwait_canonical & Hwait_match).
  assert (Hempty : current_event.(waitList) = nil).
  {
    eapply mutex_del_wait_grp_zero_implies_empty__g05_always_loop.
    - exact Hwait_canonical.
    - symmetry. exact Hsnapshot_grp.
  }
  pose proof
    (mutex_del_current_owner_restored_total__g05_always_loop
       sg e ls0 eid owner_post current m
       Hentry_lookup Hinitial_type Hinitial_fields Howner_entry
       Howner_stage Hwake_steps) as Hrestored.
  assert (Hno_live_if :
    pcp_v <> sg.(osPrioMutexCeilDis) ->
    no_live_task_at_priority current.(TskState) pcp_v).
  {
    intro Henabled.
    eapply mutex_del_no_live_task_at_freed_pcp_simple__g05_always_loop;
      eauto.
  }
  pose proof
    (mutex_del_free_validity_bundle__g05_always_loop
       sg current eid current_event m pcp_v
       Hsnapshot_lookup Hcurrent_type Hcurrent_fields Hm_pcp Hempty
       Hno_live_if Hrestored Hvalid) as Hpostvalid.
  pose proof
    (mutex_del_selected_pcp_case__g05_always_loop
       sg current eid current_event m pcp_v
       Hstable Hvalid Hsnapshot_lookup Hcurrent_type Hcurrent_fields Hm_pcp)
    as Hpcp_case.
  destruct
    (mutex_del_prepare_free_relations__g05_always_loop
       sg eid current current_event m
       Hsnapshot_lookup Hcurrent_type Hcurrent_fields Hempty) as
    (Hprepare & Hfree).
  rewrite Hm_pcp in Hfree.
  pose proof Halways as Halways0.
  unfold mutex_del_always_mode_prop in Halways0.
  destruct Halways0 as (Hopt_always & Htasks_case).
  assert (Hwake_mode :
    mutex_del_mode_wake_prop opt_abs sg eid owner_post current).
  {
    rewrite Hopt_always.
    exact Hwake_steps.
  }
  assert (Hcommit :
    mutex_del_success_commit_anchor_prop
      sg e ls0 eid opt_abs current
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp_v current)).
  {
    unfold mutex_del_success_commit_anchor_prop.
    exists owner_post,
      (mutex_del_prepare_state__g05_always_loop
         eid current_event m current).
    repeat split; assumption.
  }
  sep_apply_l_atomic
    (mutex_del_free_transition_rep_total__g05_always_loop
       sg ls0 current eid pcp_v current_event pevent
       _ _ _ _ _ _ freelist_in
       Hpcp_case Hempty PreH3 Hcore_layout Hwait_layout
       Hfree_addr Hfree_head Hvalid Hpostvalid).
  sep_apply_l_atomic
    (mutex_del_success_commit_pack__g05_always_loop
       sg e ls0 eid opt_abs pevent tasks_v X current
       (mutex_del_free_state_after__g05_always_loop
          sg eid pcp_v current)
       Hcommit Hsource Hmode PreH4).
  split_pure_spatial.
  - cancel (mutex_del_success_commit_inv
      sg e ls0 eid opt_abs pevent tasks_v X).
    cancel (perr # UChar |-> perr_in).
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - apply _derivable1_andp_intros.
    + apply _derivable1_andp_intros.
      * apply derivable1s_coq_prop_r. exact Halways.
      * apply derivable1s_coq_prop_r. exact Hrefresh.
    + apply derivable1s_coq_prop_r. exact Hlineage.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_15 : OSMutexDel_full_entail_wit_15.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hvalid : valid_stable_glob_vars sg).
  {
    unfold mutex_del_refresh_context_prop in H5.
    tauto.
  }
  Exists perr_in.
  unfold mutex_del_restore_rep.
  sep_apply_l_atomic
    (mutex_del_success_exit_pack__g05_always_loop
       sg e ls0 eid opt_abs pevent tasks_v X
       critical_anchor ls_commit ls2
       H4 H3 H2 H6 Hvalid H1).
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - cancel (mutex_del_success_exit_inv
      sg e ls0 eid opt_abs pevent tasks_v X).
    cancel (perr # UChar |-> perr_in).
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - apply derivable1s_coq_prop_r.
    exact H0.
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_16_1 : OSMutexDel_full_entail_wit_16_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists perr_v_2.
  assert (Htasks : tasks_v = 1).
  { destruct opt_abs; cbn in H4; try contradiction.
    - subst tasks_v. cbn in PreH1. lia.
    - destruct H4 as [Htasks | Htasks].
      + subst tasks_v. cbn in PreH1. lia.
      + exact Htasks. }
  subst tasks_v.
  assert (Hcache :
    mutex_del_high_ready_cache_closed_prop ls_exited ls_sched).
  { eapply mutex_del_sched_stage_cache_closed; eassumption. }
  unfold mutex_del_success_out_inv.
  Exists critical_anchor ls_commit ls_exited ls_sched.
  split_pure_spatial.
  - sep_apply_l_atomic
      (mutex_del_transition_rep_full_if_cache_closed
         sg ls_exited ls_sched Hcache).
    cancel (OutsideCritical sg ls_sched).
    cancel (UCOS2_Verify_inv sg ls_sched).
    cancel (perr # UChar |-> perr_v_2).
    repeat apply sepcon_cancel_end.
    all: apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial.
      exact (conj H6
        (conj H5
          (conj H4
            (conj H3
              (conj H7
                (conj H1 H0)))))).
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_16_2 : OSMutexDel_full_entail_wit_16_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists perr_v_2.
  unfold mutex_del_success_exit_inv.
  Intros critical_anchor commit exited.
  pureIntros.
  destruct H0 as
    [Hcommit [Hsource [Hmode [Hexit [Hvalid [Hstable Hsafe]]]]]].
  assert (Htasks : tasks_v = 0).
  { destruct opt_abs; cbn in Hmode; try contradiction.
    - exact Hmode.
    - destruct Hmode as [Hmode | Hmode]; [exact Hmode |].
      subst tasks_v.
      exfalso.
      apply PreH1.
      reflexivity. }
  subst tasks_v.
  unfold mutex_del_success_out_inv.
  Exists critical_anchor commit exited exited.
  split_pure_spatial.
  - cancel (OutsideCritical sg exited).
    cancel (UCOS2_Verify_inv sg exited).
    cancel (perr # UChar |-> perr_v_2).
    repeat apply sepcon_cancel_end.
    all: apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial.
      exact (conj Hcommit
        (conj Hsource
          (conj Hmode
            (conj Hexit
              (conj eq_refl
                (conj Hstable Hsafe)))))).
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_17 : OSMutexDel_full_entail_wit_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists perr_in.
  unfold mutex_del_unchanged_exit_inv.
  Exists ls2.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls2).
    cancel (mutex_del_restore_rep false sg ls0 ls2).
    cancel (perr # UChar |-> perr_in).
    andp_cancel.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial.
      split; [exact H2 |].
      split; [exact H1 |].
      split; [exact H3 | exact H0].
Qed.

Lemma proof_of_OSMutexDel_full_entail_wit_18 : OSMutexDel_full_entail_wit_18.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (pevent_addr_v = pevent) as Hpevent.
  { unfold mutex_del_source_entry_prop in H9.
    intuition congruence. }
  subst pevent_addr_v.
  assert (opt_abs = MutexDelInvalid) as Hopt.
  { unfold mutex_del_option_decode_prop in H0.
    intuition subst; congruence. }
  unfold mutex_del_unchanged_inside_inv.
  split_pure_spatial.
  - cancel (InsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    cancel (perr # UChar |-> perr_in).
    andp_cancel.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial. exact H8.
    + dump_pre_spatial.
      split.
      * exact H9.
      * split.
        -- unfold mutex_del_error_mode_prop.
           right; auto.
        -- exact PreH1.
Qed.

Lemma proof_of_OSMutexDel_full_return_wit_1 : OSMutexDel_full_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_no_pend_exit_inv.
  Intros critical_anchor commit exited.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct H0 as
    [Hcommit [Hsource [Hmode [Hexit [Hstable Hsafe]]]]].
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as
    [Haddr [Hvalid [Hused [Htype [[m Hfields]
      [Hnest [Htasks Hentry_owner]]]]]]].
  unfold mutex_del_no_pend_mode_prop in Hmode.
  destruct Hmode as [Hopt Htasks_v].
  subst opt_abs.
  subst tasks_v.
  unfold mutex_del_return_lineage_prop in H.
  destruct H as
    [Hpe [Hpev [Hpd [Hperr [Hnonnull [Hetype [Hisr
      [Hisrle [Hdecode Hsnap_owner]]]]]]]]].
  destruct Hsnap_owner as [Hsnap Howner_lineage].
  subst pe.
  subst pd.
  subst perr.
  subst etype.
  subst isr.
  subst pevent.
  assert (Hopt_in : opt_in = 0).
  { unfold mutex_del_option_decode_prop in Hdecode.
    intuition congruence. }
  assert (Hempty : e.(waitList) = nil).
  { unfold mutex_del_tasks_waiting_prop in Htasks.
    intuition congruence. }
  assert (Hegrp : egrp_in = 0).
  { pose proof Hsnap as Hsnapshot.
    unfold event_snapshot_of_prop in Hsnapshot.
    destruct Hsnapshot as [_ [_ [_ [_ [Hgrp _]]]]].
    rewrite Hempty in Hgrp.
    cbn in Hgrp.
    exact Hgrp. }
  assert (Hpcp : m.(mfPCP) = decode_PCP_from_cnt ecnt_in).
  { unfold mutex_del_owner_value_lineage_prop in Howner_lineage.
    destruct Howner_lineage as
      [m' [Htype' [Hfields' [Hdecode_pcp
        [Hdecode_orig [Hm_pcp Howner_shape]]]]]].
    assert (Hm : m' = m) by congruence.
    subst m'.
    exact Hm_pcp. }
  destruct
    (mutex_del_success_commit_public_facts__g06_exit_observation
       sg e ls0 eid MutexDelNoPend critical_anchor commit m
       Hused Htype Hfields Hentry_owner Hcommit)
    as [Howner_commit Hprio_commit].
  assert (Htask_exit : exited.(TskState) = commit.(TskState)).
  { eapply mutex_del_exit_anchored_preserves_task__g06_exit_observation.
    exact Hexit. }
  assert (Howner_exit :
    mutex_del_owner_restored_prop e exited.(TskState)).
  { rewrite Htask_exit. exact Howner_commit. }
  assert (Hrefine :
    mutex_del_success_post_refinement_prop
      sg e ls0 eid MutexDelNoPend exited).
  { unfold mutex_del_success_post_refinement_prop.
    exists critical_anchor, commit.
    split; assumption. }
  assert (Hsem :
    OSMutexDel_full_sem sg pevent_pre MutexDelNoPend ls0
      (OS_ERR_NONE, None) exited).
  { unfold OSMutexDel_full_sem.
    right; right; right; right; right; right; left.
    split; [exact Hnonnull |].
    split; [exact Hnest |].
    split; [reflexivity |].
    exists eid, e, m, critical_anchor, commit, exited.
    split; [exact Haddr |].
    split; [exact Hused |].
    split; [exact Htype |].
    split; [exact Hfields |].
    split; [exact Hempty |].
    split; [exact Hcommit |].
    split; [exact Hexit |].
    repeat split; reflexivity. }
  assert (Hsafe_ret : safeExec (LastSeen exited) (return 0) X).
  { eapply
      (mutex_accept_safe_return__restore_and_returns
         (OSErrCode * option addr) Z
         (OSMutexDel_full_sem sg pevent_pre MutexDelNoPend)
         (mutex_del_observe_ptr pevent_pre)
         ls0 exited (OS_ERR_NONE, None) 0 X).
    - exact Hsem.
    - intros P. change (0 = 0 /\ P = P). split; reflexivity.
    - exact Hsafe. }
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { unfold valid_stable_glob_vars in Hstable. intuition. }
  destruct (Z.eq_dec (decode_PCP_from_cnt ecnt_in) 255)
    as [Hpcp_disabled | Hpcp_enabled].
  - Left. Right.
    Exists exited 0.
    split_pure_spatial.
    + cancel (OutsideCritical sg exited).
      cancel (UCOS2_Verify_inv sg exited).
      cancel (perr_pre # UChar |-> 0).
      repeat apply sepcon_cancel_end.
      all: apply derivable1_truep_intros.
    + split_pures; dump_pre_spatial;
        first [assumption | reflexivity].
  - assert (Hprio_exit :
      prio_tbl_entry_prop exited.(TskState)
        (decode_PCP_from_cnt ecnt_in) PTFree).
    { rewrite Htask_exit.
      rewrite <- Hpcp.
      apply Hprio_commit.
      rewrite Hpcp, Hdisabled.
      exact Hpcp_enabled. }
    Left. Left. Right.
    Exists exited 0.
    split_pure_spatial.
    + cancel (OutsideCritical sg exited).
      cancel (UCOS2_Verify_inv sg exited).
      cancel (perr_pre # UChar |-> 0).
      repeat apply sepcon_cancel_end.
      all: apply derivable1_truep_intros.
    + split_pures; dump_pre_spatial;
        first [assumption | reflexivity].
Qed.

Lemma proof_of_OSMutexDel_full_return_wit_2 : OSMutexDel_full_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_unchanged_exit_inv.
  Intros exited.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct H0 as [Hsource [Herr [Hexit Hsafe]]].
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as
    [Haddr [Hvalid [Hused [Htype [[m Hmutex]
      [Hnest [Htasks Howner]]]]]]].
  unfold mutex_del_error_mode_prop in Herr.
  destruct Herr as [[Hno [Htasks_v Hcode]] | [Hinvalid Hbadcode]].
  - subst opt_abs.
    subst tasks_v.
    unfold mutex_del_return_lineage_prop in H.
    destruct H as
      [Hpe [Hpev [Hpd [Hperr [Hnonnull [Hetype [Hisr
        [Hisrle [Hdecode Hsnap_owner]]]]]]]]].
    destruct Hsnap_owner as [Hsnap Howner_lineage].
    subst pe.
    subst pd.
    subst perr.
    subst etype.
    subst isr.
    subst pevent.
    assert (Hopt : opt_in = 0).
    { unfold mutex_del_option_decode_prop in Hdecode.
      intuition congruence. }
    assert (Hwait : e.(waitList) <> nil).
    { unfold mutex_del_tasks_waiting_prop in Htasks.
      intuition congruence. }
    assert (Hsem :
      OSMutexDel_full_sem sg pevent_pre MutexDelNoPend ls0
        (OS_ERR_TASK_WAITING, Some pevent_pre) exited).
    { unfold OSMutexDel_full_sem.
      right; right; right; right; left.
      split; [exact Hnonnull |].
      split; [exact Hnest |].
      split; [reflexivity |].
      exists eid, e, m, exited.
      split; [exact Haddr |].
      split; [exact Hused |].
      split; [exact Htype |].
      split; [exact Hmutex |].
      split; [exact Hwait |].
      split; [exact Hexit |].
      repeat split; reflexivity. }
    assert (Hsafe_ret :
      safeExec (LastSeen exited) (return pevent_pre) X).
    { eapply
        (mutex_accept_safe_return__restore_and_returns
           (OSErrCode * option addr) Z
           (OSMutexDel_full_sem sg pevent_pre MutexDelNoPend)
           (mutex_del_observe_ptr pevent_pre)
           ls0 exited
           (OS_ERR_TASK_WAITING, Some pevent_pre) pevent_pre X).
      - exact Hsem.
      - intros P.
        change (pevent_pre = pevent_pre /\ P = P).
        split; reflexivity.
      - exact Hsafe. }
    pose proof Hexit as Hexit_shape.
    unfold mutex_del_exit_critical_call_prop,
      crit_rel_intr_only in Hexit_shape.
    destruct Hexit_shape as [_ Hshape].
    assert (Hsnap_exit :
      event_snapshot_of_prop sg (TskState exited) (EventState exited)
        eid e 4 ecnt_in eptr_in egrp_in evtL_in).
    { rewrite Hshape. simpl. exact Hsnap. }
    unfold mutex_del_restore_rep; simpl.
    sep_apply_l_atomic
      (mutex_del_ucos2_inv_event_validity__g06_exit_observation
         sg exited).
    pureIntros.
    assert (Hegrp : egrp_in <> 0).
    { unfold event_snapshot_of_prop in Hsnap_exit.
      destruct Hsnap_exit as
        [Hused_exit [_ [_ [_ [Hgrp_exit _]]]]].
      match goal with
      | Hevent_valid : event_vaild_cond_prop sg (TskState exited)
          (EventState exited) |- _ =>
          unfold event_vaild_cond_prop,
            valid_GlobEventAbstractState, event_in_range in Hevent_valid;
          destruct Hevent_valid as
            [_ [_ [_ [_ [_ [_ [_ Hwait_consistency]]]]]]]
      end.
      specialize (Hwait_consistency eid e Hused_exit).
      unfold Ucos2Verify.lib.event_wait.event_wait_entry_consistency
        in Hwait_consistency.
      destruct Hwait_consistency as [Hcanonical _].
      intro Hegrp0.
      rewrite Hegrp0 in Hgrp_exit.
      symmetry in Hgrp_exit.
      apply
        (proj1
           (mutex_del_wait_grp_zero_iff_empty__g06_exit_observation
              sg (TskState exited) e.(waitList) Hcanonical))
        in Hgrp_exit.
      contradiction. }
    Left. Left. Left. Right.
    Exists exited pevent_pre.
    split_pure_spatial.
    + cancel (OutsideCritical sg exited).
      cancel (UCOS2_Verify_inv sg exited).
      cancel (perr_pre # UChar |-> 73).
      apply derivable1_truep_intros.
    + split_pures; dump_pre_spatial;
        first [assumption | reflexivity].
  - lia.
Qed.

Lemma proof_of_OSMutexDel_full_return_wit_3 : OSMutexDel_full_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_success_out_inv.
  Intros critical_anchor commit exited out.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct H0 as
    [Hcommit [Hsource [Hmode [Hexit [Hout [Hstable Hsafe]]]]]].
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as
    [Haddr [Hvalid [Hused [Htype [[m Hfields]
      [Hnest [Htasks Hentry_owner]]]]]]].
  unfold mutex_del_return_lineage_prop in H.
  destruct H as
    [Hpe [Hpev [Hpd [Hperr [Hnonnull [Hetype [Hisr
      [Hisrle [Hdecode Hsnap_owner]]]]]]]]].
  destruct Hsnap_owner as [Hsnap Howner_lineage].
  subst pe.
  subst pd.
  subst perr.
  subst etype.
  subst isr.
  subst pevent.
  assert (Hpcp : m.(mfPCP) = decode_PCP_from_cnt ecnt_in).
  { unfold mutex_del_owner_value_lineage_prop in Howner_lineage.
    destruct Howner_lineage as
      [m' [Htype' [Hfields' [Hdecode_pcp
        [Hdecode_orig [Hm_pcp Howner_shape]]]]]].
    assert (Hm : m' = m) by congruence.
    subst m'. exact Hm_pcp. }
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { unfold valid_stable_glob_vars in Hstable. intuition. }
  destruct opt_abs.
  - unfold mutex_del_success_mode_prop in Hmode.
    subst tasks_v.
    cbn in Hout.
    subst out.
    assert (Hopt_in : opt_in = 0).
    { unfold mutex_del_option_decode_prop in Hdecode.
      intuition congruence. }
    assert (Hempty : e.(waitList) = nil).
    { unfold mutex_del_tasks_waiting_prop in Htasks.
      intuition congruence. }
    assert (Hegrp : egrp_in = 0).
    { pose proof Hsnap as Hsnapshot.
      unfold event_snapshot_of_prop in Hsnapshot.
      destruct Hsnapshot as [_ [_ [_ [_ [Hgrp _]]]]].
      rewrite Hempty in Hgrp. cbn in Hgrp. exact Hgrp. }
    destruct
      (mutex_del_success_commit_public_facts__g06_exit_observation
         sg e ls0 eid MutexDelNoPend critical_anchor commit m
         Hused Htype Hfields Hentry_owner Hcommit)
      as [Howner_commit Hprio_commit].
    assert (Htask_exit : exited.(TskState) = commit.(TskState)).
    { eapply mutex_del_exit_anchored_preserves_task__g06_exit_observation.
      exact Hexit. }
    assert (Howner_exit :
      mutex_del_owner_restored_prop e exited.(TskState)).
    { rewrite Htask_exit. exact Howner_commit. }
    assert (Hrefine :
      mutex_del_success_post_refinement_prop
        sg e ls0 eid MutexDelNoPend exited).
    { unfold mutex_del_success_post_refinement_prop.
      exists critical_anchor, commit. split; assumption. }
    assert (Hsem :
      OSMutexDel_full_sem sg pevent_pre MutexDelNoPend ls0
        (OS_ERR_NONE, None) exited).
    { unfold OSMutexDel_full_sem.
      right; right; right; right; right; right; left.
      split; [exact Hnonnull |].
      split; [exact Hnest |].
      split; [reflexivity |].
      exists eid, e, m, critical_anchor, commit, exited.
      split; [exact Haddr |].
      split; [exact Hused |].
      split; [exact Htype |].
      split; [exact Hfields |].
      split; [exact Hempty |].
      split; [exact Hcommit |].
      split; [exact Hexit |].
      repeat split; reflexivity. }
    assert (Hsafe_ret : safeExec (LastSeen exited) (return 0) X).
    { eapply
        (mutex_accept_safe_return__restore_and_returns
           (OSErrCode * option addr) Z
           (OSMutexDel_full_sem sg pevent_pre MutexDelNoPend)
           (mutex_del_observe_ptr pevent_pre)
           ls0 exited (OS_ERR_NONE, None) 0 X).
      - exact Hsem.
      - intros P. change (0 = 0 /\ P = P). split; reflexivity.
      - exact Hsafe. }
    destruct (Z.eq_dec (decode_PCP_from_cnt ecnt_in) 255)
      as [Hpcp_disabled | Hpcp_enabled].
    + Left. Right.
      Exists exited 0.
      split_pure_spatial.
      * cancel (OutsideCritical sg exited).
        cancel (UCOS2_Verify_inv sg exited).
        cancel (perr_pre # UChar |-> 0).
        repeat apply sepcon_cancel_end.
        all: apply derivable1_truep_intros.
      * split_pures; dump_pre_spatial;
          first [assumption | reflexivity].
    + assert (Hprio_exit :
        prio_tbl_entry_prop exited.(TskState)
          (decode_PCP_from_cnt ecnt_in) PTFree).
      { rewrite Htask_exit.
        rewrite <- Hpcp.
        apply Hprio_commit.
        rewrite Hpcp, Hdisabled. exact Hpcp_enabled. }
      Left. Left. Right.
      Exists exited 0.
      split_pure_spatial.
      * cancel (OutsideCritical sg exited).
        cancel (UCOS2_Verify_inv sg exited).
        cancel (perr_pre # UChar |-> 0).
        repeat apply sepcon_cancel_end.
        all: apply derivable1_truep_intros.
      * split_pures; dump_pre_spatial;
          first [assumption | reflexivity].
  - unfold mutex_del_success_mode_prop in Hmode.
    assert (Hopt_in : opt_in = 1).
    { unfold mutex_del_option_decode_prop in Hdecode.
      intuition congruence. }
    destruct
      (mutex_del_success_commit_public_facts__g06_exit_observation
         sg e ls0 eid MutexDelAlways critical_anchor commit m
         Hused Htype Hfields Hentry_owner Hcommit)
      as [Howner_commit Hprio_commit].
    assert (Htask_exit : exited.(TskState) = commit.(TskState)).
    { eapply mutex_del_exit_anchored_preserves_task__g06_exit_observation.
      exact Hexit. }
    assert (Hwait_exit :
      mutex_del_waiters_aborted_effective_prop
        e exited.(TskState) exited.(SchedState)).
    { eapply
        mutex_del_success_waiters_after_exit__g06_exit_observation;
        eassumption. }
    assert (Hfinal_case :
      (e.(waitList) = nil /\ out = exited) \/
      (e.(waitList) <> nil /\
       mutex_del_sched_stage_prop exited out)).
    { destruct Hmode as [Htasks0 | Htasks1].
      - assert (Hempty : e.(waitList) = nil).
        { unfold mutex_del_tasks_waiting_prop in Htasks.
          intuition congruence. }
        left. split; [exact Hempty |].
        subst tasks_v. cbn in Hout. exact Hout.
      - assert (Hnonempty : e.(waitList) <> nil).
        { unfold mutex_del_tasks_waiting_prop in Htasks.
          intuition congruence. }
        right. split; [exact Hnonempty |].
        subst tasks_v. cbn in Hout. exact Hout. }
    assert (Htask_out_exit : out.(TskState) = exited.(TskState)).
    { destruct Hmode as [Htasks0 | Htasks1].
      - subst tasks_v. cbn in Hout. subst out. reflexivity.
      - subst tasks_v. cbn in Hout.
        unfold mutex_del_sched_stage_prop in Hout.
        destruct Hout as [res Hsched].
        exact
          (proj1
             (mutex_del_atomic_sched_preserves_waiter_maps__g06_exit_observation
                exited res out Hsched)). }
    assert (Htask_out : out.(TskState) = commit.(TskState)).
    { rewrite Htask_out_exit. exact Htask_exit. }
    assert (Howner_out :
      mutex_del_owner_restored_prop e out.(TskState)).
    { rewrite Htask_out. exact Howner_commit. }
    assert (Hwait_out :
      mutex_del_waiters_aborted_effective_prop
        e out.(TskState) out.(SchedState)).
    { destruct Hmode as [Htasks0 | Htasks1].
      - subst tasks_v. cbn in Hout. subst out. exact Hwait_exit.
      - subst tasks_v. cbn in Hout.
        eapply
          mutex_del_success_waiters_after_sched__g06_exit_observation;
          eassumption. }
    assert (Hrefine :
      mutex_del_success_post_refinement_prop
        sg e ls0 eid MutexDelAlways out).
    { unfold mutex_del_success_post_refinement_prop.
      exists critical_anchor, commit, exited.
      split; [exact Hcommit |].
      split; [exact Hexit |].
      exact Hfinal_case. }
    assert (Hsem :
      OSMutexDel_full_sem sg pevent_pre MutexDelAlways ls0
        (OS_ERR_NONE, None) out).
    { unfold OSMutexDel_full_sem.
      right; right; right; right; right; right; right.
      split; [exact Hnonnull |].
      split; [exact Hnest |].
      split; [reflexivity |].
      exists eid, e, m, critical_anchor, commit, exited.
      split; [exact Haddr |].
      split; [exact Hused |].
      split; [exact Htype |].
      split; [exact Hfields |].
      split; [exact Hcommit |].
      split; [exact Hexit |].
      split; [reflexivity |].
      split; [reflexivity |].
      exact Hfinal_case. }
    assert (Hsafe_ret : safeExec (LastSeen out) (return 0) X).
    { eapply
        (mutex_accept_safe_return__restore_and_returns
           (OSErrCode * option addr) Z
           (OSMutexDel_full_sem sg pevent_pre MutexDelAlways)
           (mutex_del_observe_ptr pevent_pre)
           ls0 out (OS_ERR_NONE, None) 0 X).
      - exact Hsem.
      - intros P. change (0 = 0 /\ P = P). split; reflexivity.
      - exact Hsafe. }
    destruct (Z.eq_dec (decode_PCP_from_cnt ecnt_in) 255)
      as [Hpcp_disabled | Hpcp_enabled].
    + Left. Left. Left. Right.
      Exists out 0.
      split_pure_spatial.
      * cancel (OutsideCritical sg out).
        cancel (UCOS2_Verify_inv sg out).
        cancel (perr_pre # UChar |-> 0).
        repeat apply sepcon_cancel_end.
        all: apply derivable1_truep_intros.
      * split_pures; dump_pre_spatial;
          first [assumption | reflexivity].
    + assert (Hprio_out :
        prio_tbl_entry_prop out.(TskState)
          (decode_PCP_from_cnt ecnt_in) PTFree).
      { rewrite Htask_out.
        rewrite <- Hpcp.
        apply Hprio_commit.
        rewrite Hpcp, Hdisabled. exact Hpcp_enabled. }
      Left. Left. Left. Left.
      Exists out 0.
      split_pure_spatial.
      * cancel (OutsideCritical sg out).
        cancel (UCOS2_Verify_inv sg out).
        cancel (perr_pre # UChar |-> 0).
        repeat apply sepcon_cancel_end.
        all: apply derivable1_truep_intros.
      * split_pures; dump_pre_spatial;
          first [assumption | reflexivity].
  - unfold mutex_del_success_mode_prop in Hmode.
    contradiction.
Qed.

Lemma proof_of_OSMutexDel_full_return_wit_4 : OSMutexDel_full_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_unchanged_exit_inv.
  Intros exited.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct H0 as [Hsource [Herr [Hexit Hsafe]]].
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as
    [Haddr [Hvalid [Hused [Htype [[m Hmutex]
      [Hnest [Htasks Howner]]]]]]].
  unfold mutex_del_error_mode_prop in Herr.
  destruct Herr as [[Hno [Htasks_v Hbad]] | [Hinvalid Hcode]].
  - lia.
  - subst opt_abs.
    unfold mutex_del_return_lineage_prop in H.
    destruct H as
      [Hpe [Hpev [Hpd [Hperr [Hnonnull [Hetype [Hisr
        [Hisrle [Hdecode Hsnap]]]]]]]]].
    destruct Hsnap as [Hsnap Howner_lineage].
    subst pe.
    subst pd.
    subst perr.
    subst etype.
    subst isr.
    subst pevent.
    assert (Hopt0 : opt_in <> 0).
    { unfold mutex_del_option_decode_prop in Hdecode.
      intuition discriminate. }
    assert (Hopt1 : opt_in <> 1).
    { unfold mutex_del_option_decode_prop in Hdecode.
      intuition discriminate. }
    assert (Hsem :
      OSMutexDel_full_sem sg pevent_pre MutexDelInvalid ls0
        (OS_ERR_INVALID_OPT, Some pevent_pre) exited).
    { unfold OSMutexDel_full_sem.
      right; right; right; right; right; left.
      split; [exact Hnonnull |].
      split; [exact Hnest |].
      split; [reflexivity |].
      exists eid, e, m, exited.
      split; [exact Haddr |].
      split; [exact Hused |].
      split; [exact Htype |].
      split; [exact Hmutex |].
      split; [exact Hexit |].
      repeat split; reflexivity. }
    assert (Hsafe_ret :
      safeExec (LastSeen exited) (return pevent_pre) X).
    { eapply
        (mutex_accept_safe_return__restore_and_returns
           (OSErrCode * option addr) Z
           (OSMutexDel_full_sem sg pevent_pre MutexDelInvalid)
           (mutex_del_observe_ptr pevent_pre)
           ls0 exited
           (OS_ERR_INVALID_OPT, Some pevent_pre) pevent_pre X).
      - exact Hsem.
      - intros P.
        change (pevent_pre = pevent_pre /\ P = P).
        split; reflexivity.
      - exact Hsafe. }
    pose proof Hexit as Hexit_shape.
    unfold mutex_del_exit_critical_call_prop,
      crit_rel_intr_only in Hexit_shape.
    destruct Hexit_shape as [_ Hshape].
    assert (Hsnap_exit :
      event_snapshot_of_prop sg (TskState exited) (EventState exited)
        eid e 4 ecnt_in eptr_in egrp_in evtL_in).
    { rewrite Hshape. simpl. exact Hsnap. }
    Left. Left. Left. Left. Right.
    Exists exited pevent_pre.
    unfold mutex_del_restore_rep; simpl.
    split_pure_spatial.
    + cancel (OutsideCritical sg exited).
      cancel (UCOS2_Verify_inv sg exited).
      cancel (perr_pre # UChar |-> 7).
      apply derivable1_truep_intros.
    + split_pures; dump_pre_spatial;
        first [assumption | reflexivity].
Qed.

Lemma proof_of_OSMutexDel_full_return_wit_5 : OSMutexDel_full_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst pe.
  subst pd.
  subst isr.
  subst etype.
  sep_apply_l_atomic
    (mutex_del_event_focus_merge
       sg ls0 eid e pevent_pre
       (&((pevent_pre) # "os_event" ->ₛ "OSEventType"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventPtr"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventCnt"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventGrp"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventTbl"))
       (&("OSEventFreeList"))
       4 ecnt_in eptr_in egrp_in evtL_in freelist_in
       ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
       ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
  sep_apply_l_atomic
    (mutex_del_ucos2_inv_int_nesting_byte_range__g06_exit_observation
       sg ls0).
  pureIntros.
  assert (Hisr_range :
    0 <= intNesting (IntrState ls0) < 2 ^ 32).
  { change (0 <= intNesting (IntrState ls0) < 4294967296).
    lia. }
  rewrite (unsigned_last_nbits_eq
    (intNesting (IntrState ls0)) 32 Hisr_range) in PreH3.
  Right.
  Exists ls0 pevent_pre.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    cancel (perr_pre # UChar |-> 15).
    apply derivable1_truep_intros.
  - split_pures.
    all: try (dump_pre_spatial;
      first [assumption | reflexivity | lia | int_auto]).
    all: unfold UCOS2_Verify_inv, interrupt_inv;
      pureIntros;
      try dump_pre_spatial.
    pose proof H7 as Hsnap_sem.
    unfold event_snapshot_of_prop in Hsnap_sem.
    destruct Hsnap_sem as [Hused _].
    pose proof H9 as Howner_sem.
    unfold mutex_del_owner_snapshot_prop in Howner_sem.
    destruct Howner_sem as [_ [m [Htype [Hmutex _]]]].
    assert (Hisr : intNesting (IntrState ls0) > 0) by lia.
    assert (Hsem :
      OSMutexDel_full_sem sg pevent_pre opt_abs ls0
        (OS_ERR_DEL_ISR, Some pevent_pre) ls0).
    { unfold OSMutexDel_full_sem.
      right; right; right; left.
      split; [assumption |].
      exists eid, e, m.
      repeat split; try assumption; try reflexivity. }
    eapply
      (mutex_accept_safe_return__restore_and_returns
         (OSErrCode * option addr) Z
         (OSMutexDel_full_sem sg pevent_pre opt_abs)
         (mutex_del_observe_ptr pevent_pre)
         ls0 ls0
         (OS_ERR_DEL_ISR, Some pevent_pre) pevent_pre X).
    + exact Hsem.
    + intros P; simpl; split; reflexivity.
    + assumption.
Qed.

Lemma proof_of_OSMutexDel_full_return_wit_6 : OSMutexDel_full_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst pe.
  subst pd.
  subst isr.
  sep_apply_l_atomic
    (mutex_del_event_focus_merge
       sg ls0 eid e pevent_pre
       (&((pevent_pre) # "os_event" ->ₛ "OSEventType"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventPtr"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventCnt"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventGrp"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventTbl"))
       (&("OSEventFreeList"))
       etype ecnt_in eptr_in egrp_in evtL_in freelist_in
       ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
       ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
  Exists ls0 pevent_pre.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    cancel (perr_pre # UChar |-> 1).
    apply derivable1_truep_intros.
  - split_pures.
    all: try (dump_pre_spatial;
      first [assumption | reflexivity]).
    all: unfold UCOS2_Verify_inv, interrupt_inv;
      pureIntros;
      dump_pre_spatial.
    match goal with
    | Hsnap : event_snapshot_of_prop sg (TskState ls0) (EventState ls0)
        eid e etype ecnt_in eptr_in egrp_in evtL_in,
      Hbad : etype <> 4 |- _ =>
        pose proof Hsnap as Hsnap_sem;
        unfold event_snapshot_of_prop in Hsnap_sem;
        destruct Hsnap_sem as [Hused [Henc _]];
        assert (Hwrong : eventType e <> OS_EVENT_TYPE_MUTEX)
          by (intro Heq; rewrite Heq in Henc; simpl in Henc;
              apply Hbad; exact Henc);
        assert (Hsem :
          OSMutexDel_full_sem sg pevent_pre opt_abs ls0
            (OS_ERR_EVENT_TYPE, Some pevent_pre) ls0)
        by (unfold OSMutexDel_full_sem;
            right; right; left;
            split; [assumption |];
            exists eid, e;
            repeat split; try assumption; try reflexivity);
        eapply
          (mutex_accept_safe_return__restore_and_returns
             (OSErrCode * option addr) Z
             (OSMutexDel_full_sem sg pevent_pre opt_abs)
             (mutex_del_observe_ptr pevent_pre)
             ls0 ls0
             (OS_ERR_EVENT_TYPE, Some pevent_pre) pevent_pre X);
        [exact Hsem | intros P; simpl; split; reflexivity | assumption]
    end.
Qed.

Lemma proof_of_OSMutexDel_full_return_wit_7 : OSMutexDel_full_return_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst pe.
  subst pd.
  subst isr.
  sep_apply_l_atomic
    (mutex_del_event_focus_merge
       sg ls0 eid e pevent_pre
       (&((pevent_pre) # "os_event" ->ₛ "OSEventType"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventPtr"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventCnt"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventGrp"))
       (&((pevent_pre) # "os_event" ->ₛ "OSEventTbl"))
       (&("OSEventFreeList"))
       etype ecnt_in eptr_in egrp_in evtL_in freelist_in
       ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)
       ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
  Exists ls0 pevent_pre.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    cancel (perr_pre # UChar |-> 1).
    apply derivable1_truep_intros.
  - split_pures.
    all: try (dump_pre_spatial;
      first [assumption | reflexivity]).
    all: unfold UCOS2_Verify_inv, interrupt_inv;
      pureIntros;
      dump_pre_spatial.
    match goal with
    | Hsnap : event_snapshot_of_prop sg (TskState ls0) (EventState ls0)
        eid e etype ecnt_in eptr_in egrp_in evtL_in,
      Hbad : etype <> 4 |- _ =>
        pose proof Hsnap as Hsnap_sem;
        unfold event_snapshot_of_prop in Hsnap_sem;
        destruct Hsnap_sem as [Hused [Henc _]];
        assert (Hwrong : eventType e <> OS_EVENT_TYPE_MUTEX)
          by (intro Heq; rewrite Heq in Henc; simpl in Henc;
              apply Hbad; exact Henc);
        assert (Hsem :
          OSMutexDel_full_sem sg pevent_pre opt_abs ls0
            (OS_ERR_EVENT_TYPE, Some pevent_pre) ls0)
        by (unfold OSMutexDel_full_sem;
            right; right; left;
            split; [assumption |];
            exists eid, e;
            repeat split; try assumption; try reflexivity);
        eapply
          (mutex_accept_safe_return__restore_and_returns
             (OSErrCode * option addr) Z
             (OSMutexDel_full_sem sg pevent_pre opt_abs)
             (mutex_del_observe_ptr pevent_pre)
             ls0 ls0
             (OS_ERR_EVENT_TYPE, Some pevent_pre) pevent_pre X);
        [exact Hsem | intros P; simpl; split; reflexivity | assumption]
    end.
Qed.

Lemma proof_of_OSMutexDel_full_return_wit_8 : OSMutexDel_full_return_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst pevent_pre.
  subst pe.
  subst pd.
  subst isr.
  assert (Hsem :
    OSMutexDel_full_sem sg 0 opt_abs ls0
      (OS_ERR_PEVENT_NULL, Some 0) ls0).
  { unfold OSMutexDel_full_sem.
    left.
    repeat split; reflexivity. }
  assert (Hsafe_ret : safeExec (LastSeen ls0) (return 0) X).
  { eapply
      (mutex_accept_safe_return__restore_and_returns
         (OSErrCode * option addr) Z
         (OSMutexDel_full_sem sg 0 opt_abs)
         (mutex_del_observe_ptr 0)
         ls0 ls0
         (OS_ERR_PEVENT_NULL, Some 0) 0 X).
    - exact Hsem.
    - intros P.
      change (0 = 0 /\ P = P).
      split; reflexivity.
    - exact PreH7. }
  Exists ls0 0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    cancel (perr_pre # UChar |-> 4).
    repeat apply sepcon_cancel_end.
    all: apply derivable1_truep_intros.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity].
Qed.

Lemma proof_of_OSMutexDel_full_partial_solve_wit_6_pure : OSMutexDel_full_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sepcon_lift ((&("OSIntNesting")) # UChar |-> isr).
  prop_apply_p (store_uchar_range (&("OSIntNesting")) isr).
  Intros_p Hisr_range.
  change (0 <= isr <= 255) in Hisr_range.
  assert (Hisr_nonpos : isr <= 0).
  {
    eapply unsigned_last_nbits_32_nonpositive_uchar__focus_and_pure.
    - exact Hisr_range.
    - exact PreH1.
  }
  split_pures.
  all: dump_pre_spatial.
  all: subst; lia.
Qed.

Lemma proof_of_OSMutexDel_full_partial_solve_wit_12_pure : OSMutexDel_full_partial_solve_wit_12_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: unfold mutex_del_owner_stage_focus.
  all: Intros owner_post.
  all: unfold mutex_del_event_ready_focus_inv.
  all: LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct H13 as [_ Hcross].
  all: assert (Hpcp_range : 0 <= pcp_v /\ pcp_v < 64) by
    (eapply mutex_del_owner_stage_enabled_pcp_range__g04_no_pend_errors;
     eauto).
  all: split_pures.
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_OSMutexDel_full_partial_solve_wit_22_pure : OSMutexDel_full_partial_solve_wit_22_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p
    (store_uchar_range
       (&( pevent # "os_event" ->ₛ "OSEventGrp")) egrp_loop).
  Intros_p Hegrp_range.
  change (0 <= egrp_loop <= 255) in Hegrp_range.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change (0 <= egrp_loop < 4294967296); lia).
  split; assumption.
Qed.

Lemma proof_of_OSMutexDel_full_partial_solve_wit_23_pure : OSMutexDel_full_partial_solve_wit_23_pure.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_abort_loop_residual.
  Intros ls_owner_cur ls_loop e_loop evtL_loop.
  unfold mutex_del_event_ready_focus_inv.
  pureIntros.
  match goal with
  | Hsource : mutex_del_source_entry_prop
      sg e ls0 eid pevent tasks_v |- _ =>
      pose proof Hsource as Hsource0
  end.
  unfold mutex_del_source_entry_prop in Hsource0.
  destruct Hsource0 as
    (Hbase & Heid_valid & Hentry_lookup & Hinitial_type &
     (m & Hinitial_fields) & Hnesting & Hwaiting & Howner_entry).
  match goal with
  | Hresidual :
      mutex_del_rdyatprio_stage_prop sg e ls0 ls_owner_cur /\
      mutex_del_wake_steps sg eid ls_owner_cur ls_loop /\
      event_free_list_head_prop sg ls_loop.(EventState) freelist_in /\
      event_snapshot_of_prop
        sg ls_loop.(TskState) ls_loop.(EventState) eid e_loop
        (encode_event_type e_loop.(eventType))
        ecnt_in eptr_in 0 evtL_loop |- _ =>
      destruct Hresidual as
        (Howner_stage & Hwake_steps & Hfree_head & Hsnapshot)
  end.
  match goal with
  | Hfocus_pure :
      sched_in_range sg ls_loop.(TskState) ls_loop.(SchedState) /\
      cross_module_consistency sg ls_loop |- _ =>
      destruct Hfocus_pure as (Hsched_range & Hcross)
  end.
  destruct
    (mutex_del_owner_stage_preserves_event_core__g05_always_loop
       sg e ls0 ls_owner_cur eid Hentry_lookup Howner_stage) as
    (owner_event & Howner_lookup & Howner_type & Howner_fields).
  destruct
    (mutex_del_wake_steps_preserve_event_core__g05_always_loop
       sg eid ls_owner_cur ls_loop owner_event
       Howner_lookup Hwake_steps) as
    (current_event & Hcurrent_lookup & Hcurrent_type & Hcurrent_fields).
  pose proof Hsnapshot as Hsnapshot0.
  unfold event_snapshot_of_prop in Hsnapshot0.
  destruct Hsnapshot0 as
    (Hsnapshot_lookup & Hsnapshot_type & Hsnapshot_cnt &
     Hsnapshot_ptr & Hsnapshot_grp & Hsnapshot_tbl).
  rewrite Hsnapshot_lookup in Hcurrent_lookup.
  inversion Hcurrent_lookup; subst current_event.
  assert (Hcurrent_mutex_type :
    e_loop.(eventType) = OS_EVENT_TYPE_MUTEX) by congruence.
  assert (Hcurrent_mutex_fields :
    e_loop.(mutexFields) = Some m) by congruence.
  assert (Hvalid : valid_stable_glob_vars sg).
  {
    match goal with
    | Hrefresh : mutex_del_refresh_context_prop sg _ _ _ _ _ |- _ =>
        unfold mutex_del_refresh_context_prop in Hrefresh;
        tauto
    end.
  }
  pose proof
    (mutex_snapshot_pcp_lt64__g05_always_loop
       sg ls_loop eid e_loop m
       (encode_event_type e_loop.(eventType))
       ecnt_in eptr_in 0 evtL_loop
       Hvalid Hcross Hsnapshot Hcurrent_mutex_type
       Hcurrent_mutex_fields PreH1) as Hpcp_range.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r.
    exact (proj2 Hpcp_range).
  - apply derivable1s_coq_prop_r.
    exact (proj1 Hpcp_range).
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_1 : OSMutexDel_full_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_input_classification_prop in H2.
  destruct H2 as [Hzero | Hclass].
  - contradiction.
  - destruct Hclass as
      [Hnonzero [Hevent [Hvalid [Hlo [Hhi
       [Hsnapshot [Hcore [Hwait Hkind]]]]]]]].
    destruct Hkind as [Hnot_mutex | [Howner Hlineage]].
    + Left.
      sep_apply_l_atomic
        (mutex_del_event_focus_split
           sg ls0 eid e pevent_v
           (&((pevent_v) # "os_event" ->ₛ "OSEventType"))
           (&((pevent_v) # "os_event" ->ₛ "OSEventPtr"))
           (&((pevent_v) # "os_event" ->ₛ "OSEventCnt"))
           (&((pevent_v) # "os_event" ->ₛ "OSEventGrp"))
           (&((pevent_v) # "os_event" ->ₛ "OSEventTbl"))
           (&("OSEventFreeList"))
           etype ecnt_in eptr_in egrp_in evtL_in freelist_in
           Hsnapshot Hcore Hwait H1 H0 Hevent).
      LLM_pre_process ltac:(lia || nia || int_auto).
      split_pure_spatial.
      * repeat cancel.
        repeat first
          [ apply sepcon_cancel_end
          | apply derivable1_truep_intros ].
      * split_pures; apply derivable1s_coq_prop_r; assumption.
    + Right.
      sep_apply_l_atomic
        (mutex_del_event_focus_split
           sg ls0 eid e pevent_v
           (&((pevent_v) # "os_event" ->ₛ "OSEventType"))
           (&((pevent_v) # "os_event" ->ₛ "OSEventPtr"))
           (&((pevent_v) # "os_event" ->ₛ "OSEventCnt"))
           (&((pevent_v) # "os_event" ->ₛ "OSEventGrp"))
           (&((pevent_v) # "os_event" ->ₛ "OSEventTbl"))
           (&("OSEventFreeList"))
           etype ecnt_in eptr_in egrp_in evtL_in freelist_in
           Hsnapshot Hcore Hwait H1 H0 Hevent).
      LLM_pre_process ltac:(lia || nia || int_auto).
      split_pure_spatial.
      * repeat cancel.
        repeat first
          [ apply sepcon_cancel_end
          | apply derivable1_truep_intros ].
      * split_pures; apply derivable1s_coq_prop_r; assumption.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_2 : OSMutexDel_full_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (mutex_del_event_focus_open_interrupt sg ls0 eid).
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_3 : OSMutexDel_full_which_implies_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold os_int_nesting_addr in H.
  rewrite H.
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH1.
  asrt_simpl_pure.
  sepcon_assoc_change.
  andp_cancel.
  unfold os_int_nesting_addr.
  reflexivity.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_4 : OSMutexDel_full_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold os_int_nesting_addr in H.
  rewrite H.
  sep_apply_l_atomic
    (mutex_accept_interrupt_rebuild__restore_and_returns
       sg (IntrState ls0) isr PreH1).
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_5 : OSMutexDel_full_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (mutex_del_event_focus_close_interrupt sg ls0 eid).
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_6 : OSMutexDel_full_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold os_int_nesting_addr in H.
  rewrite H.
  sep_apply_l_atomic
    (mutex_accept_interrupt_rebuild__restore_and_returns
       sg (IntrState ls0) isr PreH1).
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_7 : OSMutexDel_full_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (mutex_del_event_focus_close_interrupt sg ls0 eid).
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_8 : OSMutexDel_full_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (mutex_del_event_owner_open_split
       sg ls0 eid e eptr_in owner_tid owner_t owner_prio
       (&((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
       PreH1 H).
  LLM_pre_process ltac:(lia || nia || int_auto).
  asrt_simpl_pure.
  sepcon_assoc_change.
  andp_cancel.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_9 : OSMutexDel_full_which_implies_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (mutex_del_owner_snapshot_nonnull_components
       sg ls0 e eptr_in owner_tid owner_t owner_prio
       (&((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
       PreH1 H) as [Hsnapshot Hlayout].
  unfold mutex_del_event_owner_open_inv,
    mutex_del_event_focus_inv.
  sep_apply_l_atomic
    (mutex_del_task_open_merge
       sg (TskState ls0) owner_tid owner_t eptr_in owner_prio
       (&((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
       Hsnapshot Hlayout).
  sepcon_assoc_change.
  cancel.
  andp_cancel.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_10 : OSMutexDel_full_which_implies_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (mutex_del_owner_stage_focus_split_priotbl__g07_entry_focus_rules
       sg e ls0 eid pcp
       ltac:(unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia)).
  Intros old_pcp_cell owner_post.
  Exists old_pcp_cell owner_post.
  cancel.
  andp_cancel.
  sepcon_assoc_change.
  cancel.
  match goal with
  | Haddr : os_tcb_prio_tbl_addr sg _ |- _ =>
      unfold os_tcb_prio_tbl_addr in Haddr;
      rewrite Haddr
  end.
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  unfold sizeof_front_end_type, sizeof_front_end_type_of_ptr_size,
    Arch32.ptr_size_Z, Arch32.ptr_size.
  change
    ((g_OSTCBPrioTbl sg + pcp * 4) # Ptr |-> old_pcp_cell |--
     (g_OSTCBPrioTbl sg + pcp * 4) # Ptr |-> old_pcp_cell).
  cancel.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_11 : OSMutexDel_full_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_no_pend_pcp_release_residual.
  Intros owner_post current_event current_tbl.
  Exists current_tbl current_event
    (encode_event_type current_event.(eventType)) owner_post.
  pose proof H4 as Hsource.
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as [Hpevent _].
  pose proof H2 as Hcore.
  unfold event_core_fields_layout_prop in Hcore.
  destruct Hcore as [Htype [Hptr Hcnt]].
  rewrite Htype, Hptr, <- Hpevent.
  destruct H5 as [Hstage [Hpcp [Hfree Hsnapshot]]].
  cancel.
  andp_cancel.
  - sepcon_assoc_change.
    repeat cancel.
    repeat first
      [ apply sepcon_cancel_end
      | apply derivable1_truep_intros ].
  - unfold event_core_fields_layout_prop.
    split.
    + rewrite Hpevent. reflexivity.
    + split.
      * rewrite Hpevent. reflexivity.
      * exact Hcnt.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_12 : OSMutexDel_full_which_implies_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_success_commit_inv.
  Intros critical_anchor commit.
  Exists commit critical_anchor.
  destruct H0 as [Hanchor [Hsource [Hmode Hsafe]]].
  cancel.
  andp_cancel.
  sepcon_assoc_change.
  repeat cancel.
  repeat first
    [ apply sepcon_cancel_end
    | apply derivable1_truep_intros ].
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_13 : OSMutexDel_full_which_implies_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_unchanged_inside_inv.
  pureIntros.
  destruct H as [Hsource [Hmode Hsafe]].
  unfold mutex_del_restore_rep.
  sepcon_assoc_change.
  cancel.
  andp_cancel.
  all: try assumption; try cancel.
  repeat apply sepcon_cancel_end.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_14 : OSMutexDel_full_which_implies_wit_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (mutex_del_event_owner_open_split
       sg ls0 eid e eptr_in owner_tid owner_t owner_prio
       (&((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
       PreH1 H).
  cancel.
  andp_cancel.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_15 : OSMutexDel_full_which_implies_wit_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (mutex_del_owner_snapshot_nonnull_components
       sg ls0 e eptr_in owner_tid owner_t owner_prio
       (&((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
       PreH1 H) as [Hsnapshot Hlayout].
  unfold mutex_del_event_owner_open_inv,
    mutex_del_event_focus_inv.
  sep_apply_l_atomic
    (mutex_del_task_open_merge
       sg ls0.(TskState) owner_tid owner_t
       eptr_in owner_prio
       (&((eptr_in) # "os_tcb" ->ₛ "OSTCBPrio"))
       Hsnapshot Hlayout).
  cancel.
  andp_cancel.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_16 : OSMutexDel_full_which_implies_wit_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_abort_loop_residual.
  Intros owner_post current current_event current_tbl.
  assert (Hrange : priotbl_index_in_range pcp) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  sep_apply_l_atomic
    (mutex_del_event_focus_split_priotbl
       sg ls0 current eid pcp Hrange).
  Intros old_pcp_cell.
  Exists old_pcp_cell.
  unfold mutex_del_abort_loop_missing_priotbl_residual.
  Exists owner_post current current_event current_tbl.
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  unfold os_tcb_prio_tbl_addr in H0.
  rewrite <- H0.
  rewrite sizeof_ptr.
  unfold Arch32.ptr_size_Z, Arch32.ptr_size.
  cbn.
  sepcon_assoc_change.
  cancel.
  andp_cancel.
  cancel.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_17 : OSMutexDel_full_which_implies_wit_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_abort_loop_pcp_release_residual,
    mutex_del_pcp_release_focus.
  destruct (Z.eqb pcp (osPrioMutexCeilDis sg)) eqn:Hpcp.
  - unfold mutex_del_abort_loop_residual.
    Intros owner_post current current_event current_tbl.
    match goal with
    | Hcore : event_core_fields_layout_prop sg eid _ _ _ |- _ =>
        pose proof Hcore as Hlayout;
        unfold event_core_fields_layout_prop in Hcore;
        destruct Hcore as [Htype_addr [Hptr_addr Hcnt_addr]]
    end.
    match goal with
    | Hsrc : mutex_del_source_entry_prop sg e ls0 eid pevent tasks_v |- _ =>
        pose proof Hsrc as Hsource;
        unfold mutex_del_source_entry_prop in Hsrc;
        destruct Hsrc as [Hbase Hsource_rest]
    end.
    rewrite <- Hbase in Htype_addr, Hptr_addr.
    match goal with
    | Hfacts : mutex_del_rdyatprio_stage_prop sg e ls0 owner_post /\
                 mutex_del_wake_steps sg eid owner_post current /\
                 event_free_list_head_prop sg current.(EventState) freelist_in /\
                 event_snapshot_of_prop sg current.(TskState)
                   current.(EventState) eid current_event _ ecnt_in eptr_in 0 current_tbl
               |- _ =>
        destruct Hfacts as [Hstage [Hwake [Hfree Hsnapshot]]]
    end.
    assert (Hsuccess : mutex_del_success_mode_prop opt_abs tasks_v).
    { match goal with
      | Hmode : mutex_del_always_mode_prop opt_abs tasks_v |- _ =>
          pose proof Hmode as Halways
      end.
      unfold mutex_del_always_mode_prop in Halways.
      destruct Halways as [Hopt Htasks].
      subst opt_abs.
      exact Htasks. }
    Exists current_tbl owner_post current_event
      (encode_event_type current_event.(eventType)) current.
    rewrite Htype_addr, Hptr_addr.
    sepcon_assoc_change.
    cancel.
    andp_cancel.
    all: try assumption; try cancel.
    all: try apply derivable1_truep_intros.
    + repeat apply sepcon_cancel_end.
      all: apply derivable1_truep_intros.
    + unfold event_core_fields_layout_prop.
      repeat split; try reflexivity.
      * now rewrite Hbase.
      * now rewrite Hbase.
      * exact Hcnt_addr.
  - unfold mutex_del_abort_loop_missing_priotbl_residual.
    Intros owner_post current current_event current_tbl.
    match goal with
    | Hcore : event_core_fields_layout_prop sg eid _ _ _ |- _ =>
        pose proof Hcore as Hlayout;
        unfold event_core_fields_layout_prop in Hcore;
        destruct Hcore as [Htype_addr [Hptr_addr Hcnt_addr]]
    end.
    match goal with
    | Hsrc : mutex_del_source_entry_prop sg e ls0 eid pevent tasks_v |- _ =>
        pose proof Hsrc as Hsource;
        unfold mutex_del_source_entry_prop in Hsrc;
        destruct Hsrc as [Hbase Hsource_rest]
    end.
    rewrite <- Hbase in Htype_addr, Hptr_addr.
    match goal with
    | Hfacts : mutex_del_rdyatprio_stage_prop sg e ls0 owner_post /\
                 mutex_del_wake_steps sg eid owner_post current /\
                 event_free_list_head_prop sg current.(EventState) freelist_in /\
                 event_snapshot_of_prop sg current.(TskState)
                   current.(EventState) eid current_event _ ecnt_in eptr_in 0 current_tbl
               |- _ =>
        destruct Hfacts as [Hstage [Hwake [Hfree Hsnapshot]]]
    end.
    assert (Hsuccess : mutex_del_success_mode_prop opt_abs tasks_v).
    { match goal with
      | Hmode : mutex_del_always_mode_prop opt_abs tasks_v |- _ =>
          pose proof Hmode as Halways
      end.
      unfold mutex_del_always_mode_prop in Halways.
      destruct Halways as [Hopt Htasks].
      subst opt_abs.
      exact Htasks. }
    Exists current_tbl owner_post current_event
      (encode_event_type current_event.(eventType)) current.
    rewrite Htype_addr, Hptr_addr.
    sepcon_assoc_change.
    cancel.
    andp_cancel.
    all: try assumption; try cancel.
    all: try apply derivable1_truep_intros.
    + repeat apply sepcon_cancel_end.
      all: apply derivable1_truep_intros.
    + unfold event_core_fields_layout_prop.
      repeat split; try reflexivity.
      * now rewrite Hbase.
      * now rewrite Hbase.
      * exact Hcnt_addr.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_18 : OSMutexDel_full_which_implies_wit_18.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_success_commit_inv.
  Intros critical_anchor ls_commit.
  destruct H0 as [Hcommit [Hsource [Hmode Hsafe]]].
  Exists ls_commit critical_anchor.
  sepcon_assoc_change.
  cancel.
  andp_cancel.
  all: try assumption; try cancel.
  repeat apply sepcon_cancel_end.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_19 : OSMutexDel_full_which_implies_wit_19.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_success_exit_inv.
  Intros critical_anchor ls_commit ls_exited.
  destruct H as
    [Hcommit [Hsource [Hmode [Hexit [Hvalid [Hstable Hsafe]]]]]].
  Exists critical_anchor ls_commit ls_exited.
  sepcon_assoc_change.
  cancel (OutsideCritical sg ls_exited).
  unfold mutex_del_transition_rep.
  Left.
  sepcon_assoc_change.
  cancel.
  andp_cancel.
  all: try assumption; try cancel.
  repeat apply sepcon_cancel_end.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_20 : OSMutexDel_full_which_implies_wit_20.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutex_del_unchanged_inside_inv.
  pureIntros.
  destruct H as [Hsource [Hmode Hsafe]].
  unfold mutex_del_restore_rep.
  sepcon_assoc_change.
  cancel.
  andp_cancel.
  all: try assumption; try cancel.
  repeat apply sepcon_cancel_end.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexDel_full_which_implies_wit_21 : OSMutexDel_full_which_implies_wit_21.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof H as Hsource.
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as [Hbase Hsource_rest].
  sep_apply_l_atomic
    (mutex_del_event_focus_merge
       sg ls0 eid e pevent
       (&((pevent) # "os_event" ->ₛ "OSEventType"))
       (&((pevent) # "os_event" ->ₛ "OSEventPtr"))
       (&((pevent) # "os_event" ->ₛ "OSEventCnt"))
       (&((pevent) # "os_event" ->ₛ "OSEventGrp"))
       (&((pevent) # "os_event" ->ₛ "OSEventTbl"))
       (&("OSEventFreeList"))
       4 ecnt_in eptr_in egrp_in evtL_in freelist_in
       H4 H3 H2 H1 H0 Hbase).
  cancel.
  andp_cancel.
  apply derivable1_truep_intros.
Qed.
