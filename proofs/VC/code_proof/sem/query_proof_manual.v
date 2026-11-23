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
From Ucos2Verify.VC.code.sem Require Import query_goal.
From Ucos2Verify.VC.code.sem Require Import query_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_source_api_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.mutex_query_spec.
Local Open Scope sac.

Lemma proof_of_OSSemQuery_entail_wit_1_2 : OSSemQuery_entail_wit_1_2.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType")) (event_slot_type_value before.(EventState) eid)).
  entailer!.
Qed. 

Lemma proof_of_OSSemQuery_entail_wit_2 : OSSemQuery_entail_wit_2.
Proof.
  pre_process. Exists entry_2 current_2 cnt_2 grp_2 evtL_2. entailer!.
Qed. 

Lemma proof_of_OSSemQuery_entail_wit_3 : OSSemQuery_entail_wit_3.
Proof.
  pre_process. Exists entry_2 current_2 cnt_2 grp_2 evtL_2. entailer!.
  all: cbn in PreH2, PreH3 |- *; lia.
Qed. 

Lemma proof_of_OSSemQuery_return_wit_1 : OSSemQuery_return_wit_1.
Proof.
  pre_process.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry observed current) by assumption.
  assert (Hsnapshot : mutex_query_copy_snapshot entry eid current cnt grp evtL) by assumption.
  pose proof Hfacts as [Hentry [_ [_ [_ [_ [_ [Htype _]]]]]]].
  set (snapshot := {| sem_query_count := cnt; sem_query_group := grp; sem_query_table := evtL |}).
  assert (Hread : sem_query_source_api_read eid entry snapshot entry).
  { exists current; split; [exact Hsnapshot|auto]. }
  assert (Hprogram : sem_query_source_api_program critical sg invocation eid pe pd before
    (0, Some snapshot) after).
  { eapply sem_query_source_api_success; try eassumption; congruence. }
  pose proof (sem_query_source_api_safe_return critical sg invocation eid pe pd before after
    0 (Some snapshot) X Hprogram PreH26) as Hsafe.
  assert (Hsrclen : Zlength evtL = OS_EVENT_TBL_SIZE).
  { destruct Hsnapshot as [_ [_ [_ Htable]]]; rewrite Htable.
    unfold encode_event_wait_tbl_values, OS_EVENT_TBL_SIZE; reflexivity. }
  sep_apply_l_atomic (sem_query_output_table_complete
    (&(pd # "os_sem_data" ->ₛ "OSEventTbl")) evtL i Hsrclen
    ltac:(unfold OS_EVENT_TBL_SIZE; lia)).
  unfold sem_query_source_api_post; Exists (Some snapshot) after.
  cbn [sem_query_source_api_output snapshot sem_query_count sem_query_group sem_query_table].
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemQuery_return_wit_2 : OSSemQuery_return_wit_2.
Proof.
  pre_process.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Htypeaddr : (&(pe # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off) by assumption.
  assert (Hwrong : event_slot_type_value before.(EventState) eid <> 3) by assumption.
  assert (Hprogram : sem_query_source_api_program critical sg invocation eid pe pd before (1, None) before).
  { eapply sem_query_source_api_wrong_type_return; try eassumption; congruence. }
  pose proof (sem_query_source_api_safe_return critical sg invocation eid pe pd before before
    1 None X Hprogram PreH12) as Hsafe.
  unfold sem_query_source_api_post; Exists (@None SemQuerySnapshot) before.
  cbn [sem_query_source_api_output].
  rewrite Htypeaddr.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  rewrite mutex_query_closed_equiv.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemQuery_return_wit_3 : OSSemQuery_return_wit_3.
Proof.
  pre_process.
  assert (Hzero : pd = 0) by congruence.
  assert (Hprogram : sem_query_source_api_program critical sg invocation eid pe pd before (9, None) before).
  { rewrite Hzero; apply sem_query_source_api_null_data_return; congruence. }
  pose proof (sem_query_source_api_safe_return critical sg invocation eid pe pd before before
    9 None X Hprogram PreH5) as Hsafe.
  unfold sem_query_source_api_post; Exists (@None SemQuerySnapshot) before.
  cbn [sem_query_source_api_output].
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemQuery_return_wit_4 : OSSemQuery_return_wit_4.
Proof.
  pre_process.
  assert (Hzero : pe = 0) by congruence.
  assert (Hprogram : sem_query_source_api_program critical sg invocation eid pe pd before (4, None) before).
  { rewrite Hzero; apply sem_query_source_api_null_event_return. }
  pose proof (sem_query_source_api_safe_return critical sg invocation eid pe pd before before
    4 None X Hprogram PreH4) as Hsafe.
  unfold sem_query_source_api_post; Exists (@None SemQuerySnapshot) before.
  cbn [sem_query_source_api_output].
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_1 : OSSemQuery_which_implies_wit_1.
Proof.
  pre_process.
  assert (Hinput : sem_query_call_input critical sg invocation pe pd before eid observed) by assumption.
  destruct (sem_query_call_input_live critical sg invocation pe pd before eid observed Hinput
    PreH1 PreH2) as [Haddr [Hid [Hlookup Hprotocol]]].
  rewrite mutex_query_closed_equiv.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hlookup).
  assert (Htypeaddr : (&(pe # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off) by assumption.
  rewrite Htypeaddr in *.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_2 : OSSemQuery_which_implies_wit_2.
Proof.
  pre_process.
  assert (Hinput : sem_query_call_input critical sg invocation pe pd before eid observed) by assumption.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  destruct (sem_query_call_input_live critical sg invocation pe pd before eid observed Hinput
    PreH1 PreH2) as [Haddr [Hid [Hlookup Hprotocol]]].
  specialize (Hprotocol PreH3).
  destruct (sem_query_public_slot_is_sem before eid observed Hlookup PreH3) as [Hused Htype].
  assert (Hencoded : encode_event_type observed.(eventType) = 3) by (rewrite Htype; reflexivity).
  assert (Htypeaddr : (&(pe # "os_event" ->ₛ "OSEventType")) =
    event_addr sg eid + OSEventType_off) by assumption.
  rewrite Htypeaddr in *.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_3 : OSSemQuery_which_implies_wit_3.
Proof.
  pre_process.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  sep_apply_l_atomic (sem_query_copy_fields_split_full sg entry_2 eid current_2 Hlookup Htype).
  Intros count group table.
  Exists count group table entry_2 current_2.
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  destruct Hlayout as [Htypeaddr [_ Hcntaddr]].
  rewrite Htypeaddr, Hcntaddr, PreH1 in *.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: assumption.
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_4 : OSSemQuery_which_implies_wit_4.
Proof.
  pre_process.
  Exists cnt_2 grp_2 evtL_2 entry_2 current_2.
  assert (Hsnap : mutex_query_copy_snapshot entry_2 eid current_2 cnt_2 grp_2 evtL_2) by assumption.
  assert (Hlayout : event_wait_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventGrp")) (&(pe # "os_event" ->ₛ "OSEventTbl"))) by assumption.
  destruct Hlayout as [Hgrpaddr Htbladdr].
  sep_apply_l_atomic (mutex_query_copy_table_group_split sg entry_2 eid current_2 pe
    (&(pe # "os_event" ->ₛ "OSEventGrp")) cnt_2 grp_2 evtL_2 Hsnap PreH1 Hgrpaddr).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_5 : OSSemQuery_which_implies_wit_5.
Proof.
  pre_process.
  Exists entry_2 current_2 cnt_2 grp_2 evtL_2.
  assert (Hcore : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  assert (Hwait : event_wait_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventGrp")) (&(pe # "os_event" ->ₛ "OSEventTbl"))) by assumption.
  destruct Hcore as [Htypeaddr [_ Hcntaddr]]; destruct Hwait as [Hgrpaddr Htbladdr].
  unfold sem_query_copy_frame, sem_query_output_fields.
  rewrite Htypeaddr, Hcntaddr, Hgrpaddr in *.
  normalize.
  Intros.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_6 : OSSemQuery_which_implies_wit_6.
Proof.
  pre_process.
  Exists entry_2 current_2 cnt_2 grp_2 evtL_2.
  sep_apply_l_atomic (sem_query_output_table_init
    (&(pd # "os_sem_data" ->ₛ "OSEventTbl")) evtL_2).
  entailer!.
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_7 : OSSemQuery_which_implies_wit_7.
Proof.
  pre_process.
  Exists entry_2 current_2 cnt_2 grp_2 evtL_2.
  assert (Hlayout : event_wait_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventGrp")) (&(pe # "os_event" ->ₛ "OSEventTbl"))) by assumption.
  destruct Hlayout as [Hgrp Htbl].
  unfold store_oseventtbl.
  sep_apply_l_atomic
    (store_array_split_to_missing_i Z oseventtbl_element_store
       (pe + OSEventTbl_off) i OS_EVENT_TBL_SIZE evtL_2 0 ltac:(
         unfold OS_EVENT_TBL_SIZE; lia)).
  sep_apply_l_atomic (sem_query_output_table_split
    (&(pd # "os_sem_data" ->ₛ "OSEventTbl")) evtL_2 i
    ltac:(unfold OS_EVENT_TBL_SIZE; lia)).
  unfold store_oseventtbl_missing_i.
  unfold oseventtbl_element_store, sizeof_OS_PRIO.
  entailer!.
  - simpl in PreH4, PreH5, Htbl.
    change (psrc_v =
      &(pe # "os_event" ->ₛ "OSEventTbl") + i * 1) in PreH4.
    change (pdest_v =
      &(pd # "os_sem_data" ->ₛ "OSEventTbl") + i * 1) in PreH5.
    assert (Hsrcaddr : psrc_v = pe + OSEventTbl_off + i * 1) by lia.
    assert (Hdstaddr :
      pdest_v = (&(pd # "os_sem_data" ->ₛ "OSEventTbl")) + i * 1)
      by lia.
    rewrite Hsrcaddr, Hdstaddr.
    entailer!.
    rewrite Z.mul_1_r; reflexivity.
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_8 : OSSemQuery_which_implies_wit_8.
Proof.
  pre_process.
  Exists entry_2 current_2 cnt_2 grp_2 evtL_2 pdest_v_2 psrc_v_2.
  assert (Hlayout : event_wait_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventGrp")) (&(pe # "os_event" ->ₛ "OSEventTbl"))) by assumption.
  destruct Hlayout as [Hgrp Htbl].
  simpl in Htbl, PreH2, PreH3.
  change (psrc_v_2 =
    &(pe # "os_event" ->ₛ "OSEventTbl") + i * 1) in PreH2.
  change (pdest_v_2 =
    &(pd # "os_sem_data" ->ₛ "OSEventTbl") + i * 1) in PreH3.
  assert (Hsrcaddr : psrc_v_2 = pe + OSEventTbl_off + i * 1) by lia.
  assert (Hdstaddr :
    pdest_v_2 = (&(pd # "os_sem_data" ->ₛ "OSEventTbl")) + i * 1)
    by lia.
  rewrite Hsrcaddr, Hdstaddr.
  unfold store_oseventtbl_missing_i.
  unfold oseventtbl_element_store, sizeof_OS_PRIO.
  prop_apply
    (store_array_missing_index_bounds__array_loop_and_returns
       Z (fun base idx value => (base + idx * 1) # UChar |-> value)
       (pe + OSEventTbl_off) i 0 OS_EVENT_TBL_SIZE evtL_2).
  Intros_p Hrange.
  prop_apply
    (store_array_missing_i_rec_Zlength Z
       (fun base idx value => (base + idx * 1) # UChar |-> value)
       (pe + OSEventTbl_off) i 0 OS_EVENT_TBL_SIZE evtL_2).
  Intros_p Hsrclen.
  sep_apply_l_atomic
    (store_array_missing_i_merge_to_array Z
       (fun base idx value => (base + idx * 1) # UChar |-> value)
       (pe + OSEventTbl_off) i OS_EVENT_TBL_SIZE
       (Znth i evtL_2 0) evtL_2 Hrange).
  rewrite (replace_Znth_Znth i evtL_2 0).
  replace ((&(pd # "os_sem_data" ->ₛ "OSEventTbl")) + i * 1) with
    ((&(pd # "os_sem_data" ->ₛ "OSEventTbl")) + i) by lia.
  sep_apply_l_atomic (sem_query_output_table_merge
    (&(pd # "os_sem_data" ->ₛ "OSEventTbl")) evtL_2 i ltac:(lia)).
  unfold store_oseventtbl.
  unfold oseventtbl_element_store, sizeof_OS_PRIO.
  entailer!.
  all: try solve [unfold event_wait_fields_layout_prop; split; assumption].
  all: cbn; lia.
Qed. 

Lemma proof_of_OSSemQuery_which_implies_wit_9 : OSSemQuery_which_implies_wit_9.
Proof.
  pre_process.
  Exists cnt_2 grp_2 evtL_2 entry_2 current_2.
  assert (Hcore : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  destruct Hcore as [_ [_ Hcount]].
  sep_apply_l_atomic (sem_query_copy_frame_restore platform critical sg invocation origin mask cpu_sr
    before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 pe
    (&(pe # "os_event" ->ₛ "OSEventCnt")) PreH1 Hcount).
  Intros.
  assert (Hfacts : sem_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry_2 observed current_2) by tauto.
  pose proof Hfacts as [_ [Hvalid [Hsaved _]]].
  unfold sem_query_source_api_restore_pre.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed. 
