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
From Ucos2Verify.VC.code.mutex Require Import query_goal.
From Ucos2Verify.VC.code.mutex Require Import query_proof_auto.
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
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.mutex_query_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexQuery_safety_wit_23 : OSMutexQuery_safety_wit_23.
Proof.
  pre_process.
  prop_apply_p (store_ushort_range (&(pe # "os_event" ->ₛ "OSEventCnt")) cnt).
  entailer!.
Qed.

Lemma proof_of_OSMutexQuery_entail_wit_1_5 : OSMutexQuery_entail_wit_1_5.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) isr).
  entailer!.
Qed.

Lemma proof_of_OSMutexQuery_entail_wit_2_2 : OSMutexQuery_entail_wit_2_2.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType")) (encode_event_type (eventType observed))).
  entailer!.
Qed.

Lemma proof_of_OSMutexQuery_entail_wit_3_1 : OSMutexQuery_entail_wit_3_1.
Proof.
  pre_process.
  Exists entry_3 current_3 cnt_4 grp_3 evtL_3.
  entailer!.
Qed.

Lemma proof_of_OSMutexQuery_entail_wit_3_2 : OSMutexQuery_entail_wit_3_2.
Proof.
  pre_process.
  Exists entry_3 current_3 cnt_4 grp_3 evtL_3.
  entailer!.
Qed.

Lemma proof_of_OSMutexQuery_entail_wit_4_1 : OSMutexQuery_entail_wit_4_1.
Proof.
  pre_process.
  Exists entry_3 current_3 cnt_4 grp_3 evtL_3.
  entailer!.
  all: cbn in PreH2, PreH3 |- *; lia.
Qed.

Lemma proof_of_OSMutexQuery_entail_wit_4_2 : OSMutexQuery_entail_wit_4_2.
Proof.
  pre_process.
  Exists entry_3 current_3 cnt_4 grp_3 evtL_3.
  entailer!.
  all: cbn in PreH2, PreH3 |- *; lia.
Qed.

Lemma proof_of_OSMutexQuery_return_wit_1 : OSMutexQuery_return_wit_1.
Proof.
  pre_process.
  assert (Hfacts : mutex_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry observed current_2) by assumption.
  assert (Hsnapshot : mutex_query_copy_snapshot entry eid current_2 cnt_3 grp_2 evtL_2) by assumption.
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Hprogram : mutex_query_call_program critical sg invocation pe pd before 0 entry).
  { eapply (mutex_query_call_success critical sg invocation pe pd before eid observed mask cpu_sr entry current_2);
      try eassumption; try lia; congruence. }
  assert (Hsafe : safeExec (LastSeen entry) (return 0) X).
  { eapply (mutex_accept_safe_return__restore_and_returns Z Z
      (mutex_query_call_program critical sg invocation pe pd) mutex_query_observe_error
      before entry 0 0 X).
    - exact Hprogram.
    - intros P; unfold mutex_query_observe_error; split; reflexivity.
    - assumption. }
  pose proof Hfacts as [_ [_ [_ [_ [_ [_ [Htype _]]]]]]].
  assert (Hencoded : encode_event_type (eventType current_2) = 4) by (rewrite Htype; reflexivity).
  assert (Hsrclen : Zlength evtL_2 = OS_EVENT_TBL_SIZE).
  { destruct Hsnapshot as [_ [_ [_ Htable]]]; rewrite Htable.
    unfold encode_event_wait_tbl_values, OS_EVENT_TBL_SIZE; reflexivity. }
  sepcon_lift (store_osprio_array (&(pd # "os_mutex_data" ->ₛ "OSEventTbl"))
    (copy_prefix_list evtL_2 outL_in i)).
  unfold store_osprio_array.
  prop_apply (store_array_Zlength__array_loop_and_returns Z oseventtbl_element_store
    (&(pd # "os_mutex_data" ->ₛ "OSEventTbl")) OS_EVENT_TBL_SIZE (copy_prefix_list evtL_2 outL_in i)).
  Intros_p Hdstlen.
  assert (Hcopy : copy_prefix_list evtL_2 outL_in i = evtL_2).
  { unfold copy_prefix_list in Hdstlen |- *.
    apply list_copy_prefix_complete_at_bound__array_loop_and_returns.
    - unfold OS_EVENT_TBL_SIZE in Hsrclen; lia.
    - lia. }
  rewrite Hcopy.
  Exists current_2 cnt_3 grp_2 evtL_2 entry.
  unfold mutex_query_call_post_prop.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_return_wit_2 : OSMutexQuery_return_wit_2.
Proof.
  pre_process.
  assert (Hfacts : mutex_query_acquire_facts critical sg invocation eid mask cpu_sr
    before entry observed current_2) by assumption.
  assert (Hsnapshot : mutex_query_copy_snapshot entry eid current_2 cnt_3 grp_2 evtL_2) by assumption.
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Hprogram : mutex_query_call_program critical sg invocation pe pd before 0 entry).
  { eapply (mutex_query_call_success critical sg invocation pe pd before eid observed mask cpu_sr entry current_2);
      try eassumption; try lia; congruence. }
  assert (Hsafe : safeExec (LastSeen entry) (return 0) X).
  { eapply (mutex_accept_safe_return__restore_and_returns Z Z
      (mutex_query_call_program critical sg invocation pe pd) mutex_query_observe_error
      before entry 0 0 X).
    - exact Hprogram.
    - intros P; unfold mutex_query_observe_error; split; reflexivity.
    - assumption. }
  pose proof Hfacts as [_ [_ [_ [_ [_ [_ [Htype _]]]]]]].
  assert (Hencoded : encode_event_type (eventType current_2) = 4) by (rewrite Htype; reflexivity).
  assert (Hsrclen : Zlength evtL_2 = OS_EVENT_TBL_SIZE).
  { destruct Hsnapshot as [_ [_ [_ Htable]]]; rewrite Htable.
    unfold encode_event_wait_tbl_values, OS_EVENT_TBL_SIZE; reflexivity. }
  sepcon_lift (store_osprio_array (&(pd # "os_mutex_data" ->ₛ "OSEventTbl"))
    (copy_prefix_list evtL_2 outL_in i)).
  unfold store_osprio_array.
  prop_apply (store_array_Zlength__array_loop_and_returns Z oseventtbl_element_store
    (&(pd # "os_mutex_data" ->ₛ "OSEventTbl")) OS_EVENT_TBL_SIZE (copy_prefix_list evtL_2 outL_in i)).
  Intros_p Hdstlen.
  assert (Hcopy : copy_prefix_list evtL_2 outL_in i = evtL_2).
  { unfold copy_prefix_list in Hdstlen |- *.
    apply list_copy_prefix_complete_at_bound__array_loop_and_returns.
    - unfold OS_EVENT_TBL_SIZE in Hsrclen; lia.
    - lia. }
  rewrite Hcopy.
  Exists current_2 cnt_3 grp_2 evtL_2 entry.
  unfold mutex_query_call_post_prop.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_return_wit_3 : OSMutexQuery_return_wit_3.
Proof.
  pre_process.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hlookup : mutex_query_lookup before eid observed) by assumption.
  assert (Hid : valid_event_id sg eid) by assumption.
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  assert (Hwrong : eventType observed <> OS_EVENT_TYPE_MUTEX).
  { intro Htype; apply PreH1; rewrite Htype; reflexivity. }
  assert (Hprogram : mutex_query_call_program critical sg invocation pe pd before 1 before).
  { eapply mutex_query_call_wrong_type_return; try eassumption; try lia; congruence. }
  assert (Hsafe : safeExec (LastSeen before) (return 1) X).
  { eapply (mutex_accept_safe_return__restore_and_returns Z Z
      (mutex_query_call_program critical sg invocation pe pd) mutex_query_observe_error
      before before 1 1 X).
    - exact Hprogram.
    - intros P; unfold mutex_query_observe_error; split; reflexivity.
    - assumption. }
  Exists before.
  unfold mutex_query_call_post_prop.
  destruct Hlayout as [Htypeaddr _]; rewrite Htypeaddr.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (mutex_query_type_merge_full sg before eid observed Hvalid Hlookup).
  rewrite mutex_query_closed_equiv.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_return_wit_4 : OSMutexQuery_return_wit_4.
Proof.
  pre_process.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Haddr : os_int_nesting_addr sg (&("OSIntNesting"))) by assumption.
  assert (Hcounter : isr = intNesting (IntrState before)) by assumption.
  assert (Hpd0 : pd = 0) by congruence.
  assert (Hprogram : mutex_query_call_program critical sg invocation pe pd before 9 before).
  { rewrite Hpd0; apply mutex_query_call_null_data_return; try lia; congruence. }
  assert (Hsafe : safeExec (LastSeen before) (return 9) X).
  { eapply (mutex_accept_safe_return__restore_and_returns Z Z
      (mutex_query_call_program critical sg invocation pe pd) mutex_query_observe_error
      before before 9 9 X).
    - exact Hprogram.
    - intros P; unfold mutex_query_observe_error; split; reflexivity.
    - assumption. }
  Exists before.
  unfold mutex_query_call_post_prop, os_int_nesting_addr in *.
  rewrite Haddr.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (mutex_query_interrupt_merge_full sg before isr Hvalid Hcounter).
  rewrite mutex_query_closed_equiv.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_return_wit_5 : OSMutexQuery_return_wit_5.
Proof.
  pre_process.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Haddr : os_int_nesting_addr sg (&("OSIntNesting"))) by assumption.
  assert (Hcounter : isr = intNesting (IntrState before)) by assumption.
  assert (Hpe0 : pe = 0) by congruence.
  assert (Hprogram : mutex_query_call_program critical sg invocation pe pd before 4 before).
  { rewrite Hpe0; apply mutex_query_call_null_event_return; lia. }
  assert (Hsafe : safeExec (LastSeen before) (return 4) X).
  { eapply (mutex_accept_safe_return__restore_and_returns Z Z
      (mutex_query_call_program critical sg invocation pe pd) mutex_query_observe_error
      before before 4 4 X).
    - exact Hprogram.
    - intros P; unfold mutex_query_observe_error; split; reflexivity.
    - assumption. }
  Exists before.
  unfold mutex_query_call_post_prop, os_int_nesting_addr in *.
  rewrite Haddr.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (mutex_query_interrupt_merge_full sg before isr Hvalid Hcounter).
  rewrite mutex_query_closed_equiv.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_return_wit_6 : OSMutexQuery_return_wit_6.
Proof.
  pre_process.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Haddr : os_int_nesting_addr sg (&("OSIntNesting"))) by assumption.
  assert (Hcounter : isr = intNesting (IntrState before)) by assumption.
  assert (Hprogram : mutex_query_call_program critical sg invocation pe pd before 6 before).
  { apply mutex_query_call_isr_return; lia. }
  assert (Hsafe : safeExec (LastSeen before) (return 6) X).
  { eapply (mutex_accept_safe_return__restore_and_returns Z Z
      (mutex_query_call_program critical sg invocation pe pd) mutex_query_observe_error
      before before 6 6 X).
    - exact Hprogram.
    - intros P; unfold mutex_query_observe_error; split; reflexivity.
    - assumption. }
  Exists before.
  unfold mutex_query_call_post_prop, os_int_nesting_addr in *.
  rewrite Haddr.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (mutex_query_interrupt_merge_full sg before isr Hvalid Hcounter).
  rewrite mutex_query_closed_equiv.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_partial_solve_wit_13_pure : OSMutexQuery_partial_solve_wit_13_pure.
Proof.
  unfold OSMutexQuery_partial_solve_wit_13_pure; right; intros.
  unfold decode_OSValue_from_cnt, decode_OwnerPrio_from_cnt, decode_PCP_from_cnt.
  assert (Hbit : Z.eqb (Z.land cnt 255) 255 = false) by (apply Z.eqb_neq; exact PreH3).
  rewrite Hbit.
  split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_OSMutexQuery_partial_solve_wit_14_pure : OSMutexQuery_partial_solve_wit_14_pure.
Proof.
  unfold OSMutexQuery_partial_solve_wit_14_pure; right; intros.
  unfold decode_OSValue_from_cnt, decode_OwnerPrio_from_cnt, decode_PCP_from_cnt.
  assert (Hbit : Z.eqb (Z.land cnt 255) 255 = true) by (apply Z.eqb_eq; exact PreH3).
  rewrite Hbit.
  split_pures; dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_1 : OSMutexQuery_which_implies_wit_1.
Proof.
  pre_process.
  rewrite mutex_query_closed_equiv.
  sep_apply_l_atomic (mutex_query_interrupt_split_full sg before).
  unfold os_int_nesting_addr in H.
  rewrite H, PreH1.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_2 : OSMutexQuery_which_implies_wit_2.
Proof.
  pre_process.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Haddr : os_int_nesting_addr sg (&("OSIntNesting"))) by assumption.
  unfold os_int_nesting_addr in Haddr; rewrite Haddr.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (mutex_query_interrupt_merge_full sg before isr Hvalid PreH1).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_3 : OSMutexQuery_which_implies_wit_3.
Proof.
  pre_process.
  assert (Hinput : mutex_query_call_input critical sg invocation pe pd before eid observed) by assumption.
  destruct (mutex_query_call_input_live critical sg invocation pe pd before eid observed Hinput
    ltac:(lia) PreH3 PreH4) as [Haddr [Hid [Hlookup Hprotocol]]].
  sep_apply_l_atomic (mutex_query_type_split_full sg before eid observed Hlookup).
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  destruct Hlayout as [Htypeaddr _].
  rewrite Htypeaddr in *.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_4 : OSMutexQuery_which_implies_wit_4.
Proof.
  pre_process.
  assert (Hinput : mutex_query_call_input critical sg invocation pe pd before eid observed) by assumption.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  destruct (mutex_query_call_input_live critical sg invocation pe pd before eid observed Hinput
    ltac:(lia) PreH3 PreH4) as [Haddr [Hid [Hlookup Hprotocol]]].
  specialize (Hprotocol (mutex_query_encoded_type_is_mutex observed PreH5)).
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  destruct Hlayout as [Htypeaddr _]; rewrite Htypeaddr in *.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  sep_apply_l_atomic (mutex_query_type_merge_full sg before eid observed Hvalid Hlookup).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_5 : OSMutexQuery_which_implies_wit_5.
Proof.
  pre_process.
  assert (Hfacts : mutex_query_acquire_facts critical sg invocation eid mask cpu_sr before entry_2 observed current_2) by assumption.
  pose proof Hfacts as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  sep_apply_l_atomic (mutex_query_copy_fields_split_full sg entry_2 eid current_2 Hlookup Htype).
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

Lemma proof_of_OSMutexQuery_which_implies_wit_6 : OSMutexQuery_which_implies_wit_6.
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

Lemma proof_of_OSMutexQuery_which_implies_wit_7 : OSMutexQuery_which_implies_wit_7.
Proof.
  pre_process.
  Exists entry_2 current_2 cnt_2 grp_2 evtL_2.
  assert (Hcore : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  assert (Hwait : event_wait_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventGrp")) (&(pe # "os_event" ->ₛ "OSEventTbl"))) by assumption.
  destruct Hcore as [Htypeaddr [_ Hcntaddr]]; destruct Hwait as [Hgrpaddr Htbladdr].
  unfold mutex_query_copy_frame, mutex_query_output_fields.
  rewrite Htypeaddr, Hcntaddr, Hgrpaddr in *.
  normalize.
  Intros.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_8 : OSMutexQuery_which_implies_wit_8.
Proof.
  pre_process.
  Exists entry_2 current_2 cnt_2 grp_2 evtL_2.
  unfold copy_prefix_list; simpl; entailer!.
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_9 : OSMutexQuery_which_implies_wit_9.
Proof.
  pre_process.
  Exists entry_2 current_2 cnt_2 grp_2 evtL_2.
  assert (Hlayout : event_wait_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventGrp")) (&(pe # "os_event" ->ₛ "OSEventTbl"))) by assumption.
  destruct Hlayout as [Hgrp Htbl].
  unfold store_oseventtbl, store_osprio_array.
  sep_apply_l_atomic
    (store_array_split_to_missing_i Z oseventtbl_element_store
       (pe + OSEventTbl_off) i OS_EVENT_TBL_SIZE evtL_2 0 ltac:(
         unfold OS_EVENT_TBL_SIZE; lia)).
  sep_apply_l_atomic
    (store_array_split_to_missing_i Z oseventtbl_element_store
       (&(pd # "os_mutex_data" ->ₛ "OSEventTbl"))
       i OS_EVENT_TBL_SIZE (copy_prefix_list evtL_2 outL_in i) 0 ltac:(
         unfold OS_EVENT_TBL_SIZE; lia)).
  unfold store_oseventtbl_missing_i, store_osprio_array_missing_i.
  unfold oseventtbl_element_store, sizeof_OS_PRIO.
  entailer!.
  - simpl in PreH4, PreH5, Htbl.
    change (psrc_v =
      &(pe # "os_event" ->ₛ "OSEventTbl") + i * 1) in PreH4.
    change (pdest_v =
      &(pd # "os_mutex_data" ->ₛ "OSEventTbl") + i * 1) in PreH5.
    assert (Hsrcaddr : psrc_v = pe + OSEventTbl_off + i * 1) by lia.
    assert (Hdstaddr :
      pdest_v = (&(pd # "os_mutex_data" ->ₛ "OSEventTbl")) + i * 1)
      by lia.
    rewrite Hsrcaddr, Hdstaddr.
    entailer!.
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_10 : OSMutexQuery_which_implies_wit_10.
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
    &(pd # "os_mutex_data" ->ₛ "OSEventTbl") + i * 1) in PreH3.
  assert (Hsrcaddr : psrc_v_2 = pe + OSEventTbl_off + i * 1) by lia.
  assert (Hdstaddr :
    pdest_v_2 = (&(pd # "os_mutex_data" ->ₛ "OSEventTbl")) + i * 1)
    by lia.
  rewrite Hsrcaddr, Hdstaddr.
  unfold store_oseventtbl_missing_i, store_osprio_array_missing_i.
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
  prop_apply
    (store_array_missing_i_rec_Zlength Z
       (fun base idx value => (base + idx * 1) # UChar |-> value)
       (&(pd # "os_mutex_data" ->ₛ "OSEventTbl"))
       i 0 OS_EVENT_TBL_SIZE (copy_prefix_list evtL_2 outL_in i)).
  Intros_p Hdstlen.
  sep_apply_l_atomic
    (store_array_missing_i_merge_to_array Z
       (fun base idx value => (base + idx * 1) # UChar |-> value)
       (pe + OSEventTbl_off) i OS_EVENT_TBL_SIZE
       (Znth i evtL_2 0) evtL_2 Hrange).
  sep_apply_l_atomic
    (store_array_missing_i_merge_to_array Z
       (fun base idx value => (base + idx * 1) # UChar |-> value)
       (&(pd # "os_mutex_data" ->ₛ "OSEventTbl"))
       i OS_EVENT_TBL_SIZE (Znth i evtL_2 0)
       (copy_prefix_list evtL_2 outL_in i) Hrange).
  rewrite (replace_Znth_Znth i evtL_2 0).
  unfold copy_prefix_list in Hdstlen |- *.
  rewrite
    (list_copy_prefix_step__array_loop_and_returns
       Z evtL_2 outL_in i 0 ltac:(
         unfold OS_EVENT_TBL_SIZE in *; lia) ltac:(
         unfold OS_EVENT_TBL_SIZE in *; lia)).
  unfold store_oseventtbl, store_osprio_array.
  unfold oseventtbl_element_store, sizeof_OS_PRIO.
  entailer!.
  all: try solve [unfold mutex_query_event_wait_layout_prop; split; assumption].
  all: cbn; lia.
Qed.

Lemma proof_of_OSMutexQuery_which_implies_wit_11 : OSMutexQuery_which_implies_wit_11.
Proof.
  pre_process.
  Exists cnt_2 grp_2 evtL_2 entry_2 current_2.
  sep_apply_l_atomic (mutex_query_copy_frame_restore platform critical sg invocation origin mask cpu_sr
    before entry_2 eid observed current_2 pd cnt_2 grp_2 evtL_2 pe PreH1).
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
Qed.
