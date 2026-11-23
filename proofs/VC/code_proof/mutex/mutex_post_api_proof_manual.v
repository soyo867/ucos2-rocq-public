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
From Ucos2Verify.VC.code.mutex Require Import mutex_post_api_goal.
From Ucos2Verify.VC.code.mutex Require Import mutex_post_api_proof_auto_checked.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_callee_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_scheduler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_history_spec.

Lemma proof_of_OSMutexPost_safety_wit_3 : OSMutexPost_safety_wit_3.
Proof.
  unfold OSMutexPost_safety_wit_3; left; intros.
  prop_apply_p (UCOS2_C_Rules.store_ushort_range
    (&(pevent_pre # "os_event" ->ₛ "OSEventCnt")) (encode_event_cnt_value current)).
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_return_wit_1 : OSMutexPost_return_wit_1.
Proof.
unfold OSMutexPost_return_wit_1; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  change 0 with (encode_os_err_code OS_ERR_NONE).
  subst committed; 
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_NONE) (scheduled := false); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_2 : OSMutexPost_return_wit_2.
Proof.
unfold OSMutexPost_return_wit_2; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  change 0 with (encode_os_err_code OS_ERR_NONE).
  subst committed; 
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_NONE) (scheduled := false); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_3 : OSMutexPost_return_wit_3.
Proof.
unfold OSMutexPost_return_wit_3; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  change 0 with (encode_os_err_code OS_ERR_NONE).
  subst committed; 
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_NONE) (scheduled := false); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_4 : OSMutexPost_return_wit_4.
Proof.
unfold OSMutexPost_return_wit_4; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { match goal with H : UCOS2_state_inv sg before |- _ =>
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile, valid_stable_glob_vars in H; tauto end. }
  assert (Herr : mutex_post_handover_error sg mutex retval_2 = OS_ERR_NONE).
  { unfold mutex_post_handover_error; rewrite Hdisabled;
     destruct Z.eq_dec; try congruence; try reflexivity; destruct Z_le_dec; try lia; reflexivity. }
  rewrite Herr in *.

  change 0 with (encode_os_err_code OS_ERR_NONE).
  subst committed; subst woken found.
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_NONE) (scheduled := true); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_5 : OSMutexPost_return_wit_5.
Proof.
unfold OSMutexPost_return_wit_5; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { match goal with H : UCOS2_state_inv sg before |- _ =>
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile, valid_stable_glob_vars in H; tauto end. }
  assert (Herr : mutex_post_handover_error sg mutex retval_3 = OS_ERR_NONE).
  { unfold mutex_post_handover_error; rewrite Hdisabled;
     destruct Z.eq_dec; try congruence; try reflexivity; destruct Z_le_dec; try lia; reflexivity. }
  rewrite Herr in *.

  change 0 with (encode_os_err_code OS_ERR_NONE).
  subst committed; subst woken found.
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_NONE) (scheduled := true); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_6 : OSMutexPost_return_wit_6.
Proof.
unfold OSMutexPost_return_wit_6; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { match goal with H : UCOS2_state_inv sg before |- _ =>
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile, valid_stable_glob_vars in H; tauto end. }
  assert (Herr : mutex_post_handover_error sg mutex retval_3 = OS_ERR_NONE).
  { unfold mutex_post_handover_error; rewrite Hdisabled;
     destruct Z.eq_dec; try congruence; try reflexivity; destruct Z_le_dec; try lia; reflexivity. }
  rewrite Herr in *.

  change 0 with (encode_os_err_code OS_ERR_NONE).
  subst committed; subst woken found.
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_NONE) (scheduled := true); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_7 : OSMutexPost_return_wit_7.
Proof.
unfold OSMutexPost_return_wit_7; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { match goal with H : UCOS2_state_inv sg before |- _ =>
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile, valid_stable_glob_vars in H; tauto end. }
  assert (Herr : mutex_post_handover_error sg mutex retval_3 = OS_ERR_PCP_LOWER).
  { unfold mutex_post_handover_error; rewrite Hdisabled;
     destruct Z.eq_dec; try congruence; try reflexivity; destruct Z_le_dec; try lia; reflexivity. }
  rewrite Herr in *.

  change 120 with (encode_os_err_code OS_ERR_PCP_LOWER).
  subst committed; subst woken found.
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_PCP_LOWER) (scheduled := true); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_8 : OSMutexPost_return_wit_8.
Proof.
unfold OSMutexPost_return_wit_8; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { match goal with H : UCOS2_state_inv sg before |- _ =>
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile, valid_stable_glob_vars in H; tauto end. }
  assert (Herr : mutex_post_handover_error sg mutex retval_3 = OS_ERR_PCP_LOWER).
  { unfold mutex_post_handover_error; rewrite Hdisabled;
     destruct Z.eq_dec; try congruence; try reflexivity; destruct Z_le_dec; try lia; reflexivity. }
  rewrite Herr in *.

  change 120 with (encode_os_err_code OS_ERR_PCP_LOWER).
  subst committed; subst woken found.
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_PCP_LOWER) (scheduled := true); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_9 : OSMutexPost_return_wit_9.
Proof.
unfold OSMutexPost_return_wit_9; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; try assumption; congruence).
  assert (Hi : call.(os_sched_call_invocation) = invocation) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Ho : call.(os_sched_call_origin) = origin) by (unfold mutex_post_api_assumptions in *; tauto).

  change 100 with (encode_os_err_code OS_ERR_NOT_MUTEX_OWNER).
  eapply mutex_post_api_critical_return_same_x with (acquired := acquired) (current := current)
    (caller := caller) (node := node) (result := OS_ERR_NOT_MUTEX_OWNER) (scheduled := false); try eassumption; rewrite ?Hi, ?Ho; eassumption.

Qed.

Lemma proof_of_OSMutexPost_return_wit_10 : OSMutexPost_return_wit_10.
Proof.

  unfold OSMutexPost_return_wit_10; left; intros.
  change 1 with (encode_os_err_code OS_ERR_EVENT_TYPE).
  eapply mutex_post_api_early_return_same_x; [|eassumption].
  try rewrite mutex_post_api_type_unsigned in *.
  unfold mutex_post_before_save_error; destruct Z_lt_dec; try lia; try reflexivity;
    destruct Z.eq_dec; try congruence; try reflexivity; destruct Z.eq_dec; congruence.

Qed.

Lemma proof_of_OSMutexPost_return_wit_11 : OSMutexPost_return_wit_11.
Proof.

  unfold OSMutexPost_return_wit_11; left; intros.
  change 4 with (encode_os_err_code OS_ERR_PEVENT_NULL).
  eapply mutex_post_api_early_return_same_x; [|eassumption].
  try rewrite mutex_post_api_type_unsigned in *.
  unfold mutex_post_before_save_error; destruct Z_lt_dec; try lia; try reflexivity;
    destruct Z.eq_dec; try congruence; try reflexivity; destruct Z.eq_dec; congruence.

Qed.

Lemma proof_of_OSMutexPost_return_wit_12 : OSMutexPost_return_wit_12.
Proof.

  unfold OSMutexPost_return_wit_12; left; intros.
  change 5 with (encode_os_err_code OS_ERR_POST_ISR).
  eapply mutex_post_api_early_return_same_x; [|eassumption].
  try rewrite mutex_post_api_type_unsigned in *.
  unfold mutex_post_before_save_error; destruct Z_lt_dec; try lia; try reflexivity;
    destruct Z.eq_dec; try congruence; try reflexivity; destruct Z.eq_dec; congruence.

Qed.

Lemma proof_of_OSMutexPost_partial_solve_wit_19_pure : OSMutexPost_partial_solve_wit_19_pure.
Proof.
  unfold OSMutexPost_partial_solve_wit_19_pure; right; intros.
  prop_apply_p (store_uchar_range (&("pcp"))
    (unsigned_last_nbits (Z.shiftr (encode_event_cnt_value current) 8) 8)).
  prop_apply_p (store_uchar_range (&("prio")) (Z.land (encode_event_cnt_value current) 255)).
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_partial_solve_wit_28_pure : OSMutexPost_partial_solve_wit_28_pure.
Proof.
  unfold OSMutexPost_partial_solve_wit_28_pure; right; intros.
  assert (Hvalid : UCOS2_state_inv sg acquired) by assumption.
  assert (Htasks : task_in_range sg acquired.(TskState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hnode : acquired.(TskState).(inUsedTaskStates) caller = Some node) by assumption.
  assert (Hrange : task_priority_in_range sg node.(curPrio))
    by (unfold task_in_range in Htasks; intuition eauto).
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
          valid_stable_glob_vars in Hvalid; tauto).
  unfold task_priority_in_range in Hrange; rewrite Hlowest in Hrange.
  rewrite mutex_del_priority_values_length.
  unfold mutex_priority_fallback; cbn [task_tcb64_image]; entailer!.
Qed.

Lemma proof_of_OSMutexPost_partial_solve_wit_29_pure : OSMutexPost_partial_solve_wit_29_pure.
Proof.
  unfold OSMutexPost_partial_solve_wit_29_pure; right; intros.
  prop_apply_p (store_uchar_range (&("prio")) retval); entailer!.
Qed.

Lemma proof_of_OSMutexPost_partial_solve_wit_31_pure : OSMutexPost_partial_solve_wit_31_pure.
Proof.
  unfold OSMutexPost_partial_solve_wit_31_pure; right; intros.
  assert (Hvalid : UCOS2_state_inv sg acquired) by assumption.
  assert (Htasks : task_in_range sg acquired.(TskState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hnode : acquired.(TskState).(inUsedTaskStates) caller = Some node) by assumption.
  assert (Hrange : task_priority_in_range sg node.(curPrio))
    by (unfold task_in_range in Htasks; intuition eauto).
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
          valid_stable_glob_vars in Hvalid; tauto).
  unfold task_priority_in_range in Hrange; rewrite Hlowest in Hrange.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding node.(curPrio) ltac:(lia))
    as [Hx [Hy Hencode]].
  rewrite mutex_del_priority_values_length.
  unfold sched_row_values; rewrite Zlength_correct, map_length; simpl.
  unfold mutex_priority_image_fields; cbn [task_tcb64_image]; entailer!.
Qed.

Lemma proof_of_OSMutexPost_partial_solve_wit_35_pure : OSMutexPost_partial_solve_wit_35_pure.
Proof.
  unfold OSMutexPost_partial_solve_wit_35_pure; right; intros.
  prop_apply_p (store_uchar_range (&("prio")) (Z.land (encode_event_cnt_value current) 255)); entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_1 : OSMutexPost_which_implies_wit_1.
Proof.
unfold OSMutexPost_which_implies_wit_1; left; intros.
apply (mutex_post_api_entry_split source_env external platform saved_local sg call mask before).
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_2 : OSMutexPost_which_implies_wit_2.
Proof.
  unfold OSMutexPost_which_implies_wit_2; left; intros.
  rewrite UCOS2_inv_split_interrupt.
  unfold interrupt_inv, store_int_state, mutex_post_nesting_frame,
    interrupt_inv_no_int_nesting.
  Intros_p Hvalid.
  Intros_p Hint.
  pose proof Hvalid as Hrange.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, interrupt_in_range in Hrange.
  rewrite PreH1.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) before.(IntrState).(intNesting)).
  entailer!; unfold interrupt_in_range in *; tauto.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_3 : OSMutexPost_which_implies_wit_3.
Proof.
  unfold OSMutexPost_which_implies_wit_3; left; intros.
  match goal with H : mutex_post_api_assumptions _ _ _ _ _ _ _ _ _ |- _ => destruct H as [Hvalid _] end.
  rewrite UCOS2_inv_split_interrupt.
  unfold interrupt_inv, store_int_state, mutex_post_nesting_frame,
    interrupt_inv_no_int_nesting.
  rewrite PreH1; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_4 : OSMutexPost_which_implies_wit_4.
Proof.
unfold OSMutexPost_which_implies_wit_4; left; intros.
apply (mutex_post_api_entry_merge source_env external platform saved_local sg call mask before).
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_5 : OSMutexPost_which_implies_wit_5.
Proof. exact proof_of_OSMutexPost_which_implies_wit_3. Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_6 : OSMutexPost_which_implies_wit_6.
Proof.
unfold OSMutexPost_which_implies_wit_6; left; intros.
apply (mutex_post_api_entry_merge source_env external platform saved_local sg call mask before).
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_7 : OSMutexPost_which_implies_wit_7.
Proof. exact proof_of_OSMutexPost_which_implies_wit_3. Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_8 : OSMutexPost_which_implies_wit_8.
Proof.
unfold OSMutexPost_which_implies_wit_8; left; intros.

  assert (Hinput : mutex_post_api_input critical sg invocation pe before eid observed)
    by (unfold mutex_post_api_assumptions in *; tauto).
  destruct (mutex_post_api_input_slot critical sg invocation pe before eid observed Hinput ltac:(lia) ltac:(congruence))
    as [Hpe [Hid Hslot]].
  assert (Htable : event_table_layout_prop sg) by (unfold mutex_post_api_layout, mutex_del_parent_layout in *; tauto).
  pose proof (Htable eid Hid) as Hlayout.
  destruct (event_object_layout_core_proj sg eid Hlayout) as [Htype _].
  subst pe; rewrite Htype.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot); Intros; entailer!.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_9 : OSMutexPost_which_implies_wit_9.
Proof.
unfold OSMutexPost_which_implies_wit_9; left; intros.

  assert (Hvalid : UCOS2_state_inv sg before) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Hpe : pe = event_addr sg eid) by assumption; subst pe.
  assert (Hlayout : event_object_layout_prop sg eid) by assumption.
  destruct (event_object_layout_core_proj sg eid Hlayout) as [Htype _].
  rewrite Htype; apply sem_query_type_merge_full; exact Hvalid.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_10 : OSMutexPost_which_implies_wit_10.
Proof.
unfold OSMutexPost_which_implies_wit_10; left; intros.
apply (mutex_post_api_entry_merge source_env external platform saved_local sg call mask before).
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_11 : OSMutexPost_which_implies_wit_11.
Proof.
unfold OSMutexPost_which_implies_wit_11; left; intros.

  assert (Hvalid : UCOS2_state_inv sg before) by (unfold mutex_post_api_assumptions in *; tauto).
  assert (Hpe : pe = event_addr sg eid) by assumption; subst pe.
  assert (Hlayout : event_object_layout_prop sg eid) by assumption.
  destruct (event_object_layout_core_proj sg eid Hlayout) as [Htype _].
  rewrite Htype; apply sem_query_type_merge_full; exact Hvalid.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_12 : OSMutexPost_which_implies_wit_12.
Proof.
unfold OSMutexPost_which_implies_wit_12; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid) by (apply mutex_post_api_prefix_of_guards; assumption).
  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  destruct (Hadmit Hprefix) as [Hstage Havailable].
  pose proof (mutex_post_api_stage_from_task sg call before Hvalid Hstage Havailable) as Hcall.
  pose proof (proj2 (Hlink Hprefix)) as Hclients.
  sep_apply_l_atomic (mutex_post_api_entry_merge source_env external platform saved_local sg call mask before).
  unfold mutex_post_api_save_pre; entailer!.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_13 : OSMutexPost_which_implies_wit_13.
Proof.
unfold OSMutexPost_which_implies_wit_13; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid) by (apply mutex_post_api_prefix_of_guards; assumption).
  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  unfold mutex_post_api_save_post; Intros acquired.
  destruct H as [Hstage [Hinterval Hsaved]].
  rewrite Hi in Hinterval.
  destruct (mutex_post_api_interval_acquire critical sg invocation pe before eid observed acquired Hvalid Hinput Hprefix Hinterval)
    as [current [mutex [Hlookup [Htype [Hfields [Hgen Hafter]]]]]].
  sep_apply_l_atomic (mutex_del_continuation_acquired_owner_use source_env external platform saved_local sg call acquired).
  Intros_p Huse; Exists mutex current acquired; rewrite Hi, Ho; entailer!.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_14 : OSMutexPost_which_implies_wit_14.
Proof.
unfold OSMutexPost_which_implies_wit_14; left; intros.

  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  destruct (kernel_call_task_source_current_at call acquired (proj1 PreH3)) as [Hcurrent [node [Hnode Hgen]]].
  set (caller := call.(os_sched_call_stack).(stackLeaseSlot)) in *.
  assert (Haddress : tcb_field_address (task_slot_addr sg caller) TCBStkPtr = task_slot_addr sg caller)
    by (unfold mutex_post_api_layout, mutex_del_parent_layout in PreH2; intuition eauto).
  sep_apply_l_atomic (mutex_post_api_owned_pointer sg acquired caller node Haddress Hnode); Intros_p Hpointer.
  Exists caller node; unfold mutex_post_native_caller; entailer!.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_15 : OSMutexPost_which_implies_wit_15.
Proof.
  unfold OSMutexPost_which_implies_wit_15; left; intros.
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [_ Hcnt]].
  rewrite Hcnt; unfold OSEventCnt_off.
  sep_apply_l_atomic (mutex_post_commit_rep_split sg acquired eid current PreH19).
  pose proof (mutex_post_commit_field_split sg acquired eid
    (event_image sg acquired.(TskState) current) EventCntField
    ltac:(unfold event_fields; simpl; tauto)) as Hsplit.
  cbn [event_cell event_field_offset event_image] in Hsplit.
  Intros.
  exact Hsplit.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_16 : OSMutexPost_which_implies_wit_16.
Proof.
  unfold OSMutexPost_which_implies_wit_16; left; intros.
  destruct (mutex_post_source_count_decode sg acquired eid current mutex PreH24 PreH19 PreH20 PreH21)
    as [Hpcp Hsnapshot].
  assert (Hprio : prio = mutex_post_snapshot_byte mutex).
  { rewrite <- PreH29 in Hsnapshot; rewrite unsigned_last_nbits_eq in Hsnapshot by lia; assumption. }
  assert (Hceiling : pcp = mutex.(mfPCP)) by congruence.
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [Hptr Hcnt]].
  rewrite Hcnt, Hptr; unfold OSEventCnt_off, OSEventPtr_off.
  pose proof (mutex_post_commit_field_merge sg acquired eid (event_image sg acquired.(TskState) current)
    EventCntField ltac:(unfold event_fields; simpl; tauto)) as Hmerge.
  cbn [event_cell event_field_offset event_image] in Hmerge; sep_apply_l_atomic Hmerge.
  pose proof (mutex_post_comparison_split sg acquired eid (event_image sg acquired.(TskState) current)
    (encode_event_ptr_value sg current) eq_refl) as Hsplit.
  rewrite PreH2, PreH26 in Hsplit; cbn [encode_task_link] in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_17 : OSMutexPost_which_implies_wit_17.
Proof.
  unfold OSMutexPost_which_implies_wit_17; left; intros.
  pose proof (mutex_post_current_owner_comparison sg acquired eid current mutex caller node
    PreH24 PreH27 PreH26 PreH19 PreH20 PreH21) as Hcompare.
  rewrite PreH26 in Hcompare; cbn [encode_task_link] in Hcompare.
  assert (Hnotowner : mutex.(mfOwner) <> Some caller) by tauto.
  assert (Hcritical : mutex_post_critical sg eid caller acquired mutex_post_not_owner_error false acquired).
  { unfold mutex_post_not_owner_error; eapply mutex_post_not_owner; eassumption. }
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [Hptr _]].
  rewrite Hptr; unfold OSEventPtr_off.
  pose proof (mutex_post_comparison_merge sg acquired eid (event_image sg acquired.(TskState) current)
    (encode_event_ptr_value sg current) eq_refl) as Hmerge.
  rewrite PreH2, PreH26 in Hmerge; cbn [encode_task_link] in Hmerge.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (mutex_post_commit_rep_merge sg acquired eid current PreH24 PreH19); entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_18 : OSMutexPost_which_implies_wit_18.
Proof.
unfold OSMutexPost_which_implies_wit_18; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid) by (apply mutex_post_api_prefix_of_guards; assumption).
  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  pose proof (proj2 (Hlink Hprefix)) as Hclients.
  rewrite <- Hi, <- Ho.
  eapply mutex_post_api_restore_merge; eassumption.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_19 : OSMutexPost_which_implies_wit_19.
Proof.
  unfold OSMutexPost_which_implies_wit_19; left; intros.
  apply mutex_post_api_restore_source_post_without_schedule.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_20 : OSMutexPost_which_implies_wit_20.
Proof.
  unfold OSMutexPost_which_implies_wit_20; left; intros.
  pose proof (mutex_post_current_owner_comparison sg acquired eid current mutex caller node
    PreH24 PreH27 PreH26 PreH19 PreH20 PreH21) as Hcompare.
  rewrite PreH26 in Hcompare; cbn [encode_task_link] in Hcompare.
  assert (Howner : mutex.(mfOwner) = Some caller) by tauto.
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [Hptr _]].
  rewrite Hptr; unfold OSEventPtr_off.
  pose proof (mutex_post_comparison_merge sg acquired eid (event_image sg acquired.(TskState) current)
    (encode_event_ptr_value sg current) eq_refl) as Hmerge.
  rewrite PreH2, PreH26 in Hmerge; cbn [encode_task_link] in Hmerge.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (mutex_post_commit_rep_merge sg acquired eid current PreH24 PreH19); entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_21 : OSMutexPost_which_implies_wit_21.
Proof.
  unfold OSMutexPost_which_implies_wit_21; left; intros.
  assert (Hprotocol : mutex_protocol_consistency sg acquired).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, cross_module_consistency in PreH24; tauto. }
  destruct (Hprotocol eid current mutex PreH19 PreH20 PreH21) as [Hpcp _].
  assert (Hlowest : sg.(osLowestPrio) = 63 /\ sg.(osPrioMutexCeilDis) = 255).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      valid_stable_glob_vars in PreH24; tauto. }
  destruct Hlowest as [Hlowest Hdisabled].
  assert (Hrange : 0 <= pcp < 64).
  { unfold valid_mutex_pcp in Hpcp; rewrite Hlowest, Hdisabled in Hpcp; lia. }
  pose proof (UCOS2_inv_split_priority_cell sg acquired pcp Hrange) as Hsplit.
  rewrite PreH3 in Hsplit; sep_apply_l_atomic Hsplit; Intros; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_22 : OSMutexPost_which_implies_wit_22.
Proof.
  unfold OSMutexPost_which_implies_wit_22; left; intros.
  rewrite <- PreH3.
  sep_apply_l_atomic (mutex_post_reserved_resources_merge_cell sg acquired pcp ltac:(lia)).
  sep_apply_l_atomic (mutex_post_reserved_resources_split_priority sg acquired pcp caller node
    (proj1 PreH24) PreH27).
  unfold mutex_post_priority_input; rewrite PreH2, PreH3, PreH4, PreH5, PreH6, PreH26.
  cbn [encode_task_link]; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_23 : OSMutexPost_which_implies_wit_23.
Proof.
unfold OSMutexPost_which_implies_wit_23; left; intros.

  assert (Hrange : 0 <= node.(curPrio) < 64).
  { pose proof PreH24 as [Hprofile [Htasks _]].
    assert (Hlowest : sg.(osLowestPrio) = 63)
      by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
    unfold task_in_range in Htasks.
    assert (Hp : task_priority_in_range sg node.(curPrio)) by (intuition eauto).
    unfold task_priority_in_range in Hp; rewrite Hlowest in Hp; lia. }
  assert (Hprio : 0 <= prio < 64).
  { destruct PreH30 as [[_ ->]|[[Hlo Hhi] _]]; lia. }
  assert (Haddress : tcb_field_address (task_slot_addr sg caller) TCBStkPtr = task_slot_addr sg caller)
    by (unfold mutex_post_api_layout, mutex_del_parent_layout in PreH8; intuition eauto).
  pose proof (tcb64_storage_split (task_slot_addr sg caller) (task_tcb64_image sg node) TCBStkPtr) as Hsplit.
  pose proof (tcb64_storage_merge (task_slot_addr sg caller) (task_tcb64_image sg node) TCBStkPtr) as Hmerge.
  cbn [tcb_cell task_tcb64_image] in Hsplit, Hmerge; rewrite Haddress in Hsplit, Hmerge.
  sep_apply_l_atomic Hsplit.
  sep_apply_l_atomic (mutex_del_pointer_cell_not_reserved (task_slot_addr sg caller) node.(tcbStkPtr)); Intros_p Hpointer.
  sep_apply_l_atomic Hmerge.
  pose proof (tcb64_storage_split (task_slot_addr sg caller) (task_tcb64_image sg node) TCBPrio) as Hprio_split.
  cbn [tcb_cell tcb_field_address task_tcb64_image] in Hprio_split.
  sep_apply_l_atomic Hprio_split; entailer!.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_24 : OSMutexPost_which_implies_wit_24.
Proof.
  unfold OSMutexPost_which_implies_wit_24; left; intros.
  pose proof (tcb64_storage_merge (task_slot_addr sg caller) (task_tcb64_image sg node) TCBPrio) as Hmerge.
  cbn [tcb_cell tcb_field_address task_tcb64_image] in Hmerge.
  exact Hmerge.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_25 : OSMutexPost_which_implies_wit_25.
Proof.
  unfold OSMutexPost_which_implies_wit_25; left; intros.
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      valid_stable_glob_vars in PreH24; tauto. }
  assert (Henabled : mutex_pcp_enabled sg mutex) by (unfold mutex_pcp_enabled; congruence).
  destruct (mutex_post_owner_scan_properties sg acquired eid current mutex caller node prio
    PreH24 PreH19 PreH20 PreH21 PreH28 Henabled PreH27 PreH32 PreH31)
    as [base [Hbase [Heffective [Hbounds [Hrange [Hne Halias]]]]]].
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      valid_stable_glob_vars in PreH24; tauto. }
  unfold task_priority_in_range in Hrange; rewrite Hlowest in Hrange.
  subst pcp.
  assert (Hprepare : mutex_post_prepare sg mutex caller acquired
    (mutex_post_owner_priority_state sg acquired mutex.(mfPCP) caller node prio)).
  { unfold mutex_post_prepare; destruct Z.eq_dec; [contradiction|].
    exists node, prio; repeat split; assumption || reflexivity. }
  pose proof (mutex_post_owner_priority_update_merge sg acquired eid current mutex caller node prio
    PreH24 PreH23 PreH19 PreH20 PreH21 PreH28 Henabled PreH27 PreH32 PreH31 PreH33) as Hmerge.
  unfold mutex_post_priority_output in Hmerge.
  rewrite PreH2, PreH3, PreH4, PreH5, PreH6, PreH26 in Hmerge; cbn [encode_task_link] in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_26 : OSMutexPost_which_implies_wit_26.
Proof.
  unfold OSMutexPost_which_implies_wit_26; left; intros.
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      valid_stable_glob_vars in PreH24; tauto. }
  assert (Henabled : mutex_pcp_enabled sg mutex) by (unfold mutex_pcp_enabled; congruence).
  destruct (mutex_post_owner_scan_properties sg acquired eid current mutex caller node prio
    PreH24 PreH19 PreH20 PreH21 PreH28 Henabled PreH27 PreH32 PreH31)
    as [base [Hbase [Heffective [Hbounds [Hrange [Hne Halias]]]]]].
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      valid_stable_glob_vars in PreH24; tauto. }
  unfold task_priority_in_range in Hrange; rewrite Hlowest in Hrange.
  subst pcp.
  assert (Hprepare : mutex_post_prepare sg mutex caller acquired
    (mutex_post_owner_priority_state sg acquired mutex.(mfPCP) caller node prio)).
  { unfold mutex_post_prepare; destruct Z.eq_dec; [contradiction|].
    exists node, prio; repeat split; assumption || reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_27 : OSMutexPost_which_implies_wit_27.
Proof.
  unfold OSMutexPost_which_implies_wit_27; left; intros.
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      valid_stable_glob_vars in PreH24; tauto. }
  assert (Henabled : mutex_pcp_enabled sg mutex) by (unfold mutex_pcp_enabled; congruence).
  destruct (mutex_post_owner_scan_properties sg acquired eid current mutex caller node prio
    PreH24 PreH19 PreH20 PreH21 PreH28 Henabled PreH27 PreH32 PreH31)
    as [base [Hbase [Heffective [Hbounds [Hrange [Hne Halias]]]]]].
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      valid_stable_glob_vars in PreH24; tauto. }
  unfold task_priority_in_range in Hrange; rewrite Hlowest in Hrange.
  subst pcp.
  assert (Hprepare : mutex_post_prepare sg mutex caller acquired
    (mutex_post_owner_priority_state sg acquired mutex.(mfPCP) caller node prio)).
  { unfold mutex_post_prepare; destruct Z.eq_dec; [contradiction|].
    exists node, prio; repeat split; assumption || reflexivity. }
  pose proof (tcb64_storage_merge (task_slot_addr sg caller) (task_tcb64_image sg node) TCBPrio) as Htcb.
  cbn [tcb_cell tcb_field_address task_tcb64_image] in Htcb; sep_apply_l_atomic Htcb.
  pose proof (mutex_post_owner_priority_skip_merge sg acquired eid current mutex caller node prio
    PreH24 PreH23 PreH19 PreH20 PreH21 PreH28 Henabled PreH27 PreH32 PreH31 PreH33) as Hmerge.
  unfold mutex_post_priority_input in Hmerge.
  rewrite PreH2, PreH3, PreH4, PreH5, PreH6, PreH26 in Hmerge; cbn [encode_task_link] in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_28 : OSMutexPost_which_implies_wit_28.
Proof.
  unfold OSMutexPost_which_implies_wit_28; left; intros.
  set (prepared := mutex_post_owner_priority_state sg acquired pcp caller node prio).
  assert (Hlookup : mutex_query_lookup prepared eid current).
  { unfold prepared, mutex_query_lookup; rewrite mutex_post_owner_priority_event_state_eq; exact PreH19. }
  Exists prepared; unfold UCOS2_inv; Intros; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_29 : OSMutexPost_which_implies_wit_29.
Proof. exact proof_of_OSMutexPost_which_implies_wit_28. Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_30 : OSMutexPost_which_implies_wit_30.
Proof.
  unfold OSMutexPost_which_implies_wit_30; left; intros.
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      valid_stable_glob_vars in PreH24; tauto. }
  assert (Hprepare : mutex_post_prepare sg mutex caller acquired acquired).
  { unfold mutex_post_prepare; destruct Z.eq_dec; [reflexivity|congruence]. }
  Exists acquired; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_31 : OSMutexPost_which_implies_wit_31.
Proof.
  unfold OSMutexPost_which_implies_wit_31; left; intros.
  subst pe; destruct (event_object_layout_wait_proj sg eid PreH16) as [Hgrp _].
  sep_apply_l_atomic (mutex_post_commit_rep_split sg prepared eid current PreH30); Intros.
  sep_apply_l_atomic (mutex_post_commit_field_split sg prepared eid (event_image sg prepared.(TskState) current)
    EventGrpField ltac:(unfold event_fields; simpl; tauto)).
  rewrite Hgrp; cbn [event_cell event_field_offset event_image]; unfold OSEventGrp_off; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_32 : OSMutexPost_which_implies_wit_32.
Proof.
  unfold OSMutexPost_which_implies_wit_32; left; intros.
  subst pe; destruct (event_object_layout_wait_proj sg eid PreH16) as [Hgrp _].
  assert (Hnonzero : encode_event_wait_grp current.(waitList) prepared.(TskState) <> 0).
  { intro E; rewrite E in PreH32; contradiction. }
  rewrite Hgrp; unfold OSEventGrp_off.
  pose proof (mutex_post_commit_field_merge sg prepared eid (event_image sg prepared.(TskState) current)
    EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hmerge.
  cbn [event_cell event_field_offset event_image] in Hmerge.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (mutex_post_commit_rep_merge sg prepared eid current PreH31 PreH30).
  unfold UCOS2_inv; Intros.
  apply (mutex_post_wake_split sg eid prepared current PreH31 PreH30 Hnonzero PreH16).
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_33 : OSMutexPost_which_implies_wit_33.
Proof.
  unfold OSMutexPost_which_implies_wit_33; left; intros.
  assert (Hreturned : event_task_rdy_post sg prepared.(TskState) eid current waiter waiting 0 16 0
    (encode_ready_grp prepared.(SchedState).(readyList) prepared.(TskState))
    (sched_row_values prepared.(TskState) prepared.(SchedState).(readyList)) prio |--
    “ (prio = waiting.(curPrio)) ”).
  { unfold event_task_rdy_post; entailer!. }
  prop_apply_p Hreturned; Intros.
  assert (Hpriority : prio = waiting.(curPrio)) by assumption.
  pose proof (event_task_rdy_selection sg prepared.(TskState) eid current waiter waiting PreH33)
    as [_ [_ [_ [Hrange _]]]].
  pose proof (mutex_post_wake_owner_selection sg prepared eid current waiter waiting prio PreH33 Hpriority)
    as [Htable Howner].
  sep_apply_l_atomic (mutex_post_wake_merge_inv sg eid prepared current waiter waiting prio
    PreH31 PreH30 PreH20 PreH33); Intros.
  set (woken := event_wake_state sg prepared eid current waiter waiting PendMutex 0 PendOK).
  set (found := event_set_wait_list current (remove_Z_eqb waiter current.(waitList))).
  assert (Hlookup : mutex_query_lookup woken eid found).
  { unfold woken, found, mutex_query_lookup.
    cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState
      update_event_field_raw inUsedEventStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Htype : found.(eventType) = mutex_post_kind) by exact PreH20.
  assert (Hmutex : found.(mutexFields) = Some mutex) by exact PreH21.
  assert (Hselection : mutex_post_wake_selection woken.(TskState) waiter waiting prio)
    by (split; assumption).
  fold woken.
  sep_apply_l_atomic (mutex_post_commit_rep_split sg woken eid found Hlookup); Intros.
  sep_apply_l_atomic (mutex_post_commit_field_split sg woken eid (event_image sg woken.(TskState) found)
    EventCntField ltac:(unfold event_fields; simpl; tauto)).
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [_ Hcnt]].
  rewrite Hcnt; unfold OSEventCnt_off; cbn [event_cell event_field_offset event_image].
  Exists found woken; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_34 : OSMutexPost_which_implies_wit_34.
Proof.
  unfold OSMutexPost_which_implies_wit_34; left; intros.
  destruct PreH40 as [Hpriority Htable].
  pose proof (event_task_rdy_selection sg prepared.(TskState) eid current waiter waiting PreH33)
    as [_ [_ [_ [Hrange _]]]].
  assert (Hprio : 0 <= prio < 64) by lia.
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [Hptr Hcnt]].
  rewrite Hcnt, Hptr; unfold OSEventCnt_off, OSEventPtr_off.
  pose proof (mutex_post_commit_field_merge_updated sg woken eid (event_image sg woken.(TskState) found)
    EventCntField (Some (Z.lor (Z.land (encode_event_cnt_value found) 65280) prio))
    ltac:(unfold event_fields; simpl; tauto)) as Hmerge.
  cbn [event_cell event_field_offset] in Hmerge; sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (mutex_post_commit_field_split sg woken eid
    (event_write (event_image sg woken.(TskState) found) EventCntField
      (Some (Z.lor (Z.land (encode_event_cnt_value found) 65280) prio)))
    EventPtrField ltac:(unfold event_fields; simpl; tauto)).
  unfold mutex_post_commit_field_frame, mutex_post_native_owner_store_frame.
  pose proof (store_prio_tbl_split_cell sg woken.(TskState).(prioTbl) prio Hprio) as Hsplit.
  rewrite Htable, PreH3 in Hsplit; cbn [prio_tbl_entry_to_addr] in Hsplit.
  sep_apply_l_atomic Hsplit; cbn [event_cell event_field_offset event_write field_update event_image]; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_35 : OSMutexPost_which_implies_wit_35.
Proof.
unfold OSMutexPost_which_implies_wit_35; left; intros.

  destruct PreH40 as [Hpriority Htable].
  pose proof (event_task_rdy_selection sg prepared.(TskState) eid current waiter waiting PreH33)
    as [_ [_ [_ [Hrange _]]]].
  assert (Hprio : 0 <= prio < 64) by (rewrite Hpriority; exact Hrange).
  assert (Hstep : event_task_rdy sg prepared eid PendMutex 0 PendOK = Some (prio, woken)).
  { pose proof PreH33 as [Hsg [_ [_ [Htasks [Hwait [Hhead Hold]]]]]].
    destruct current.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
    inversion Hhead; subst head; rewrite Hpriority, PreH34.
    eapply event_task_rdy_selects_waiter; eassumption. }
  assert (Hgroup : encode_event_wait_grp current.(waitList) prepared.(TskState) <> 0)
    by (intro E; rewrite E in PreH32; contradiction).
  pose proof (mutex_post_prepare_reserved_slot sg mutex caller acquired prepared PreH29) as Hslot.
  assert (Hslot_woken : mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ woken.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved).
  { rewrite PreH34; exact Hslot. }
  pose proof (mutex_post_wake_owner_selection sg prepared eid current waiter waiting prio PreH33 Hpriority) as [_ Howner].
  rewrite <- PreH34, <- PreH35 in Howner.
  destruct (mutex_post_count_fields sg woken eid found mutex PreH39 PreH36 PreH37 PreH38)
    as [Hpcp [Hsnapshot Hcount]].
  assert (Hrun : mutex_post_critical sg eid caller acquired (mutex_post_handover_error sg mutex prio) true
    (mutex_post_owner_state woken eid found mutex (Some waiter) (Some prio)))
    by (eapply mutex_post_handover; eassumption).
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [Hptr _]].
  rewrite Hptr, <- PreH3; unfold OSEventPtr_off, mutex_post_native_owner_store_frame.
  pose proof (store_prio_tbl_merge_cell sg woken.(TskState).(prioTbl) prio Hprio) as Htable_merge.
  rewrite Htable in Htable_merge; cbn [prio_tbl_entry_to_addr] in Htable_merge.
  transitivity
    (((sg.(g_OSTCBPrioTbl) + prio * sizeof(PTR)) # Ptr |-> task_slot_addr sg waiter **
       store_prio_tbl_missing_i sg woken.(TskState).(prioTbl) prio) **
     ((event_addr sg eid + 4) # Ptr |-> task_slot_addr sg waiter **
       event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
         (event_write (event_image sg woken.(TskState) found) EventCntField
           (Some (Z.lor (Z.land (encode_event_cnt_value found) 65280) prio))) EventPtrField **
       mutex_post_event_table_frame sg woken eid)); [entailer!|].
  sep_apply_l_atomic Htable_merge.
  transitivity ((event_addr sg eid + 4) # Ptr |-> task_slot_addr sg waiter **
    mutex_post_commit_field_frame sg woken eid
      (event_write (event_image sg woken.(TskState) found) EventCntField
        (Some (Z.lor (Z.land (encode_event_cnt_value found) 65280) prio))) EventPtrField);
    [unfold mutex_post_commit_field_frame; entailer!|].
  pose proof (mutex_post_commit_field_merge_updated sg woken eid
    (event_write (event_image sg woken.(TskState) found) EventCntField
      (Some (Z.lor (Z.land (encode_event_cnt_value found) 65280) prio))) EventPtrField (Some (task_slot_addr sg waiter))
    ltac:(unfold event_fields; simpl; tauto)) as Hmerge.
  cbn [event_cell event_field_offset] in Hmerge; sep_apply_l_atomic Hmerge.
  assert (Himage : event_write (event_write (event_image sg woken.(TskState) found) EventCntField
      (Some (Z.lor (Z.land (encode_event_cnt_value found) 65280) prio))) EventPtrField (Some (task_slot_addr sg waiter)) =
      mutex_post_handover_image (event_image sg woken.(TskState) found) prio (task_slot_addr sg waiter)).
  { apply functional_extensionality; intros field; destruct field;
      unfold mutex_post_handover_image, event_write, field_update, event_image; simpl; reflexivity. }
  rewrite Himage.
  rewrite (mutex_post_handover_image_decoded_eq sg woken.(TskState) found mutex (mutex_post_snapshot_byte mutex)
    waiter prio PreH37 PreH38 Hcount Hpcp Hsnapshot ltac:(lia)).
  sep_apply_l_atomic (mutex_post_commit_owner_merge_inv sg woken eid found mutex (Some waiter) (Some prio)
    PreH39 PreH36 PreH37 PreH38 Hslot_woken Howner).
  Exists (mutex_post_owner_state woken eid found mutex (Some waiter) (Some prio)); entailer!.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_36 : OSMutexPost_which_implies_wit_36.
Proof.
unfold OSMutexPost_which_implies_wit_36; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid) by (apply mutex_post_api_prefix_of_guards; assumption).
  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  pose proof (proj2 (Hlink Hprefix)) as Hclients.
  rewrite <- Hi, <- Ho.
  eapply mutex_post_api_restore_merge; eassumption.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_37 : OSMutexPost_which_implies_wit_37.
Proof.
  unfold OSMutexPost_which_implies_wit_37; left; intros.
  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; assumption).
  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  pose proof (Hlink Hprefix) as Hsched.
  assert (Hlayout : kernel_tcb_stack_field_layout sg).
  { unfold mutex_post_api_layout, mutex_del_parent_layout in PreH2;
    unfold kernel_tcb_stack_field_layout; intros slot Hslot; intuition eauto. }
  sep_apply_l_atomic (mutex_post_api_restore_source_sched_call source_env external platform
    critical saved_local sg call mask checkpoint Hlayout Hsched).
  Intros restored unmasked; Exists unmasked restored;
    unfold mutex_post_api_scheduler_link in *; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_38 : OSMutexPost_which_implies_wit_38.
Proof.
  unfold OSMutexPost_which_implies_wit_38; left; intros.
  apply mutex_api_scheduler_callee_after_restore; assumption.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_39 : OSMutexPost_which_implies_wit_39.
Proof.
unfold OSMutexPost_which_implies_wit_39; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid) by (apply mutex_post_api_prefix_of_guards; assumption).
  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  pose proof (proj2 (Hlink Hprefix)) as Hclients.
  rewrite <- Hi, <- Ho.
  eapply mutex_post_api_restore_merge; eassumption.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_40 : OSMutexPost_which_implies_wit_40.
Proof.
  unfold OSMutexPost_which_implies_wit_40; left; intros.
  assert (Hprefix : mutex_post_api_prefix pe before eid)
    by (apply mutex_post_api_prefix_of_guards; assumption).
  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  pose proof (Hlink Hprefix) as Hsched.
  assert (Hlayout : kernel_tcb_stack_field_layout sg).
  { unfold mutex_post_api_layout, mutex_del_parent_layout in PreH2;
    unfold kernel_tcb_stack_field_layout; intros slot Hslot; intuition eauto. }
  sep_apply_l_atomic (mutex_post_api_restore_source_sched_call source_env external platform
    critical saved_local sg call mask checkpoint Hlayout Hsched).
  Intros restored unmasked; Exists unmasked restored;
    unfold mutex_post_api_scheduler_link in *; entailer!.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_41 : OSMutexPost_which_implies_wit_41.
Proof.
  unfold OSMutexPost_which_implies_wit_41; left; intros.
  apply mutex_api_scheduler_callee_after_restore; assumption.
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_42 : OSMutexPost_which_implies_wit_42.
Proof.
unfold OSMutexPost_which_implies_wit_42; left; intros.

  subst pe; destruct (event_object_layout_wait_proj sg eid PreH16) as [Hgrp _].
  destruct (event_object_layout_core_proj sg eid PreH16) as [_ [_ Hcnt]].
  rewrite Hgrp, Hcnt; unfold OSEventGrp_off, OSEventCnt_off.
  pose proof (mutex_post_commit_field_merge sg prepared eid (event_image sg prepared.(TskState) current)
    EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hmerge.
  cbn [event_cell event_field_offset event_image] in Hmerge; sep_apply_l_atomic Hmerge.
  pose proof (mutex_post_commit_field_split sg prepared eid (event_image sg prepared.(TskState) current)
    EventCntField ltac:(unfold event_fields; simpl; tauto)) as Hsplit.
  cbn [event_cell event_field_offset event_image] in Hsplit; exact Hsplit.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_43 : OSMutexPost_which_implies_wit_43.
Proof.
  unfold OSMutexPost_which_implies_wit_43; left; intros.
  destruct (mutex_post_count_fields sg prepared eid current mutex PreH31 PreH30 PreH20 PreH21)
    as [Hpcp [Hsnapshot Hcount]].
  assert (Hcast : unsigned_last_nbits (encode_event_cnt_value current) 16 = encode_event_cnt_value current).
  { apply unsigned_last_nbits_eq; rewrite Hcount; cbn; lia. }
  rewrite Hcast.
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [Hptr Hcnt]].
  rewrite Hcnt, Hptr; unfold OSEventCnt_off, OSEventPtr_off.
  pose proof (mutex_post_commit_field_merge_updated sg prepared eid (event_image sg prepared.(TskState) current)
    EventCntField (Some (Z.lor (encode_event_cnt_value current) 255))
    ltac:(unfold event_fields; simpl; tauto)) as Hmerge.
  cbn [event_cell event_field_offset] in Hmerge.
  sep_apply_l_atomic Hmerge.
  apply (mutex_post_commit_field_split sg prepared eid
    (event_write (event_image sg prepared.(TskState) current) EventCntField
      (Some (Z.lor (encode_event_cnt_value current) 255)))
    EventPtrField ltac:(unfold event_fields; simpl; tauto)).
Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_44 : OSMutexPost_which_implies_wit_44.
Proof.
unfold OSMutexPost_which_implies_wit_44; left; intros.

  assert (Hgroup : encode_event_wait_grp current.(waitList) prepared.(TskState) = 0).
  { rewrite (mutex_del_parent_group_cast sg prepared current.(waitList) PreH31) in PreH32; exact PreH32. }
  pose proof (mutex_del_event_group_zero_implies_empty sg prepared eid current PreH31 PreH30 Hgroup) as Hempty.
  pose proof (mutex_post_prepare_reserved_slot sg mutex caller acquired prepared PreH29) as Hslot.
  destruct (mutex_post_count_fields sg prepared eid current mutex PreH31 PreH30 PreH20 PreH21)
    as [Hpcp [Hsnapshot Hcount]].
  assert (Hrun : mutex_post_critical sg eid caller acquired mutex_post_success false
    (mutex_post_owner_state prepared eid current mutex None None))
    by (eapply mutex_post_empty; eassumption).
  subst pe; destruct (event_object_layout_core_proj sg eid PreH16) as [_ [Hptr _]].
  rewrite Hptr; unfold OSEventPtr_off.
  pose proof (mutex_post_commit_field_merge_updated sg prepared eid
    (event_write (event_image sg prepared.(TskState) current) EventCntField
      (Some (Z.lor (encode_event_cnt_value current) 255))) EventPtrField (Some 0)
    ltac:(unfold event_fields; simpl; tauto)) as Hmerge.
  cbn [event_cell event_field_offset] in Hmerge; sep_apply_l_atomic Hmerge.
  assert (Himage : event_write (event_write (event_image sg prepared.(TskState) current) EventCntField
      (Some (Z.lor (encode_event_cnt_value current) 255))) EventPtrField (Some 0) =
      mutex_post_empty_image (event_image sg prepared.(TskState) current)).
  { unfold mutex_post_empty_image; cbn [event_image option_map].
    rewrite (unsigned_last_nbits_eq (encode_event_cnt_value current) 16) by (rewrite Hcount; cbn; lia).
    reflexivity. }
  rewrite Himage.
  rewrite (mutex_post_empty_image_decoded_eq sg prepared.(TskState) current mutex (mutex_post_snapshot_byte mutex)
    PreH20 PreH21 Hcount Hpcp Hsnapshot).
  sep_apply_l_atomic (mutex_post_commit_owner_merge_inv sg prepared eid current mutex None None
    PreH31 PreH30 PreH20 PreH21 Hslot Hempty).
  Exists (mutex_post_owner_state prepared eid current mutex None None); entailer!.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_45 : OSMutexPost_which_implies_wit_45.
Proof.
unfold OSMutexPost_which_implies_wit_45; left; intros.

  assert (Hprefix : mutex_post_api_prefix pe before eid) by (apply mutex_post_api_prefix_of_guards; assumption).
  destruct PreH1 as [Hvalid [Hinput [Hi [Ho [Hadmit Hlink]]]]].
  pose proof (proj2 (Hlink Hprefix)) as Hclients.
  rewrite <- Hi, <- Ho.
  eapply mutex_post_api_restore_merge; eassumption.

Qed.

Lemma proof_of_OSMutexPost_which_implies_wit_46 : OSMutexPost_which_implies_wit_46.
Proof.
  unfold OSMutexPost_which_implies_wit_46; left; intros.
  apply mutex_post_api_restore_source_post_without_schedule.
Qed.
