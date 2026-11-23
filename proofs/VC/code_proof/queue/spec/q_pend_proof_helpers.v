Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_call_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** These are observations at the empty-Queue branch. They are not a public entry restriction and do
    not assert a global invariant between the three native TCB stores and
    OS_EventTaskWait. The existing single-wait protocol supplies the
    unlinked caller. The Queue-specific unavailable fact comes from the actual count. *)
Definition q_pend_wait_entry sg entry eid current tid old : Prop :=
  UCOS2_state_inv sg entry /\
  entry.(SchedState).(curTaskID) = Some tid /\
  entry.(TskState).(inUsedTaskStates) tid = Some old /\
  mutex_query_lookup entry eid current /\
  current.(eventType) = OS_EVENT_TYPE_Q /\
  (exists queue, current.(queueFields) = Some queue /\ queue_entries queue <= 0) /\
  old.(curPrio) <> sg.(osLowestPrio) /\ old.(eventPtr) = None /\
  old.(eventMultiWaitEvents) = [] /\ old.(tcbFlagNode) = 0 /\
  In tid entry.(SchedState).(readyList) /\ event_object_layout_prop sg eid.

(** Reuse the complete Sem prefix residual unchanged. Only the pending
    status bit differs; there is no second model of a partially ready TCB. *)
Definition q_pend_wait_call_frame sg entry eid current tid old timeout : Assertion :=
  event_task_wait_tcb_rest (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendQ timeout)) **
  store_prio_tbl sg entry.(TskState).(prioTbl) **
  sem_post_task_frame sg entry.(TskState) tid **
  UCharArray.missing_i sg.(g_OSRdyTbl) (old.(curPrio) / 8) 0 8
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte entry.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte entry.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg entry.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> entry.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if entry.(SchedState).(isRunning) then 1 else 0) **
  event_task_wait_event_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (old.(curPrio) / 8) (event_image sg entry.(TskState) current) **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  UCOS2_raw_rep_missing_task_storage_sched_event sg entry.

Definition q_pend_wait_call_pre sg entry eid current tid old timeout : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
  tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
  tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + old.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8) **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    # UChar |-> encode_event_wait_grp current.(waitList) entry.(TskState) **
  (sg.(g_OSRdyTbl) + old.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  q_pend_wait_call_frame sg entry eid current tid old timeout.

Definition q_pend_wait_call_post sg entry eid current tid old timeout : Assertion :=
  event_task_wait_post sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
    sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8))
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState)) **
  q_pend_wait_call_frame sg entry eid current tid old timeout.

Lemma q_pend_wait_prefix_split : forall sg state tid old,
  UCOS2_state_inv sg state -> state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_inv sg state |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some old.(dly)) **
  sem_pend_prefix_frame sg state tid old.
Proof.
  intros * Hvalid Hcurrent Hnode.
  sep_apply_l_atomic (sem_pend_full_task_split sg state tid old Hvalid Hnode).
  sep_apply_l_atomic (sem_pend_tcb_three_fields_split (task_slot_addr sg tid)
    (task_tcb64_image sg old) TCBDly ltac:(discriminate) ltac:(discriminate)).
  unfold sem_pend_full_task_frame, sem_pend_prefix_frame, sem_pend_sched_without_current,
    sched_raw_rep, sched_physical_rep.
  cbn [task_tcb64_image]; rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Lemma q_pend_tcb_merge_wait_prefix : forall sg tid old timeout,
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 4)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBDly |--
  tcb64_storage_rep (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendQ timeout)).
Proof.
  intros; rewrite task_prepare_event_wait_image_eq.
  apply sem_pend_tcb_three_fields_merge_updated; discriminate.
Qed.

Lemma q_pend_wait_entry_prio : forall sg entry eid current tid old,
  q_pend_wait_entry sg entry eid current tid old -> valid_task_prio sg old.(curPrio).
Proof.
  intros * [Hvalid [_ [Hold [_ [_ [_ [Hnonidle _]]]]]]].
  pose proof Hvalid as [Hprofile _].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  pose proof (sem_pend_task_priority_in_range sg entry tid old Hvalid Hold) as Hrange.
  unfold valid_task_prio; lia.
Qed.

Lemma q_pend_wait_entry_row_in_range : forall sg entry eid current tid old,
  q_pend_wait_entry sg entry eid current tid old -> 0 <= old.(curPrio) / 8 < 8.
Proof.
  intros * [Hvalid [_ [Hold _]]].
  pose proof (sem_pend_task_priority_in_range sg entry tid old Hvalid Hold) as Hrange.
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma q_pend_wait_entry_resource_conditions : forall sg entry eid current tid old,
  q_pend_wait_entry sg entry eid current tid old ->
  event_type_to_pend_type current.(eventType) = Some PendQ /\
  event_wait_resource_unavailable current /\
  (forall mutex, current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some mutex -> mutex.(mfOwner) <> Some tid).
Proof.
  intros * [_ [_ [_ [_ [Htype [[queue [Hfields Hempty]] _]]]]]].
  split; [rewrite Htype; reflexivity|]. split.
  - unfold event_wait_resource_unavailable; rewrite Htype, Hfields.
    destruct queue.(qMessages) as [|message rest] eqn:Hmessages; [reflexivity|].
    unfold queue_entries in Hempty; rewrite Hmessages, Zlength_cons in Hempty.
    pose proof (Zlength_nonneg rest); lia.
  - intros mutex Hmutex; congruence.
Qed.

(** The three real stores have occurred, but ready membership and EventPtr
    still describe the old state. Reassemble storage only and expose the
    exact cells consumed by the already checked internal helper. *)
Lemma q_pend_wait_prefix_split_call : forall sg entry eid current tid old timeout,
  q_pend_wait_entry sg entry eid current tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 4)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_prefix_frame sg entry tid old |--
  q_pend_wait_call_pre sg entry eid current tid old timeout.
Proof.
  intros * Hentry.
  pose proof (q_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [Hcur [Hold [He [Htype [Howner [Hnonidle
    [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  unfold sem_pend_prefix_frame.
  sepcon_assoc_change.
  sep_apply_l_atomic (q_pend_tcb_merge_wait_prefix sg tid old timeout).
  sep_apply_l_atomic (event_task_wait_tcb_split (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendQ timeout))).
  unfold sem_pend_sched_without_current, UCOS2_raw_rep_missing_task_storage_sched.
  sep_apply_l_atomic (sched_rows_split_cell sg entry.(TskState) entry.(SchedState).(readyList)
    (old.(curPrio) / 8) Hrow).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid current He).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_wait_event_split_c_fields sg eid
    (event_image sg entry.(TskState) current) (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState)) Hlayout Hrow
    (event_table_image_eq sg entry.(TskState) current (old.(curPrio) / 8) Hrow) eq_refl).
  unfold q_pend_wait_call_pre, q_pend_wait_call_frame,
    UCOS2_raw_rep_missing_task_storage_sched_event.
  cbn [task_tcb64_image task_prepare_event_wait].
  try rewrite Hnone; cbn [encode_event_link].
  entailer!.
  cbn [task_prepare_event_wait eventPtr curPrio tcb_y_of_prio].
  rewrite Hnone; reflexivity.
Qed.

Lemma q_pend_wait_call_merge : forall sg entry eid current tid old timeout,
  q_pend_wait_entry sg entry eid current tid old ->
  q_pend_wait_call_post sg entry eid current tid old timeout |--
  UCOS2_inv sg (event_pend_state sg entry eid current tid old PendQ timeout).
Proof.
  intros * Hentry.
  pose proof (q_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  pose proof (q_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hprio.
  destruct (q_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hentry)
    as [Hkind [Hunavailable Hnotowner]].
  destruct Hentry as [Hvalid [Hcur [Hold [He [Htype [Howner [Hnonidle
    [Hnone [Hmulti0 [Hflag [Hready Hlayout]]]]]]]]]]].
  pose proof Hvalid as [Hprofile [Htasks [[Hrdy Hmeta] [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg)
    by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hpriorities _]]]]]]]].
  pose proof (Hpriorities tid old Hold) as Hrange.
  pose proof (sched_ready_in_range_implies_structure sg entry.(TskState) entry.(SchedState) Hrdy)
    as Hstructure.
  unfold q_pend_wait_call_post, q_pend_wait_call_frame, event_task_wait_post.
  pose proof (event_task_wait_tcb_merge_event_ptr (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendQ timeout)) (event_addr sg eid)) as Htcb.
  change (tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (event_addr sg eid)) **
    tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
    tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
    tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
    event_task_wait_tcb_rest (task_slot_addr sg tid)
      (task_tcb64_image sg (task_prepare_event_wait old PendQ timeout)) |--
    tcb64_storage_rep (task_slot_addr sg tid)
      (tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendQ timeout))
        TCBEventPtr (Some (event_addr sg eid)))) in Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb.
  unfold tcb_y_of_prio in Htcb.
  sepcon_assoc_change.
  sep_apply_l_atomic Htcb.
  assert (Himage : tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendQ timeout))
    TCBEventPtr (Some (event_addr sg eid)) =
    task_tcb64_image sg (task_set_event_ptr (task_prepare_event_wait old PendQ timeout) (Some eid)))
    by (symmetry; apply task_set_event_ptr_image_eq).
  rewrite Himage.
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid
    (task_set_event_ptr (task_prepare_event_wait old PendQ timeout) (Some eid)) Hmulti Hprofiling).
  sep_apply_l_atomic (event_task_wait_event_merge_c_fields sg eid (event_image sg entry.(TskState) current)
    (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) Hlayout Hrow).
  sep_apply_l_atomic (event_task_wait_ready_merge_removed_task sg entry.(TskState) entry.(SchedState)
    tid old Hsg Hunique Hold Hrange Hstructure Hrow).
  assert (Hindex : forall state, sched_raw_rep sg entry.(TskState) state =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_set_event_ptr (task_prepare_event_wait old PendQ timeout) (Some eid))) state).
  { intro state; apply sched_raw_rep_priority_ext; intros slot Hin.
    cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  intros heap Hheap.
  apply (UCOS2_inv_merge_event_pend_storage sg entry eid current tid old PendQ timeout
    Hvalid He Hold Hprio Hnone Hmulti0 Hflag Hready Hkind Hunavailable Hnotowner heap).
  revert heap Hheap.
  match goal with |- forall heap : model, ?P heap -> ?Q heap => change (P |-- Q) end.
  cbn [event_pend_state event_wait_state replace_SchedS replace_EventS replace_TskS TskState SchedState].
  rewrite <- Hindex; unfold sched_raw_rep, sched_physical_rep.
  cbn [sched_remove_ready_task curSchedPrio highRdyPrio curTaskID highRdyTid ctxSwCtr isRunning].
  try rewrite Hcur; cbn [encode_task_link].
  entailer!.
  unfold sched_remove_ready_task, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  cbn; rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma q_pend_wait_entry_preserves_validity : forall sg entry eid current tid old timeout,
  q_pend_wait_entry sg entry eid current tid old ->
  UCOS2_state_inv sg (event_pend_state sg entry eid current tid old PendQ timeout).
Proof.
  intros * Hentry.
  pose proof (q_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hprio.
  destruct (q_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hentry)
    as [Hkind [Hunavailable Hnotowner]].
  destruct Hentry as [Hvalid [Hcur [Hold [He [Htype [Howner [Hnonidle
    [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  eapply UCOS2_event_pend_preserves_validity; eassumption.
Qed.

(** Queue cleanup writes a fourth field, OSTCBMsg. Do not use the Sem
    three-field cleanup frame to silently forget this real store. *)
Definition q_pend_cleanup_residual base image : Assertion :=
  tcb64_fields_rep base
    (remove TCBField_eq_dec TCBMsg
      (remove TCBField_eq_dec TCBEventPtr
        (remove TCBField_eq_dec TCBStatPend
          (remove TCBField_eq_dec TCBStat tcb_fields)))) image.

Lemma q_pend_tcb_cleanup_split : forall base image,
  tcb64_storage_rep base image |--
  tcb_cell base TCBStat (image TCBStat) **
  tcb_cell base TCBStatPend (image TCBStatPend) **
  tcb_cell base TCBEventPtr (image TCBEventPtr) **
  tcb_cell base TCBMsg (image TCBMsg) ** q_pend_cleanup_residual base image.
Proof.
  intros base image.
  sep_apply_l_atomic (sem_pend_tcb_three_fields_split base image TCBEventPtr
    ltac:(discriminate) ltac:(discriminate)).
  unfold sem_pend_tcb_residual.
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBEventPtr
      (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)))
    base image TCBMsg
    ltac:(repeat apply sem_pend_tcb_fields_remove_nodup; apply tcb_fields_nodup)
    ltac:(repeat apply in_in_remove; try discriminate; apply tcb_fields_complete)).
  unfold q_pend_cleanup_residual; entailer!.
Qed.

Lemma q_pend_tcb_merge_cleanup : forall sg tid old,
  tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBMsg (Some 0) **
  q_pend_cleanup_residual (task_slot_addr sg tid) (task_tcb64_image sg old) |--
  tcb64_storage_rep (task_slot_addr sg tid)
    (task_tcb64_image sg (task_message_pend_cleanup false old)).
Proof.
  intros sg tid old; unfold q_pend_cleanup_residual.
  sep_apply_l_atomic (tcb64_fields_rep_merge_updated
    (remove TCBField_eq_dec TCBEventPtr
      (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)))
    (task_slot_addr sg tid) (task_tcb64_image sg old) TCBMsg (Some 0)
    ltac:(repeat apply sem_pend_tcb_fields_remove_nodup; apply tcb_fields_nodup)
    ltac:(repeat apply in_in_remove; try discriminate; apply tcb_fields_complete)).
  fold (sem_pend_tcb_residual (task_slot_addr sg tid)
    (tcb_write (task_tcb64_image sg old) TCBMsg (Some 0)) TCBEventPtr).
  sep_apply_l_atomic (sem_pend_tcb_three_fields_merge_updated (task_slot_addr sg tid)
    (tcb_write (task_tcb64_image sg old) TCBMsg (Some 0)) TCBEventPtr 0 0 0
    ltac:(discriminate) ltac:(discriminate)).
  assert (Himage : task_tcb64_image sg (task_message_pend_cleanup false old) =
    tcb_write (tcb_write (tcb_write (tcb_write (task_tcb64_image sg old)
      TCBMsg (Some 0)) TCBStat (Some 0)) TCBStatPend (Some 0)) TCBEventPtr (Some 0)).
  { apply functional_extensionality; intros []; reflexivity. }
  rewrite Himage; entailer!.
Qed.

Definition q_pend_cleanup_frame sg state tid old : Assertion :=
  q_pend_cleanup_residual (task_slot_addr sg tid) (task_tcb64_image sg old) **
  store_prio_tbl sg state.(TskState).(prioTbl) ** sem_post_task_frame sg state.(TskState) tid **
  sem_pend_sched_without_current sg state ** UCOS2_raw_rep_missing_task_storage_sched sg state.

Lemma q_pend_cleanup_split : forall sg state tid old,
  UCOS2_state_inv sg state -> state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_inv sg state |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
  tcb_cell (task_slot_addr sg tid) TCBMsg (Some (encode_msg old.(msg))) **
  q_pend_cleanup_frame sg state tid old.
Proof.
  intros * Hvalid Hcur Hold.
  sep_apply_l_atomic (sem_pend_full_task_split sg state tid old Hvalid Hold).
  sep_apply_l_atomic (q_pend_tcb_cleanup_split (task_slot_addr sg tid) (task_tcb64_image sg old)).
  unfold sem_pend_full_task_frame, q_pend_cleanup_frame, sem_pend_sched_without_current,
    sched_raw_rep, sched_physical_rep.
  cbn [task_tcb64_image]; rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma q_pend_cleanup_merge : forall sg state tid old,
  sem_pend_cleanup_entry sg state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBMsg (Some 0) **
  q_pend_cleanup_frame sg state tid old |--
  UCOS2_inv sg (message_pend_cleanup_state sg state tid old).
Proof.
  intros * [Hvalid [Hcur [Hold [Hnone [Hmulti0 [Hflag Hready]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold q_pend_cleanup_frame; sepcon_assoc_change.
  sep_apply_l_atomic (q_pend_tcb_merge_cleanup sg tid old).
  sep_apply_l_atomic (sem_post_task_storage_merge sg state.(TskState) tid
    (task_message_pend_cleanup false old) Hmulti Hprofiling).
  intros heap Hheap.
  apply (UCOS2_inv_merge_event_pend_cleanup sg state tid old true
    Hvalid Hold Hnone Hmulti0 Hflag Hready heap).
  revert heap Hheap.
  match goal with |- forall m : model, ?P m -> ?Q m => change (P |-- Q) end.
  cbn [event_pend_cleanup_state replace_TskS TskState].
  rewrite Hmulti; unfold task_message_pend_cleanup, sem_pend_sched_without_current,
    sched_raw_rep, sched_physical_rep.
  rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

(** The C-visible pair is kept together: NULL is a successful message on
    the OK arm, whereas ABORT and timeout each return their own error. *)
Definition q_pend_resume_result sg eid resumed message code cleaned : Prop :=
  exists error, code = encode_os_err_code error /\
    q_pend_resume_critical sg eid resumed (message, error) cleaned.

Definition q_pend_cleanup_observation sg resumed eid message code cleaning tid node : Prop :=
  sem_pend_cleanup_entry sg cleaning tid node /\
  q_pend_resume_result sg eid resumed message code (message_pend_cleanup_state sg cleaning tid node).

Lemma q_pend_resume_cleanup_without_timeout : forall sg resumed eid tid old,
  sem_pend_resume_entry sg resumed eid tid old -> old.(statPend) <> PendTimeout ->
  q_pend_cleanup_observation sg resumed eid
    (fst (q_pend_resume_observation (encode_pend_status old.(statPend)) (encode_msg old.(msg))))
    (encode_os_err_code (snd (q_pend_resume_observation
      (encode_pend_status old.(statPend)) (encode_msg old.(msg))))) resumed tid old.
Proof.
  intros sg resumed eid tid old Hentry Hnotimeout.
  destruct Hentry as [Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]].
  split.
  - unfold sem_pend_cleanup_entry.
    split; [exact Hvalid|]. split; [exact Hcur|]. split; [exact Hold|].
    split; [destruct old.(statPend); assumption || contradiction|].
    split; [exact Hmulti|]. split; assumption.
  - exists (snd (q_pend_resume_observation (encode_pend_status old.(statPend)) (encode_msg old.(msg)))).
    split; [reflexivity|]. exists tid, old.
    split; [exact Hcur|]. split; [exact Hold|].
    destruct old.(statPend); split; reflexivity || contradiction.
Qed.

Lemma q_pend_resume_cleanup_ok : forall sg resumed eid tid old message,
  sem_pend_resume_entry sg resumed eid tid old -> encode_pend_status old.(statPend) = 0 ->
  message = encode_msg old.(msg) ->
  q_pend_cleanup_observation sg resumed eid message 0 resumed tid old.
Proof.
  intros * Hentry Hstatus ->.
  assert (Hok : old.(statPend) = PendOK) by (destruct old.(statPend); cbn in Hstatus; congruence).
  pose proof (q_pend_resume_cleanup_without_timeout _ _ _ _ _ Hentry ltac:(congruence)) as Hresult.
  rewrite Hok in Hresult; exact Hresult.
Qed.

Lemma q_pend_resume_cleanup_abort : forall sg resumed eid tid old,
  sem_pend_resume_entry sg resumed eid tid old -> encode_pend_status old.(statPend) = 2 ->
  q_pend_cleanup_observation sg resumed eid 0 14 resumed tid old.
Proof.
  intros * Hentry Hstatus.
  assert (Habort : old.(statPend) = PendAbort) by (destruct old.(statPend); cbn in Hstatus; congruence).
  pose proof (q_pend_resume_cleanup_without_timeout _ _ _ _ _ Hentry ltac:(congruence)) as Hresult.
  rewrite Habort in Hresult; exact Hresult.
Qed.

Lemma q_pend_resume_timeout_lookup : forall sg resumed eid tid old,
  sem_pend_resume_entry sg resumed eid tid old ->
  encode_pend_status old.(statPend) <> 0 -> encode_pend_status old.(statPend) <> 2 ->
  old.(statPend) = PendTimeout /\
  exists current, mutex_query_lookup resumed eid current /\ In tid current.(waitList).
Proof.
  intros sg resumed eid tid old [Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hnotok Hnotabort.
  assert (Htimeout : old.(statPend) = PendTimeout)
    by (destruct old.(statPend); cbn in *; congruence).
  split; [exact Htimeout|]. rewrite Htimeout in Hregistration.
  eapply q_pend_resume_timeout_event; eassumption.
Qed.

Lemma q_pend_resume_cleanup_timeout : forall sg resumed eid tid old current,
  sem_pend_resume_entry sg resumed eid tid old -> old.(statPend) = PendTimeout ->
  mutex_query_lookup resumed eid current ->
  q_pend_cleanup_observation sg resumed eid 0 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None).
Proof.
  intros sg resumed eid tid old current Hentry Htimeout He.
  destruct Hentry as [Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]].
  rewrite Htimeout in Hregistration.
  destruct (q_pend_resume_timeout_event sg resumed eid tid old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (found = current) by congruence; subst found.
  split.
  - unfold sem_pend_cleanup_entry.
    split; [eapply UCOS2_event_task_remove_preserves_validity; eassumption|].
    split; [exact Hcur|]. split.
    + cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + split; [reflexivity|]. split; [exact Hmulti|]. split; assumption.
  - exists OS_ERR_TIMEOUT; split; [reflexivity|]. exists tid, old.
    split; [exact Hcur|]. split; [exact Hold|]. rewrite Htimeout.
    split; [reflexivity|]. exists current; auto.
Qed.

(** Reinsert the untouched message cell only for the existing Remove
    callee's three-field frame. It is exposed again on the returned world. *)
Lemma q_pend_cleanup_frame_merge_message : forall sg state tid old,
  tcb_cell (task_slot_addr sg tid) TCBMsg (Some (encode_msg old.(msg))) **
  q_pend_cleanup_frame sg state tid old |-- sem_pend_cleanup_frame sg state tid old.
Proof.
  intros; unfold q_pend_cleanup_frame, q_pend_cleanup_residual, sem_pend_cleanup_frame,
    sem_pend_tcb_residual.
  sep_apply_l_atomic (tcb64_fields_rep_merge
    (remove TCBField_eq_dec TCBEventPtr
      (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)))
    (task_slot_addr sg tid) (task_tcb64_image sg old) TCBMsg
    ltac:(repeat apply sem_pend_tcb_fields_remove_nodup; apply tcb_fields_nodup)
    ltac:(repeat apply in_in_remove; try discriminate; apply tcb_fields_complete)).
  entailer!.
Qed.

Lemma q_pend_resume_split_remove_call : forall sg resumed eid tid old current,
  sem_pend_resume_entry sg resumed eid tid old -> mutex_query_lookup resumed eid current ->
  event_object_layout_prop sg eid ->
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
  tcb_cell (task_slot_addr sg tid) TCBMsg (Some (encode_msg old.(msg))) **
  q_pend_cleanup_frame sg resumed tid old |--
  event_task_remove_pre (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_remove_call_frame sg resumed eid current tid old.
Proof.
  intros * Hentry He Hlayout.
  sep_apply_l_atomic (q_pend_cleanup_frame_merge_message sg resumed tid old).
  sep_apply_l_atomic (sem_pend_resume_split_remove_call sg resumed eid tid old current Hentry He Hlayout).
  entailer!.
Qed.

(** Reindex the existing parked map solely through the actual TCB stores.
    No new stack owner, future return, or event lifetime is introduced. *)
Lemma q_pend_wait_call_continuations_merge : forall external platform environment saved_local sg call
  entry eid current tid old timeout,
  q_pend_wait_entry sg entry eid current tid old ->
  q_pend_wait_call_post sg entry eid current tid old timeout **
  sem_pend_optional_continuation_resources external platform environment saved_local call entry |--
  UCOS2_inv sg (event_pend_state sg entry eid current tid old PendQ timeout) **
  sem_pend_optional_continuation_resources external platform environment saved_local call
    (event_pend_state sg entry eid current tid old PendQ timeout).
Proof.
  intros * Hentry; pose proof Hentry as [_ [_ [Hold _]]].
  sep_apply_l_atomic (sem_pend_optional_continuation_task_update external platform environment saved_local
    call entry tid old (task_set_event_ptr (task_prepare_event_wait old PendQ timeout) (Some eid))
    Hold eq_refl eq_refl).
  sep_apply_l_atomic (q_pend_wait_call_merge sg entry eid current tid old timeout Hentry).
  unfold sem_pend_optional_continuation_resources; destruct environment; entailer!.
Qed.

Lemma q_pend_remove_call_cleanup_split : forall external platform environment saved_local sg call resumed eid current tid old,
  sem_pend_resume_entry sg resumed eid tid old -> old.(statPend) = PendTimeout ->
  mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_remove_call_frame sg resumed eid current tid old **
  sem_pend_optional_continuation_resources external platform environment saved_local call resumed |--
  coq_prop (q_pend_cleanup_observation sg resumed eid 0 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None)) &&
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
   tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
   tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
   tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
   tcb_cell (task_slot_addr sg tid) TCBMsg (Some (encode_msg old.(msg))) **
   q_pend_cleanup_frame sg (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None) **
   sem_pend_optional_continuation_resources external platform environment saved_local call
     (event_task_remove_state resumed eid current tid old)).
Proof.
  intros * Hentry Htimeout He Hlayout.
  pose proof (q_pend_resume_cleanup_timeout sg resumed eid tid old current Hentry Htimeout He) as Hcleanup.
  pose proof Hentry as [_ [_ [Hold _]]].
  pose proof (proj1 Hcleanup) as [Hvalid [Hcur [Hnode Hrest]]].
  sep_apply_l_atomic (sem_pend_optional_continuation_task_update external platform environment saved_local
    call resumed tid old (task_set_event_ptr old None) Hold eq_refl eq_refl).
  sep_apply_l_atomic (sem_pend_remove_call_merge sg resumed eid current tid old Hentry Htimeout He Hlayout).
  sep_apply_l_atomic (q_pend_cleanup_split sg (event_task_remove_state resumed eid current tid old)
    tid (task_set_event_ptr old None) Hvalid Hcur Hnode).
  unfold sem_pend_optional_continuation_resources; destruct environment;
    cbn [task_set_event_ptr stat statPend eventPtr msg encode_event_link]; entailer!.
Qed.

Lemma q_pend_cleanup_continuations_merge : forall external platform environment saved_local sg call state tid old,
  sem_pend_cleanup_entry sg state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBMsg (Some 0) **
  q_pend_cleanup_frame sg state tid old **
  sem_pend_optional_continuation_resources external platform environment saved_local call state |--
  UCOS2_inv sg (message_pend_cleanup_state sg state tid old) **
  sem_pend_optional_continuation_resources external platform environment saved_local call
    (message_pend_cleanup_state sg state tid old).
Proof.
  intros * Hentry; pose proof Hentry as [Hvalid [_ [Hold _]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  sep_apply_l_atomic (sem_pend_optional_continuation_task_update external platform environment saved_local
    call state tid old (task_message_pend_cleanup false old) Hold eq_refl eq_refl).
  sep_apply_l_atomic (q_pend_cleanup_merge sg state tid old Hentry).
  unfold sem_pend_optional_continuation_resources; destruct environment;
    cbn [message_pend_cleanup_state event_pend_cleanup_state replace_TskS TskState]; try rewrite Hmulti; entailer!.
  unfold task_tcb_init_continuation_capsules.
  cbn [message_pend_cleanup_state event_pend_cleanup_state replace_TskS TskState].
  rewrite Hmulti; reflexivity.
Qed.

