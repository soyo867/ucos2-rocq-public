Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** These are observations at the unavailable-Mutex branch, after any
    owner-priority update. They are not a public entry restriction and do
    not assert a global invariant between the three native TCB stores and
    OS_EventTaskWait. The existing single-wait protocol supplies the
    unlinked caller; actual source ownership supplies the non-self owner. *)
Definition mutex_pend_wait_entry sg entry eid current tid old : Prop :=
  UCOS2_state_inv sg entry /\
  entry.(SchedState).(curTaskID) = Some tid /\
  entry.(TskState).(inUsedTaskStates) tid = Some old /\
  mutex_query_lookup entry eid current /\
  current.(eventType) = OS_EVENT_TYPE_MUTEX /\
  (exists mutex owner, current.(mutexFields) = Some mutex /\
    mutex.(mfOwner) = Some owner /\ owner <> tid) /\
  old.(curPrio) <> sg.(osLowestPrio) /\ old.(eventPtr) = None /\
  old.(eventMultiWaitEvents) = [] /\ old.(tcbFlagNode) = 0 /\
  In tid entry.(SchedState).(readyList) /\ event_object_layout_prop sg eid.

(** Reuse the complete Sem prefix residual unchanged. Only the pending
    status bit differs; there is no second model of a partially ready TCB. *)
Definition mutex_pend_wait_call_frame sg entry eid current tid old timeout : Assertion :=
  event_task_wait_tcb_rest (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendMutex timeout)) **
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

Definition mutex_pend_wait_call_pre sg entry eid current tid old timeout : Assertion :=
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
  mutex_pend_wait_call_frame sg entry eid current tid old timeout.

Definition mutex_pend_wait_call_post sg entry eid current tid old timeout : Assertion :=
  event_task_wait_post sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
    sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8))
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState)) **
  mutex_pend_wait_call_frame sg entry eid current tid old timeout.

Lemma mutex_pend_wait_prefix_split : forall sg state tid old,
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

Lemma mutex_pend_tcb_merge_wait_prefix : forall sg tid old timeout,
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 16)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBDly |--
  tcb64_storage_rep (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendMutex timeout)).
Proof.
  intros; rewrite task_prepare_event_wait_image_eq.
  apply sem_pend_tcb_three_fields_merge_updated; discriminate.
Qed.

Lemma mutex_pend_wait_entry_prio : forall sg entry eid current tid old,
  mutex_pend_wait_entry sg entry eid current tid old -> valid_task_prio sg old.(curPrio).
Proof.
  intros * [Hvalid [_ [Hold [_ [_ [_ [Hnonidle _]]]]]]].
  pose proof Hvalid as [Hprofile _].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  pose proof (sem_pend_task_priority_in_range sg entry tid old Hvalid Hold) as Hrange.
  unfold valid_task_prio; lia.
Qed.

Lemma mutex_pend_wait_entry_row_in_range : forall sg entry eid current tid old,
  mutex_pend_wait_entry sg entry eid current tid old -> 0 <= old.(curPrio) / 8 < 8.
Proof.
  intros * [Hvalid [_ [Hold _]]].
  pose proof (sem_pend_task_priority_in_range sg entry tid old Hvalid Hold) as Hrange.
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma mutex_pend_wait_entry_resource_conditions : forall sg entry eid current tid old,
  mutex_pend_wait_entry sg entry eid current tid old ->
  event_type_to_pend_type current.(eventType) = Some PendMutex /\
  event_wait_resource_unavailable current /\
  (forall mutex, current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some mutex -> mutex.(mfOwner) <> Some tid).
Proof.
  intros * [_ [_ [_ [_ [Htype [[mutex [owner [Hfields [Howner Hother]]]] _]]]]]].
  split; [rewrite Htype; reflexivity|]. split.
  - unfold event_wait_resource_unavailable; rewrite Htype, Hfields, Howner; discriminate.
  - intros found _ Hfound; assert (found = mutex) by congruence; subst found.
    rewrite Howner; congruence.
Qed.

(** The three real stores have occurred, but ready membership and EventPtr
    still describe the old state. Reassemble storage only and expose the
    exact cells consumed by the already checked internal helper. *)
Lemma mutex_pend_wait_prefix_split_call : forall sg entry eid current tid old timeout,
  mutex_pend_wait_entry sg entry eid current tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 16)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_prefix_frame sg entry tid old |--
  mutex_pend_wait_call_pre sg entry eid current tid old timeout.
Proof.
  intros * Hentry.
  pose proof (mutex_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [Hcur [Hold [He [Htype [Howner [Hnonidle
    [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  unfold sem_pend_prefix_frame.
  sepcon_assoc_change.
  sep_apply_l_atomic (mutex_pend_tcb_merge_wait_prefix sg tid old timeout).
  sep_apply_l_atomic (event_task_wait_tcb_split (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendMutex timeout))).
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
  unfold mutex_pend_wait_call_pre, mutex_pend_wait_call_frame,
    UCOS2_raw_rep_missing_task_storage_sched_event.
  cbn [task_tcb64_image task_prepare_event_wait].
  try rewrite Hnone; cbn [encode_event_link].
  entailer!.
  cbn [task_prepare_event_wait eventPtr curPrio tcb_y_of_prio].
  rewrite Hnone; reflexivity.
Qed.

Lemma mutex_pend_wait_call_merge : forall sg entry eid current tid old timeout,
  mutex_pend_wait_entry sg entry eid current tid old ->
  mutex_pend_wait_call_post sg entry eid current tid old timeout |--
  UCOS2_inv sg (event_pend_state sg entry eid current tid old PendMutex timeout).
Proof.
  intros * Hentry.
  pose proof (mutex_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  pose proof (mutex_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hprio.
  destruct (mutex_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hentry)
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
  unfold mutex_pend_wait_call_post, mutex_pend_wait_call_frame, event_task_wait_post.
  pose proof (event_task_wait_tcb_merge_event_ptr (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendMutex timeout)) (event_addr sg eid)) as Htcb.
  change (tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (event_addr sg eid)) **
    tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
    tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
    tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
    event_task_wait_tcb_rest (task_slot_addr sg tid)
      (task_tcb64_image sg (task_prepare_event_wait old PendMutex timeout)) |--
    tcb64_storage_rep (task_slot_addr sg tid)
      (tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendMutex timeout))
        TCBEventPtr (Some (event_addr sg eid)))) in Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb.
  unfold tcb_y_of_prio in Htcb.
  sepcon_assoc_change.
  sep_apply_l_atomic Htcb.
  assert (Himage : tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendMutex timeout))
    TCBEventPtr (Some (event_addr sg eid)) =
    task_tcb64_image sg (task_set_event_ptr (task_prepare_event_wait old PendMutex timeout) (Some eid)))
    by (symmetry; apply task_set_event_ptr_image_eq).
  rewrite Himage.
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid
    (task_set_event_ptr (task_prepare_event_wait old PendMutex timeout) (Some eid)) Hmulti Hprofiling).
  sep_apply_l_atomic (event_task_wait_event_merge_c_fields sg eid (event_image sg entry.(TskState) current)
    (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) Hlayout Hrow).
  sep_apply_l_atomic (event_task_wait_ready_merge_removed_task sg entry.(TskState) entry.(SchedState)
    tid old Hsg Hunique Hold Hrange Hstructure Hrow).
  assert (Hindex : forall state, sched_raw_rep sg entry.(TskState) state =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_set_event_ptr (task_prepare_event_wait old PendMutex timeout) (Some eid))) state).
  { intro state; apply sched_raw_rep_priority_ext; intros slot Hin.
    cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  intros heap Hheap.
  apply (UCOS2_inv_merge_event_pend_storage sg entry eid current tid old PendMutex timeout
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

Lemma mutex_pend_wait_entry_preserves_validity : forall sg entry eid current tid old timeout,
  mutex_pend_wait_entry sg entry eid current tid old ->
  UCOS2_state_inv sg (event_pend_state sg entry eid current tid old PendMutex timeout).
Proof.
  intros * Hentry.
  pose proof (mutex_pend_wait_entry_prio _ _ _ _ _ _ Hentry) as Hprio.
  destruct (mutex_pend_wait_entry_resource_conditions _ _ _ _ _ _ Hentry)
    as [Hkind [Hunavailable Hnotowner]].
  destruct Hentry as [Hvalid [Hcur [Hold [He [Htype [Howner [Hnonidle
    [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  eapply UCOS2_event_pend_preserves_validity; eassumption.
Qed.
