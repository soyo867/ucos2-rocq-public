Require Export Ucos2Verify.VC.code.queue.spec.q_post_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.error_codes.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The caller of the checked TCB64 OS_EventTaskRdy lends these resources.
    There is exactly one priority table, one focused TCB and one ECB; all
    Queue control blocks and message slots remain in the global residual. *)
Definition q_post_task_frame (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (tid : TaskID) : Assertion :=
  store_map_missing_i (used_task_rep sg) tasks.(inUsedTaskStates) tid **
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error tasks.(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg tasks.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> tasks.(taskCount) ** task_reg_allocator_rep sg tasks.

Lemma q_post_task_storage_split : forall sg tasks tid old,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tasks.(inUsedTaskStates) tid = Some old ->
  task_public_storage sg tasks |--
  tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg old) **
  store_prio_tbl sg tasks.(prioTbl) ** q_post_task_frame sg tasks tid.
Proof.
  intros sg tasks tid old Hmulti Hprofile Hold.
  sep_apply_l_atomic (task_public_storage_split_task sg tasks tid old Hold).
  rewrite used_task_rep_tcb64, task_slot_addr_tcb64 by assumption.
  unfold task_public_storage_without_task, task_public_storage_without_used_map,
    q_post_task_frame; entailer!.
Qed.

Lemma q_post_task_storage_merge : forall sg tasks tid new,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg new) **
  store_prio_tbl sg tasks.(prioTbl) ** q_post_task_frame sg tasks tid |--
  task_public_storage sg (glob_task_set_usedtask tasks tid new).
Proof.
  intros sg tasks tid new Hmulti Hprofile.
  rewrite task_slot_addr_tcb64 by assumption.
  rewrite <- used_task_rep_tcb64 by assumption.
  sep_apply_r_atomic (task_public_storage_merge_updated_task sg tasks tid new).
  unfold q_post_task_frame, task_public_storage_without_task,
    task_public_storage_without_used_map; entailer!.
Qed.

Definition q_post_wake_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (tid : TaskID) : Assertion :=
  q_post_task_frame sg entry.(TskState) tid **
  sched_physical_rep sg entry.(SchedState) **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  UCOS2_raw_rep_missing_task_storage_sched_event sg entry.

Definition q_post_wake_result (sg : StableGlobVars) (eid : EventID) (message : addr)
  (entry after : UCOS2_Verify_State) (priority : Z) : Prop :=
  event_task_rdy sg entry eid PendQ message PendOK = Some (priority, after).

Lemma q_post_wake_split : forall sg entry eid current,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(eventType) = OS_EVENT_TYPE_Q ->
  encode_event_wait_grp current.(waitList) entry.(TskState) <> 0 ->
  event_object_layout_prop sg eid ->
  UCOS2_inv sg entry ** unmap_table_rep sg |-- EX tid, EX old,
    coq_prop (event_task_rdy_entry sg entry.(TskState) eid current tid old) &&
    (event_task_rdy_pre sg entry.(TskState) eid current tid old 4 0
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
      (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
     q_post_wake_frame sg entry eid tid).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype Hnonempty Hlayout.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg)
    by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  destruct current.(waitList) as [|tid tail] eqn:Hlist;
    [contradiction Hnonempty; reflexivity|].
  destruct (q_post_wake_head sg entry eid current tid tail 0
    Hvalid Hlookup Htype Hlist) as [old [Hold Hrest]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  assert (Hentry : event_task_rdy_entry sg entry.(TskState) eid current tid old).
  { unfold event_task_rdy_entry; split; [exact Hsg|]; split; [exact Hlayout|].
    split; [exact Hmulti|]; split; [exact Htasks|].
    split; [exact (Hentries eid current Hlookup)|].
    split; [rewrite Hlist; reflexivity|exact Hold]. }
  rewrite UCOS2_inv_open_task_storage_sched_event; Intros.
  sep_apply_l_atomic (q_post_task_storage_split sg entry.(TskState) tid old Hmulti Hprofiling Hold).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState)
    eid current Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  Exists tid old; unfold event_task_rdy_pre, q_post_wake_frame, used_event_rep.
  entailer!; unfold sched_row_values; reflexivity.
Qed.

Lemma q_post_wake_merge : forall sg entry eid current tid old message priority,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(eventType) = OS_EVENT_TYPE_Q ->
  event_task_rdy_entry sg entry.(TskState) eid current tid old ->
  event_task_rdy_post sg entry.(TskState) eid current tid old message 4 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  q_post_wake_frame sg entry eid tid |-- EX after,
    coq_prop (q_post_wake_result sg eid message entry after priority) &&
    (UCOS2_inv sg after ** unmap_table_rep sg).
Proof.
  intros sg entry eid current tid old message priority Hvalid Hlookup Htype Hentry.
  pose proof Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (event_task_rdy_selection sg entry.(TskState) eid current tid old Hentry)
    as [_ [_ [_ [Hprio _]]]].
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendQ)
    by (rewrite Htype; reflexivity).
  destruct current.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (q_post_wake_head sg entry eid current tid tail message
    Hvalid Hlookup Htype Hlist) as [found [Hfound [Hstep [Hafter Hlast]]]].
  assert (found = old) by congruence; subst found.
  unfold event_task_rdy_post, q_post_wake_frame; Intros.
  assert (Hreturned : priority = old.(curPrio)) by tauto; subst priority.
  rewrite (event_task_rdy_typed_image_eq sg old message 4 0 PendQ PendOK eq_refl eq_refl).
  rewrite (event_task_rdy_scheduler_group_eq sg entry.(TskState) entry.(SchedState) tid old _ Hold).
  rewrite (event_task_rdy_scheduler_rows_eq sg entry.(TskState) entry.(SchedState) tid old _ Hold Hprio).
  sep_apply_l_atomic (q_post_task_storage_merge sg entry.(TskState) tid
    (task_event_wake_single old PendQ message PendOK) Hmulti Hprofiling).
  fold (used_event_rep sg entry.(TskState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg entry.(TskState) entry.(EventState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  rewrite <- sched_rows_array_equiv.
  rewrite <- (sched_wake_by_status_physical_rep_eq sg entry.(TskState) entry.(SchedState) tid
    (task_status_clear_wait (encode_task_status old.(stat)) 4)).
  assert (Hstatus : task_status_clear_wait (encode_task_status old.(stat)) 4 =
    encode_task_status (task_event_wake_single old PendQ message PendOK).(stat)).
  { change (task_status_clear_wait (encode_task_status old.(stat)) 4 =
      encode_task_status (task_clear_pending_status old.(stat) PendQ)).
    rewrite task_clear_pending_status_encoding; reflexivity. }
  rewrite Hstatus.
  assert (Hindex : forall s, sched_raw_rep sg entry.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_event_wake_single old PendQ message PendOK)) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    simpl; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  set (woken_sched := sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
    (encode_task_status (task_event_wake_single old PendQ message PendOK).(stat))).
  assert (Hsched :
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp woken_sched.(readyList) entry.(TskState) **
    sched_rows_rep sg entry.(TskState) woken_sched.(readyList) [0;1;2;3;4;5;6;7] **
    sched_physical_rep sg woken_sched |--
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_event_wake_single old PendQ message PendOK)) woken_sched).
  { rewrite <- Hindex; unfold sched_raw_rep; reflexivity. }
  sep_apply_l_atomic Hsched.
  pose proof (UCOS2_inv_merge_event_wake sg entry eid current tid old PendQ message PendOK
    Hvalid Hlookup ltac:(rewrite Hlist; left; reflexivity) Hold Hkind) as Hmerge.
  cbn zeta in Hmerge.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS
    TskState SchedState EventState] in Hmerge.
  fold woken_sched in Hmerge.
  sep_apply_l_atomic Hmerge.
  Exists (event_wake_state sg entry eid current tid old PendQ message PendOK).
  unfold q_post_wake_result; entailer!.
Qed.

Lemma q_post_wake_critical : forall sg entry eid current message priority after,
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  encode_event_wait_grp current.(waitList) entry.(TskState) <> 0 ->
  q_post_wake_result sg eid message entry after priority ->
  q_post_critical sg QueuePostBack eid message entry (OS_ERR_NONE, true) after.
Proof.
  intros sg entry eid current message priority after Hlookup Hgroup Hstep.
  exists current; split; [exact Hlookup|].
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup); split; [reflexivity|].
  exists priority; exact Hstep.
Qed.

Lemma q_post_full_critical : forall sg entry eid current q message,
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(queueFields) = Some q ->
  encode_event_wait_grp current.(waitList) entry.(TskState) = 0 ->
  q.(qSize) <= queue_entries q ->
  q_post_critical sg QueuePostBack eid message entry (OS_ERR_Q_FULL, false) entry.
Proof.
  intros sg entry eid current q message Hlookup Hq Hgroup Hfull.
  exists current; split; [exact Hlookup|].
  rewrite Hgroup; exists q; split; [exact Hq|].
  rewrite (proj2 (Z.leb_le _ _) Hfull); split; reflexivity.
Qed.

Lemma q_post_enqueue_critical : forall sg entry eid current q message slots next,
  entry.(EventState).(inUsedEventStates) eid = Some current ->
  current.(queueFields) = Some q ->
  encode_event_wait_grp current.(waitList) entry.(TskState) = 0 ->
  entry.(EventState).(publishedQueueBytes) q.(qID) = Some slots ->
  queue_enqueue_back q message = Some next ->
  q_post_critical sg QueuePostBack eid message entry (OS_ERR_NONE, false)
    (replace_EventS (queue_update entry.(EventState) eid current next
      (q_post_enqueue_slots false q message slots)) entry).
Proof.
  intros sg entry eid current q message slots next Hlookup Hq Hgroup Hslots Hstep.
  assert (Hroom : queue_entries q < q.(qSize)).
  { unfold queue_enqueue_back in Hstep.
    destruct (Z.ltb (queue_entries q) q.(qSize)) eqn:E; [apply Z.ltb_lt; exact E|discriminate]. }
  exists current; split; [exact Hlookup|].
  rewrite Hgroup; exists q; split; [exact Hq|].
  rewrite (proj2 (Z.leb_gt _ _) Hroom).
  exists slots, next; repeat split; assumption || reflexivity.
Qed.

Definition q_post_lookup (state : UCOS2_Verify_State) (eid : EventID)
  (node : OSEventAbstractState) : Prop :=
  state.(EventState).(inUsedEventStates) eid = Some node.

Definition q_post_field_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (node : OSEventAbstractState) (field : EventField) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) node) field **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Lemma q_post_field_split_full : forall sg state eid node field,
  q_post_lookup state eid node ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    (event_cell (event_addr sg eid) field ((event_image sg state.(TskState) node) field) **
     q_post_field_frame sg state eid node field).
Proof.
  intros sg state eid node field Hlookup Hfield.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState)
    eid node Hlookup).
  unfold used_event_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) node) field Hfield).
  unfold q_post_field_frame; entailer!.
Qed.

Lemma q_post_field_merge_full : forall sg state eid node field,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_cell (event_addr sg eid) field ((event_image sg state.(TskState) node) field) **
    q_post_field_frame sg state eid node field |-- UCOS2_inv sg state.
Proof.
  intros sg state eid node field Hvalid Hlookup Hfield; unfold q_post_field_frame.
  sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) node) field Hfield).
  fold (used_event_rep sg state.(TskState) eid node).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg state.(TskState) state.(EventState)
    eid node Hlookup).
  rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

Definition q_post_type_frame sg state eid node :=
  q_post_field_frame sg state eid node EventTypeField.
Definition q_post_group_frame sg state eid node :=
  q_post_field_frame sg state eid node EventGrpField.
Definition q_post_group (entry : UCOS2_Verify_State) (current : OSEventAbstractState) : Z :=
  encode_event_wait_grp current.(waitList) entry.(TskState).


