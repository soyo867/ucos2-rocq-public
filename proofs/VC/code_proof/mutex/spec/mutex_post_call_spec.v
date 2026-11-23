Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From AUXLib Require Import ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import CArch Mem ConAssertion.
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
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected native Post: reserve this Mutex's PCP before scanning the
    remaining aliases.  Unlike Delete, this is a real Reserved pointer cell.
    The frozen Delete library is reused only for common pure/structural
    facts; no Free-cell resource is asserted at any Post source stage. *)
Definition mutex_post_reserved_table (entry : UCOS2_Verify_State)
  (ceiling : Priority) : Priority -> PrioTblEntry :=
  update_prio_tbl entry.(TskState).(prioTbl) ceiling PTReserved.

Definition mutex_post_reserved_state (entry : UCOS2_Verify_State)
  (ceiling : Priority) : UCOS2_Verify_State :=
  mutex_del_ceiling_view entry ceiling.

Definition mutex_post_reserved_resources (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (ceiling : Priority) : Assertion :=
  store_prio_tbl sg (mutex_post_reserved_table entry ceiling) **
  UCOS2_raw_rep_missing_priority_table sg entry.

Lemma mutex_post_reserved_resources_merge_cell : forall sg entry ceiling,
  0 <= ceiling < 64 ->
  (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)) # Ptr |-> 1 **
    store_prio_tbl_missing_i sg entry.(TskState).(prioTbl) ceiling **
    UCOS2_raw_rep_missing_priority_table sg entry |--
  mutex_post_reserved_resources sg entry ceiling.
Proof.
  intros sg entry ceiling Hrange; unfold mutex_post_reserved_resources,
    mutex_post_reserved_table.
  pose proof (store_prio_tbl_merge_updated_cell sg
    entry.(TskState).(prioTbl) ceiling PTReserved Hrange) as Hmerge.
  cbn [prio_tbl_entry_to_addr] in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma mutex_post_reserved_priority_frame_eq : forall sg entry ceiling,
  UCOS2_raw_rep_missing_priority_table sg entry =
  UCOS2_raw_rep_missing_priority_table sg (mutex_post_reserved_state entry ceiling).
Proof.
  intros; unfold UCOS2_raw_rep_missing_priority_table.
  rewrite (sched_raw_rep_change_task_index sg entry.(TskState)
    (mutex_del_ceiling_view_tasks entry.(TskState) ceiling) entry.(SchedState) eq_refl),
    (UCOS2_raw_rep_missing_task_storage_sched_task_map_frame sg entry
      (mutex_del_ceiling_view_tasks entry.(TskState) ceiling) eq_refl eq_refl).
  reflexivity.
Qed.

Lemma mutex_post_reserved_resources_raw_equiv : forall sg entry ceiling,
  mutex_post_reserved_resources sg entry ceiling --||--
  UCOS2_raw_rep sg (mutex_post_reserved_state entry ceiling).
Proof.
  intros; rewrite UCOS2_raw_rep_priority_table_equiv.
  unfold mutex_post_reserved_resources; rewrite (mutex_post_reserved_priority_frame_eq sg entry ceiling).
  split; reflexivity.
Qed.

(** A proof-only comparison of scan observations.  Neither value denotes a
    real task address.  It does not change the Post heap into Delete's heap. *)
Lemma mutex_post_scan_matches_released : forall sg entry ceiling owner p,
  task_slot_addr sg owner <> 0 -> task_slot_addr sg owner <> 1 ->
  0 <= p < 64 ->
  (Znth p (mutex_del_priority_values sg (mutex_post_reserved_table entry ceiling)) 0 =
      task_slot_addr sg owner <->
   Znth p (mutex_del_priority_values sg (mutex_del_released_table entry ceiling)) 0 =
      task_slot_addr sg owner).
Proof.
  intros sg entry ceiling owner p Hzero Hone Hp.
  repeat rewrite mutex_del_priority_values_lookup by exact Hp.
  unfold mutex_post_reserved_table, mutex_del_released_table, update_prio_tbl.
  destruct (Z.eq_dec p ceiling); [|reflexivity].
  cbn [prio_tbl_entry_to_addr]; split; intro E; exfalso;
    [apply Hone|apply Hzero]; symmetry; exact E.
Qed.

Lemma mutex_post_scan_result_released : forall sg entry ceiling owner fallback priority,
  task_slot_addr sg owner <> 0 -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_post_reserved_table entry ceiling))
    (task_slot_addr sg owner) fallback priority ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_del_released_table entry ceiling))
    (task_slot_addr sg owner) fallback priority.
Proof.
  intros sg entry ceiling owner fallback priority Hzero Hone Hscan.
  destruct Hscan as [[Hnone E]|[Hp [Hhit Hmin]]].
  - left; split; [|exact E]. intros p Hp Hhit; apply (Hnone p Hp).
    apply (proj2 (mutex_post_scan_matches_released sg entry ceiling owner p Hzero Hone Hp)); exact Hhit.
  - right; split; [exact Hp|]. split.
    + apply (proj1 (mutex_post_scan_matches_released sg entry ceiling owner priority Hzero Hone Hp)); exact Hhit.
    + intros p Hp' Hhit'; apply Hmin; [exact Hp'|].
      apply (proj2 (mutex_post_scan_matches_released sg entry ceiling owner p Hzero Hone Hp')); exact Hhit'.
Qed.

Definition mutex_post_relocated_state (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (ceiling owner : Z)
  (node : TaskAbstractState) (priority : Priority) : UCOS2_Verify_State :=
  mutex_del_ceiling_view
    (mutex_del_relocated_state sg entry ceiling owner node priority) ceiling.

Definition mutex_post_owner_priority_state (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (ceiling owner : Z)
  (node : TaskAbstractState) (priority : Priority) : UCOS2_Verify_State :=
  if Z.eq_dec node.(curPrio) priority then mutex_post_reserved_state entry ceiling
  else mutex_post_relocated_state sg entry ceiling owner node priority.

Lemma mutex_post_owner_priority_state_ceiling_view_eq : forall sg entry ceiling owner node priority,
  mutex_post_owner_priority_state sg entry ceiling owner node priority =
  mutex_del_ceiling_view
    (mutex_del_owner_priority_state sg entry ceiling owner node priority) ceiling.
Proof.
  intros; unfold mutex_post_owner_priority_state, mutex_del_owner_priority_state.
  destruct Z.eq_dec; [|reflexivity].
  unfold mutex_post_reserved_state, mutex_del_ceiling_view, mutex_del_released_state,
    mutex_del_ceiling_view_tasks, mutex_del_released_tasks, mutex_del_released_table.
  cbn [replace_TskS TskState inUsedTaskStates unUsedTaskStates tcbListHead prioTbl
    taskRegNextID parkedTaskStacks taskLifecycle taskCount]; rewrite update_prio_tbl_overwrite.
  destruct entry; reflexivity.
Qed.

Lemma mutex_post_owner_scan_properties : forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_post_reserved_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority ->
  exists base,
    task_base_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner base /\
    task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority /\
    node.(curPrio) <= priority <= base /\ task_priority_in_range sg priority /\
    priority <> mutex.(mfPCP) /\ entry.(TskState).(prioTbl) priority = PTTask owner.
Proof.
  intros sg entry eid event mutex owner node priority Hvalid He Htype Hm Ho Henabled Hnode Hone Hscan.
  pose proof (mutex_del_live_task_pointer_nonzero sg entry owner node Hvalid Hnode) as Hzero.
  apply (mutex_post_scan_result_released sg entry mutex.(mfPCP) owner node.(curPrio) priority Hzero Hone) in Hscan.
  destruct (mutex_del_owner_scan_properties sg entry eid event mutex owner priority
    Hvalid He Htype Hm Ho Henabled Hone ltac:(intros other Hother;
      rewrite Hnode in Hother; injection Hother as E; subst other; exact Hscan))
    as [other [base [Hother Hrest]]].
  rewrite Hnode in Hother; injection Hother as E; subst other; exists base; exact Hrest.
Qed.

Lemma mutex_post_owner_scan_preserves_validity : forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_post_reserved_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority ->
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  UCOS2_state_inv sg
    (mutex_post_owner_priority_state sg entry mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority Hvalid He Htype Hm Ho Henabled Hnode Hone Hscan Huse.
  destruct (mutex_post_owner_scan_properties sg entry eid event mutex owner node priority
    Hvalid He Htype Hm Ho Henabled Hnode Hone Hscan)
    as [base [Hbase [Heffective [[Hmono Hbound] Hrest]]]].
  rewrite mutex_post_owner_priority_state_ceiling_view_eq.
  eapply mutex_del_owner_priority_ceiling_view_preserves_validity; try eassumption.
  intros mid e Hget.
  exact (mutex_owner_event_unlinked_not_waiter sg entry.(TskState) entry.(EventState)
    eid event mutex owner node (proj1 (proj2 (proj2 (proj2 Hvalid))))
    Huse He Htype Hm Ho Hnode mid e Hget).
Qed.

(** The ordered source guards are ISR, NULL, then Type.  No acquired-current,
    ready, stack or Mutex-owner fact is required on these early returns. *)
Definition mutex_post_before_save_error (pevent observed_type observed_nesting : Z)
  : option OSErrCode :=
  if Z_lt_dec 0 observed_nesting then Some OS_ERR_POST_ISR
  else if Z.eq_dec pevent 0 then Some OS_ERR_PEVENT_NULL
  else if Z.eq_dec observed_type 4 then None else Some OS_ERR_EVENT_TYPE.

Lemma mutex_post_before_save_isr : forall pevent observed_type observed_nesting,
  0 < observed_nesting ->
  mutex_post_before_save_error pevent observed_type observed_nesting = Some OS_ERR_POST_ISR.
Proof. intros; unfold mutex_post_before_save_error; destruct Z_lt_dec; [reflexivity|lia]. Qed.

Lemma mutex_post_before_save_null : forall observed_type observed_nesting,
  observed_nesting <= 0 ->
  mutex_post_before_save_error 0 observed_type observed_nesting = Some OS_ERR_PEVENT_NULL.
Proof.
  intros; unfold mutex_post_before_save_error; destruct Z_lt_dec; [lia|].
  destruct Z.eq_dec; [reflexivity|congruence].
Qed.

Lemma mutex_post_before_save_continues_iff : forall pevent observed_type observed_nesting,
  mutex_post_before_save_error pevent observed_type observed_nesting = None <->
  observed_nesting <= 0 /\ pevent <> 0 /\ observed_type = 4.
Proof.
  intros; unfold mutex_post_before_save_error; destruct Z_lt_dec;
    [split; [discriminate|lia]|].
  destruct Z.eq_dec; [split; [discriminate|tauto]|].
  destruct Z.eq_dec; split; intros; try discriminate; try tauto; lia.
Qed.

(** Exact owned input/output of the selected native relocation. The Delete
    caller's residual is reusable because it contains no priority-table
    cell. Here every priority-table image contains the actual Reserved tag. *)
Definition mutex_post_priority_input (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (ceiling owner : Z) (node : TaskAbstractState) : Assertion :=
  tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (mutex_del_priority_values sg (mutex_post_reserved_table entry ceiling)) **
  UCharArray.full sg.(g_OSRdyTbl) 8
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg entry.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte entry.(SchedState).(curSchedPrio).

Lemma mutex_post_reserved_resources_split_priority : forall sg entry ceiling owner node,
  selected_kernel_profile sg -> entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_post_reserved_resources sg entry ceiling |--
  mutex_post_priority_input sg entry ceiling owner node ** mutex_del_priority_frame sg entry owner.
Proof.
  intros sg entry ceiling owner node Hprofile Hnode.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold mutex_post_reserved_resources, UCOS2_raw_rep_missing_priority_table,
    task_public_storage_without_prio_tbl, store_used_task_map.
  sep_apply_l_atomic (store_map_split (used_task_rep sg) owner node
    entry.(TskState).(inUsedTaskStates) Hnode).
  unfold mutex_post_priority_input, mutex_del_priority_frame, sched_raw_rep, sched_physical_rep.
  rewrite used_task_rep_tcb64, <- task_slot_addr_tcb64 by assumption.
  rewrite sched_rows_array_equiv; unfold store_prio_tbl, mutex_del_priority_values; entailer!.
Qed.

Lemma mutex_post_priority_input_merge_reserved : forall sg entry ceiling owner node,
  selected_kernel_profile sg -> entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_post_priority_input sg entry ceiling owner node ** mutex_del_priority_frame sg entry owner |--
  mutex_post_reserved_resources sg entry ceiling.
Proof.
  intros sg entry ceiling owner node Hprofile Hnode.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold mutex_post_priority_input, mutex_del_priority_frame.
  rewrite task_slot_addr_tcb64 by assumption; rewrite <- used_task_rep_tcb64 by assumption.
  rewrite <- sched_rows_array_equiv.
  unfold mutex_post_reserved_resources, UCOS2_raw_rep_missing_priority_table,
    task_public_storage_without_prio_tbl, store_used_task_map, sched_raw_rep, sched_physical_rep,
    store_prio_tbl, mutex_del_priority_values.
  entailer!.
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) owner node entry.(TskState).(inUsedTaskStates) Hnode).
  entailer!.
Qed.

Definition mutex_post_priority_output (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (ceiling owner : Z) (node : TaskAbstractState) (priority : Priority) : Assertion :=
  tcb64_storage_rep (task_slot_addr sg owner)
    (mutex_priority_image (task_tcb64_image sg node) priority) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (replace_Znth priority (task_slot_addr sg owner)
      (mutex_del_priority_values sg (mutex_post_reserved_table entry ceiling))) **
  UCharArray.full sg.(g_OSRdyTbl) 8
    (mutex_priority_rows (sched_row_values entry.(TskState) entry.(SchedState).(readyList))
      (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)) priority) **
  sg.(g_OSRdyGrp) # UChar |->
    mutex_priority_group (sched_row_values entry.(TskState) entry.(SchedState).(readyList))
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
      (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio))
      (tcb_bit_y_of_prio node.(curPrio)) priority **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg entry.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> mutex_priority_current (task_slot_addr sg owner)
    (encode_task_link sg entry.(SchedState).(curTaskID))
    (sched_priority_byte entry.(SchedState).(curSchedPrio)) priority.

Lemma mutex_post_relocated_table_eq : forall sg entry ceiling owner node priority,
  (mutex_post_relocated_state sg entry ceiling owner node priority).(TskState).(prioTbl) =
  mutex_post_reserved_table entry ceiling.
Proof. intros; apply update_prio_tbl_overwrite. Qed.

Lemma mutex_post_relocated_other_modules_eq : forall sg entry ceiling owner node priority,
  (forall eid event, entry.(EventState).(inUsedEventStates) eid = Some event ->
    ~ In owner event.(waitList)) ->
  UCOS2_raw_rep_missing_task_storage_sched sg entry =
  UCOS2_raw_rep_missing_task_storage_sched sg
    (mutex_post_relocated_state sg entry ceiling owner node priority).
Proof.
  intros; rewrite (mutex_del_relocated_other_modules_eq sg entry ceiling owner node priority H).
  unfold mutex_post_relocated_state, mutex_del_ceiling_view.
  apply UCOS2_raw_rep_missing_task_storage_sched_task_map_frame; reflexivity.
Qed.

Lemma mutex_post_wake_split : forall sg eid state event,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_object_layout_prop sg eid ->
  UCOS2_raw_rep sg state ** unmap_table_rep sg |-- EX tid, EX old,
    coq_prop (event_task_rdy_entry sg state.(TskState) eid event tid old) &&
    (event_task_rdy_pre sg state.(TskState) eid event tid old 16 0
       (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
       (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
     mutex_del_wake_frame sg state eid tid).
Proof.
  intros sg eid state event Hvalid He Hnonzero Hlayout.
  pose proof Hvalid as [Hprofile [Htasks [Hsched [Hevents Hrest]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  destruct event.(waitList) as [|tid tail] eqn:Hlist; [contradiction Hnonzero; reflexivity|].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail
    Hsg Htasks (Hentries eid event He) Hlist) as [old [Hold Hselection]].
  assert (Hentry : event_task_rdy_entry sg state.(TskState) eid event tid old).
  { split; [exact Hsg|]. split; [exact Hlayout|]. split; [exact Hmulti|].
    split; [exact Htasks|]. split; [exact (Hentries eid event He)|].
    split; [rewrite Hlist; reflexivity|exact Hold]. }
  rewrite mutex_del_raw_task_sched_event_equiv.
  sep_apply_l_atomic (mutex_del_wake_task_storage_split sg state.(TskState) tid old Hmulti Hprofiling Hold).
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid event He).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  Exists tid old; unfold event_task_rdy_pre, mutex_del_wake_frame, used_event_rep.
  entailer!; unfold sched_row_values; reflexivity.
Qed.

Lemma mutex_post_event_task_rdy_merge_raw : forall sg eid state event tid old priority,
  selected_kernel_profile sg ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_task_rdy_entry sg state.(TskState) eid event tid old ->
  event_task_rdy_post sg state.(TskState) eid event tid old 0 16 0
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
  mutex_del_wake_frame sg state eid tid |--
  coq_prop (event_task_rdy sg state eid PendMutex 0 PendOK =
    Some (priority, event_wake_state sg state eid event tid old PendMutex 0 PendOK)) &&
  (UCOS2_raw_rep sg (event_wake_state sg state eid event tid old PendMutex 0 PendOK) **
   unmap_table_rep sg).
Proof.
  intros sg eid state event tid old priority Hprofile He Hentry.
  pose proof Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (event_task_rdy_selection sg state.(TskState) eid event tid old Hentry) as [_ [_ [_ [Hprio _]]]].
  destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  pose proof (event_task_rdy_selects_waiter sg state eid event tid tail old PendMutex 0 PendOK
    Hsg Htasks Hwait He Hlist Hold) as Hstep.
  unfold event_task_rdy_post, mutex_del_wake_frame; Intros.
  assert (Hreturned : priority = old.(curPrio)) by tauto; subst priority.
  rewrite (event_task_rdy_typed_image_eq sg old 0 16 0 PendMutex PendOK eq_refl eq_refl).
  rewrite (event_task_rdy_scheduler_group_eq sg state.(TskState) state.(SchedState) tid old _ Hold).
  rewrite (event_task_rdy_scheduler_rows_eq sg state.(TskState) state.(SchedState) tid old _ Hold Hprio).
  sep_apply_l_atomic (mutex_del_wake_task_storage_merge sg state.(TskState) tid
    (task_event_wake_single old PendMutex 0 PendOK) Hmulti Hprofiling).
  fold (used_event_rep sg state.(TskState) eid (event_set_wait_list event (remove_Z_eqb tid event.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg state.(TskState) state.(EventState) eid
    (event_set_wait_list event (remove_Z_eqb tid event.(waitList)))).
  rewrite <- sched_rows_array_equiv.
  rewrite <- (sched_wake_by_status_physical_rep_eq sg state.(TskState) state.(SchedState) tid
    (task_status_clear_wait (encode_task_status old.(stat)) 16)).
  assert (Hstatus : task_status_clear_wait (encode_task_status old.(stat)) 16 =
    encode_task_status (task_event_wake_single old PendMutex 0 PendOK).(stat)).
  { change (task_status_clear_wait (encode_task_status old.(stat)) 16 =
      encode_task_status (task_clear_pending_status old.(stat) PendMutex)).
    rewrite task_clear_pending_status_encoding; reflexivity. }
  rewrite Hstatus.
  assert (Hindex : forall s, sched_raw_rep sg state.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid (task_event_wake_single old PendMutex 0 PendOK)) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    simpl; destruct (Z.eqb slot tid) eqn:E; [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  set (woken_sched := sched_wake_by_status sg state.(TskState) state.(SchedState) tid
    (encode_task_status (task_event_wake_single old PendMutex 0 PendOK).(stat))).
  assert (Hsched :
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp woken_sched.(readyList) state.(TskState) **
    sched_rows_rep sg state.(TskState) woken_sched.(readyList) [0;1;2;3;4;5;6;7] **
    sched_physical_rep sg woken_sched |--
    sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid
      (task_event_wake_single old PendMutex 0 PendOK)) woken_sched).
  { rewrite <- Hindex; unfold sched_raw_rep; reflexivity. }
  sep_apply_l_atomic Hsched.
  pose proof (mutex_del_raw_event_wake_merge sg state eid event tid old PendMutex 0 PendOK He Hold) as Hmerge.
  cbn zeta in Hmerge; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState SchedState EventState] in Hmerge.
  fold woken_sched in Hmerge; sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Lemma mutex_post_priority_output_merge_raw : forall sg entry ceiling owner node priority,
  UCOS2_state_inv sg entry ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> 0 <= priority < 64 ->
  mutex_post_reserved_table entry ceiling priority = PTTask owner ->
  (forall eid event, entry.(EventState).(inUsedEventStates) eid = Some event ->
    ~ In owner event.(waitList)) ->
  mutex_post_priority_output sg entry ceiling owner node priority **
    mutex_del_priority_frame sg entry owner |--
  UCOS2_raw_rep sg (mutex_post_relocated_state sg entry ceiling owner node priority).
Proof.
  intros sg entry ceiling owner node priority Hvalid Hnode Hpriority Halias Habsent.
  pose proof Hvalid as [Hprofile [Htasks [Hsched Hrest]]].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (mutex_del_live_task_pointer_nonzero sg entry owner node Hvalid Hnode) as Hnonnull.
  destruct (mutex_del_relocated_ready_encoding sg entry.(TskState) entry.(SchedState)
    owner node priority (proj1 Hprofile) Htasks Hsched Hnode Hpriority) as [Hgroup Hrows].
  set (updated := (mutex_post_relocated_state sg entry ceiling owner node priority).(TskState)).
  set (ready := mutex_del_relocated_ready sg entry.(TskState) entry.(SchedState) owner node priority).
  destruct (sched_encoding_priority_ext ready updated
    (glob_task_set_usedtask entry.(TskState) owner (mutex_priority_task node priority))
    ltac:(intros; reflexivity)) as [Hgroup_index Hrows_index].
  assert (Hrow_values : sched_row_values updated ready =
    sched_row_values (glob_task_set_usedtask entry.(TskState) owner
      (mutex_priority_task node priority)) ready).
  { unfold sched_row_values; apply map_ext; exact Hrows_index. }
  fold ready in Hgroup, Hrows.
  rewrite <- Hgroup_index in Hgroup; rewrite <- Hrow_values in Hrows.
  pose proof (used_task_rep_tcb64 sg owner (mutex_priority_task node priority) Hmulti Hprofiling) as Htcb.
  rewrite <- task_slot_addr_tcb64 in Htcb by assumption.
  assert (Hoff : forall slot, slot <> owner ->
    entry.(TskState).(inUsedTaskStates) slot = updated.(inUsedTaskStates) slot).
  { intros slot Hneq; unfold updated; cbn [mutex_post_relocated_state mutex_del_ceiling_view
      mutex_del_ceiling_view_tasks mutex_del_relocated_state replace_TskS replace_SchedS TskState
      mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates].
    apply Z.eqb_neq in Hneq; rewrite Hneq; reflexivity. }
  unfold mutex_post_priority_output.
  rewrite mutex_priority_image_task_eq, <- Htcb.
  rewrite mutex_del_priority_values_rewrite_alias by assumption.
  rewrite mutex_del_priority_current_eq by exact Hnonnull.
  rewrite <- Hgroup, <- Hrows.
  unfold mutex_del_priority_frame.
  rewrite (mutex_post_relocated_other_modules_eq sg entry ceiling owner node priority Habsent).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (used_task_rep sg)
    entry.(TskState).(inUsedTaskStates) updated.(inUsedTaskStates) owner Hoff)).
  assert (Hlookup : updated.(inUsedTaskStates) owner = Some (mutex_priority_task node priority))
    by (apply mutex_del_relocated_tasks_lookup).
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) owner (mutex_priority_task node priority)
    updated.(inUsedTaskStates) Hlookup).
  eapply derivable1_trans with (y :=
    task_public_storage sg updated **
    sched_raw_rep sg updated (mutex_del_relocated_sched sg entry owner node priority) **
    UCOS2_raw_rep_missing_task_storage_sched sg
      (mutex_post_relocated_state sg entry ceiling owner node priority)).
  - unfold task_public_storage, store_used_task_map.
    assert (Htable : updated.(prioTbl) = mutex_post_reserved_table entry ceiling)
      by apply mutex_post_relocated_table_eq.
    rewrite Htable.
    unfold store_prio_tbl, mutex_del_priority_values, sched_raw_rep, sched_physical_rep.
    rewrite sched_rows_array_equiv.
    unfold updated, ready, mutex_post_relocated_state, mutex_del_ceiling_view,
      mutex_del_ceiling_view_tasks, mutex_del_relocated_state,
      mutex_del_relocated_tasks, mutex_del_relocated_sched.
    cbn [replace_TskS replace_SchedS TskState glob_task_set_usedtask inUsedTaskStates
      unUsedTaskStates tcbListHead prioTbl taskCount taskLifecycle taskRegNextID parkedTaskStacks
      readyList curTaskID curSchedPrio highRdyTid highRdyPrio ctxSwCtr isRunning].
    entailer!.
  - unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
    entailer!.
Qed.

(** This is the completed pair of count/owner stores, not the intermediate
    count-only heap. The low byte is the new owner's observed priority;
    the no-waiter path uses the available marker and no owner. *)
Lemma mutex_post_replace_low_byte :
  forall pcp old new,
    0 <= pcp <= 255 ->
    0 <= old <= 255 ->
    0 <= new <= 255 ->
    Z.lor (Z.land (pcp * 256 + old) 65280) new =
      pcp * 256 + new.
Proof.
  intros pcp old new Hpcp Hold Hnew.
  set (x := pcp * 256 + old).
  assert (Hx : 0 <= x <= 65535) by (unfold x; nia).
  assert (Hlow : Z.land x 255 = old).
  {
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    replace (2 ^ 8) with 256 by reflexivity.
    unfold x.
    rewrite Z.add_comm, Z.mod_add by lia.
    apply Z.mod_small.
    lia.
  }
  assert (Hhigh : Z.land x 65280 = x - old).
  {
    replace 65280 with (Z.land (Z.lnot 255) 65535) by reflexivity.
    rewrite Z.land_assoc.
    rewrite <- Z.sub_land_same_l.
    rewrite Hlow.
    replace 65535 with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia.
    apply Z.mod_small.
    lia.
  }
  rewrite Hhigh.
  assert (Hdisjoint : Z.land (x - old) new = 0).
  {
    assert (Hnew_mask : Z.land new 255 = new).
    {
      replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia.
      apply Z.mod_small.
      lia.
    }
    unfold x.
    replace (pcp * 256 + old - old) with (pcp * 256) by lia.
    rewrite <- Hnew_mask.
    rewrite (Z.land_comm new 255).
    rewrite Z.land_assoc.
    assert (Hpcp_mask : Z.land (pcp * 256) 255 = 0).
    {
      replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      apply Z.mod_mul.
      lia.
    }
    rewrite Hpcp_mask.
    reflexivity.
  }
  pose proof (Z.add_lor_land (x - old) new) as Hsum.
  rewrite Hdisjoint in Hsum.
  unfold x in *.
  lia.
Qed.

Lemma mutex_post_available_count :
  forall pcp orig,
    0 <= pcp <= 255 ->
    0 <= orig <= 255 ->
    Z.lor
      (unsigned_last_nbits (pcp * 256 + orig) 16) 255 =
      pcp * 256 + 255.
Proof.
  intros pcp orig Hpcp Horig.
  rewrite unsigned_last_nbits_eq by (cbn; nia).
  assert (Hlow : Z.land (pcp * 256 + orig) 255 = orig).
  {
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    replace (2 ^ 8) with 256 by reflexivity.
    rewrite Z.add_comm, Z.mod_add by lia.
    apply Z.mod_small.
    lia.
  }
  pose proof (Z.add_lor_land (pcp * 256 + orig) 255) as Hsum.
  rewrite Hlow in Hsum.
  lia.
Qed.

Definition mutex_post_owner_event (event : OSEventAbstractState) (mutex : MutexFields)
  (owner : option TaskID) (snapshot : option Priority) : OSEventAbstractState :=
  {| eventGeneration := event.(eventGeneration); eventName := event.(eventName);
     eventPadding1 := event.(eventPadding1); eventPadding2 := event.(eventPadding2);
     eventPadding3 := event.(eventPadding3); eventPadding19 := event.(eventPadding19);
     eventType := event.(eventType);
     mutexFields := Some {| mfPCP := mutex.(mfPCP); mfOwner := owner; mfOwnerOrigPrio := snapshot |};
     semFields := event.(semFields); mboxFields := event.(mboxFields);
     queueFields := event.(queueFields); waitList := event.(waitList) |}.

Definition mutex_post_owner_result (tasks : Glob_TaskAbstractState)
  (event : OSEventAbstractState) (owner : option TaskID) (snapshot : option Priority) : Prop :=
  match owner, snapshot with
  | None, None => event.(waitList) = []
  | Some tid, Some priority => exists node,
      tasks.(inUsedTaskStates) tid = Some node /\ priority = node.(curPrio) /\
      ~ In tid event.(waitList)
  | _, _ => False
  end.

Definition mutex_post_owner_state (state : UCOS2_Verify_State) (eid : EventID)
  (event : OSEventAbstractState) (mutex : MutexFields)
  (owner : option TaskID) (snapshot : option Priority) : UCOS2_Verify_State :=
  replace_EventS (update_event_field_raw state.(EventState) eid
    (mutex_post_owner_event event mutex owner snapshot)) state.

Lemma mutex_post_owner_event_wait_entry : forall sg tasks eid event mutex owner snapshot,
  event_wait_entry_consistency sg tasks eid event ->
  event_wait_entry_consistency sg tasks eid (mutex_post_owner_event event mutex owner snapshot).
Proof. intros; exact H. Qed.

Lemma mutex_post_owner_event_lookup : forall state eid event mutex owner snapshot mid after,
  (mutex_post_owner_state state eid event mutex owner snapshot).(EventState).(inUsedEventStates) mid = Some after ->
  (mid = eid /\ after = mutex_post_owner_event event mutex owner snapshot) \/
  (mid <> eid /\ state.(EventState).(inUsedEventStates) mid = Some after).
Proof.
  intros; cbn [mutex_post_owner_state replace_EventS EventState update_event_field_raw inUsedEventStates] in H.
  destruct (Z.eqb mid eid) eqn:E; [apply Z.eqb_eq in E|apply Z.eqb_neq in E].
  - left; split; [exact E|congruence].
  - right; auto.
Qed.

Lemma mutex_post_owner_slot_claim_iff : forall sg state eid event mutex owner snapshot p,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  ((exists mid e m,
      (mutex_post_owner_state state eid event mutex owner snapshot).(EventState).(inUsedEventStates) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\ mutex_reserves_priority_slot sg m p) <->
   (exists mid e m, state.(EventState).(inUsedEventStates) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\ mutex_reserves_priority_slot sg m p)).
Proof.
  intros sg state eid event mutex owner snapshot p He Htype Hm; split.
  - intros [mid [e [m [Hget [Hty [Hfields Hclaim]]]]]].
    destruct (mutex_post_owner_event_lookup state eid event mutex owner snapshot mid e Hget)
      as [[E Eevent]|[Hne Hbefore]].
    + subst mid e; cbn [mutex_post_owner_event mutexFields] in Hfields.
      injection Hfields as E; subst m.
      exists eid, event, mutex; split; [exact He|]. split; [exact Htype|].
      split; [exact Hm|exact Hclaim].
    + exists mid, e, m; auto.
  - intros [mid [e [m [Hget [Hty [Hfields Hclaim]]]]]].
    destruct (Z.eq_dec mid eid) as [->|Hne].
    + rewrite He in Hget; injection Hget as E; subst e.
      rewrite Hm in Hfields; injection Hfields as E; subst m.
      exists eid, (mutex_post_owner_event event mutex owner snapshot),
        {| mfPCP := mutex.(mfPCP); mfOwner := owner; mfOwnerOrigPrio := snapshot |}.
      split; [cbn [mutex_post_owner_state replace_EventS EventState update_event_field_raw inUsedEventStates];
        rewrite Z.eqb_refl; reflexivity|].
      split; [exact Htype|]. split; [reflexivity|exact Hclaim].
    + exists mid, e, m; split; [|auto].
      cbn [mutex_post_owner_state replace_EventS EventState update_event_field_raw inUsedEventStates].
      apply Z.eqb_neq in Hne; rewrite Hne; exact Hget.
Qed.

Lemma mutex_post_owner_alias_consistency : forall sg state eid event mutex owner snapshot,
  cross_module_consistency sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_priority_alias_consistency sg state.(TskState)
    (mutex_post_owner_state state eid event mutex owner snapshot).(EventState).
Proof.
  intros sg state eid event mutex owner snapshot [[_ [_ Halias]] _] He Htype Hm Hslot tid node Hnode.
  destruct (Halias tid node Hnode) as [base [Hbase [Heffective Hclaims]]].
  exists base; split; [exact Hbase|]. split; [exact Heffective|].
  intros p Hp; destruct (Hclaims p Hp) as [E|[Hlt [mid [e [m [Hget [Hty [Hfields [Ho [Henabled Epcp]]]]]]]]]].
  - left; exact E.
  - right; split; [exact Hlt|].
    assert (Hne : mid <> eid).
    { intro E; subst mid; rewrite He in Hget; injection Hget as E; subst e.
      rewrite Hm in Hfields; injection Hfields as E; subst m.
      destruct Hslot as [Hdisabled|Hreserved].
      - contradiction.
      - destruct Hp as [_ Hbad]; rewrite <- Epcp, Hreserved in Hbad; discriminate. }
    exists mid, e, m; split.
    + cbn [mutex_post_owner_state replace_EventS EventState update_event_field_raw inUsedEventStates].
      apply Z.eqb_neq in Hne; rewrite Hne; exact Hget.
    + repeat split; assumption.
Qed.

Lemma mutex_post_new_owner_snapshot : forall sg state event mutex owner snapshot tid,
  UCOS2_state_inv sg state ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_post_owner_result state.(TskState) event owner snapshot -> owner = Some tid ->
  exists node base priority,
    state.(TskState).(inUsedTaskStates) tid = Some node /\
    task_base_priority sg state.(TskState).(prioTbl) tid base /\ snapshot = Some priority /\
    task_priority_in_range sg priority /\ priority <= base /\
    ~ In tid event.(waitList) /\
    (mutex_pcp_enabled sg mutex -> mutex.(mfPCP) <> base) /\
    (mutex_pcp_enabled sg mutex -> priority <> mutex.(mfPCP)).
Proof.
  intros sg state event mutex owner snapshot tid Hvalid Hslot Hresult Howner; subst owner.
  destruct snapshot as [priority|]; [|contradiction].
  destruct Hresult as [node [Hnode [-> Habsent]]].
  pose proof Hvalid as [_ [_ [_ [_ [[[_ [_ Halias]] _] _]]]]].
  destruct (Halias tid node Hnode) as [base [Hbase [Heffective Hclaims]]].
  exists node, base, node.(curPrio); split; [exact Hnode|]. split; [exact Hbase|].
  split; [reflexivity|]. split; [exact (proj1 (proj1 Heffective))|]. split.
  - eapply task_effective_priority_le_base; eassumption.
  - split; [exact Habsent|]. split; intros Henabled E.
    + destruct Hslot as [Hdisabled|Hreserved]; [contradiction|].
      destruct (proj1 Hbase) as [_ Hhit]; rewrite <- E, Hreserved in Hhit; discriminate.
    + destruct Hslot as [Hdisabled|Hreserved]; [contradiction|].
      destruct (proj1 Heffective) as [_ Hhit]; rewrite E, Hreserved in Hhit; discriminate.
Qed.

Lemma mutex_post_owner_event_fields : forall sg state event mutex owner snapshot,
  UCOS2_state_inv sg state ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event_fields_consistency event ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_post_owner_result state.(TskState) event owner snapshot ->
  event_fields_consistency (mutex_post_owner_event event mutex owner snapshot) /\
  event_payload_consistency sg (mutex_post_owner_event event mutex owner snapshot).
Proof.
  intros sg state event mutex owner snapshot Hvalid Htype Hfields Hslot Hresult.
  split.
  - unfold event_fields_consistency, mutex_post_owner_event; simpl; rewrite Htype.
    unfold event_fields_consistency in Hfields; rewrite Htype in Hfields.
    split; [discriminate|tauto].
  - unfold event_payload_consistency, mutex_post_owner_event; simpl; rewrite Htype.
    destruct owner as [tid|]; destruct snapshot as [priority|]; try contradiction.
    + destruct (mutex_post_new_owner_snapshot sg state event mutex (Some tid) (Some priority) tid
        Hvalid Hslot Hresult eq_refl) as [node [base [prio [_ [_ [E [Hrange Hrest]]]]]]].
      injection E as E; subst prio.
      assert (Htag : sg.(osLowestPrio) = 63 /\ sg.(osPrioMutexCeilDis) = 255)
        by (destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
      unfold mutex_fields_consistency, task_priority_in_range; cbn.
      unfold task_priority_in_range in Hrange; split; [lia|discriminate].
    + split; [exact I|]. intro H; exact Hresult.
Qed.

Lemma mutex_post_owner_wait_consistency : forall sg state eid event mutex owner snapshot,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_wait_object_consistency sg state ->
  event_wait_object_consistency sg (mutex_post_owner_state state eid event mutex owner snapshot).
Proof.
  intros sg state eid event mutex owner snapshot He [Hentries [Hback Hclosed]].
  split.
  - intros mid e Hget.
    destruct (mutex_post_owner_event_lookup state eid event mutex owner snapshot mid e Hget)
      as [[-> ->]|[Hne Hbefore]].
    + apply mutex_post_owner_event_wait_entry; exact (Hentries eid event He).
    + exact (Hentries mid e Hbefore).
  - split.
    + intros tid node mid e Hnode Hget Hreference.
      destruct (mutex_post_owner_event_lookup state eid event mutex owner snapshot mid e Hget)
        as [[-> ->]|[Hne Hbefore]].
      * exact (Hback tid node eid event Hnode He Hreference).
      * exact (Hback tid node mid e Hnode Hbefore Hreference).
    + eapply task_event_reference_closure_preserved_by_event_extension; [|exact Hclosed].
      intros mid [e Hget]; destruct (Z.eq_dec mid eid) as [->|Hne].
      * exists (mutex_post_owner_event event mutex owner snapshot).
        cbn [mutex_post_owner_state replace_EventS EventState update_event_field_raw inUsedEventStates].
        rewrite Z.eqb_refl; reflexivity.
      * exists e; cbn [mutex_post_owner_state replace_EventS EventState update_event_field_raw inUsedEventStates].
        apply Z.eqb_neq in Hne; rewrite Hne; exact Hget.
Qed.

Lemma mutex_post_owner_cross_module_consistency : forall sg state eid event mutex owner snapshot,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_post_owner_result state.(TskState) event owner snapshot ->
  cross_module_consistency sg (mutex_post_owner_state state eid event mutex owner snapshot).
Proof.
  intros sg state eid event mutex owner snapshot Hvalid He Htype Hm Hslot Hresult.
  pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  pose proof Hcross as [[Hcreator [Hslots Halias]] [Hsnapshot [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  pose proof (mutex_post_owner_slot_claim_iff sg state eid event mutex owner snapshot) as Hclaims.
  split.
  - split.
    + intros p reservation Hreservation Hclaim; apply (Hcreator p reservation Hreservation).
      apply (proj1 (Hclaims p He Htype Hm)); exact Hclaim.
    + split.
      * intros p Hp; specialize (Hslots p Hp); cbn [mutex_post_owner_state replace_EventS TskState EventState].
        destruct (state.(TskState).(prioTbl) p).
        -- intro Hclaim; apply Hslots; apply (proj1 (Hclaims p He Htype Hm)); exact Hclaim.
        -- destruct Hslots as [Hreservation|[Hclaim|Hpending]].
           ++ left; exact Hreservation.
           ++ right; left; apply (proj2 (Hclaims p He Htype Hm)); exact Hclaim.
           ++ right; right; exact Hpending.
        -- exact Hslots.
      * exact (mutex_post_owner_alias_consistency sg state eid event mutex owner snapshot Hcross He Htype Hm Hslot).
  - split.
    + intros mid e m tid Hget Hty Hfields Howner.
      destruct (mutex_post_owner_event_lookup state eid event mutex owner snapshot mid e Hget)
        as [[-> ->]|[Hne Hbefore]].
      * cbn [mutex_post_owner_event mutexFields] in Hfields; injection Hfields as E; subst m.
        destruct (mutex_post_new_owner_snapshot sg state event mutex owner snapshot tid
          Hvalid Hslot Hresult Howner) as [node [base [priority Hfacts]]].
        exists node, base, priority; cbn [mutex_post_owner_event mfOwnerOrigPrio waitList mfPCP mutex_pcp_enabled] in *.
        tauto.
      * exact (Hsnapshot mid e m tid Hbefore Hty Hfields Howner).
    + split; [apply mutex_post_owner_wait_consistency; assumption|]. split.
      * intros mid e m Hget Hty Hfields.
        destruct (mutex_post_owner_event_lookup state eid event mutex owner snapshot mid e Hget)
          as [[-> ->]|[Hne Hbefore]].
        -- cbn [mutex_post_owner_event mutexFields] in Hfields; injection Hfields as E; subst m.
           pose proof (Hprotocol eid event mutex He Htype Hm) as [Hpcp Hrest].
           split; [exact Hpcp|]. split.
           ++ destruct owner as [tid|]; destruct snapshot as [priority|]; try contradiction; [|exact I].
              destruct (mutex_post_new_owner_snapshot sg state event mutex (Some tid) (Some priority) tid
                Hvalid Hslot Hresult eq_refl) as [node [base [prio [_ [_ [E [Hrange Hfacts]]]]]]].
              injection E as E; subst prio; split; [exact Hrange|].
              exact (proj2 (proj2 (proj2 Hfacts))).
           ++ destruct Hslot as [Hdisabled|Hreserved]; [left; exact Hdisabled|].
              destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)) as [E|Hne];
                [left; exact E|right; split; [exact Hne|left; exact Hreserved]].
        -- exact (Hprotocol mid e m Hbefore Hty Hfields).
      * split.
        -- eapply mutex_enabled_pcp_unique_transport; [|exact Hunique].
           intros mid e m Hget Hty Hfields.
           destruct (mutex_post_owner_event_lookup state eid event mutex owner snapshot mid e Hget)
             as [[-> ->]|[Hne Hbefore]].
           ++ cbn [mutex_post_owner_event mutexFields] in Hfields; injection Hfields as E; subst m.
              exists event, mutex; auto.
           ++ exists e, m; auto.
        -- split; [exact Hflags|exact Htimer].
Qed.

Lemma mutex_post_owner_state_preserves_validity : forall sg state eid event mutex owner snapshot,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_post_owner_result state.(TskState) event owner snapshot ->
  UCOS2_state_inv sg (mutex_post_owner_state state eid event mutex owner snapshot).
Proof.
  intros sg state eid event mutex owner snapshot Hvalid He Htype Hm Hslot Hresult.
  pose proof Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus
    [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]].
  pose proof Hevents as [_ [_ [_ [Hfields [_ [_ Hentries]]]]]].
  destruct (mutex_post_owner_event_fields sg state event mutex owner snapshot
    Hvalid Htype (Hfields eid event He) Hslot Hresult) as [HfieldsAfter HpayloadAfter].
  assert (HeventsAfter : event_in_range sg state.(TskState)
    (update_event_field_raw state.(EventState) eid (mutex_post_owner_event event mutex owner snapshot))).
  { eapply event_update_preserves_in_range; [exact Hevents|exact He|reflexivity|
      exact HfieldsAfter|exact HpayloadAfter|reflexivity|].
    apply mutex_post_owner_event_wait_entry; exact (Hentries eid event He). }
  assert (HreferencesAfter : kernel_names_valid sg
    (mutex_post_owner_state state eid event mutex owner snapshot)).
  { apply kernel_names_valid_replace_event; [exact Hreferences|].
    eapply event_update_preserves_name_references; [exact He|reflexivity]. }
  assert (HpendingAfter : pending_mutex_consistency sg state.(TskState)
    (mutex_post_owner_state state eid event mutex owner snapshot).(EventState)).
  { eapply pending_mutex_consistency_frame with (tasks := state.(TskState)) (events := state.(EventState));
      [reflexivity|reflexivity|reflexivity| |exact Hpending].
    intros p Hclaim; apply (proj1 (mutex_post_owner_slot_claim_iff sg state eid event mutex owner snapshot p He Htype Hm));
      exact Hclaim. }
  split; [exact Hprofile|]. split; [exact Htasks|]. split; [exact Hsched|].
  split; [exact HeventsAfter|]. split.
  - eapply mutex_post_owner_cross_module_consistency; eassumption.
  - split; [exact Hidle|]. split; [exact Hstatus|]. split; [exact Hflags|].
    split; [exact Hmemory|]. split; [exact Htimer|]. split; [exact Hstats|].
    split; [exact Hcontrol|]. split; [exact Hnames|]. split; [exact HreferencesAfter|].
    split; [exact Hstacks|exact HpendingAfter].
Qed.

Lemma mutex_post_owner_priority_event_state_eq : forall sg entry ceiling owner node priority,
  (mutex_post_owner_priority_state sg entry ceiling owner node priority).(EventState) = entry.(EventState).
Proof. intros; unfold mutex_post_owner_priority_state; destruct Z.eq_dec; reflexivity. Qed.

Lemma mutex_post_owner_priority_table_eq : forall sg entry ceiling owner node priority,
  (mutex_post_owner_priority_state sg entry ceiling owner node priority).(TskState).(prioTbl) =
    mutex_post_reserved_table entry ceiling.
Proof.
  intros; unfold mutex_post_owner_priority_state; destruct Z.eq_dec;
    [reflexivity|apply mutex_post_relocated_table_eq].
Qed.

Lemma mutex_post_wake_owner_selection : forall sg state eid event tid old priority,
  event_task_rdy_entry sg state.(TskState) eid event tid old ->
  priority = old.(curPrio) ->
  (event_wake_state sg state eid event tid old PendMutex 0 PendOK).(TskState).(prioTbl) priority = PTTask tid /\
  mutex_post_owner_result
    (event_wake_state sg state eid event tid old PendMutex 0 PendOK).(TskState)
    (event_set_wait_list event (remove_Z_eqb tid event.(waitList))) (Some tid) (Some priority).
Proof.
  intros sg state eid event tid old priority Hentry ->.
  pose proof (event_task_rdy_selection sg state.(TskState) eid event tid old Hentry) as [_ [Htable _]].
  split; [exact Htable|].
  exists (task_event_wake_single old PendMutex 0 PendOK); split.
  - cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity.
  - split; [reflexivity|]. apply remove_Z_eqb_notin.
Qed.

Lemma mutex_post_wake_merge_inv : forall sg eid state event tid old priority,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event_task_rdy_entry sg state.(TskState) eid event tid old ->
  event_task_rdy_post sg state.(TskState) eid event tid old 0 16 0
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
  mutex_del_wake_frame sg state eid tid |--
  coq_prop (event_task_rdy sg state eid PendMutex 0 PendOK =
    Some (priority, event_wake_state sg state eid event tid old PendMutex 0 PendOK)) &&
  (UCOS2_inv sg (event_wake_state sg state eid event tid old PendMutex 0 PendOK) ** unmap_table_rep sg).
Proof.
  intros sg eid state event tid old priority Hvalid He Htype Hentry.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hin : In tid event.(waitList)).
  { destruct event.(waitList) as [|head tail]; [discriminate|]; inversion Hhead; subst; simpl; auto. }
  assert (Hafter : UCOS2_state_inv sg (event_wake_state sg state eid event tid old PendMutex 0 PendOK)).
  { eapply UCOS2_event_wake_preserves_validity; [exact Hvalid|exact He|exact Hin|exact Hold|].
    rewrite Htype; reflexivity. }
  sep_apply_l_atomic (mutex_post_event_task_rdy_merge_raw sg eid state event tid old priority
    (proj1 Hvalid) He Hentry).
  Intros; unfold UCOS2_inv; entailer!.
Qed.

Lemma mutex_post_wake_handover_preserves_validity : forall sg state eid event mutex tid old priority,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  event_task_rdy_entry sg state.(TskState) eid event tid old -> priority = old.(curPrio) ->
  UCOS2_state_inv sg
    (mutex_post_owner_state (event_wake_state sg state eid event tid old PendMutex 0 PendOK)
      eid (event_set_wait_list event (remove_Z_eqb tid event.(waitList))) mutex
      (Some tid) (Some priority)).
Proof.
  intros sg state eid event mutex tid old priority Hvalid He Htype Hm Hslot Hentry Hpriority.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hin : In tid event.(waitList)).
  { destruct event.(waitList) as [|head tail]; [discriminate|]; inversion Hhead; subst; simpl; auto. }
  eapply mutex_post_owner_state_preserves_validity.
  - eapply UCOS2_event_wake_preserves_validity; [exact Hvalid|exact He|exact Hin|exact Hold|].
    rewrite Htype; reflexivity.
  - cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState update_event_field_raw inUsedEventStates].
    rewrite Z.eqb_refl; reflexivity.
  - exact Htype.
  - exact Hm.
  - exact Hslot.
  - exact (proj2 (mutex_post_wake_owner_selection sg state eid event tid old priority Hentry Hpriority)).
Qed.

Definition mutex_post_empty_image (image : EventStorage) : EventStorage :=
  event_write
    (event_write image EventCntField
      (option_map (fun count => Z.lor (unsigned_last_nbits count 16) 255) (image EventCntField)))
    EventPtrField (Some 0).

Definition mutex_post_handover_image (image : EventStorage) (priority pointer : Z) : EventStorage :=
  let high := event_write image EventCntField
    (option_map (fun count => Z.land count 65280) (image EventCntField)) in
  let counted := event_write high EventCntField
    (option_map (fun count => Z.lor count priority) (high EventCntField)) in
  event_write counted EventPtrField (Some pointer).

Lemma mutex_post_empty_image_event_eq : forall sg tasks event mutex owner snapshot,
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex.(mfOwnerOrigPrio) = Some snapshot ->
  0 <= mutex.(mfPCP) <= 255 -> 0 <= snapshot <= 255 ->
  mutex_post_empty_image (event_image sg tasks event) =
    event_image sg tasks (mutex_post_owner_event event mutex None None).
Proof.
  intros sg tasks event mutex owner snapshot Htype Hm Ho Hsnapshot Hpcp Hrange.
  apply functional_extensionality; intro field; destruct field;
    unfold mutex_post_empty_image, event_write, field_update, event_image, mutex_post_owner_event;
    simpl; try reflexivity.
  - unfold encode_event_ptr_value; simpl; rewrite Htype; reflexivity.
  - unfold encode_event_cnt_value; simpl; rewrite Htype, Hm, Ho, Hsnapshot.
    f_equal; apply mutex_post_available_count; assumption.
Qed.

Lemma mutex_post_handover_image_event_eq : forall sg tasks event mutex previous snapshot owner priority,
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some previous -> mutex.(mfOwnerOrigPrio) = Some snapshot ->
  0 <= mutex.(mfPCP) <= 255 -> 0 <= snapshot <= 255 -> 0 <= priority <= 255 ->
  mutex_post_handover_image (event_image sg tasks event) priority (task_slot_addr sg owner) =
    event_image sg tasks (mutex_post_owner_event event mutex (Some owner) (Some priority)).
Proof.
  intros sg tasks event mutex previous snapshot owner priority Htype Hm Ho Hsnapshot Hpcp Hrange Hpriority.
  apply functional_extensionality; intro field; destruct field;
    unfold mutex_post_handover_image, event_write, field_update, event_image, mutex_post_owner_event;
    simpl; try reflexivity.
  - unfold encode_event_ptr_value; simpl; rewrite Htype; reflexivity.
  - unfold encode_event_cnt_value; simpl; rewrite Htype, Hm, Ho, Hsnapshot.
    f_equal; apply mutex_post_replace_low_byte; assumption.
Qed.

Definition mutex_post_event_frame (sg : StableGlobVars) (state : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Lemma mutex_post_event_split : forall sg state eid event,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  UCOS2_inv sg state |--
  coq_prop (UCOS2_state_inv sg state) &&
  (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
     (event_image sg state.(TskState) event) ** mutex_post_event_frame sg state eid).
Proof.
  intros sg state eid event He; rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid event He).
  unfold used_event_rep, mutex_post_event_frame; entailer!.
Qed.

Lemma mutex_post_owner_event_merge_inv : forall sg state eid event mutex owner snapshot,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_post_owner_result state.(TskState) event owner snapshot ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) (mutex_post_owner_event event mutex owner snapshot)) **
  mutex_post_event_frame sg state eid |--
  UCOS2_inv sg (mutex_post_owner_state state eid event mutex owner snapshot).
Proof.
  intros sg state eid event mutex owner snapshot Hvalid He Htype Hm Hslot Hresult.
  unfold mutex_post_event_frame; fold (used_event_rep sg state.(TskState) eid
    (mutex_post_owner_event event mutex owner snapshot)).
  pose proof (mutex_post_owner_state_preserves_validity sg state eid event mutex owner snapshot
    Hvalid He Htype Hm Hslot Hresult) as Hafter.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_event sg state eid event
    (mutex_post_owner_event event mutex owner snapshot) Hafter He eq_refl eq_refl).
  entailer!.
Qed.

Definition mutex_post_prepare (sg : StableGlobVars) (mutex : MutexFields) (owner : TaskID)
  (entry after : UCOS2_Verify_State) : Prop :=
  if Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis) then after = entry
  else exists node priority,
    entry.(TskState).(inUsedTaskStates) owner = Some node /\
    mutex_effective_priority_result
      (mutex_del_priority_values sg (mutex_post_reserved_table entry mutex.(mfPCP)))
      (task_slot_addr sg owner) node.(curPrio) priority /\
    after = mutex_post_owner_priority_state sg entry mutex.(mfPCP) owner node priority.

Lemma mutex_post_prepare_event_state_eq : forall sg mutex owner entry after,
  mutex_post_prepare sg mutex owner entry after -> after.(EventState) = entry.(EventState).
Proof.
  intros sg mutex owner entry after Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; reflexivity|].
  destruct Hprepare as [node [priority [_ [_ ->]]]]; apply mutex_post_owner_priority_event_state_eq.
Qed.

Lemma mutex_post_prepare_properties : forall sg entry eid event mutex owner after,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> task_slot_addr sg owner <> 1 ->
  mutex_post_prepare sg mutex owner entry after ->
  UCOS2_state_inv sg after /\ after.(EventState) = entry.(EventState) /\
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ after.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved).
Proof.
  intros sg entry eid event mutex owner after Hvalid Huse He Htype Hm Ho Hone Hprepare.
  pose proof (mutex_post_prepare_event_state_eq sg mutex owner entry after Hprepare) as Hevents.
  unfold mutex_post_prepare in Hprepare; destruct Z.eq_dec as [Hdisabled|Henabled].
  - subst after; auto.
  - destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
    split.
    + eapply mutex_post_owner_scan_preserves_validity; eassumption.
    + split; [exact Hevents|]. right; rewrite mutex_post_owner_priority_table_eq.
      apply update_prio_tbl_same.
Qed.

Lemma mutex_post_prepare_preserves_owner_use : forall sg mutex owner entry after,
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  mutex_post_prepare sg mutex owner entry after ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg mutex owner entry after Huse Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; exact Huse|].
  destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
  unfold mutex_post_owner_priority_state; destruct Z.eq_dec; [exact Huse|].
  change (mutex_owner_event_unlinked
    (glob_task_set_usedtask (mutex_del_ceiling_view_tasks entry.(TskState) mutex.(mfPCP)) owner
      (mutex_priority_task node priority)) entry.(EventState)).
  eapply mutex_owner_event_unlinked_task_fields_frame;
    [exact Hnode|reflexivity|reflexivity|exact Huse].
Qed.

Lemma mutex_post_wake_commit_preserves_validity : forall sg state eid event mutex priority woken found owner,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendOK = Some (priority, woken) ->
  woken.(EventState).(inUsedEventStates) eid = Some found ->
  woken.(TskState).(prioTbl) priority = PTTask owner ->
  UCOS2_state_inv sg (mutex_post_owner_state woken eid found mutex (Some owner) (Some priority)).
Proof.
  intros sg state eid event mutex priority woken found owner Hvalid He Htype Hm Hslot Hnonzero Hstep Hfound Htable.
  destruct (event_wake_decompose sg state eid event PendMutex 0 PendOK priority woken
    Hvalid He ltac:(rewrite Htype; reflexivity) Hnonzero Hstep)
    as [tid [tail [old [Hlist [Hold [Hp [Ew [Hw Hlookup]]]]]]]].
  rewrite Hlookup in Hfound; injection Hfound as E; subst found.
  assert (Hselection : state.(TskState).(prioTbl) old.(curPrio) = PTTask tid).
  { pose proof Hvalid as [Hprofile [Htasks [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
    destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail
      (proj1 Hprofile) Htasks (Hentries eid event He) Hlist) as [node [Hnode [Hprio Hsel]]].
    rewrite Hold in Hnode; injection Hnode as E; subst node; congruence. }
  assert (Eowner : owner = tid).
  { rewrite Ew, Hp in Htable; change (state.(TskState).(prioTbl) old.(curPrio) = PTTask owner) in Htable.
    rewrite Hselection in Htable; congruence. }
  subst owner; eapply mutex_post_owner_state_preserves_validity;
    [exact Hw|exact Hlookup|exact Htype|exact Hm| |].
  - rewrite Ew; exact Hslot.
  - exists (task_event_wake_single old PendMutex 0 PendOK); split.
    + rewrite Ew; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
        glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    + split; [exact Hp|].
      pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
      pose proof (proj1 (Hentries eid event He)) as [Hnodup _].
      rewrite Hlist in Hnodup; inversion Hnodup; assumption.
Qed.

Definition mutex_post_handover_error (sg : StableGlobVars) (mutex : MutexFields) (priority : Z) : OSErrCode :=
  if Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis) then OS_ERR_NONE
  else if Z_le_dec priority mutex.(mfPCP) then OS_ERR_PCP_LOWER else OS_ERR_NONE.

(** Protected source stages only. [caller] must be bound to the actual
    OSTCBCur read by the same invocation; this relation does not supply that
    execution/heap producer. Each constructor retains the literal branch
    and records whether the source invokes OS_Sched after Restore. *)
Inductive mutex_post_critical (sg : StableGlobVars) (eid : EventID) (caller : TaskID)
  : UCOS2_Verify_State -> OSErrCode -> bool -> UCOS2_Verify_State -> Prop :=
| mutex_post_not_owner : forall entry event mutex,
    entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) <> Some caller ->
    mutex_post_critical sg eid caller entry OS_ERR_NOT_MUTEX_OWNER false entry
| mutex_post_empty : forall entry event mutex prepared,
    entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some caller -> mutex_post_prepare sg mutex caller entry prepared ->
    encode_event_wait_grp event.(waitList) prepared.(TskState) = 0 ->
    mutex_post_critical sg eid caller entry OS_ERR_NONE false
      (mutex_post_owner_state prepared eid event mutex None None)
| mutex_post_handover : forall entry event mutex prepared priority woken found owner,
    entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some caller -> mutex_post_prepare sg mutex caller entry prepared ->
    encode_event_wait_grp event.(waitList) prepared.(TskState) <> 0 ->
    event_task_rdy sg prepared eid PendMutex 0 PendOK = Some (priority, woken) ->
    woken.(EventState).(inUsedEventStates) eid = Some found ->
    woken.(TskState).(prioTbl) priority = PTTask owner ->
    mutex_post_critical sg eid caller entry (mutex_post_handover_error sg mutex priority) true
      (mutex_post_owner_state woken eid found mutex (Some owner) (Some priority)).

Lemma mutex_post_critical_preserves_validity : forall sg eid caller entry result schedule after,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  task_slot_addr sg caller <> 1 ->
  mutex_post_critical sg eid caller entry result schedule after -> UCOS2_state_inv sg after.
Proof.
  intros sg eid caller entry result schedule after Hvalid Huse Hpointer Hsource; destruct Hsource.
  - exact Hvalid.
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    assert (He : prepared.(EventState).(inUsedEventStates) eid = Some event) by (rewrite Hevents; exact H).
    eapply mutex_post_owner_state_preserves_validity;
      [exact Hprepared|exact He|exact H0|exact H1|exact Hslot|].
    exact (mutex_del_event_group_zero_implies_empty sg prepared eid event Hprepared He H4).
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    eapply mutex_post_wake_commit_preserves_validity; try eassumption.
    rewrite Hevents; exact H.
Qed.

Lemma mutex_post_priority_input_not_reserved : forall sg entry ceiling owner node,
  selected_kernel_profile sg ->
  tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner ->
  mutex_post_priority_input sg entry ceiling owner node |--
  coq_prop (task_slot_addr sg owner <> 1) && mutex_post_priority_input sg entry ceiling owner node.
Proof.
  intros sg entry ceiling owner node Hprofile Haddress.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold mutex_post_priority_input.
  pose proof (used_task_rep_tcb64 sg owner node Hmulti Hprofiling) as Htcb.
  rewrite <- task_slot_addr_tcb64 in Htcb by assumption; rewrite <- Htcb.
  eapply derivable1_trans.
  - do 5 (eapply derivable1_sepcon_mono; [|reflexivity]).
    exact (mutex_del_task_storage_pointer_not_reserved sg owner node Haddress).
  - Intros; entailer!.
Qed.

Lemma mutex_post_owner_priority_skip_merge : forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_post_reserved_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority -> node.(curPrio) = priority ->
  mutex_post_priority_input sg entry mutex.(mfPCP) owner node ** mutex_del_priority_frame sg entry owner |--
  UCOS2_inv sg (mutex_post_owner_priority_state sg entry mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority Hvalid Huse He Htype Hm Ho
    Henabled Hnode Hone Hscan Hequal.
  pose proof (mutex_post_owner_scan_preserves_validity sg entry eid event mutex owner node priority
    Hvalid He Htype Hm Ho Henabled Hnode Hone Hscan Huse) as Hafter.
  sep_apply_l_atomic (mutex_post_priority_input_merge_reserved sg entry mutex.(mfPCP) owner node (proj1 Hvalid) Hnode).
  rewrite mutex_post_reserved_resources_raw_equiv.
  unfold UCOS2_inv, mutex_post_owner_priority_state in *.
  destruct Z.eq_dec; [entailer!|contradiction].
Qed.

Lemma mutex_post_owner_priority_update_merge : forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_post_reserved_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority -> node.(curPrio) <> priority ->
  mutex_post_priority_output sg entry mutex.(mfPCP) owner node priority ** mutex_del_priority_frame sg entry owner |--
  UCOS2_inv sg (mutex_post_owner_priority_state sg entry mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority Hvalid Huse He Htype Hm Ho
    Henabled Hnode Hone Hscan Hdifferent.
  pose proof (mutex_post_owner_scan_preserves_validity sg entry eid event mutex owner node priority
    Hvalid He Htype Hm Ho Henabled Hnode Hone Hscan Huse) as Hafter.
  pose proof (mutex_del_owner_use_implies_not_waiter sg entry eid event mutex owner
    Hvalid Huse He Htype Hm Ho) as Habsent.
  destruct (mutex_post_owner_scan_properties sg entry eid event mutex owner node priority
    Hvalid He Htype Hm Ho Henabled Hnode Hone Hscan)
    as [base [Hbase [Heffective [Hbounds [Hrange [Hne Halias]]]]]].
  assert (Hprio : 0 <= priority < 64).
  { assert (Hlowest : sg.(osLowestPrio) = 63)
      by (pose proof (proj1 Hvalid) as Hprofile;
        unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
    unfold task_priority_in_range in Hrange; lia. }
  assert (Htable : mutex_post_reserved_table entry mutex.(mfPCP) priority = PTTask owner).
  { unfold mutex_post_reserved_table; rewrite update_prio_tbl_other by exact Hne; exact Halias. }
  sep_apply_l_atomic (mutex_post_priority_output_merge_raw sg entry mutex.(mfPCP) owner node priority
    Hvalid Hnode Hprio Htable Habsent).
  unfold UCOS2_inv, mutex_post_owner_priority_state in *.
  destruct Z.eq_dec; [contradiction|entailer!].
Qed.

Lemma mutex_post_current_owner_comparison : forall sg state eid event mutex caller node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) caller = Some node ->
  state.(SchedState).(curTaskID) = Some caller ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (encode_task_link sg state.(SchedState).(curTaskID) = encode_event_ptr_value sg event <->
   mutex.(mfOwner) = Some caller).
Proof.
  intros sg state eid event mutex caller node Hvalid Hnode Hcurrent He Htype Hm.
  pose proof (mutex_del_live_task_pointer_nonzero sg state caller node Hvalid Hnode) as Hnonzero.
  unfold encode_event_ptr_value; rewrite Htype, Hm, Hcurrent.
  destruct mutex.(mfOwner) as [owner|]; cbn [encode_task_link].
  - split.
    + intro E; apply task_slot_addr_injective in E; congruence.
    + intro E; injection E as E; subst owner; reflexivity.
  - split; [intro E; contradiction|discriminate].
Qed.

Lemma mutex_post_before_save_wrong_type : forall pevent observed_type observed_nesting,
  observed_nesting <= 0 -> pevent <> 0 -> observed_type <> 4 ->
  mutex_post_before_save_error pevent observed_type observed_nesting = Some OS_ERR_EVENT_TYPE.
Proof.
  intros; unfold mutex_post_before_save_error; destruct Z_lt_dec; [lia|].
  destruct Z.eq_dec; [contradiction|]. destruct Z.eq_dec; [contradiction|reflexivity].
Qed.

Lemma mutex_post_release_preserves_owner_use : forall state eid event mutex,
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  mutex_owner_event_unlinked
    (mutex_post_owner_state state eid event mutex None None).(TskState)
    (mutex_post_owner_state state eid event mutex None None).(EventState).
Proof.
  intros state eid event mutex Huse mid found held owner node Hfound Htype Hm Ho Hnode.
  destruct (mutex_post_owner_event_lookup state eid event mutex None None mid found Hfound)
    as [[-> ->]|[Hne Hbefore]].
  - cbn [mutex_post_owner_event mutexFields] in Hm; injection Hm as E; subst held; discriminate.
  - eapply Huse; eassumption.
Qed.

Lemma mutex_post_wake_commit_preserves_owner_use : forall sg state eid event mutex priority woken found owner,
  UCOS2_state_inv sg state -> mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  state.(EventState).(inUsedEventStates) eid = Some event -> event.(eventType) = OS_EVENT_TYPE_MUTEX ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendOK = Some (priority, woken) ->
  woken.(EventState).(inUsedEventStates) eid = Some found ->
  woken.(TskState).(prioTbl) priority = PTTask owner ->
  let after := mutex_post_owner_state woken eid found mutex (Some owner) (Some priority) in
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg state eid event mutex priority woken found owner Hvalid Huse He Htype Hnonzero Hstep Hfound Htable after.
  destruct (event_wake_decompose sg state eid event PendMutex 0 PendOK priority woken
    Hvalid He ltac:(rewrite Htype; reflexivity) Hnonzero Hstep)
    as [tid [tail [old [Hlist [Hold [Hp [Ew [Hw Hlookup]]]]]]]].
  pose proof Hvalid as [Hprofile [Htasks [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
  destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail
    (proj1 Hprofile) Htasks (Hentries eid event He) Hlist) as [node [Hnode [Hprio Hsel]]].
  rewrite Hold in Hnode; injection Hnode as E; subst node.
  assert (Eowner : owner = tid).
  { rewrite Ew, Hp in Htable; change (state.(TskState).(prioTbl) old.(curPrio) = PTTask owner) in Htable.
    congruence. }
  subst owner.
  assert (Hmulti : old.(eventMultiWaitEvents) = []).
  { pose proof (Hentries eid event He) as [_ Hphases]; rewrite Htype in Hphases.
    destruct (Hphases tid ltac:(rewrite Hlist; simpl; auto)) as [node [Hnode [_ [Hmulti Hphase]]]].
    rewrite Hold in Hnode; injection Hnode as E; subst node; exact Hmulti. }
  change (mutex_owner_event_unlinked woken.(TskState)
    (owner_acquire_update woken.(EventState) eid found mutex tid priority)).
  eapply owner_acquire_update_preserves_event_unlinked with (node := task_event_wake_single old PendMutex 0 PendOK).
  - rewrite Ew; apply event_wake_preserves_mutex_owner_event_unlinked; assumption.
  - rewrite Ew; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - reflexivity.
  - exact Hmulti.
Qed.

Lemma mutex_post_critical_preserves_owner_use : forall sg eid caller entry result schedule after,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  task_slot_addr sg caller <> 1 -> mutex_post_critical sg eid caller entry result schedule after ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg eid caller entry result schedule after Hvalid Huse Hpointer Hsource; destruct Hsource.
  - exact Huse.
  - apply mutex_post_release_preserves_owner_use.
    eapply mutex_post_prepare_preserves_owner_use; eassumption.
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    eapply mutex_post_wake_commit_preserves_owner_use; try eassumption.
    + eapply mutex_post_prepare_preserves_owner_use; eassumption.
    + rewrite Hevents; exact H.
Qed.

(** Consume the existing client-use protocol along the SAME registered
    interval. Neither this pure consumer nor [critical_region_interval]
    supplies the missing unmasked C observation loan or CPU caller binding. *)
Lemma mutex_post_critical_interval_preserves_validity :
  forall critical sg invocation before entry eid caller result schedule after,
  (forall action initial final,
    critical_region_clients critical action -> UCOS2_state_inv sg initial ->
    mutex_owner_event_unlinked initial.(TskState) initial.(EventState) ->
    kernel_client_step action sg initial final ->
    mutex_owner_event_unlinked final.(TskState) final.(EventState)) ->
  critical_region_interval critical sg invocation before entry ->
  UCOS2_state_inv sg before -> mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  task_slot_addr sg caller <> 1 -> mutex_post_critical sg eid caller entry result schedule after ->
  UCOS2_state_inv sg after /\ mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros critical sg invocation before entry eid caller result schedule after
    Hclients Hinterval Hvalid Huse Hpointer Hsource.
  pose proof (proj1 (critical_region_interval_transports_resources critical sg invocation before entry Hinterval Hvalid))
    as Hentry.
  pose proof (critical_region_interval_preserves_mutex_owner_event_unlinked critical sg invocation before entry
    Hclients Hinterval Hvalid Huse) as Hentryuse.
  split.
  - exact (mutex_post_critical_preserves_validity sg eid caller entry result schedule after
      Hentry Hentryuse Hpointer Hsource).
  - exact (mutex_post_critical_preserves_owner_use sg eid caller entry result schedule after
      Hentry Hentryuse Hpointer Hsource).
Qed.

(** Protected count/owner stores temporarily break the abstract Event image.
    Keep the ACTUAL image and priority table separately owned until all stores
    finish. This frame is for the masked source segment, not an unmasked loan
    and not a full invariant for the intermediate count-only image. *)
Definition mutex_post_event_table_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  task_public_storage_without_prio_tbl sg state.(TskState) **
  sched_raw_rep sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state.

Definition mutex_post_commit_rep (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (image : EventStorage) : Assertion :=
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) image **
  (store_prio_tbl sg state.(TskState).(prioTbl) ** mutex_post_event_table_frame sg state eid).

Lemma mutex_post_event_table_frame_merge : forall sg state eid,
  store_prio_tbl sg state.(TskState).(prioTbl) ** mutex_post_event_table_frame sg state eid
    --||-- mutex_post_event_frame sg state eid.
Proof.
  intros; unfold mutex_post_event_table_frame, mutex_post_event_frame,
    UCOS2_raw_rep_missing_event_queue, UCOS2_raw_rep_missing_two,
    UCOS2_raw_rep_missing_task_storage_sched_event.
  unfold UCOS2_selected_rep.
  cbn [UCOS2_module_rep UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect].
  unfold task_shared_rep.
  rewrite task_public_storage_prio_tbl_equiv; split; entailer!.
Qed.

Lemma mutex_post_commit_rep_split : forall sg state eid event,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    mutex_post_commit_rep sg state eid (event_image sg state.(TskState) event).
Proof.
  intros sg state eid event He.
  sep_apply_l_atomic (mutex_post_event_split sg state eid event He); Intros.
  unfold mutex_post_commit_rep; rewrite mutex_post_event_table_frame_merge; entailer!.
Qed.

Definition mutex_post_commit_field_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (image : EventStorage)
  (field : EventField) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) image field **
  store_prio_tbl sg state.(TskState).(prioTbl) ** mutex_post_event_table_frame sg state eid.

Lemma mutex_post_commit_field_split : forall sg state eid image field,
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  mutex_post_commit_rep sg state eid image |--
    event_cell (event_addr sg eid) field (image field) **
    mutex_post_commit_field_frame sg state eid image field.
Proof.
  intros; unfold mutex_post_commit_rep, mutex_post_commit_field_frame.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) image field H); entailer!.
Qed.

Lemma mutex_post_commit_field_merge : forall sg state eid image field,
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_cell (event_addr sg eid) field (image field) **
    mutex_post_commit_field_frame sg state eid image field |--
  mutex_post_commit_rep sg state eid image.
Proof.
  intros; unfold mutex_post_commit_rep, mutex_post_commit_field_frame.
  sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) image field H); entailer!.
Qed.

Lemma mutex_post_commit_field_merge_updated : forall sg state eid image field value,
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_cell (event_addr sg eid) field value **
    mutex_post_commit_field_frame sg state eid image field |--
  mutex_post_commit_rep sg state eid (event_write image field value).
Proof.
  intros; unfold mutex_post_commit_rep, mutex_post_commit_field_frame.
  sep_apply_l_atomic (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) image field value H); entailer!.
Qed.

Definition mutex_post_commit_priority_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (image : EventStorage)
  (priority : Priority) : Assertion :=
  store_prio_tbl_missing_i sg state.(TskState).(prioTbl) priority **
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) image **
  mutex_post_event_table_frame sg state eid.

Lemma mutex_post_commit_priority_split : forall sg state eid image priority,
  0 <= priority < 64 ->
  mutex_post_commit_rep sg state eid image |--
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) priority) **
  mutex_post_commit_priority_frame sg state eid image priority.
Proof.
  intros; unfold mutex_post_commit_rep, mutex_post_commit_priority_frame.
  sep_apply_l_atomic (store_prio_tbl_split_cell sg state.(TskState).(prioTbl) priority H); entailer!.
Qed.

Lemma mutex_post_commit_priority_merge : forall sg state eid image priority,
  0 <= priority < 64 ->
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) priority) **
  mutex_post_commit_priority_frame sg state eid image priority |--
  mutex_post_commit_rep sg state eid image.
Proof.
  intros; unfold mutex_post_commit_rep, mutex_post_commit_priority_frame.
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg state.(TskState).(prioTbl) priority H); entailer!.
Qed.

Lemma mutex_post_commit_owner_read : forall sg state eid image priority owner,
  0 <= priority < 64 -> state.(TskState).(prioTbl) priority = PTTask owner ->
  mutex_post_commit_rep sg state eid image |--
    (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> task_slot_addr sg owner **
    mutex_post_commit_priority_frame sg state eid image priority.
Proof.
  intros sg state eid image priority owner Hrange Howner.
  pose proof (mutex_post_commit_priority_split sg state eid image priority Hrange) as Hsplit.
  rewrite Howner in Hsplit; exact Hsplit.
Qed.

Lemma mutex_post_commit_owner_merge_inv : forall sg state eid event mutex owner snapshot,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  mutex_post_owner_result state.(TskState) event owner snapshot ->
  mutex_post_commit_rep sg state eid
    (event_image sg state.(TskState) (mutex_post_owner_event event mutex owner snapshot)) |--
  UCOS2_inv sg (mutex_post_owner_state state eid event mutex owner snapshot).
Proof.
  intros; unfold mutex_post_commit_rep; rewrite mutex_post_event_table_frame_merge.
  eapply mutex_post_owner_event_merge_inv; eassumption.
Qed.

Definition mutex_post_comparison_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (image : EventStorage) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) image EventPtrField **
  store_prio_tbl sg state.(TskState).(prioTbl) **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  task_public_storage_without_prio_tbl sg state.(TskState) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
  sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if state.(SchedState).(isRunning) then 1 else 0) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state.

Lemma mutex_post_comparison_split : forall sg state eid image pointer,
  image EventPtrField = Some pointer ->
  mutex_post_commit_rep sg state eid image |--
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) **
  (event_addr sg eid + 4) # Ptr |-> pointer **
  mutex_post_comparison_frame sg state eid image.
Proof.
  intros sg state eid image pointer Hptr.
  unfold mutex_post_commit_rep, mutex_post_event_table_frame,
    mutex_post_comparison_frame, sched_raw_rep, sched_physical_rep.
  pose proof (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) image EventPtrField ltac:(unfold event_fields; simpl; tauto)) as Hsplit.
  rewrite Hptr in Hsplit; cbn [event_cell event_field_offset] in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma mutex_post_comparison_merge : forall sg state eid image pointer,
  image EventPtrField = Some pointer ->
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) **
  (event_addr sg eid + 4) # Ptr |-> pointer **
  mutex_post_comparison_frame sg state eid image |--
  mutex_post_commit_rep sg state eid image.
Proof.
  intros sg state eid image pointer Hptr.
  eapply derivable1_trans; [|apply (mutex_post_commit_field_merge sg state eid image EventPtrField
    ltac:(unfold event_fields; simpl; tauto))].
  unfold mutex_post_commit_field_frame, mutex_post_event_table_frame,
    mutex_post_comparison_frame, sched_raw_rep, sched_physical_rep.
  rewrite Hptr; cbn [event_cell event_field_offset]; entailer!.
Qed.

Definition mutex_post_snapshot_byte (mutex : MutexFields) : Z :=
  match mutex.(mfOwnerOrigPrio) with Some snapshot => snapshot | None => 255 end.

Lemma mutex_post_count_fields : forall sg state eid event mutex,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  0 <= mutex.(mfPCP) <= 255 /\ 0 <= mutex_post_snapshot_byte mutex <= 255 /\
  encode_event_cnt_value event = mutex.(mfPCP) * 256 + mutex_post_snapshot_byte mutex.
Proof.
  intros sg state eid event mutex Hvalid He Htype Hmutex.
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hlowest : sg.(osLowestPrio) = 63) by
    (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255) by
    (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hprotocol : mutex_protocol_consistency sg state).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, cross_module_consistency in Hvalid; tauto. }
  destruct (Hprotocol eid event mutex He Htype Hmutex) as [Hpcp [Hfields Hslot]].
  assert (Hpcprange : 0 <= mutex.(mfPCP) <= 255).
  { unfold valid_mutex_pcp in Hpcp; rewrite Hlowest, Hdisabled in Hpcp; lia. }
  split; [exact Hpcprange|].
  unfold mutex_post_snapshot_byte, encode_event_cnt_value; rewrite Htype, Hmutex.
  destruct mutex.(mfOwner), mutex.(mfOwnerOrigPrio); try contradiction.
  - destruct Hfields as [[Hlo Hhi] Hne]; rewrite Hlowest in Hhi; split; [lia|reflexivity].
  - split; [lia|reflexivity].
Qed.

Lemma mutex_post_count_decode : forall ceiling snapshot,
  0 <= ceiling <= 255 -> 0 <= snapshot <= 255 ->
  unsigned_last_nbits (Z.shiftr (ceiling * 256 + snapshot) 8) 8 = ceiling /\
  unsigned_last_nbits (Z.land (ceiling * 256 + snapshot) 255) 8 = snapshot.
Proof.
  intros ceiling snapshot Hceiling Hsnapshot.
  assert (Hcast : forall value, 0 <= value <= 255 -> unsigned_last_nbits value 8 = value).
  { intros value Hrange; unfold unsigned_last_nbits.
    change (value mod 256 = value); apply Z.mod_small; lia. }
  split.
  - rewrite Z.shiftr_div_pow2 by lia; replace (2 ^ 8) with 256 by reflexivity.
    rewrite Z.add_comm, Z.div_add by lia.
    rewrite (Z.div_small snapshot 256) by lia; cbn; apply Hcast; exact Hceiling.
  - replace 255 with (Z.ones 8) at 1 by reflexivity.
    rewrite Z.land_ones by lia; replace (2 ^ 8) with 256 by reflexivity.
    rewrite Z.add_comm, Z.mod_add by lia.
    rewrite (Z.mod_small snapshot 256) by lia; apply Hcast; exact Hsnapshot.
Qed.

Lemma mutex_post_source_count_decode : forall sg state eid event mutex,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  unsigned_last_nbits (Z.shiftr (encode_event_cnt_value event) 8) 8 = mutex.(mfPCP) /\
  unsigned_last_nbits (Z.land (encode_event_cnt_value event) 255) 8 = mutex_post_snapshot_byte mutex.
Proof.
  intros sg state eid event mutex Hvalid He Htype Hmutex.
  destruct (mutex_post_count_fields sg state eid event mutex Hvalid He Htype Hmutex)
    as [Hceiling [Hsnapshot Hcount]].
  rewrite Hcount; apply mutex_post_count_decode; assumption.
Qed.

(** Physical effect of one native 16-bit count store. Its two little-endian
    bytes are one typed source operation, not two interruptible C stores.
    This case-local producer is derived from the shared byte-store rules. *)
Definition mutex_post_count_store_bytes (stored : Z) : list Z :=
  [stored mod 256; (stored / 256) mod 256].

Definition mutex_post_count_store_writes (address stored : Z) : list (Mem.addr * Mem.byte) :=
  KernelHeapStorage.byte_list_writes address (mutex_post_count_store_bytes stored).

Lemma mutex_post_count_store_execution : forall address stored before,
  0 <= stored < 65536 -> (address # UShort |->_) before ->
  exists after,
    kernel_heap_execution (mutex_post_count_store_writes address stored) before after /\
    (address # UShort |-> stored) after.
Proof.
  intros address stored before Hrange [Haddress Hbefore].
  change (store_2byte_noninit address before) in Hbefore.
  assert (Hsplit : store_2byte_noninit address |-- store_bytes_noninit address 2 ** emp).
  { unfold store_2byte_noninit; cbn [store_bytes_noninit]; entailer!. }
  assert (Hbytes : Forall (fun byte => 0 <= byte < 256) (mutex_post_count_store_bytes stored)).
  { unfold mutex_post_count_store_bytes; repeat constructor; apply Z.mod_pos_bound; lia. }
  destruct (KernelHeapStorage.byte_list_store_execution (mutex_post_count_store_bytes stored)
    address emp before Hbytes (Hsplit _ Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  split; [split; [exact Haddress|]; change (stored >= 0 /\ stored <= 65535); lia|].
  change (store_2byte address stored after).
  exists (stored mod 256), ((stored / 256) mod 256); split.
  - change (stored mod 65536 = (stored mod 256) mod 256 + ((stored / 256) mod 256) mod 256 * 256).
    rewrite !Z.mod_mod by lia.
    rewrite (Z.mod_small stored 65536 Hrange).
    assert (Hhigh : 0 <= stored / 256 < 256).
    { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
    rewrite (Z.mod_small (stored / 256) 256 Hhigh).
    pose proof (Z.div_mod stored 256 ltac:(lia)); lia.
  - assert (Hmerge : KernelHeapStorage.byte_list_rep address (mutex_post_count_store_bytes stored) ** emp |--
      store_byte address (stored mod 256) ** store_byte (address + 1) ((stored / 256) mod 256)).
    { unfold mutex_post_count_store_bytes; cbn [KernelHeapStorage.byte_list_rep]; entailer!. }
    exact (Hmerge _ Hafter).
Qed.

Lemma mutex_post_framed_count_store_execution : forall address stored (frame : Assertion) before,
  0 <= stored < 65536 -> (address # UShort |->_ ** frame) before ->
  exists after,
    kernel_heap_execution (mutex_post_count_store_writes address stored) before after /\
    (address # UShort |-> stored ** frame) after.
Proof.
  intros address stored frame before Hrange [cell [rest [Hjoin [Hcell Hrest]]]].
  destruct (mutex_post_count_store_execution address stored cell Hrange Hcell) as [final [Hrun Hfinal]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [whole [Hwhole Hwholejoin]].
  exists whole; split; [exact Hwhole|].
  exists final, rest; split; [exact Hwholejoin|]; split; assumption.
Qed.

Lemma mutex_post_commit_count_store : forall sg state eid image old stored (private : Assertion) before,
  image EventCntField = Some old -> 0 <= stored < 65536 ->
  (mutex_post_commit_rep sg state eid image ** private) before ->
  exists after,
    kernel_heap_execution (mutex_post_count_store_writes (event_addr sg eid + 8) stored) before after /\
    (mutex_post_commit_rep sg state eid (event_write image EventCntField (Some stored)) ** private) after.
Proof.
  intros sg state eid image old stored private before Hcount Hrange Hbefore.
  assert (Hsplit : mutex_post_commit_rep sg state eid image ** private |--
    (event_addr sg eid + 8) # UShort |->_ **
    (mutex_post_commit_field_frame sg state eid image EventCntField ** private)).
  { sep_apply_l_atomic (mutex_post_commit_field_split sg state eid image EventCntField
      ltac:(unfold event_fields; simpl; tauto)).
    rewrite Hcount; cbn [event_cell event_field_offset].
    sep_apply_l_atomic (store_ushort_undef_store_ushort (event_addr sg eid + 8) old); entailer!. }
  destruct (mutex_post_framed_count_store_execution (event_addr sg eid + 8) stored
    (mutex_post_commit_field_frame sg state eid image EventCntField ** private) before Hrange (Hsplit _ Hbefore))
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : (event_addr sg eid + 8) # UShort |-> stored **
    (mutex_post_commit_field_frame sg state eid image EventCntField ** private) |--
    mutex_post_commit_rep sg state eid (event_write image EventCntField (Some stored)) ** private).
  { pose proof (mutex_post_commit_field_merge_updated sg state eid image EventCntField (Some stored)
      ltac:(unfold event_fields; simpl; tauto)) as Hfield.
    cbn [event_cell event_field_offset] in Hfield; sep_apply_l_atomic Hfield; entailer!. }
  exact (Hmerge _ Hafter).
Qed.

Lemma mutex_post_commit_pointer_store : forall sg state eid image old stored (private : Assertion) before,
  image EventPtrField = Some old -> 0 <= stored < 4294967296 ->
  (mutex_post_commit_rep sg state eid image ** private) before ->
  exists after,
    kernel_heap_execution (KernelHeapStorage.pointer_store_writes (event_addr sg eid + 4) stored) before after /\
    (mutex_post_commit_rep sg state eid (event_write image EventPtrField (Some stored)) ** private) after.
Proof.
  intros sg state eid image old stored private before Hptr Hrange Hbefore.
  assert (Hsplit : mutex_post_commit_rep sg state eid image ** private |--
    (event_addr sg eid + 4) # Ptr |->_ **
    (mutex_post_commit_field_frame sg state eid image EventPtrField ** private)).
  { sep_apply_l_atomic (mutex_post_commit_field_split sg state eid image EventPtrField
      ltac:(unfold event_fields; simpl; tauto)).
    rewrite Hptr; cbn [event_cell event_field_offset].
    sep_apply_l_atomic (store_ptr_undef_store_ptr (event_addr sg eid + 4) old); entailer!. }
  destruct (KernelHeapStorage.framed_pointer_store_execution (event_addr sg eid + 4) stored
    (mutex_post_commit_field_frame sg state eid image EventPtrField ** private) before Hrange (Hsplit _ Hbefore))
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : (event_addr sg eid + 4) # Ptr |-> stored **
    (mutex_post_commit_field_frame sg state eid image EventPtrField ** private) |--
    mutex_post_commit_rep sg state eid (event_write image EventPtrField (Some stored)) ** private).
  { pose proof (mutex_post_commit_field_merge_updated sg state eid image EventPtrField (Some stored)
      ltac:(unfold event_fields; simpl; tauto)) as Hfield.
    cbn [event_cell event_field_offset] in Hfield; sep_apply_l_atomic Hfield; entailer!. }
  exact (Hmerge _ Hafter).
Qed.

Lemma mutex_post_commit_owner_observation : forall sg state eid image priority owner (private : Assertion) heap,
  0 <= priority < 64 -> state.(TskState).(prioTbl) priority = PTTask owner ->
  (mutex_post_commit_rep sg state eid image ** private) heap ->
  KernelHeapObservation.pointer_load
    (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) (task_slot_addr sg owner) heap.
Proof.
  intros sg state eid image priority owner private heap Hrange Howner Hheap.
  assert (Hsplit : mutex_post_commit_rep sg state eid image ** private |--
    (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> task_slot_addr sg owner **
    (mutex_post_commit_priority_frame sg state eid image priority ** private)).
  { sep_apply_l_atomic (mutex_post_commit_owner_read sg state eid image priority owner Hrange Howner); entailer!. }
  eapply KernelHeapObservation.framed_pointer_store_load; exact (Hsplit _ Hheap).
Qed.

Lemma mutex_post_empty_image_decoded_eq : forall sg tasks event mutex snapshot,
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  encode_event_cnt_value event = mutex.(mfPCP) * 256 + snapshot ->
  0 <= mutex.(mfPCP) <= 255 -> 0 <= snapshot <= 255 ->
  mutex_post_empty_image (event_image sg tasks event) =
    event_image sg tasks (mutex_post_owner_event event mutex None None).
Proof.
  intros sg tasks event mutex snapshot Htype Hmutex Hcount Hpcp Hsnapshot.
  apply functional_extensionality; intros field; destruct field;
    unfold mutex_post_empty_image, event_write, field_update, event_image, mutex_post_owner_event;
    simpl; try reflexivity.
  - unfold encode_event_ptr_value; simpl; rewrite Htype; reflexivity.
  - rewrite Hcount; unfold encode_event_cnt_value; simpl; rewrite Htype.
    f_equal; apply mutex_post_available_count; assumption.
Qed.

Lemma mutex_post_handover_image_decoded_eq : forall sg tasks event mutex snapshot owner priority,
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  encode_event_cnt_value event = mutex.(mfPCP) * 256 + snapshot ->
  0 <= mutex.(mfPCP) <= 255 -> 0 <= snapshot <= 255 -> 0 <= priority <= 255 ->
  mutex_post_handover_image (event_image sg tasks event) priority (task_slot_addr sg owner) =
    event_image sg tasks (mutex_post_owner_event event mutex (Some owner) (Some priority)).
Proof.
  intros sg tasks event mutex snapshot owner priority Htype Hmutex Hcount Hpcp Hsnapshot Hpriority.
  apply functional_extensionality; intros field; destruct field;
    unfold mutex_post_handover_image, event_write, field_update, event_image, mutex_post_owner_event;
    simpl; try reflexivity.
  - unfold encode_event_ptr_value; simpl; rewrite Htype; reflexivity.
  - rewrite Hcount; unfold encode_event_cnt_value; simpl; rewrite Htype.
    f_equal; apply mutex_post_replace_low_byte; assumption.
Qed.

Definition mutex_post_empty_store_writes (sg : StableGlobVars) (eid : EventID) (count : Z)
  : list (Mem.addr * Mem.byte) :=
  mutex_post_count_store_writes (event_addr sg eid + 8)
    (Z.lor (unsigned_last_nbits count 16) 255) ++
  KernelHeapStorage.pointer_store_writes (event_addr sg eid + 4) 0.

Lemma mutex_post_empty_store_execution : forall sg state eid event mutex (private : Assertion) before,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  (UCOS2_inv sg state ** private) before ->
  exists after,
    kernel_heap_execution (mutex_post_empty_store_writes sg eid (encode_event_cnt_value event)) before after /\
    (UCOS2_inv sg (mutex_post_owner_state state eid event mutex None None) ** private) after.
Proof.
  intros sg state eid event mutex private before Hvalid He Htype Hmutex Hslot Hgroup Hbefore.
  destruct (mutex_post_count_fields sg state eid event mutex Hvalid He Htype Hmutex)
    as [Hpcp [Hsnapshot Hcount]].
  assert (Havailable : Z.lor (unsigned_last_nbits (encode_event_cnt_value event) 16) 255 = mutex.(mfPCP) * 256 + 255).
  { rewrite Hcount; apply mutex_post_available_count; assumption. }
  assert (Hrange : 0 <= Z.lor (unsigned_last_nbits (encode_event_cnt_value event) 16) 255 < 65536)
    by (rewrite Havailable; lia).
  assert (Hsplit : UCOS2_inv sg state ** private |--
    mutex_post_commit_rep sg state eid (event_image sg state.(TskState) event) ** private).
  { sep_apply_l_atomic (mutex_post_commit_rep_split sg state eid event He); Intros; entailer!. }
  destruct (mutex_post_commit_count_store sg state eid (event_image sg state.(TskState) event)
    (encode_event_cnt_value event) (Z.lor (unsigned_last_nbits (encode_event_cnt_value event) 16) 255)
    private before eq_refl Hrange (Hsplit _ Hbefore)) as [middle [Hfirst Hmiddle]].
  destruct (mutex_post_commit_pointer_store sg state eid
    (event_write (event_image sg state.(TskState) event) EventCntField
      (Some (Z.lor (unsigned_last_nbits (encode_event_cnt_value event) 16) 255)))
    (encode_event_ptr_value sg event) 0 private middle eq_refl ltac:(lia) Hmiddle)
    as [after [Hsecond Hafter]].
  exists after; split.
  - unfold mutex_post_empty_store_writes; eapply KernelHeapStorage.heap_execution_append; eassumption.
  - change ((mutex_post_commit_rep sg state eid
      (mutex_post_empty_image (event_image sg state.(TskState) event)) ** private) after) in Hafter.
    rewrite (mutex_post_empty_image_decoded_eq sg state.(TskState) event mutex
      (mutex_post_snapshot_byte mutex) Htype Hmutex Hcount Hpcp Hsnapshot) in Hafter.
    assert (Hmerge : mutex_post_commit_rep sg state eid
      (event_image sg state.(TskState) (mutex_post_owner_event event mutex None None)) ** private |--
      UCOS2_inv sg (mutex_post_owner_state state eid event mutex None None) ** private).
    { sep_apply_l_atomic (mutex_post_commit_owner_merge_inv sg state eid event mutex None None
        Hvalid He Htype Hmutex Hslot
        (mutex_del_event_group_zero_implies_empty sg state eid event Hvalid He Hgroup)); entailer!. }
    exact (Hmerge _ Hafter).
Qed.

Lemma mutex_post_empty_store_preserves_resources : forall sg state eid event mutex (private : Assertion) before after,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  (UCOS2_inv sg state ** private) before ->
  kernel_heap_execution (mutex_post_empty_store_writes sg eid (encode_event_cnt_value event)) before after ->
  (UCOS2_inv sg (mutex_post_owner_state state eid event mutex None None) ** private) after.
Proof.
  intros sg state eid event mutex private before after Hvalid He Htype Hmutex Hslot Hgroup Hbefore Hrun.
  destruct (mutex_post_empty_store_execution sg state eid event mutex private before
    Hvalid He Htype Hmutex Hslot Hgroup Hbefore) as [final [Hfinal Hpost]].
  pose proof (kernel_heap_execution_deterministic _ _ _ _ Hrun Hfinal) as E; subst final; exact Hpost.
Qed.

(** Literal count reads use the two actual memory bytes, including QCP's
    modulo-byte encoding. This is an observation, not ownership or a rule
    allowing interference to be omitted. *)
Definition mutex_post_count_load (address observed : Z) (heap : model) : Prop :=
  0 <= observed < 65536 /\ exists low high,
    heap.(ConAssertion.s_mem) address = value low /\
    heap.(ConAssertion.s_mem) (address + 1) = value high /\ merge_short low high observed.

Lemma mutex_post_count_load_deterministic : forall address first second heap,
  mutex_post_count_load address first heap -> mutex_post_count_load address second heap -> first = second.
Proof.
  intros address first second heap [Hfirst [a [b [Ha [Hb Hmerge]]]]]
    [Hsecond [a' [b' [Ha' [Hb' Hmerge']]]]].
  assert (a = a') by congruence; assert (b = b') by congruence; subst a' b'.
  change (first mod 65536 = a mod 256 + b mod 256 * 256) in Hmerge.
  change (second mod 65536 = a mod 256 + b mod 256 * 256) in Hmerge'.
  rewrite (Z.mod_small first _ Hfirst) in Hmerge.
  rewrite (Z.mod_small second _ Hsecond) in Hmerge'; congruence.
Qed.

Lemma mutex_post_count_store_load : forall address observed heap,
  (address # UShort |-> observed) heap -> mutex_post_count_load address observed heap.
Proof.
  intros address observed heap [[Haddress Hrange] [a [b [Hmerge Hcells]]]].
  destruct (KernelHeapObservation.framed_byte_store_observation address a
    (store_byte (address + 1) b) heap Hcells) as [low [Hlow Hloweq]].
  assert (Hswap : store_byte address a ** store_byte (address + 1) b |--
    store_byte (address + 1) b ** store_byte address a) by entailer!.
  destruct (KernelHeapObservation.framed_byte_store_observation (address + 1) b
    (store_byte address a) heap (Hswap _ Hcells)) as [high [Hhigh Hhigheq]].
  split; [change (observed >= 0 /\ observed <= 65535) in Hrange; lia|].
  exists low, high; split; [exact Hlow|]; split; [exact Hhigh|].
  eapply merge_short_eqm; eassumption.
Qed.

Lemma mutex_post_count_load_frame : forall address observed owned private whole,
  mutex_post_count_load address observed owned -> join owned private whole ->
  mutex_post_count_load address observed whole.
Proof.
  intros address observed owned private whole [Hrange [low [high [Hlow [Hhigh Hmerge]]]]] [Hjoin _].
  split; [exact Hrange|]; exists low, high.
  split; [exact (proj2 (mem_join_Some3 _ _ _ _ _ Hjoin Hlow))|].
  split; [exact (proj2 (mem_join_Some3 _ _ _ _ _ Hjoin Hhigh))|exact Hmerge].
Qed.

Lemma mutex_post_commit_count_observation : forall sg state eid image count (private : Assertion) heap,
  image EventCntField = Some count -> (mutex_post_commit_rep sg state eid image ** private) heap ->
  mutex_post_count_load (event_addr sg eid + 8) count heap.
Proof.
  intros sg state eid image count private heap Hcount Hheap.
  assert (Hsplit : mutex_post_commit_rep sg state eid image ** private |--
    (event_addr sg eid + 8) # UShort |-> count **
    (mutex_post_commit_field_frame sg state eid image EventCntField ** private)).
  { sep_apply_l_atomic (mutex_post_commit_field_split sg state eid image EventCntField
      ltac:(unfold event_fields; simpl; tauto)).
    rewrite Hcount; cbn [event_cell event_field_offset]; entailer!. }
  destruct (Hsplit _ Hheap) as [cell [rest [Hjoin [Hcell Hrest]]]].
  eapply mutex_post_count_load_frame; [eapply mutex_post_count_store_load; exact Hcell|exact Hjoin].
Qed.

(** Only the final masked C stores and their actual reads are described
    here. The caller must separately bind this fragment to the ordinary C
    command semantics and to the earlier EventTaskRdy owned call. *)
Inductive mutex_post_empty_store_fragment (sg : StableGlobVars) (eid : EventID)
  : model -> model -> Prop :=
| MutexPostEmptyStores : forall before count middle after,
    mutex_post_count_load (event_addr sg eid + 8) count before ->
    kernel_heap_execution
      (mutex_post_count_store_writes (event_addr sg eid + 8)
        (Z.lor (unsigned_last_nbits count 16) 255)) before middle ->
    kernel_heap_execution (KernelHeapStorage.pointer_store_writes (event_addr sg eid + 4) 0) middle after ->
    mutex_post_empty_store_fragment sg eid before after.

Lemma mutex_post_empty_fragment_preserves_resources : forall sg state eid event mutex
  (private : Assertion) before after,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  (UCOS2_inv sg state ** private) before -> mutex_post_empty_store_fragment sg eid before after ->
  (UCOS2_inv sg (mutex_post_owner_state state eid event mutex None None) ** private) after.
Proof.
  intros sg state eid event mutex private before after Hvalid He Htype Hmutex Hslot Hgroup Hbefore Hsource.
  assert (Hsplit : UCOS2_inv sg state ** private |--
    mutex_post_commit_rep sg state eid (event_image sg state.(TskState) event) ** private).
  { sep_apply_l_atomic (mutex_post_commit_rep_split sg state eid event He); Intros; entailer!. }
  pose proof (mutex_post_commit_count_observation sg state eid (event_image sg state.(TskState) event)
    (encode_event_cnt_value event) private before eq_refl (Hsplit _ Hbefore)) as Hcount.
  destruct Hsource as [before observed middle after Hread Hfirst Hsecond].
  pose proof (mutex_post_count_load_deterministic _ _ _ _ Hread Hcount) as E; subst observed.
  eapply mutex_post_empty_store_preserves_resources; try eassumption.
  unfold mutex_post_empty_store_writes; eapply KernelHeapStorage.heap_execution_append; eassumption.
Qed.

Inductive mutex_post_handover_store_fragment (sg : StableGlobVars) (eid : EventID) (priority : Z)
  : model -> model -> Prop :=
| MutexPostHandoverStores : forall before count high_heap high counted_heap pointer after,
    mutex_post_count_load (event_addr sg eid + 8) count before ->
    kernel_heap_execution (mutex_post_count_store_writes (event_addr sg eid + 8) (Z.land count 65280))
      before high_heap ->
    mutex_post_count_load (event_addr sg eid + 8) high high_heap ->
    kernel_heap_execution (mutex_post_count_store_writes (event_addr sg eid + 8) (Z.lor high priority))
      high_heap counted_heap ->
    KernelHeapObservation.pointer_load (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) pointer counted_heap ->
    kernel_heap_execution (KernelHeapStorage.pointer_store_writes (event_addr sg eid + 4) pointer)
      counted_heap after ->
    mutex_post_handover_store_fragment sg eid priority before after.

Lemma mutex_post_commit_count_store_preserves_resources :
  forall sg state eid image old stored (private : Assertion) before after,
  image EventCntField = Some old -> 0 <= stored < 65536 ->
  (mutex_post_commit_rep sg state eid image ** private) before ->
  kernel_heap_execution (mutex_post_count_store_writes (event_addr sg eid + 8) stored) before after ->
  (mutex_post_commit_rep sg state eid (event_write image EventCntField (Some stored)) ** private) after.
Proof.
  intros sg state eid image old stored private before after Hcount Hrange Hbefore Hrun.
  destruct (mutex_post_commit_count_store sg state eid image old stored private before Hcount Hrange Hbefore)
    as [final [Hfinal Hpost]].
  pose proof (kernel_heap_execution_deterministic _ _ _ _ Hrun Hfinal) as E; subst final; exact Hpost.
Qed.

Lemma mutex_post_commit_pointer_store_preserves_resources :
  forall sg state eid image old stored (private : Assertion) before after,
  image EventPtrField = Some old -> 0 <= stored < 4294967296 ->
  (mutex_post_commit_rep sg state eid image ** private) before ->
  kernel_heap_execution (KernelHeapStorage.pointer_store_writes (event_addr sg eid + 4) stored) before after ->
  (mutex_post_commit_rep sg state eid (event_write image EventPtrField (Some stored)) ** private) after.
Proof.
  intros sg state eid image old stored private before after Hptr Hrange Hbefore Hrun.
  destruct (mutex_post_commit_pointer_store sg state eid image old stored private before Hptr Hrange Hbefore)
    as [final [Hfinal Hpost]].
  pose proof (kernel_heap_execution_deterministic _ _ _ _ Hrun Hfinal) as E; subst final; exact Hpost.
Qed.

Lemma mutex_post_handover_fragment_preserves_resources : forall sg state eid event mutex priority owner
  (private : Assertion) before after,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  0 <= priority < 64 -> state.(TskState).(prioTbl) priority = PTTask owner ->
  mutex_post_owner_result state.(TskState) event (Some owner) (Some priority) ->
  (UCOS2_inv sg state ** private) before -> mutex_post_handover_store_fragment sg eid priority before after ->
  (UCOS2_inv sg (mutex_post_owner_state state eid event mutex (Some owner) (Some priority)) ** private) after.
Proof.
  intros sg state eid event mutex priority owner private before after
    Hvalid He Htype Hmutex Hslot Hpriority Howner Hresult Hbefore Hsource.
  destruct (mutex_post_count_fields sg state eid event mutex Hvalid He Htype Hmutex)
    as [Hpcp [Hsnapshot Hcount]].
  assert (Hhigh : Z.land (encode_event_cnt_value event) 65280 = mutex.(mfPCP) * 256).
  { rewrite Hcount.
    pose proof (mutex_post_replace_low_byte mutex.(mfPCP) (mutex_post_snapshot_byte mutex) 0
      Hpcp Hsnapshot ltac:(lia)) as Hzero.
    rewrite Z.lor_0_r, Z.add_0_r in Hzero; exact Hzero. }
  assert (Hhighrange : 0 <= Z.land (encode_event_cnt_value event) 65280 < 65536) by (rewrite Hhigh; lia).
  assert (Hcounted : Z.lor (Z.land (encode_event_cnt_value event) 65280) priority = mutex.(mfPCP) * 256 + priority).
  { rewrite Hcount; apply mutex_post_replace_low_byte; lia. }
  assert (Hcountedrange : 0 <= Z.lor (Z.land (encode_event_cnt_value event) 65280) priority < 65536)
    by (rewrite Hcounted; lia).
  assert (Hsplit : UCOS2_inv sg state ** private |--
    mutex_post_commit_rep sg state eid (event_image sg state.(TskState) event) ** private).
  { sep_apply_l_atomic (mutex_post_commit_rep_split sg state eid event He); Intros; entailer!. }
  pose proof (Hsplit _ Hbefore) as Hinitial.
  pose proof (mutex_post_commit_count_observation sg state eid (event_image sg state.(TskState) event)
    (encode_event_cnt_value event) private before eq_refl Hinitial) as Hinitialread.
  destruct Hsource as [before count high_heap high counted_heap pointer after
    Hread Hfirst Hhighread Hsecond Hpointerread Hlast].
  pose proof (mutex_post_count_load_deterministic _ _ _ _ Hread Hinitialread) as Ecount; subst count.
  pose proof (mutex_post_commit_count_store_preserves_resources sg state eid
    (event_image sg state.(TskState) event) (encode_event_cnt_value event)
    (Z.land (encode_event_cnt_value event) 65280) private before high_heap
    eq_refl Hhighrange Hinitial Hfirst) as Hhighheap.
  pose proof (mutex_post_commit_count_observation sg state eid
    (event_write (event_image sg state.(TskState) event) EventCntField
      (Some (Z.land (encode_event_cnt_value event) 65280)))
    (Z.land (encode_event_cnt_value event) 65280) private high_heap eq_refl Hhighheap) as Hactualhigh.
  pose proof (mutex_post_count_load_deterministic _ _ _ _ Hhighread Hactualhigh) as Ehigh; subst high.
  pose proof (mutex_post_commit_count_store_preserves_resources sg state eid
    (event_write (event_image sg state.(TskState) event) EventCntField
      (Some (Z.land (encode_event_cnt_value event) 65280)))
    (Z.land (encode_event_cnt_value event) 65280)
    (Z.lor (Z.land (encode_event_cnt_value event) 65280) priority) private high_heap counted_heap
    eq_refl Hcountedrange Hhighheap Hsecond) as Hcountedheap.
  pose proof (mutex_post_commit_owner_observation sg state eid
    (event_write
      (event_write (event_image sg state.(TskState) event) EventCntField
        (Some (Z.land (encode_event_cnt_value event) 65280))) EventCntField
      (Some (Z.lor (Z.land (encode_event_cnt_value event) 65280) priority)))
    priority owner private counted_heap Hpriority Howner Hcountedheap) as Hactualpointer.
  pose proof (KernelHeapObservation.pointer_load_deterministic _ _ _ _ Hpointerread Hactualpointer) as Epointer;
    subst pointer.
  pose proof (mutex_post_commit_pointer_store_preserves_resources sg state eid
    (event_write
      (event_write (event_image sg state.(TskState) event) EventCntField
        (Some (Z.land (encode_event_cnt_value event) 65280))) EventCntField
      (Some (Z.lor (Z.land (encode_event_cnt_value event) 65280) priority)))
    (encode_event_ptr_value sg event) (task_slot_addr sg owner) private counted_heap after
    eq_refl (proj1 Hactualpointer) Hcountedheap Hlast) as Hafter.
  change ((mutex_post_commit_rep sg state eid
    (mutex_post_handover_image (event_image sg state.(TskState) event) priority (task_slot_addr sg owner)) ** private) after) in Hafter.
  rewrite (mutex_post_handover_image_decoded_eq sg state.(TskState) event mutex
    (mutex_post_snapshot_byte mutex) owner priority Htype Hmutex Hcount Hpcp Hsnapshot ltac:(lia)) in Hafter.
  assert (Hmerge : mutex_post_commit_rep sg state eid
    (event_image sg state.(TskState) (mutex_post_owner_event event mutex (Some owner) (Some priority))) ** private |--
    UCOS2_inv sg (mutex_post_owner_state state eid event mutex (Some owner) (Some priority)) ** private).
  { sep_apply_l_atomic (mutex_post_commit_owner_merge_inv sg state eid event mutex (Some owner) (Some priority)
      Hvalid He Htype Hmutex Hslot Hresult); entailer!. }
  exact (Hmerge _ Hafter).
Qed.

Lemma mutex_post_handover_fragment_exists : forall sg state eid image count old_pointer priority owner
  (private : Assertion) before,
  image EventCntField = Some count -> image EventPtrField = Some old_pointer ->
  0 <= Z.land count 65280 < 65536 -> 0 <= Z.lor (Z.land count 65280) priority < 65536 ->
  0 <= priority < 64 -> state.(TskState).(prioTbl) priority = PTTask owner ->
  (mutex_post_commit_rep sg state eid image ** private) before ->
  exists after,
    mutex_post_handover_store_fragment sg eid priority before after /\
    (mutex_post_commit_rep sg state eid
      (mutex_post_handover_image image priority (task_slot_addr sg owner)) ** private) after.
Proof.
  intros sg state eid image count old_pointer priority owner private before
    Hcount Hptr Hhighrange Hcountedrange Hpriority Howner Hbefore.
  pose proof (mutex_post_commit_count_observation sg state eid image count private before Hcount Hbefore) as Hread.
  destruct (mutex_post_commit_count_store sg state eid image count (Z.land count 65280)
    private before Hcount Hhighrange Hbefore) as [high_heap [Hfirst Hhighheap]].
  pose proof (mutex_post_commit_count_observation sg state eid
    (event_write image EventCntField (Some (Z.land count 65280)))
    (Z.land count 65280) private high_heap eq_refl Hhighheap) as Hhighread.
  destruct (mutex_post_commit_count_store sg state eid
    (event_write image EventCntField (Some (Z.land count 65280)))
    (Z.land count 65280) (Z.lor (Z.land count 65280) priority) private high_heap
    eq_refl Hcountedrange Hhighheap) as [counted_heap [Hsecond Hcountedheap]].
  pose proof (mutex_post_commit_owner_observation sg state eid
    (event_write (event_write image EventCntField (Some (Z.land count 65280)))
      EventCntField (Some (Z.lor (Z.land count 65280) priority)))
    priority owner private counted_heap Hpriority Howner Hcountedheap) as Hownerread.
  assert (Hptrstill :
    event_write (event_write image EventCntField (Some (Z.land count 65280)))
      EventCntField (Some (Z.lor (Z.land count 65280) priority)) EventPtrField = Some old_pointer)
    by exact Hptr.
  destruct (mutex_post_commit_pointer_store sg state eid
    (event_write (event_write image EventCntField (Some (Z.land count 65280)))
      EventCntField (Some (Z.lor (Z.land count 65280) priority)))
    old_pointer (task_slot_addr sg owner) private counted_heap Hptrstill (proj1 Hownerread) Hcountedheap)
    as [after [Hlast Hafter]].
  exists after; split.
  - econstructor; eassumption.
  - unfold mutex_post_handover_image; rewrite Hcount; exact Hafter.
Qed.

(** Actual owned EventTaskRdy Ensure -> actual count/count/table/owner
    memory fragment -> restored invariant. The returned priority equation
    is extracted from the callee's owned postcondition, not a caller guard. *)
Lemma mutex_post_wake_fragment_preserves_resources : forall sg state eid event mutex tid old priority
  (private : Assertion) before after,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  event_task_rdy_entry sg state.(TskState) eid event tid old ->
  ((event_task_rdy_post sg state.(TskState) eid event tid old 0 16 0
      (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
    mutex_del_wake_frame sg state eid tid) ** private) before ->
  mutex_post_handover_store_fragment sg eid priority before after ->
  ((UCOS2_inv sg (mutex_post_owner_state
      (event_wake_state sg state eid event tid old PendMutex 0 PendOK) eid
      (event_set_wait_list event (remove_Z_eqb tid event.(waitList))) mutex (Some tid) (Some priority)) **
    unmap_table_rep sg) ** private) after.
Proof.
  intros sg state eid event mutex tid old priority private before after
    Hvalid He Htype Hmutex Hslot Hentry Hbefore Hsource.
  assert (Hreturn : priority = old.(curPrio)).
  { destruct Hbefore as [callee [rest [Hjoin [Hcallee Hprivate]]]].
    destruct Hcallee as [owned [frame [Hownedjoin [Howned Hframe]]]].
    exact (proj2 (proj1 Howned)). }
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hin : In tid event.(waitList)).
  { destruct event.(waitList) as [|head tail]; [discriminate Hhead|].
    injection Hhead as E; subst head; simpl; auto. }
  assert (Hwoken : UCOS2_state_inv sg (event_wake_state sg state eid event tid old PendMutex 0 PendOK)).
  { eapply UCOS2_event_wake_preserves_validity; [exact Hvalid|exact He|exact Hin|exact Hold|].
    rewrite Htype; reflexivity. }
  assert (Hlookup : (event_wake_state sg state eid event tid old PendMutex 0 PendOK).(EventState).(inUsedEventStates) eid =
    Some (event_set_wait_list event (remove_Z_eqb tid event.(waitList)))).
  { cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState update_event_field_raw inUsedEventStates].
    rewrite Z.eqb_refl; reflexivity. }
  destruct (mutex_post_wake_owner_selection sg state eid event tid old priority Hentry Hreturn) as [Htable Hresult].
  pose proof (event_task_rdy_selection sg state.(TskState) eid event tid old Hentry) as [_ [_ [_ [Hrange _]]]].
  assert (Hmerge : (event_task_rdy_post sg state.(TskState) eid event tid old 0 16 0
      (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
    mutex_del_wake_frame sg state eid tid) ** private |--
    UCOS2_inv sg (event_wake_state sg state eid event tid old PendMutex 0 PendOK) **
      (unmap_table_rep sg ** private)).
  { sep_apply_l_atomic (mutex_post_wake_merge_inv sg eid state event tid old priority Hvalid He Htype Hentry).
    Intros; entailer!. }
  pose proof (mutex_post_handover_fragment_preserves_resources sg
    (event_wake_state sg state eid event tid old PendMutex 0 PendOK) eid
    (event_set_wait_list event (remove_Z_eqb tid event.(waitList))) mutex priority tid
    (unmap_table_rep sg ** private) before after Hwoken Hlookup Htype Hmutex Hslot
    ltac:(rewrite Hreturn; exact Hrange) Htable Hresult (Hmerge _ Hbefore) Hsource) as Hafter.
  assert (Hreorder : UCOS2_inv sg (mutex_post_owner_state
      (event_wake_state sg state eid event tid old PendMutex 0 PendOK) eid
      (event_set_wait_list event (remove_Z_eqb tid event.(waitList))) mutex (Some tid) (Some priority)) **
    (unmap_table_rep sg ** private) |--
    (UCOS2_inv sg (mutex_post_owner_state
      (event_wake_state sg state eid event tid old PendMutex 0 PendOK) eid
      (event_set_wait_list event (remove_Z_eqb tid event.(waitList))) mutex (Some tid) (Some priority)) **
    unmap_table_rep sg) ** private) by entailer!.
  exact (Hreorder _ Hafter).
Qed.

Lemma mutex_post_empty_fragment_exists : forall sg state eid image count old_pointer
  (private : Assertion) before,
  image EventCntField = Some count -> image EventPtrField = Some old_pointer ->
  0 <= Z.lor (unsigned_last_nbits count 16) 255 < 65536 ->
  (mutex_post_commit_rep sg state eid image ** private) before ->
  exists after,
    mutex_post_empty_store_fragment sg eid before after /\
    (mutex_post_commit_rep sg state eid (mutex_post_empty_image image) ** private) after.
Proof.
  intros sg state eid image count old_pointer private before Hcount Hptr Hrange Hbefore.
  pose proof (mutex_post_commit_count_observation sg state eid image count private before Hcount Hbefore) as Hread.
  destruct (mutex_post_commit_count_store sg state eid image count
    (Z.lor (unsigned_last_nbits count 16) 255) private before Hcount Hrange Hbefore)
    as [middle [Hfirst Hmiddle]].
  assert (Hptrstill : event_write image EventCntField
    (Some (Z.lor (unsigned_last_nbits count 16) 255)) EventPtrField = Some old_pointer) by exact Hptr.
  destruct (mutex_post_commit_pointer_store sg state eid
    (event_write image EventCntField (Some (Z.lor (unsigned_last_nbits count 16) 255)))
    old_pointer 0 private middle Hptrstill ltac:(lia) Hmiddle) as [after [Hlast Hafter]].
  exists after; split; [econstructor; eassumption|].
  unfold mutex_post_empty_image; rewrite Hcount; exact Hafter.
Qed.

Lemma mutex_post_empty_fragment_from_invariant : forall sg state eid event mutex
  (private : Assertion) before,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  (UCOS2_inv sg state ** private) before ->
  exists after,
    mutex_post_empty_store_fragment sg eid before after /\
    (UCOS2_inv sg (mutex_post_owner_state state eid event mutex None None) ** private) after.
Proof.
  intros sg state eid event mutex private before Hvalid He Htype Hmutex Hslot Hgroup Hbefore.
  destruct (mutex_post_count_fields sg state eid event mutex Hvalid He Htype Hmutex)
    as [Hpcp [Hsnapshot Hcount]].
  assert (Hrange : 0 <= Z.lor (unsigned_last_nbits (encode_event_cnt_value event) 16) 255 < 65536).
  { rewrite Hcount, mutex_post_available_count by assumption; lia. }
  assert (Hsplit : UCOS2_inv sg state ** private |--
    mutex_post_commit_rep sg state eid (event_image sg state.(TskState) event) ** private).
  { sep_apply_l_atomic (mutex_post_commit_rep_split sg state eid event He); Intros; entailer!. }
  destruct (mutex_post_empty_fragment_exists sg state eid (event_image sg state.(TskState) event)
    (encode_event_cnt_value event) (encode_event_ptr_value sg event) private before
    eq_refl eq_refl Hrange (Hsplit _ Hbefore)) as [after [Hsource Hafter]].
  exists after; split; [exact Hsource|].
  eapply mutex_post_empty_fragment_preserves_resources; eassumption.
Qed.

Lemma mutex_post_handover_fragment_from_invariant : forall sg state eid event mutex priority owner
  (private : Assertion) before,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ state.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved) ->
  0 <= priority < 64 -> state.(TskState).(prioTbl) priority = PTTask owner ->
  mutex_post_owner_result state.(TskState) event (Some owner) (Some priority) ->
  (UCOS2_inv sg state ** private) before ->
  exists after,
    mutex_post_handover_store_fragment sg eid priority before after /\
    (UCOS2_inv sg (mutex_post_owner_state state eid event mutex (Some owner) (Some priority)) ** private) after.
Proof.
  intros sg state eid event mutex priority owner private before
    Hvalid He Htype Hmutex Hslot Hpriority Howner Hresult Hbefore.
  destruct (mutex_post_count_fields sg state eid event mutex Hvalid He Htype Hmutex)
    as [Hpcp [Hsnapshot Hcount]].
  assert (Hhigh : Z.land (encode_event_cnt_value event) 65280 = mutex.(mfPCP) * 256).
  { rewrite Hcount.
    pose proof (mutex_post_replace_low_byte mutex.(mfPCP) (mutex_post_snapshot_byte mutex) 0
      Hpcp Hsnapshot ltac:(lia)) as Hzero.
    rewrite Z.lor_0_r, Z.add_0_r in Hzero; exact Hzero. }
  assert (Hhighrange : 0 <= Z.land (encode_event_cnt_value event) 65280 < 65536) by (rewrite Hhigh; lia).
  assert (Hcountedrange : 0 <= Z.lor (Z.land (encode_event_cnt_value event) 65280) priority < 65536).
  { rewrite Hcount, mutex_post_replace_low_byte by lia; lia. }
  assert (Hsplit : UCOS2_inv sg state ** private |--
    mutex_post_commit_rep sg state eid (event_image sg state.(TskState) event) ** private).
  { sep_apply_l_atomic (mutex_post_commit_rep_split sg state eid event He); Intros; entailer!. }
  destruct (mutex_post_handover_fragment_exists sg state eid (event_image sg state.(TskState) event)
    (encode_event_cnt_value event) (encode_event_ptr_value sg event) priority owner private before
    eq_refl eq_refl Hhighrange Hcountedrange Hpriority Howner (Hsplit _ Hbefore))
    as [after [Hsource Hafter]].
  exists after; split; [exact Hsource|].
  eapply mutex_post_handover_fragment_preserves_resources; eassumption.
Qed.
