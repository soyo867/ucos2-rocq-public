Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.tick Ucos2Verify.lib.memory Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** These residuals expose the actual EventTaskWait footprint. They retain
    the existing Flag fields owner and every other configured module. No
    padding owner is created or discarded, and no transient prefix is
    advertised as a valid kernel state. *)
Definition sem_pend_fields_task_sched_frame sg state : Assertion :=
  flag_fields_configured_rep sg state.(FlagState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state.

Definition sem_pend_fields_task_sched_event_frame sg state : Assertion :=
  interrupt_inv sg state.(IntrState) ** queue_storage_rep sg state.(EventState) **
  tick_inv sg state.(TickState) ** flag_fields_configured_rep sg state.(FlagState) **
  memory_configured_rep sg state.(MemoryState) **
  timer_configured_rep sg state.(TimerState) ** statistics_rep sg state.(StatsState) **
  kernel_control_rep sg state.(ControlState) ** store_name_bytes state.(NameState) **
  store_parked_stacks state.(TskState).(parkedTaskStacks).

Lemma sem_pend_fields_task_sched_frame_split_event : forall sg state,
  sem_pend_fields_task_sched_frame sg state --||--
  event_raw_rep sg state.(TskState) state.(EventState) **
    sem_pend_fields_task_sched_event_frame sg state.
Proof.
  intros; unfold sem_pend_fields_task_sched_frame, sem_pend_fields_task_sched_event_frame,
    UCOS2_raw_rep_missing_task_storage_sched_flag; split; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_inv_split_task_sched_event : forall sg state,
  UCOS2_fields_inv sg state --||-- coq_prop (UCOS2_state_inv sg state) &&
    (task_public_storage sg state.(TskState) **
     sched_raw_rep sg state.(TskState) state.(SchedState) **
     event_raw_rep sg state.(TskState) state.(EventState) **
     sem_pend_fields_task_sched_event_frame sg state).
Proof.
  intros; rewrite UCOS2_fields_inv_split_task_storage_sched_flag.
  unfold sem_pend_fields_task_sched_event_frame, UCOS2_raw_rep_missing_task_storage_sched_flag.
  split; apply coq_prop_andp_left; intro Hvalid; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Definition sem_pend_fields_full_task_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (tid : TaskID) : Assertion :=
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  sched_raw_rep sg entry.(TskState) entry.(SchedState) **
  sem_pend_fields_task_sched_frame sg entry.

Lemma sem_pend_fields_full_task_split : forall sg entry tid old,
  UCOS2_state_inv sg entry -> entry.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_fields_inv sg entry |-- tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg old) **
    sem_pend_fields_full_task_frame sg entry tid.
Proof.
  intros sg entry tid old Hvalid Hold; pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  rewrite UCOS2_fields_inv_split_task_storage_sched_flag; Intros.
  sep_apply_l_atomic (sem_post_task_storage_split sg entry.(TskState) tid old Hmulti Hprofiling Hold).
  unfold sem_pend_fields_full_task_frame, sem_pend_fields_task_sched_frame; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Definition sem_pend_fields_prefix_frame sg entry tid old : Assertion :=
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBDly **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  sem_pend_sched_without_current sg entry ** sem_pend_fields_task_sched_frame sg entry.

Lemma sem_pend_fields_wait_prefix_split : forall sg state tid old,
  UCOS2_state_inv sg state -> state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_fields_inv sg state |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some old.(dly)) **
  sem_pend_fields_prefix_frame sg state tid old.
Proof.
  intros * Hvalid Hcurrent Hnode.
  sep_apply_l_atomic (sem_pend_fields_full_task_split sg state tid old Hvalid Hnode).
  sep_apply_l_atomic (sem_pend_tcb_three_fields_split (task_slot_addr sg tid)
    (task_tcb64_image sg old) TCBDly ltac:(discriminate) ltac:(discriminate)).
  unfold sem_pend_fields_full_task_frame, sem_pend_fields_prefix_frame, sem_pend_sched_without_current,
    sched_raw_rep, sched_physical_rep.
  cbn [task_tcb64_image]; rewrite Hcurrent; cbn [encode_task_link]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_count_merge_unchanged : forall sg entry eid current,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
    sem_pend_fields_count_frame sg entry eid current |-- UCOS2_fields_inv sg entry.
Proof.
  intros sg entry eid current Hvalid Hlookup Htype.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields;
    [|contradiction].
  unfold sem_pend_fields_count_frame, encode_event_cnt_value; rewrite Htype, Hfields.
  sep_apply_l_atomic (sem_rep_merge_count sg entry.(TskState) eid current fields Htype Hfields).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState)
    eid current Hlookup).
  rewrite sem_pend_fields_inv_split_event_queue; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_acquired_wait_prefix : forall sg context entry eid current,
  sem_pend_task_call_stage sg context entry ->
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  encode_event_cnt_value current = 0 -> event_object_layout_prop sg eid ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
    sem_pend_fields_count_frame sg entry eid current |--
  EX node,
    coq_prop (sem_pend_wait_entry sg entry eid current context.(os_sched_call_stack).(stackLeaseSlot) node /\
      context.(os_sched_call_origin) = RunningInvocation
        context.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration) /\
      kernel_call_task_source context entry /\
      sched_current_consistency entry.(TskState) entry.(SchedState) /\
      0 <= encode_task_status node.(stat) <= 255) &&
    (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
       TCBStat (Some (encode_task_status node.(stat))) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
       TCBStatPend (Some (encode_pend_status node.(statPend))) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) TCBDly (Some node.(dly)) **
     sem_pend_fields_prefix_frame sg entry context.(os_sched_call_stack).(stackLeaseSlot) node).
Proof.
  intros sg context entry eid current Hstage Hvalid Hlookup Htype Hzero Hlayout.
  destruct (sem_pend_task_stage_wait_entry sg context entry eid current
    Hstage Hvalid Hlookup Htype Hzero Hlayout) as [node [Hentry [Horigin [Hsource Hcache]]]].
  pose proof Hentry as [_ [_ [Hcurrent [Hnode _]]]].
  sep_apply_l_atomic (sem_pend_fields_count_merge_unchanged sg entry eid current Hvalid Hlookup Htype).
  sep_apply_l_atomic (sem_pend_fields_wait_prefix_split sg entry context.(os_sched_call_stack).(stackLeaseSlot)
    node Hvalid Hcurrent Hnode).
  pose proof (encode_task_status_in_range node.(stat)) as Hrange.
  assert (Hbyte_range : 0 <= encode_task_status node.(stat) <= 255).
  { unfold task.encode_task_status; lia. }
  Exists node; entailer!; try (match goal with
    | |- ?left |-- coq_prop ?fact && ?right =>
        let Hspatial := fresh "Hspatial" in
        assert (Hspatial : left |-- right) by entailer!;
        let heap := fresh "heap" in let Hheap := fresh "Hheap" in
        intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
    end).
Qed.

Definition sem_pend_fields_wait_call_frame sg entry eid current tid old timeout : Assertion :=
  event_task_wait_tcb_rest (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)) **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
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
  sem_pend_fields_task_sched_event_frame sg entry.

Definition sem_pend_fields_wait_call_post sg entry eid current tid old timeout : Assertion :=
  event_task_wait_post sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
    sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8))
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState)) **
  sem_pend_fields_wait_call_frame sg entry eid current tid old timeout.

Lemma sem_pend_fields_wait_prefix_split_call : forall sg entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 1)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_fields_prefix_frame sg entry tid old |--
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
  sem_pend_fields_wait_call_frame sg entry eid current tid old timeout.
Proof.
  intros * Hentry.
  pose proof (sem_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [_ [_ [Hold [He [Htype [Hnonidle [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  unfold sem_pend_fields_prefix_frame.
  sepcon_assoc_change.
  pose proof (sem_pend_tcb_merge_wait_prefix sg tid old timeout) as Hmerge.
  lazymatch type of Hmerge with
  | ?prefix |-- _ =>
      lazymatch goal with
      | |- ?whole |-- _ =>
          lazymatch whole with
          | ?a ** (?b ** (?c ** (?d ** ?frame))) =>
              assert (Hpacked : whole |-- prefix ** frame) by entailer!;
              rewrite Hpacked, Hmerge
          end
      end
  end.
  sepcon_assoc_change.
  sep_apply_l_atomic (event_task_wait_tcb_split (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))).
  unfold sem_pend_sched_without_current, sem_pend_fields_task_sched_frame,
    UCOS2_raw_rep_missing_task_storage_sched_flag.
  sep_apply_l_atomic (sched_rows_split_cell sg entry.(TskState) entry.(SchedState).(readyList)
    (old.(curPrio) / 8) Hrow).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid current He).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_wait_event_split_c_fields sg eid
    (event_image sg entry.(TskState) current) (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState)) Hlayout Hrow
    (event_table_image_eq sg entry.(TskState) current (old.(curPrio) / 8) Hrow) eq_refl).
  unfold sem_pend_fields_wait_call_frame, sem_pend_fields_task_sched_event_frame.
  cbn [task_tcb64_image task_prepare_event_wait].
  try rewrite Hnone; cbn [encode_event_link].
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
  cbn [task_prepare_event_wait eventPtr curPrio tcb_y_of_prio].
  rewrite Hnone; reflexivity.
Qed.

Lemma sem_pend_fields_event_pend_preserves_residual : forall sg state eid current tid old kind timeout,
  state.(EventState).(inUsedEventStates) eid = Some current ->
  sem_pend_fields_task_sched_event_frame sg state |--
    sem_pend_fields_task_sched_event_frame sg (event_pend_state sg state eid current tid old kind timeout).
Proof.
  intros sg state eid current tid old kind timeout Hlookup.
  unfold sem_pend_fields_task_sched_event_frame, event_pend_state, event_wait_state; simpl.
  unfold event_insert_waiter.
  sep_apply_l_atomic (queue_set_event_wait_list_preserves_storage sg state.(EventState) eid current
    (insert_sorted_by
      (wait_prio_key sg (glob_task_set_usedtask state.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid))))
      tid (remove_Z_eqb tid current.(waitList))) Hlookup); repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_event_pend_storage_merge : forall sg s eid e tid old kind timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil -> old.(tcbFlagNode) = 0 ->
  In tid s.(SchedState).(readyList) ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  let post := event_pend_state sg s eid e tid old kind timeout in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_mark_waiter (event_image sg s.(TskState) e)
      (old.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) s.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) s.(TskState))
      (Z.shiftl 1 (old.(curPrio) mod 8)) (Z.shiftl 1 (old.(curPrio) / 8))) **
    event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid) **
  sem_pend_fields_task_sched_event_frame sg s |-- UCOS2_fields_inv sg post.
Proof.
  intros sg s eid e tid old kind timeout Hvalid He Hold Hprio Hnull Hmulti Hflagnull
    Hready Hkind Hunavailable Hnotowner post.
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hvalid; tauto. }
  assert (Hrow : 0 <= old.(curPrio) / 8 < 8).
  { destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    unfold valid_task_prio in Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hevent : post.(EventState) =
    update_event_field_raw s.(EventState) eid (event_insert_waiter sg s.(TskState) e tid)).
  { unfold post, event_pend_state, event_wait_state; cbn zeta.
    change (update_event_field_raw s.(EventState) eid
      (event_insert_waiter sg (glob_task_set_usedtask s.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid))) e tid) =
      update_event_field_raw s.(EventState) eid (event_insert_waiter sg s.(TskState) e tid)).
    rewrite (event_insert_waiter_update_task_eq sg s.(TskState) tid old
      (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid)) e tid Hold eq_refl).
    reflexivity. }
  rewrite (event_insert_waiter_reconstructs_raw_rep
    sg s.(TskState) s.(EventState) eid e tid old Hold Hrow).
  rewrite <- Hevent.
  assert (Hvalid_after : UCOS2_state_inv sg post).
  { apply (UCOS2_event_pend_preserves_validity sg s eid e tid old kind timeout
      Hvalid He Hold Hprio Hnull Hmulti Hflagnull Hready Hkind Hunavailable Hnotowner). }
  assert (Hindex : event_raw_rep sg s.(TskState) post.(EventState) =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (sem_pend_fields_event_pend_preserves_residual sg s eid e tid old kind timeout He).
  fold post; rewrite sem_pend_fields_inv_split_task_sched_event; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

Lemma sem_pend_fields_wait_call_merge : forall sg entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  sem_pend_fields_wait_call_post sg entry eid current tid old timeout |--
  UCOS2_fields_inv sg (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * Hentry.
  pose proof (sem_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [Hcount [Hcur [Hold [He [Htype [Hnonidle [Hnone [Hmulti0 [Hflag [Hready Hlayout]]]]]]]]]]].
  pose proof Hvalid as [Hprofile [Htasks [[Hrdy Hmeta] [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hpriorities _]]]]]]]].
  pose proof (Hpriorities tid old Hold) as Hrange.
  assert (Hprio : valid_task_prio sg old.(curPrio))
    by (unfold valid_task_prio, task_priority_in_range in *; lia).
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
  assert (Hunavailable : event_wait_resource_unavailable current).
  { pose proof Hevents as [_ [_ [_ [_ [Hpayload _]]]]].
    specialize (Hpayload eid current He); unfold event_payload_consistency in Hpayload.
    unfold event_wait_resource_unavailable; rewrite Htype in Hpayload |- *.
    destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
    unfold encode_event_cnt_value in Hcount; rewrite Htype, Hfields in Hcount; exact Hcount. }
  assert (Hnotowner : forall m, current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) by (intros; congruence).
  pose proof (sched_ready_in_range_implies_structure sg entry.(TskState) entry.(SchedState) Hrdy) as Hstructure.
  unfold sem_pend_fields_wait_call_post, sem_pend_fields_wait_call_frame, event_task_wait_post.
  pose proof (event_task_wait_tcb_merge_event_ptr (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)) (event_addr sg eid)) as Htcb.
  change (tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (event_addr sg eid)) **
    tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
    tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
    tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
    event_task_wait_tcb_rest (task_slot_addr sg tid)
      (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)) |--
    tcb64_storage_rep (task_slot_addr sg tid)
      (tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))
        TCBEventPtr (Some (event_addr sg eid)))) in Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb.
  unfold tcb_y_of_prio in Htcb.
  sepcon_assoc_change.
  sep_apply_l_atomic Htcb.
  assert (Himage : tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))
    TCBEventPtr (Some (event_addr sg eid)) =
    task_tcb64_image sg (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)))
    by (symmetry; apply task_set_event_ptr_image_eq).
  rewrite Himage.
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid
    (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)) Hmulti Hprofiling).
  sep_apply_l_atomic (event_task_wait_event_merge_c_fields sg eid (event_image sg entry.(TskState) current)
    (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) Hlayout Hrow).
  pose proof (event_task_wait_ready_merge_removed_task sg entry.(TskState) entry.(SchedState)
    tid old Hsg Hunique Hold Hrange Hstructure Hrow) as Hready_merge.
  lazymatch type of Hready_merge with
  | ?ready_fields |-- _ =>
      lazymatch goal with
      | |- ?whole |-- _ =>
          lazymatch whole with
          | ?event ** (?tasks ** (?current_cell ** (?row ** (?group ** (?missing ** ?frame))))) =>
              assert (Hpacked_ready : whole |--
                ready_fields ** (event ** (tasks ** (current_cell ** frame)))) by entailer!;
              rewrite Hpacked_ready, Hready_merge
          end
      end
  end.
  sepcon_assoc_change.
  assert (Hindex : forall s, sched_raw_rep sg entry.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    change (option_map curPrio (entry.(TskState).(inUsedTaskStates) slot) =
      option_map curPrio (if Z.eqb slot tid then
        Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
        else entry.(TskState).(inUsedTaskStates) slot)).
    destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  pose proof (sem_pend_fields_event_pend_storage_merge sg entry eid current tid old PendSem timeout
    Hvalid He Hold Hprio Hnone Hmulti0 Hflag Hready Hkind Hunavailable Hnotowner) as Hmerge_storage.
  let merge_type := type of Hmerge_storage in
  let merge_type := eval cbv zeta in merge_type in
  lazymatch merge_type with
  | ?pre |-- _ =>
      lazymatch goal with
      | |- ?left |-- _ =>
          assert (Hresources : left |-- pre);
          [ | intros heap Hheap; exact (Hmerge_storage heap (Hresources heap Hheap)) ]
      end
  end.
  cbn [event_pend_state event_wait_state replace_SchedS replace_EventS replace_TskS TskState SchedState].
  rewrite <- Hindex; unfold sched_raw_rep, sched_physical_rep.
  cbn [sched_remove_ready_task curSchedPrio highRdyPrio curTaskID highRdyTid ctxSwCtr isRunning].
  try rewrite Hcur; cbn [encode_task_link].
  repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
  unfold sched_remove_ready_task, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  cbn; rewrite Hcur; cbn [encode_task_link]; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.

(** A literal TCB update keeps the existing capsule descriptors, including
    their arbitrary local assertions. Only generation and saved-SP fields
    are used to reindex the current map; complete Task maps are not equal. *)
Lemma sem_pend_fields_task_update_preserves_coverage : forall tasks active tid old updated,
  tasks.(inUsedTaskStates) tid = Some old ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  task_stack_live_coverage tasks active ->
  task_stack_live_coverage (glob_task_set_usedtask tasks tid updated) active.
Proof.
  intros tasks active tid old updated Hlookup Hgeneration Hcoverage.
  eapply task_stack_live_coverage_used_map_frame with (before := tasks);
    [|reflexivity|exact Hcoverage].
  intros slot node Hnode.
  change ((if Z.eqb slot tid then Some updated else tasks.(inUsedTaskStates) slot) = Some node) in Hnode.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
    exists old; auto.
  - exists node; auto.
Qed.

Lemma sem_pend_fields_task_update_continuations : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local tasks tid old updated,
  tasks.(inUsedTaskStates) tid = Some old ->
  updated.(taskGeneration) = old.(taskGeneration) -> updated.(tcbStkPtr) = old.(tcbStkPtr) ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) tasks.(parkedTaskStacks) |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi (glob_task_set_usedtask tasks tid updated) local)
    (glob_task_set_usedtask tasks tid updated).(parkedTaskStacks).
Proof.
  intros external platform port abi local tasks tid old updated Hlookup Hgeneration Hsp.
  cbn [glob_task_set_usedtask parkedTaskStacks].
  apply kernel_saved_continuation_map_reindex.
  intros key payload node Hpayload Hnode Hgen.
  change ((if Z.eqb (fst key) tid then Some updated
    else tasks.(inUsedTaskStates) (fst key)) = Some node) in Hnode.
  destruct (Z.eqb (fst key) tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; rewrite Hslot; injection Hnode as Hnode; subst node.
    exists old; repeat split; assumption || congruence.
  - exists node; repeat split; assumption || reflexivity.
Qed.

(** Source/body-specific counterpart of
    sem_pend_wait_call_continuation_merge_source. The actual raw helper post
    is merged with fields resources and the current local map. The Save
    acquisition index remains distinct from the updated waiting state. *)
Lemma sem_pend_fields_wait_call_continuation_merge_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local
  critical sg active context saved acquired entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  task_stack_live_coverage entry.(TskState) active ->
  critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved acquired ** os_sched_context_resources external context **
  sem_pend_fields_wait_call_post sg entry eid current tid old timeout ** unmap_table_rep sg **
  store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
    entry.(TskState).(parkedTaskStacks) |--
  coq_prop (let waiting := event_pend_state sg entry eid current tid old PendSem timeout in
    UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
    sched_current_consistency waiting.(TskState) waiting.(SchedState)) &&
  kernel_continuation_call_masked abi kernel_program_fields_inv local critical sg active context saved acquired
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros external platform port abi local critical sg active context saved acquired entry
    eid current tid old timeout Hentry Hsource Hcache Hcoverage.
  pose proof Hentry as [_ [_ [_ [Hold _]]]].
  set (waiting := event_pend_state sg entry eid current tid old PendSem timeout).
  assert (Hcovered : task_stack_live_coverage waiting.(TskState) active).
  { apply (sem_pend_fields_task_update_preserves_coverage entry.(TskState) active tid old
      (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
      Hold eq_refl Hcoverage). }
  pose proof (sem_pend_wait_preserves_call_source sg context entry eid current tid old timeout
    Hentry Hsource Hcache) as Hwaiting.
  sep_apply_l_atomic (sem_pend_fields_wait_call_merge sg entry eid current tid old timeout Hentry).
  sep_apply_l_atomic (sem_pend_fields_task_update_continuations external platform port abi local
    entry.(TskState) tid old (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
    Hold eq_refl eq_refl).
  unfold kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap; fold waiting; repeat (match goal with
    | |- coq_prop _ && _ |-- _ => apply coq_prop_andp_left; intro
    end); entailer!; try (match goal with
      | |- ?left |-- coq_prop ?fact && ?right =>
          let Hspatial := fresh "Hspatial" in
          assert (Hspatial : left |-- right) by entailer!;
          let heap := fresh "heap" in let Hheap := fresh "Hheap" in
          intros heap Hheap; split; [change fact; tauto | exact (Hspatial heap Hheap)]
      end).
Qed.
