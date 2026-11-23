Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import AUXLib.ListLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.

Import ListNotations TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Export Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.timer.
Require Export Ucos2Verify.lib.ucos2_timer_region.

(** Candidate spatial contract for the unchanged OSTimeTick implementation
    while the interrupted caller owns the Timer pool body. The complete
    pure invariant and original function semantics are retained. This
    file does not justify a smaller external Hook contract by cancellation
    from the old full-heap contract: that implementation/contract connection
    remains an explicit dependency of this candidate. *)
Definition time_tick_complement_missing_module (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (m : UCOS2Module) : Assertion :=
  timer_images_type_rep sg s.(TimerState) **
  timer_service_globals_rep sg s.(TimerState) **
  UCOS2_raw_rep_missing_two sg s TimerModule m.

Definition time_tick_complement_missing_tick sg s :=
  time_tick_complement_missing_module sg s TickModule.
Definition time_tick_complement_missing_sched sg s :=
  time_tick_complement_missing_module sg s SchedModule.
Definition time_tick_complement_missing_task sg s :=
  time_tick_complement_missing_module sg s TaskModule.

Definition time_tick_complement_missing_task_storage_sched (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  timer_images_type_rep sg s.(TimerState) **
  timer_service_globals_rep sg s.(TimerState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) **
  UCOS2_selected_rep sg s (fun m =>
    match m with TimerModule | TaskModule | SchedModule => false | _ => true end).

Definition time_tick_complement_without_time (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSTickStepState) # UChar |-> time_tick_step s ** time_tick_complement_missing_tick sg s.

Definition time_tick_complement_without_step (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSTime) # UInt |-> time_tick_time s ** time_tick_complement_missing_tick sg s.

Definition time_tick_complement_sched_without_running (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> time_tick_ready_group s **
  UCharArray.full sg.(g_OSRdyTbl) 8 (time_tick_ready_rows s) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg s.(SchedState).(curTaskID) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(SchedState).(ctxSwCtr) **
  time_tick_complement_missing_sched sg s.

Definition time_tick_complement_task_without_head (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  store_used_task_map sg s.(TskState).(inUsedTaskStates) **
  task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage)
    s.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error s.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTaskCtr) # UChar |-> s.(TskState).(taskCount) **
  store_prio_tbl sg s.(TskState).(prioTbl) ** task_reg_allocator_rep sg s.(TskState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) ** time_tick_complement_missing_task sg s.

Definition time_tick_complement_cursor_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (tid : TaskID) (node : TaskAbstractState) : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid node (TCBCommonField TCBPrio) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  time_tick_complement_missing_task_storage_sched sg s.

Definition time_tick_complement_body_residual (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (tid : TaskID) (node : TaskAbstractState) : Assertion :=
  time_tick_task_retained sg tid node ** task_public_storage_without_task sg s.(TskState) tid **
  sched_physical_rep sg s.(SchedState) ** time_tick_complement_missing_task_storage_sched sg s.

(** The real port Hook reaches OSSemPost/OS_EventTaskRdy. Its read-only
    unmap table is NOT part of UCOS2_inv; it must be supplied explicitly.
    Bind the actual C globals and ECB field interpretation as well as the
    port-private OSTmrCtr cell. No address equality follows from a name or
    from pure state validity alone. The original full Tick contract is
    unchanged; this candidate makes its own outstanding call inputs explicit. *)
Definition time_tick_complement_hook_bindings (sg : StableGlobVars)
  (counter_address : Z) : Prop :=
  counter_address = (&("OSTmrCtr")) /\
  (&("OSTmrSemSignal")) = sg.(g_OSTmrSemSignal) /\
  (&("OSUnMapTbl")) = sg.(g_OSUnMapTbl) /\
  (&("OSTCBPrioTbl")) = sg.(g_OSTCBPrioTbl) /\
  (&("OSRdyGrp")) = sg.(g_OSRdyGrp) /\
  (&("OSRdyTbl")) = sg.(g_OSRdyTbl) /\
  (&("OSIntNesting")) = sg.(g_OSIntNesting) /\
  (&("OSLockNesting")) = sg.(g_OSLockNesting) /\
  event_table_layout_prop sg.

Definition time_tick_complement_client_frame (critical : CriticalRegionResources)
  (application : TimeTickApplicationResources) (sg : StableGlobVars) (invocation : nat)
  (region_entry : UCOS2_Verify_State) (app_value counter_address counter : Z) : Assertion :=
  coq_prop (time_tick_complement_hook_bindings sg counter_address) &&
  (time_tick_client_frame critical application sg invocation region_entry
     app_value counter_address counter ** unmap_table_rep sg).

Definition time_tick_complement_owned (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (app : TimeTickApplicationResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (region_entry : UCOS2_Verify_State) (app_value counter_address counter : Z)
  (s : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin 192 **
  time_tick_complement_client_frame critical app sg invocation region_entry
    app_value counter_address counter ** UCOS2_inv_missing_timer_pool_body sg s.

Definition time_tick_complement_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (application : TimeTickApplicationResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (region_entry initial : UCOS2_Verify_State) (app_value counter_address counter : Z)
  (X : UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (time_tick_entry sg invocation origin initial /\
    safeExec (time_tick_exact_state initial) (time_tick_sem application sg app_value counter)
      (fun _ after => X after)) &&
  time_tick_complement_owned platform critical application sg invocation origin region_entry
    app_value counter_address counter initial.

Definition time_tick_complement_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (application : TimeTickApplicationResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (region_entry initial : UCOS2_Verify_State) (app_value counter_address counter : Z)
  (X : UCOS2_Verify_State -> Prop) : Assertion :=
  EX app_after counter_after hook_state,
    coq_prop (time_tick_hook_result application sg app_value counter initial
      app_after counter_after hook_state /\
      X (time_tick_serialized_after_hook sg hook_state)) &&
    time_tick_complement_owned platform critical application sg invocation origin region_entry
      app_after counter_address counter_after (time_tick_serialized_after_hook sg hook_state).

Lemma time_tick_complement_split_module : forall sg s m,
  m <> TimerModule ->
  UCOS2_inv_missing_timer_pool_body sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
    (UCOS2_module_rep sg s m ** time_tick_complement_missing_module sg s m).
Proof.
  intros sg s m Hdistinct.
  unfold UCOS2_inv_missing_timer_pool_body, UCOS2_raw_rep_missing_timer_pool_body,
    UCOS2_raw_rep_missing_timer, time_tick_complement_missing_module.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg s TimerModule m) by congruence.
  split; entailer!.
Qed.

Lemma time_tick_complement_split_tick : forall sg s,
  UCOS2_inv_missing_timer_pool_body sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
    (tick_inv sg s.(TickState) ** time_tick_complement_missing_tick sg s).
Proof. intros; apply (time_tick_complement_split_module sg s TickModule); discriminate. Qed.

Lemma time_tick_complement_split_sched : forall sg s,
  UCOS2_inv_missing_timer_pool_body sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
    (sched_raw_rep sg s.(TskState) s.(SchedState) ** time_tick_complement_missing_sched sg s).
Proof. intros; apply (time_tick_complement_split_module sg s SchedModule); discriminate. Qed.

Lemma time_tick_complement_split_task : forall sg s,
  UCOS2_inv_missing_timer_pool_body sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
    (task_shared_rep sg s.(TskState) ** time_tick_complement_missing_task sg s).
Proof. intros; apply (time_tick_complement_split_module sg s TaskModule); discriminate. Qed.

Lemma time_tick_complement_open_task_storage_sched : forall sg s,
  UCOS2_inv_missing_timer_pool_body sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
    (task_public_storage sg s.(TskState) ** sched_raw_rep sg s.(TskState) s.(SchedState) **
     time_tick_complement_missing_task_storage_sched sg s).
Proof.
  intros sg s.
  unfold UCOS2_inv_missing_timer_pool_body, UCOS2_raw_rep_missing_timer_pool_body,
    UCOS2_raw_rep_missing_timer, UCOS2_raw_rep_missing_module,
    time_tick_complement_missing_task_storage_sched, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  unfold task_shared_rep; split; entailer!.
Qed.

Lemma time_tick_complement_merge_updated_task_storage_sched : forall sg old post,
  UCOS2_state_inv sg post ->
  time_tick_complement_missing_task_storage_sched sg old =
    time_tick_complement_missing_task_storage_sched sg post ->
  task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
    time_tick_complement_missing_task_storage_sched sg old |--
  UCOS2_inv_missing_timer_pool_body sg post.
Proof.
  intros sg old post Hvalid Hframe.
  rewrite Hframe, time_tick_complement_open_task_storage_sched; entailer!.
Qed.

Lemma time_tick_complement_merge_counted : forall sg s,
  UCOS2_state_inv sg s ->  0 <= time_tick_step s < 256 ->
  sg.(g_OSTime) # UInt |-> ((time_tick_time s + 1) mod 4294967296) **
    time_tick_complement_without_time sg s |-- UCOS2_inv_missing_timer_pool_body sg (time_tick_counted_state s).
Proof.
  intros sg s Hvalid Hstep.
  rewrite time_tick_complement_split_tick.
  assert (Hpost : UCOS2_state_inv sg (time_tick_counted_state s)).
  { unfold time_tick_counted_state, UCOS2_state_inv, UCOS2_state_inv_with_ready in *; exact Hvalid. }
  assert (Hrange : 0 <= (time_tick_time s + 1) mod 4294967296 < 4294967296)
    by (apply Z.mod_pos_bound; lia).
  unfold time_tick_complement_without_time, tick_inv, store_tick_state, time_tick_time, time_tick_step,
    time_tick_counted_state, tick_counter_advance in *.
  cbn [replace_TickS TickState].
  assert (Hres : time_tick_complement_missing_tick sg
    (replace_TickS (tick_counter_advance s.(TickState)) s) =
    time_tick_complement_missing_tick sg s) by reflexivity.
  change (time_tick_complement_missing_tick sg
    (replace_TickS {| ostime := (s.(TickState).(ostime) + 1) mod 4294967296;
      tickStepState := s.(TickState).(tickStepState) |} s) =
    time_tick_complement_missing_tick sg s) in Hres.
  rewrite Hres; entailer!.
Qed.

Lemma time_tick_complement_split_step : forall sg s,
  UCOS2_inv_missing_timer_pool_body sg s |--
    coq_prop (UCOS2_state_inv sg s /\
      0 <= time_tick_time s < 4294967296) &&
    (sg.(g_OSTickStepState) # UChar |-> time_tick_step s ** time_tick_complement_without_step sg s).
Proof.
  intros; rewrite time_tick_complement_split_tick.
  unfold tick_inv, store_tick_state, time_tick_time, time_tick_step, time_tick_complement_without_step;
    entailer!.
Qed.

Lemma time_tick_complement_merge_step : forall sg s value,
  UCOS2_state_inv sg s -> 
  0 <= time_tick_time s < 4294967296 -> 0 <= value < 256 ->
  sg.(g_OSTickStepState) # UChar |-> value ** time_tick_complement_without_step sg s |--
    UCOS2_inv_missing_timer_pool_body sg (time_tick_step_write s value).
Proof.
  intros sg s value Hvalid Htime Hvalue; rewrite time_tick_complement_split_tick.
  assert (Hpost : UCOS2_state_inv sg (time_tick_step_write s value)).
  { unfold time_tick_step_write, UCOS2_state_inv, UCOS2_state_inv_with_ready in *; exact Hvalid. }
  assert (Hres : time_tick_complement_missing_tick sg (time_tick_step_write s value) =
    time_tick_complement_missing_tick sg s) by reflexivity.
  unfold time_tick_complement_without_step, tick_inv, store_tick_state.
  rewrite Hres; cbn [time_tick_step_write replace_TickS TickState];
    unfold time_tick_time in *; entailer!.
  cbn; entailer!.
Qed.

Lemma time_tick_complement_running_resources : forall sg s,
  UCOS2_inv_missing_timer_pool_body sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (sg.(g_OSRunning) # UChar |-> time_tick_running s ** time_tick_complement_sched_without_running sg s).
Proof.
  intros; rewrite time_tick_complement_split_sched; unfold sched_raw_rep.
  rewrite sched_rows_array_equiv; unfold sched_physical_rep,
    time_tick_complement_sched_without_running, time_tick_running, time_tick_ready_group, time_tick_ready_rows;
    split; entailer!.
Qed.

Lemma time_tick_complement_head_resources : forall sg s,
  UCOS2_inv_missing_timer_pool_body sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (sg.(g_OSTCBList) # Ptr |-> time_tick_list_head sg s ** time_tick_complement_task_without_head sg s).
Proof.
  intros; rewrite time_tick_complement_split_task.
  unfold task_shared_rep, task_public_storage, time_tick_list_head, time_tick_complement_task_without_head;
    split; entailer!.
Qed.

Lemma time_tick_complement_task_step_preserves_residual : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  time_tick_complement_missing_task_storage_sched sg s =
    time_tick_complement_missing_task_storage_sched sg (tick_task_step sg tid t s).
Proof.
  intros sg s tid t Hlookup.
  pose proof (tick_task_step_event_rep_eq sg s tid t Hlookup) as Hevent.
  unfold time_tick_complement_missing_task_storage_sched, UCOS2_selected_rep.
  cbn [UCOS2_module_rep].
  rewrite Hevent; unfold tick_task_step;
    destruct (Z.eqb t.(dly) 0); [reflexivity|];
    destruct (Z.eqb (tick_task_update t).(dly) 0); reflexivity.
Qed.

Lemma time_tick_complement_task_step_merge_resources : forall sg s tid t,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some t ->
  task_public_storage sg (tick_task_step sg tid t s).(TskState) **
    sched_raw_rep sg (tick_task_step sg tid t s).(TskState)
      (tick_task_step sg tid t s).(SchedState) **
    time_tick_complement_missing_task_storage_sched sg s |--
    UCOS2_inv_missing_timer_pool_body sg (tick_task_step sg tid t s).
Proof.
  intros sg s tid t Hmulti Hvalid Hlookup.
  pose proof (time_tick_task_step_preserves_state_inv sg tid t s Hmulti Hvalid Hlookup) as Hpost.
  rewrite (time_tick_complement_task_step_preserves_residual sg s tid t Hlookup).
  rewrite time_tick_complement_open_task_storage_sched; entailer!.
Qed.

Lemma time_tick_complement_owned_entails_post : forall platform critical application sg
  invocation origin region_entry initial app_value counter_address counter X
  app_after counter_after hook_state,
  time_tick_hook_result application sg app_value counter initial app_after counter_after hook_state ->
  time_tick_continuation application sg app_value counter initial X ->
  UCOS2_inv_missing_timer_pool_body sg (time_tick_serialized_after_hook sg hook_state) **
  interrupt_platform_running platform invocation origin 192 **
  time_tick_complement_client_frame critical application sg invocation region_entry
    app_after counter_address counter_after |--
  time_tick_complement_post platform critical application sg invocation origin region_entry initial
    app_value counter_address counter X.
Proof.
  intros platform critical application sg invocation origin region_entry initial app_value
    counter_address counter X app_after counter_after hook_state Hhook Hcontinuation.
  pose proof (time_tick_return_continuation application sg app_value counter initial X
    app_after counter_after hook_state Hcontinuation Hhook) as HX.
  unfold time_tick_complement_post.
  Exists app_after counter_after hook_state.
  unfold time_tick_complement_owned; entailer!.
Qed.

Lemma time_tick_complement_running_merge : forall sg s,
  UCOS2_state_inv sg s ->
  sg.(g_OSRunning) # UChar |-> time_tick_running s **
  time_tick_complement_sched_without_running sg s |-- UCOS2_inv_missing_timer_pool_body sg s.
Proof.
  intros sg s Hvalid; rewrite (time_tick_complement_running_resources sg s); entailer!.
Qed.

Lemma time_tick_complement_cursor_split_priority : forall sg s tid node,
  s.(TskState).(inUsedTaskStates) tid = Some node ->
  UCOS2_inv_missing_timer_pool_body sg s |--
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> time_tick_priority node **
  time_tick_complement_cursor_residual sg s tid node.
Proof.
  intros sg s tid node Hlookup.
  sep_apply_l_atomic (proj1 (time_tick_complement_open_task_storage_sched sg s)).
  Intros.
  sep_apply_l_atomic (task_public_storage_split_field sg s.(TskState) tid node
    (TCBCommonField TCBPrio) Hlookup (tcb_configured_common_field_in _ _ _)).
  unfold time_tick_complement_cursor_residual.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell].
  unfold time_tick_priority; entailer!.
Qed.

Lemma time_tick_complement_cursor_merge_priority : forall sg s tid node,
  UCOS2_state_inv sg s ->
  s.(TskState).(inUsedTaskStates) tid = Some node ->
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> time_tick_priority node **
  time_tick_complement_cursor_residual sg s tid node |-- UCOS2_inv_missing_timer_pool_body sg s.
Proof.
  intros sg s tid node Hvalid Hlookup.
  unfold time_tick_complement_cursor_residual.
  pose proof (task_public_storage_merge_field sg s.(TskState) tid node
    (TCBCommonField TCBPrio) Hlookup (tcb_configured_common_field_in _ _ _)) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Hmerge.
  unfold time_tick_priority.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (time_tick_complement_merge_updated_task_storage_sched sg s s Hvalid eq_refl).
  entailer!.
Qed.

Lemma time_tick_complement_inv_split_body : forall sg s tid node,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  time_tick_lookup s tid node ->
  UCOS2_inv_missing_timer_pool_body sg s |--
  time_tick_body_cells sg tid node (time_tick_ready_group s) (time_tick_ready_rows s) **
    time_tick_complement_body_residual sg s tid node.
Proof.
  intros sg s tid node Hmulti Hlookup.
  sep_apply_l_atomic (proj1 (time_tick_complement_open_task_storage_sched sg s)).
  Intros.
  sep_apply_l_atomic (task_public_storage_split_task sg s.(TskState) tid node Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  fold (time_tick_ready_group s) (time_tick_ready_rows s).
  unfold time_tick_complement_body_residual.
  cancel (task_public_storage_without_task sg s.(TskState) tid).
  cancel (sched_physical_rep sg s.(SchedState)).
  cancel (time_tick_complement_missing_task_storage_sched sg s).
  sep_apply_r_atomic (proj1 (time_tick_task_body_resources__task_update_backedges
    sg tid node (time_tick_ready_group s) (time_tick_ready_rows s) Hmulti)).
  entailer!.
Qed.

Lemma time_tick_complement_body_merge_task_step : forall sg s tid node,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg s -> time_tick_lookup s tid node ->
  time_tick_body_cells sg tid (tick_task_update node)
    (time_tick_ready_group (tick_task_step sg tid node s))
    (time_tick_ready_rows (tick_task_step sg tid node s)) **
    time_tick_complement_body_residual sg s tid node |--
  UCOS2_inv_missing_timer_pool_body sg (tick_task_step sg tid node s).
Proof.
  intros sg s tid node Hmulti Hvalid Hlookup.
  unfold time_tick_complement_body_residual.
  rewrite <- (time_tick_task_retained_eq sg tid node).
  sep_apply_l_atomic (proj2 (time_tick_task_body_resources__task_update_backedges
    sg tid (tick_task_update node)
    (time_tick_ready_group (tick_task_step sg tid node s))
    (time_tick_ready_rows (tick_task_step sg tid node s)) Hmulti)).
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg s.(TskState) tid
    (tick_task_update node)).
  rewrite <- (tick_task_step_task_state_eq sg tid node s Hlookup).
  assert (Hphysical : sched_physical_rep sg (tick_task_step sg tid node s).(SchedState) =
    sched_physical_rep sg s.(SchedState)).
  { unfold tick_task_step; destruct (Z.eqb node.(dly) 0); [reflexivity|].
    destruct (Z.eqb (tick_task_update node).(dly) 0); [|reflexivity].
    apply sched_wake_by_status_physical_rep_eq. }
  rewrite <- Hphysical.
  sep_apply_r_atomic (time_tick_complement_task_step_merge_resources sg s tid node Hmulti Hvalid Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  unfold time_tick_ready_group, time_tick_ready_rows; entailer!.
Qed.
