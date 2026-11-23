Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.lib.kernel_program_storage.
Require Export Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Export Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The prefix is the existing source-ordered argument check. It reads no
    kernel memory. The protected phase below starts after the actual Save
    acquisition and ends before Restore. [current_priority] is the value of
    the actual protected OSTCBCur->OSTCBPrio read, on BOTH request branches;
    its initialization/ownership is a separate acquisition obligation.

    An error's false bit observes that no Scheduler call follows that exit;
    it does not describe the temporary C local [self] on the error path.
    On success the bit uses TCB pointer identity, including priority aliases.
    Neither this relation nor its invariant lemmas claim a whole API return
    or produce a Scheduler/CPU/stack owner. *)
Definition task_suspend_resolved_priority (sg : StableGlobVars)
  (request current_priority : Priority) : Priority :=
  if Z.eqb request sg.(osPrioSelf) then current_priority else request.

Definition task_suspend_protected (sg : StableGlobVars)
  (request current_priority : Priority)
  : program UCOS2_Verify_State (OSErrCode * bool) :=
  fun acquired result released =>
    let selected := task_suspend_resolved_priority sg request current_priority in
    task_priority_in_range sg selected /\
    if Z.eqb selected sg.(osTaskIdlePrio) then
      result = (OS_ERR_TASK_SUSPEND_IDLE, false) /\ released = acquired
    else match acquired.(TskState).(prioTbl) selected with
    | PTFree => result = (OS_ERR_TASK_SUSPEND_PRIO, false) /\ released = acquired
    | PTReserved => result = (OS_ERR_TASK_NOT_EXIST, false) /\ released = acquired
    | PTTask tid => exists target,
        acquired.(TskState).(inUsedTaskStates) tid = Some target /\
        result = (OS_ERR_NONE,
          Z.eqb (task_slot_addr sg tid)
            (encode_task_link sg acquired.(SchedState).(curTaskID))) /\
        released = task_suspend_state acquired tid target
    end.

Lemma task_suspend_resolved_priority_self : forall sg current_priority,
  task_suspend_resolved_priority sg sg.(osPrioSelf) current_priority = current_priority.
Proof. intros; unfold task_suspend_resolved_priority; rewrite Z.eqb_refl; reflexivity. Qed.

Lemma task_suspend_resolved_priority_explicit : forall sg request current_priority,
  request <> sg.(osPrioSelf) ->
  task_suspend_resolved_priority sg request current_priority = request.
Proof.
  intros; unfold task_suspend_resolved_priority;
    rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
Qed.

(** A caller selects the already established Task or generic-view resource
    interface.  A handler never acquires a fictitious Task allocation lease. *)
Inductive TaskSuspendCaller : Type :=
| TaskSuspendTask : OsSchedCallContext -> TaskSuspendCaller
| TaskSuspendDisabled : OsExecutionView -> TaskSuspendCaller.

Definition task_suspend_view (caller : TaskSuspendCaller) : OsExecutionView :=
  match caller with
  | TaskSuspendTask call => os_sched_execution_view call
  | TaskSuspendDisabled view => view
  end.

Definition task_suspend_same_call (returned original : TaskSuspendCaller) : Prop :=
  match returned, original with
  | TaskSuspendTask next, TaskSuspendTask old => task_tcb_init_stack_same_call next old
  | TaskSuspendDisabled next, TaskSuspendDisabled old => next = old
  | _, _ => False
  end.

Definition task_suspend_closed environment critical saved_local sg caller mask state : Assertion :=
  match caller with
  | TaskSuspendTask call =>
      task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
      unmap_table_rep sg
  | TaskSuspendDisabled view =>
      coq_prop (UCOS2_state_inv sg state) &&
      sched_disabled_closed environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask state
  end.

Definition task_suspend_call_resources environment saved_local sg caller state : Assertion :=
  match caller with
  | TaskSuspendTask call =>
      coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
      (os_sched_context_resources environment.(task_stack_call_external) call **
       task_tcb_init_continuation_capsules environment saved_local state ** unmap_table_rep sg)
  | TaskSuspendDisabled view => os_execution_view_resources environment.(task_stack_call_external) view
  end.

Definition task_suspend_masked environment critical saved_local sg caller saved acquired released : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    (task_suspend_view caller).(os_execution_invocation)
    (task_suspend_view caller).(os_execution_origin) saved acquired **
  UCOS2_inv sg released ** task_suspend_call_resources environment saved_local sg caller released.

(** These are exactly the observations in the existing source-aware Task
    summaries, or the interval of the generic CPU contract.  The separately
    named completed-call rely below does not add facts to either summary. *)
Definition task_suspend_save_observation critical sg original returned mask saved before acquired : Prop :=
  match original, returned with
  | TaskSuspendTask call, TaskSuspendTask next =>
      task_tcb_init_stack_same_call next call /\
      task_tcb_init_call_preserved sg call.(os_sched_call_invocation) before acquired /\
      (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved call before acquired) /\
      interrupt_saved_value mask saved
  | TaskSuspendDisabled view, TaskSuspendDisabled next =>
      next = view /\ critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
      interrupt_saved_value mask saved
  | _, _ => False
  end.

Definition task_suspend_restore_observation critical sg original returned released current : Prop :=
  match original, returned with
  | TaskSuspendTask call, TaskSuspendTask next =>
      task_tcb_init_stack_same_call next call /\
      task_tcb_init_call_preserved sg call.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved call released current)
  | TaskSuspendDisabled view, TaskSuspendDisabled next =>
      next = view /\ critical_region_interval critical sg view.(os_execution_invocation) released current
  | _, _ => False
  end.

Definition task_suspend_save_post environment critical saved_local sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_suspend_save_observation critical sg original returned mask saved before acquired) &&
    task_suspend_masked environment critical saved_local sg returned saved acquired acquired.

Definition task_suspend_restore_post environment critical saved_local sg original saved released : Assertion :=
  EX returned current,
    coq_prop (task_suspend_restore_observation critical sg original returned released current) &&
    task_suspend_closed environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current.

(** A reversible view of the actual priority read.  It places no live-task
    classification on a non-SELF request: a readable public-free image can
    provide the same view.  No owner is copied.  The selected priority range
    is required only for SELF, whose next C access uses that byte as an index. *)
Definition task_suspend_current_read_view sg request state pointer priority
  (residual : Assertion) : Prop :=
  pointer = encode_task_link sg state.(SchedState).(curTaskID) /\
  0 <= priority <= 255 /\
  (request = sg.(osPrioSelf) -> task_priority_in_range sg priority) /\
  (UCOS2_inv sg state |--
    sg.(g_OSTCBCur) # Ptr |-> pointer **
    tcb_field_address pointer TCBPrio # UChar |-> priority ** residual) /\
  (sg.(g_OSTCBCur) # Ptr |-> pointer **
    tcb_field_address pointer TCBPrio # UChar |-> priority ** residual |-- UCOS2_inv sg state).

Definition task_suspend_current_readable sg request state : Prop :=
  exists pointer priority residual,
    task_suspend_current_read_view sg request state pointer priority residual.

Definition task_suspend_caller_source sg caller state : Prop :=
  match caller with
  | TaskSuspendTask call =>
      kernel_call_task_source call state /\ kernel_call_stack_available call state /\
      tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
        task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) /\
      task_idle_ready sg state.(TskState)
  | TaskSuspendDisabled view => sched_disabled_entry_source view state
  end.

Definition task_suspend_scheduler_clients critical caller : Prop :=
  match caller with
  | TaskSuspendTask _ => kernel_sched_ready_clients critical
  | TaskSuspendDisabled view => sched_disabled_completed_clients critical view
  end.

(** Public C-environment R at actual completed-call endpoints.  The first
    conjunct supplies a reversible view of the same acquired heap.  Its
    source clauses are consumed only if the protected operation actually
    requests Scheduler; early argument errors consume none of this premise.
    The second conjunct transports those source observations through the
    SAME Restore return.  No operation result, suspend bit, bitmap update,
    Scheduler return or future termination is assumed here. *)
Definition task_suspend_completed_calls critical sg original request mask before : Prop :=
  (forall returned saved acquired,
    task_suspend_save_observation critical sg original returned mask saved before acquired ->
    UCOS2_state_inv sg acquired ->
    task_suspend_current_readable sg request acquired /\
    (forall pointer priority residual released,
      task_suspend_current_read_view sg request acquired pointer priority residual ->
      task_suspend_protected sg request priority acquired (OS_ERR_NONE, true) released ->
      task_suspend_caller_source sg returned acquired)) /\
  (forall acquired_call saved acquired pointer priority residual released returned current,
    task_suspend_save_observation critical sg original acquired_call mask saved before acquired ->
    task_suspend_current_read_view sg request acquired pointer priority residual ->
    task_suspend_protected sg request priority acquired (OS_ERR_NONE, true) released ->
    task_suspend_restore_observation critical sg acquired_call returned released current ->
    task_suspend_caller_source sg acquired_call released ->
    task_suspend_caller_source sg returned current).

Definition task_suspend_scheduler_pre environment critical saved_local sg caller mask before : Assertion :=
  match caller with
  | TaskSuspendTask call =>
      coq_prop (kernel_sched_ready_clients critical) &&
      os_sched_continuation_call_pre environment saved_local kernel_program_inv sg call mask before
  | TaskSuspendDisabled view =>
      coq_prop (sched_disabled_completed_clients critical view /\ UCOS2_state_inv sg before /\
        sched_disabled_entry_source view before) &&
      sched_disabled_closed environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask before
  end.

Definition task_suspend_scheduler_post environment critical saved_local sg caller mask before : Assertion :=
  match caller with
  | TaskSuspendTask call =>
      os_sched_continuation_return_post environment saved_local kernel_program_inv sg call mask before
  | TaskSuspendDisabled view =>
      sched_disabled_contextual_post environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask before
  end.

Definition task_suspend_tail_post environment critical saved_local sg caller mask before
  (scheduled : bool) : Assertion :=
  if scheduled then task_suspend_scheduler_post environment critical saved_local sg caller mask before
  else task_suspend_closed environment critical saved_local sg caller mask before.

(** The same immutable pool address interpretation used by the initializer.
    Only its four-byte alignment is needed here: no initialization-only
    heap, current-task condition, or unrelated layout conjunct is required. *)
Lemma task_suspend_tcb_pool_alignment_from_init : forall sg,
  init_tcb_list_layout sg -> sg.(g_OSTCBTbl) mod 4 = 0.
Proof. intros sg [_ [_ [_ [Haligned _]]]]; exact Haligned. Qed.

Lemma task_suspend_tcb_slot_not_reserved : forall sg tid,
  sg.(g_OSTCBTbl) mod 4 = 0 -> task_slot_addr sg tid <> 1.
Proof.
  intros sg tid Haligned Heq.
  pose proof (Z.div_mod sg.(g_OSTCBTbl) 4 ltac:(lia)) as Hdivision.
  rewrite Haligned in Hdivision.
  unfold task_slot_addr, tcb_configured_size, tcb_layout_size in Heq.
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled);
    destruct sg.(osKernelConfig).(cfgTaskProfile); lia.
Qed.

Definition task_suspend_call_pre environment critical saved_local sg caller mask before request
  (frame : Assertion) : Assertion :=
  coq_prop (valid_stable_glob_vars sg /\ sg.(osKernelConfig).(cfgArgumentChecks) = true /\
    0 <= request <= 255) &&
  match task_suspend_argument_error sg request with
  | Some _ => frame
  | None => coq_prop (sg.(g_OSTCBTbl) mod 4 = 0 /\
      task_suspend_completed_calls critical sg caller request mask before /\
      task_suspend_scheduler_clients critical caller) &&
      (task_suspend_closed environment critical saved_local sg caller mask before ** frame)
  end.

Definition task_suspend_call_post environment critical saved_local sg original mask before request
  (frame : Assertion) (result : Z) : Assertion :=
  match task_suspend_argument_error sg request with
  | Some error => coq_prop (result = encode_os_err_code error) && frame
  | None => EX saved acquired_call acquired pointer priority residual released checkpoint_call checkpoint scheduled error,
      coq_prop (task_suspend_save_observation critical sg original acquired_call mask saved before acquired /\
        task_suspend_current_read_view sg request acquired pointer priority residual /\
        result = encode_os_err_code error /\
        task_suspend_protected sg request priority acquired (error, scheduled) released /\
        task_suspend_restore_observation critical sg acquired_call checkpoint_call released checkpoint) &&
      (task_suspend_tail_post environment critical saved_local sg checkpoint_call mask checkpoint scheduled ** frame)
  end.

(** Local assertion vocabulary.  These definitions expose the actual field
    owner and leave one reconstructible complement, including all parked
    stacks, rather than retaining a second copy of the global invariant. *)
Definition task_suspend_addresses (sg : StableGlobVars)
  (current_tcb ints locks high current high_tcb table counter unmap group rows : Z) : Prop :=
  current_tcb = sg.(g_OSTCBCur) /\
  os_sched_global_addresses sg ints locks high current high_tcb table counter unmap group rows.

Definition task_suspend_argument_none sg request : Prop :=
  task_suspend_argument_error sg request = None.

Definition task_suspend_entry_facts sg request : Prop :=
  valid_stable_glob_vars sg /\ sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  0 <= request <= 255 /\ task_suspend_argument_none sg request /\
  sg.(g_OSTCBTbl) mod 4 = 0.

Definition task_suspend_acquired_facts critical sg caller request mask before saved
  acquired_call acquired pointer priority residual : Prop :=
  task_suspend_entry_facts sg request /\
  task_suspend_completed_calls critical sg caller request mask before /\
  task_suspend_scheduler_clients critical caller /\
  task_suspend_save_observation critical sg caller acquired_call mask saved before acquired /\
  UCOS2_state_inv sg acquired /\
  task_suspend_current_read_view sg request acquired pointer priority residual.

Definition task_suspend_step sg request priority acquired result self released : Prop :=
  exists error, result = encode_os_err_code error /\
    task_suspend_protected sg request priority acquired (error, Z.eqb self 1) released.

Lemma task_suspend_step_none : forall sg request priority acquired self released,
  task_suspend_step sg request priority acquired 0 self released <->
  task_suspend_protected sg request priority acquired (OS_ERR_NONE, Z.eqb self 1) released.
Proof.
  intros; split.
  - intros [error [Hvalue Hstep]].
    assert (error = OS_ERR_NONE) by (apply encode_os_err_code_injective; simpl; congruence).
    subst error; exact Hstep.
  - intro Hstep; exists OS_ERR_NONE; split; [reflexivity|exact Hstep].
Qed.

Definition task_suspend_tokens environment critical saved_local sg caller saved acquired state : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    (task_suspend_view caller).(os_execution_invocation)
    (task_suspend_view caller).(os_execution_origin) saved acquired **
  task_suspend_call_resources environment saved_local sg caller state.

Definition task_suspend_current_pointer sg state : Z :=
  encode_task_link sg state.(SchedState).(curTaskID).

Definition task_suspend_table_value sg state selected : Z :=
  prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) selected).

Lemma task_suspend_table_value_reserved : forall sg state selected,
  sg.(g_OSTCBTbl) mod 4 = 0 ->
  task_suspend_table_value sg state selected = 1 ->
  state.(TskState).(prioTbl) selected = PTReserved.
Proof.
  intros sg state selected Haligned Hvalue.
  unfold task_suspend_table_value in Hvalue.
  destruct (state.(TskState).(prioTbl) selected) as [| |tid] eqn:Hentry;
    cbn [prio_tbl_entry_to_addr] in Hvalue.
  - discriminate Hvalue.
  - reflexivity.
  - exfalso; exact (task_suspend_tcb_slot_not_reserved sg tid Haligned Hvalue).
Qed.

Definition task_suspend_table_frame sg state selected : Assertion :=
  store_prio_tbl_missing_i sg state.(TskState).(prioTbl) selected **
  task_public_storage_without_prio_tbl sg state.(TskState) **
  sched_raw_rep sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state.

Definition task_suspend_work_frame sg state : Assertion :=
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if state.(SchedState).(isRunning) then 1 else 0) **
  UCOS2_raw_rep_missing_task_storage_sched sg state.

Definition task_suspend_lookup state selected tid target : Prop :=
  state.(TskState).(prioTbl) selected = PTTask tid /\
  state.(TskState).(inUsedTaskStates) tid = Some target.

Definition task_suspend_target_facts sg state selected tid target : Prop :=
  UCOS2_state_inv sg state /\ task_suspend_lookup state selected tid target /\
  task_priority_in_range sg selected /\ selected <> sg.(osTaskIdlePrio) /\
  task_priority_in_range sg target.(curPrio).

Definition task_suspend_self_byte sg state tid : Z :=
  if Z.eqb (task_slot_addr sg tid) (task_suspend_current_pointer sg state) then 1 else 0.

Definition task_suspend_cleared_row state target : Z :=
  Z.land (encode_ready_tbl_at_or state.(SchedState).(readyList) state.(TskState)
    (tcb_y_of_prio target.(curPrio)))
    (unsigned_last_nbits (Z.lnot (tcb_bit_x_of_prio target.(curPrio))) 8).

Definition task_suspend_updated_group state target : Z :=
  if Z.eqb (task_suspend_cleared_row state target) 0 then
    Z.land (os_sched_group state)
      (unsigned_last_nbits (Z.lnot (tcb_bit_y_of_prio target.(curPrio))) 8)
  else os_sched_group state.

Lemma task_suspend_protected_resolved_idle : forall sg request current_priority acquired,
  task_priority_in_range sg sg.(osTaskIdlePrio) ->
  task_suspend_resolved_priority sg request current_priority = sg.(osTaskIdlePrio) ->
  task_suspend_protected sg request current_priority acquired
    (OS_ERR_TASK_SUSPEND_IDLE, false) acquired.
Proof.
  intros; unfold task_suspend_protected; rewrite H0, Z.eqb_refl;
    split; [exact H|split; reflexivity].
Qed.

Lemma task_suspend_protected_free : forall sg request current_priority acquired,
  let selected := task_suspend_resolved_priority sg request current_priority in
  task_priority_in_range sg selected -> selected <> sg.(osTaskIdlePrio) ->
  acquired.(TskState).(prioTbl) selected = PTFree ->
  task_suspend_protected sg request current_priority acquired
    (OS_ERR_TASK_SUSPEND_PRIO, false) acquired.
Proof.
  intros sg request current_priority acquired selected Hrange Hidle Htable.
  unfold task_suspend_protected; cbn zeta; fold selected.
  rewrite (proj2 (Z.eqb_neq _ _) Hidle), Htable.
  split; [exact Hrange|split; reflexivity].
Qed.

Lemma task_suspend_protected_reserved : forall sg request current_priority acquired,
  let selected := task_suspend_resolved_priority sg request current_priority in
  task_priority_in_range sg selected -> selected <> sg.(osTaskIdlePrio) ->
  acquired.(TskState).(prioTbl) selected = PTReserved ->
  task_suspend_protected sg request current_priority acquired
    (OS_ERR_TASK_NOT_EXIST, false) acquired.
Proof.
  intros sg request current_priority acquired selected Hrange Hidle Htable.
  unfold task_suspend_protected; cbn zeta; fold selected.
  rewrite (proj2 (Z.eqb_neq _ _) Hidle), Htable.
  split; [exact Hrange|split; reflexivity].
Qed.

Lemma task_suspend_protected_task : forall sg request current_priority acquired tid target,
  let selected := task_suspend_resolved_priority sg request current_priority in
  task_priority_in_range sg selected -> selected <> sg.(osTaskIdlePrio) ->
  acquired.(TskState).(prioTbl) selected = PTTask tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some target ->
  task_suspend_protected sg request current_priority acquired
    (OS_ERR_NONE, Z.eqb (task_slot_addr sg tid)
      (encode_task_link sg acquired.(SchedState).(curTaskID)))
    (task_suspend_state acquired tid target).
Proof.
  intros sg request current_priority acquired tid target selected Hrange Hidle Htable Htarget.
  unfold task_suspend_protected; cbn zeta; fold selected.
  rewrite (proj2 (Z.eqb_neq _ _) Hidle), Htable.
  split; [exact Hrange|exists target; repeat split; assumption || reflexivity].
Qed.

Lemma task_suspend_protected_deterministic : forall sg request current_priority acquired r1 s1 r2 s2,
  task_suspend_protected sg request current_priority acquired r1 s1 ->
  task_suspend_protected sg request current_priority acquired r2 s2 ->
  r1 = r2 /\ s1 = s2.
Proof.
  intros sg request current_priority acquired r1 s1 r2 s2 [_ H1] [_ H2].
  destruct (Z.eqb (task_suspend_resolved_priority sg request current_priority)
    sg.(osTaskIdlePrio)); [destruct H1, H2; split; congruence|].
  destruct (acquired.(TskState).(prioTbl)
    (task_suspend_resolved_priority sg request current_priority)).
  - destruct H1, H2; split; congruence.
  - destruct H1, H2; split; congruence.
  - destruct H1 as [a [Ha [Hr1 Hs1]]], H2 as [b [Hb [Hr2 Hs2]]].
    assert (a = b) by congruence; subst b; split; congruence.
Qed.

Lemma task_suspend_protected_error_frame : forall sg request current_priority acquired result released,
  task_suspend_protected sg request current_priority acquired result released ->
  fst result <> OS_ERR_NONE -> released = acquired /\ snd result = false.
Proof.
  intros sg request current_priority acquired result released [_ Hstep] Herror.
  destruct (Z.eqb (task_suspend_resolved_priority sg request current_priority)
    sg.(osTaskIdlePrio)); [destruct Hstep as [-> ->]; split; reflexivity|].
  destruct (acquired.(TskState).(prioTbl)
    (task_suspend_resolved_priority sg request current_priority)).
  - destruct Hstep as [-> ->]; split; reflexivity.
  - destruct Hstep as [-> ->]; split; reflexivity.
  - destruct Hstep as [target [_ [-> _]]]; contradiction Herror; reflexivity.
Qed.

Lemma task_suspend_protected_success : forall sg request current_priority acquired scheduled released,
  task_suspend_protected sg request current_priority acquired (OS_ERR_NONE, scheduled) released ->
  exists tid target,
    acquired.(TskState).(prioTbl)
      (task_suspend_resolved_priority sg request current_priority) = PTTask tid /\
    acquired.(TskState).(inUsedTaskStates) tid = Some target /\
    scheduled = Z.eqb (task_slot_addr sg tid)
      (encode_task_link sg acquired.(SchedState).(curTaskID)) /\
    released = task_suspend_state acquired tid target.
Proof.
  intros sg request current_priority acquired scheduled released [_ Hstep].
  destruct (Z.eqb (task_suspend_resolved_priority sg request current_priority)
    sg.(osTaskIdlePrio)); [destruct Hstep as [Hbad _]; discriminate Hbad|].
  destruct (acquired.(TskState).(prioTbl)
    (task_suspend_resolved_priority sg request current_priority)) as [| |tid] eqn:Htable.
  - destruct Hstep as [Hbad _]; discriminate Hbad.
  - destruct Hstep as [Hbad _]; discriminate Hbad.
  - destruct Hstep as [target [Htarget [Hresult Hreleased]]].
    injection Hresult as Hscheduled.
    exists tid, target; repeat split; assumption || reflexivity.
Qed.

(** No priority-equality premise is used: an inherited or permanent alias
    that names the current TCB requests scheduling just as SELF does. *)
Lemma task_suspend_protected_current_alias : forall sg request current_priority acquired tid target,
  let selected := task_suspend_resolved_priority sg request current_priority in
  task_priority_in_range sg selected -> selected <> sg.(osTaskIdlePrio) ->
  acquired.(TskState).(prioTbl) selected = PTTask tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some target ->
  acquired.(SchedState).(curTaskID) = Some tid ->
  task_suspend_protected sg request current_priority acquired (OS_ERR_NONE, true)
    (task_suspend_state acquired tid target).
Proof.
  intros sg request current_priority acquired tid target selected Hrange Hidle Htable Htarget Hcurrent.
  pose proof (task_suspend_protected_task sg request current_priority acquired tid target
    Hrange Hidle Htable Htarget) as Hstep.
  rewrite Hcurrent in Hstep; unfold encode_task_link in Hstep.
  rewrite Z.eqb_refl in Hstep; exact Hstep.
Qed.

Lemma task_suspend_protected_preserves_validity : forall sg request current_priority acquired result released,
  UCOS2_state_inv sg acquired ->
  task_suspend_protected sg request current_priority acquired result released ->
  UCOS2_state_inv sg released.
Proof.
  intros sg request current_priority acquired result released Hvalid [_ Hstep].
  destruct (Z.eqb (task_suspend_resolved_priority sg request current_priority)
    sg.(osTaskIdlePrio)); [destruct Hstep as [_ ->]; exact Hvalid|].
  destruct (acquired.(TskState).(prioTbl)
    (task_suspend_resolved_priority sg request current_priority)).
  - destruct Hstep as [_ ->]; exact Hvalid.
  - destruct Hstep as [_ ->]; exact Hvalid.
  - destruct Hstep as [target [Htarget [_ ->]]].
    eapply UCOS2_task_suspend_preserves_validity; eassumption.
Qed.

Lemma task_suspend_protected_preserves_idle_ready : forall sg request current_priority acquired result released,
  UCOS2_state_inv sg acquired -> task_idle_ready sg acquired.(TskState) ->
  task_suspend_protected sg request current_priority acquired result released ->
  task_idle_ready sg released.(TskState).
Proof.
  intros sg request current_priority acquired result released Hvalid Hidle [Hrange Hstep].
  destruct (Z.eqb (task_suspend_resolved_priority sg request current_priority)
    sg.(osTaskIdlePrio)) eqn:Htest; [destruct Hstep as [_ ->]; exact Hidle|].
  apply Z.eqb_neq in Htest.
  destruct (acquired.(TskState).(prioTbl)
    (task_suspend_resolved_priority sg request current_priority)) as [| |tid] eqn:Htable.
  - destruct Hstep as [_ ->]; exact Hidle.
  - destruct Hstep as [_ ->]; exact Hidle.
  - destruct Hstep as [target [Htarget [_ ->]]].
    eapply task_update_non_idle_preserves_idle_ready; [exact Htarget| |exact Hidle].
    eapply task_suspend_table_target_non_idle; eassumption.
Qed.

Lemma task_suspend_protected_merge_inv : forall sg request current_priority acquired result released,
  UCOS2_state_inv sg acquired ->
  task_suspend_protected sg request current_priority acquired result released ->
  task_public_storage sg released.(TskState) **
  sched_raw_rep sg released.(TskState) released.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg acquired |-- UCOS2_inv sg released.
Proof.
  intros sg request current_priority acquired result released Hvalid [_ Hstep].
  destruct (Z.eqb (task_suspend_resolved_priority sg request current_priority)
    sg.(osTaskIdlePrio));
    [destruct Hstep as [_ ->]; apply UCOS2_inv_merge_updated_task_storage_sched;
      [exact Hvalid|reflexivity]|].
  destruct (acquired.(TskState).(prioTbl)
    (task_suspend_resolved_priority sg request current_priority)).
  - destruct Hstep as [_ ->]; apply UCOS2_inv_merge_updated_task_storage_sched;
      [exact Hvalid|reflexivity].
  - destruct Hstep as [_ ->]; apply UCOS2_inv_merge_updated_task_storage_sched;
      [exact Hvalid|reflexivity].
  - destruct Hstep as [target [Htarget [_ ->]]]; apply UCOS2_inv_merge_task_suspend; assumption.
Qed.

(** This is the released protected world, before any Restore interval.
    It supplies selection's nonempty-ready condition without claiming that
    the suspended outgoing task remains a ready member. *)
Lemma task_suspend_protected_ready_nonempty : forall sg request current_priority acquired result released,
  UCOS2_state_inv sg acquired -> task_idle_ready sg acquired.(TskState) ->
  task_suspend_protected sg request current_priority acquired result released ->
  released.(SchedState).(readyList) <> [].
Proof.
  intros sg request current_priority acquired result released Hvalid Hidle Hstep.
  pose proof (task_suspend_protected_preserves_validity sg request current_priority
    acquired result released Hvalid Hstep) as Hpost.
  destruct Hpost as [_ [_ [Hsched _]]].
  eapply sched_idle_ready_nonempty; [exact (proj1 Hsched)|].
  eapply task_suspend_protected_preserves_idle_ready; eassumption.
Qed.

Lemma task_suspend_protected_lifecycle_frame : forall sg request current_priority acquired result released,
  task_suspend_protected sg request current_priority acquired result released ->
  released.(TskState).(taskLifecycle) = acquired.(TskState).(taskLifecycle) /\
  (forall observer origin, task_invocation_active acquired.(TskState) observer origin ->
    task_invocation_active released.(TskState) observer origin).
Proof.
  intros sg request current_priority acquired result released [_ Hstep].
  destruct (Z.eqb (task_suspend_resolved_priority sg request current_priority)
    sg.(osTaskIdlePrio)); [destruct Hstep as [_ ->]; split; [reflexivity|auto]|].
  destruct (acquired.(TskState).(prioTbl)
    (task_suspend_resolved_priority sg request current_priority)).
  - destruct Hstep as [_ ->]; split; [reflexivity|auto].
  - destruct Hstep as [_ ->]; split; [reflexivity|auto].
  - destruct Hstep as [target [Htarget [_ ->]]]; split; [reflexivity|].
    intros observer origin Hactive; eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Htarget|reflexivity|exact Hactive].
Qed.

Lemma task_suspend_protected_event_frame : forall sg request current_priority acquired result released,
  task_suspend_protected sg request current_priority acquired result released ->
  released.(EventState) = acquired.(EventState).
Proof.
  intros sg request current_priority acquired result released [_ Hstep].
  destruct (Z.eqb (task_suspend_resolved_priority sg request current_priority)
    sg.(osTaskIdlePrio)); [destruct Hstep as [_ ->]; reflexivity|].
  destruct (acquired.(TskState).(prioTbl)
    (task_suspend_resolved_priority sg request current_priority)).
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [_ ->]; reflexivity.
  - destruct Hstep as [target [_ [_ ->]]]; reflexivity.
Qed.

(** These split/merge instances access a single native field at a time.
    In particular the current-priority read must be merged before opening
    a target that may be the SAME TCB. They neither duplicate a TCB owner
    nor assume that a requested priority is its effective priority. *)
Lemma task_suspend_priority_split : forall sg tasks tid target,
  tasks.(inUsedTaskStates) tid = Some target ->
  task_public_storage sg tasks |--
    tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> target.(curPrio) **
    task_public_storage_without_field sg tasks tid target (TCBCommonField TCBPrio).
Proof.
  intros sg tasks tid target Htarget.
  exact (task_public_storage_split_field sg tasks tid target (TCBCommonField TCBPrio)
    Htarget (tcb_configured_common_field_in _ _ _)).
Qed.

Lemma task_suspend_priority_merge : forall sg tasks tid target,
  tasks.(inUsedTaskStates) tid = Some target ->
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> target.(curPrio) **
  task_public_storage_without_field sg tasks tid target (TCBCommonField TCBPrio) |--
  task_public_storage sg tasks.
Proof.
  intros sg tasks tid target Htarget.
  exact (task_public_storage_merge_field sg tasks tid target (TCBCommonField TCBPrio)
    Htarget (tcb_configured_common_field_in _ _ _)).
Qed.

(** The source reads OSTCBCur and its actual priority after Save on both
    request branches. A source-level acquired-current admission supplies
    the two lookup equalities below; UCOS2_state_inv alone intentionally
    does not assert a live current task. This decomposition contains one
    TCB owner and its inverse returns that owner before opening target. *)
Lemma task_suspend_current_priority_split_merge : forall sg acquired current target caller,
  acquired.(SchedState).(curTaskID) = Some current ->
  acquired.(TskState).(inUsedTaskStates) current = Some target ->
  exists residual,
    (UCOS2_raw_rep sg acquired ** caller |--
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg current **
      tcb_field_address (task_slot_addr sg current) TCBPrio # UChar |-> target.(curPrio) **
      residual) /\
    (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg current **
      tcb_field_address (task_slot_addr sg current) TCBPrio # UChar |-> target.(curPrio) **
      residual |-- UCOS2_raw_rep sg acquired ** caller).
Proof.
  intros sg acquired current target caller Hcurrent Htarget.
  set (rest :=
    (sg.(g_OSRdyGrp) # UChar |->
        encode_ready_grp acquired.(SchedState).(readyList) acquired.(TskState) **
     sched_rows_rep sg acquired.(TskState) acquired.(SchedState).(readyList)
       [0;1;2;3;4;5;6;7] **
     sg.(g_OSPrioCur) # UChar |-> sched_priority_byte acquired.(SchedState).(curSchedPrio) **
     sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte acquired.(SchedState).(highRdyPrio) **
     sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg acquired.(SchedState).(highRdyTid) **
     sg.(g_OSCtxSwCtr) # UInt |-> acquired.(SchedState).(ctxSwCtr) **
     sg.(g_OSRunning) # UChar |-> (if acquired.(SchedState).(isRunning) then 1 else 0)) **
    UCOS2_raw_rep_missing_task_storage_sched sg acquired ** caller).
  exists (task_public_storage_without_field sg acquired.(TskState) current target
    (TCBCommonField TCBPrio) ** rest).
  split.
  - unfold rest, UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
    sep_apply_l_atomic (task_suspend_priority_split sg acquired.(TskState)
      current target Htarget).
    unfold sched_raw_rep, sched_physical_rep.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!.
  - unfold UCOS2_raw_rep, task_shared_rep.
    sepcon_right_assoc.
    sep_apply_r_atomic (task_suspend_priority_merge sg acquired.(TskState)
      current target Htarget).
    unfold rest, UCOS2_raw_rep_missing_task_storage_sched, sched_raw_rep, sched_physical_rep.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Lemma task_suspend_status_merge_updated : forall sg tasks tid target,
  tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |->
    Z.lor (encode_task_status target.(stat)) task_suspend_mask **
  task_public_storage_without_field sg tasks tid target (TCBCommonField TCBStat) |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (task_suspend target)).
Proof.
  intros; apply (task_public_storage_merge_updated_field sg tasks tid target
    (task_suspend target) (TCBCommonField TCBStat)
    (Some (Z.lor (encode_task_status target.(stat)) task_suspend_mask)));
    [apply tcb_configured_common_field_in|apply task_suspend_layout_image_eq].
Qed.

(** The complete configured TCB image differs in exactly the status cell;
    pending kind/result, delay, links, generation, stacks, names, registers
    and every other configured field remain the same protected observation. *)
Lemma task_suspend_layout_image_frame : forall sg target field,
  field <> TCBCommonField TCBStat ->
  task_layout_image sg (task_suspend target) field = task_layout_image sg target field.
Proof.
  intros; rewrite task_suspend_layout_image_eq.
  unfold tcb_layout_write; apply field_update_other; assumption.
Qed.

(** Source-level row/group equations include an already non-ready target.
    The target's effective priority supplies masks; the request may be an
    unrelated alias. No ready-membership precondition is introduced. *)
Lemma task_suspend_bitmap_encoding : forall sg tasks scheduler tid target,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) tid = Some target ->
  task_priority_in_range sg target.(curPrio) ->
  sched_ready_structure sg tasks scheduler ->
  let cleared := Z.land
    (encode_ready_tbl_at_or scheduler.(readyList) tasks (target.(curPrio) / 8))
    (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (target.(curPrio) mod 8))) 8) in
  encode_ready_grp (sched_remove_ready_task scheduler tid).(readyList)
    (glob_task_set_usedtask tasks tid (task_suspend target)) =
    (if Z.eqb cleared 0 then
      Z.land (encode_ready_grp scheduler.(readyList) tasks)
        (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (target.(curPrio) / 8))) 8)
     else encode_ready_grp scheduler.(readyList) tasks) /\
  forall row,
    encode_ready_tbl_at_or (sched_remove_ready_task scheduler tid).(readyList)
      (glob_task_set_usedtask tasks tid (task_suspend target)) row =
    (if Z.eqb row (target.(curPrio) / 8) then
       Z.land (encode_ready_tbl_at_or scheduler.(readyList) tasks row)
         (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (target.(curPrio) mod 8))) 8)
     else encode_ready_tbl_at_or scheduler.(readyList) tasks row).
Proof.
  intros sg tasks scheduler tid target Hsg Hunique Htarget Hpriority Hstructure.
  cbn zeta.
  pose proof (sched_remove_ready_encoding sg tasks scheduler tid target
    Hsg Hunique Htarget Hpriority Hstructure) as Hencoding.
  cbn zeta in Hencoding.
  destruct (sched_encoding_priority_ext
    (sched_remove_ready_task scheduler tid).(readyList)
    (glob_task_set_usedtask tasks tid (task_suspend target)) tasks
    ltac:(intros slot Hmember; simpl; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Htarget; reflexivity|reflexivity]))
    as [Hgroup Hrows].
  rewrite Hgroup; split; [exact (proj1 Hencoding)|].
  intro row; rewrite Hrows; exact (proj2 Hencoding row).
Qed.

Lemma task_suspend_row_values_eq : forall sg tasks scheduler tid target,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) tid = Some target ->
  task_priority_in_range sg target.(curPrio) ->
  sched_ready_structure sg tasks scheduler -> 0 <= target.(curPrio) / 8 < 8 ->
  sched_row_values (glob_task_set_usedtask tasks tid (task_suspend target))
    (sched_remove_ready_task scheduler tid).(readyList) =
  replace_Znth (target.(curPrio) / 8)
    (Z.land (encode_ready_tbl_at_or scheduler.(readyList) tasks (target.(curPrio) / 8))
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (target.(curPrio) mod 8))) 8))
    (sched_row_values tasks scheduler.(readyList)).
Proof.
  intros sg tasks scheduler tid target Hsg Hunique Htarget Hpriority Hstructure Hrow.
  destruct (task_suspend_bitmap_encoding sg tasks scheduler tid target
    Hsg Hunique Htarget Hpriority Hstructure) as [_ Htable].
  unfold sched_row_values; cbn [map].
  rewrite (Htable 0), (Htable 1), (Htable 2), (Htable 3),
    (Htable 4), (Htable 5), (Htable 6), (Htable 7).
  set (row := target.(curPrio) / 8) in *.
  assert (Hcases : row = 0 \/ row = 1 \/ row = 2 \/ row = 3 \/
    row = 4 \/ row = 5 \/ row = 6 \/ row = 7) by lia.
  repeat destruct Hcases as [Hcases|Hcases]; rewrite Hcases; reflexivity.
Qed.

(** Unlike the member-only convenience lemma, this reconstruction also
    covers suspended, waiting or delayed targets which are already absent
    from readyList. It consumes the actual updated cell and array hole. *)
Lemma task_suspend_merge_updated_rows : forall sg tasks scheduler tid target,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) tid = Some target ->
  task_priority_in_range sg target.(curPrio) ->
  sched_ready_structure sg tasks scheduler -> 0 <= target.(curPrio) / 8 < 8 ->
  (sg.(g_OSRdyTbl) + (target.(curPrio) / 8) * sizeof(UCHAR)) # UChar |->
    Z.land (encode_ready_tbl_at_or scheduler.(readyList) tasks (target.(curPrio) / 8))
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (target.(curPrio) mod 8))) 8) **
  UCharArray.missing_i sg.(g_OSRdyTbl) (target.(curPrio) / 8) 0 8
    (sched_row_values tasks scheduler.(readyList)) |--
  sched_rows_rep sg (glob_task_set_usedtask tasks tid (task_suspend target))
    (sched_remove_ready_task scheduler tid).(readyList) [0;1;2;3;4;5;6;7].
Proof.
  intros sg tasks scheduler tid target Hsg Hunique Htarget Hpriority Hstructure Hrow.
  rewrite sched_rows_array_equiv.
  rewrite (task_suspend_row_values_eq sg tasks scheduler tid target
    Hsg Hunique Htarget Hpriority Hstructure Hrow).
  apply sched_rows_merge_updated_array; exact Hrow.
Qed.

Lemma task_suspend_same_call_refl : forall caller,
  task_suspend_same_call caller caller.
Proof. intros [call|view]; simpl; [repeat split|]; reflexivity. Qed.

Lemma task_suspend_same_call_trans : forall first middle last,
  task_suspend_same_call first middle -> task_suspend_same_call middle last ->
  task_suspend_same_call first last.
Proof.
  intros [first|first] [middle|middle] [last|last]; simpl; try tauto;
    unfold task_tcb_init_stack_same_call; intuition congruence.
Qed.

Lemma task_suspend_save_observation_same_call : forall critical sg original returned mask saved before acquired,
  task_suspend_save_observation critical sg original returned mask saved before acquired ->
  task_suspend_same_call returned original /\ interrupt_saved_value mask saved.
Proof. intros critical sg [original|original] [returned|returned]; simpl; tauto. Qed.

Lemma task_suspend_restore_observation_same_call : forall critical sg original returned released current,
  task_suspend_restore_observation critical sg original returned released current ->
  task_suspend_same_call returned original.
Proof. intros critical sg [original|original] [returned|returned]; simpl; tauto. Qed.

Lemma task_suspend_scheduler_clients_same_call : forall critical returned original,
  task_suspend_same_call returned original ->
  task_suspend_scheduler_clients critical original -> task_suspend_scheduler_clients critical returned.
Proof.
  intros critical [returned|returned] [original|original] Hsame Hclients;
    cbn [task_suspend_same_call task_suspend_scheduler_clients] in *; try contradiction.
  - exact Hclients.
  - subst returned; exact Hclients.
Qed.

Lemma task_suspend_task_save_post : forall environment critical saved_local sg call mask saved before,
  task_tcb_init_continuation_save_output environment critical saved_local sg call mask saved before **
    unmap_table_rep sg |--
  task_suspend_save_post environment critical saved_local sg (TaskSuspendTask call) mask saved before.
Proof.
  intros; unfold task_tcb_init_continuation_save_output; Intros returned acquired.
  unfold task_suspend_save_post; Exists (TaskSuspendTask returned) acquired.
  unfold task_suspend_save_observation, task_suspend_masked, task_suspend_view,
    os_sched_execution_view, task_suspend_call_resources, task_tcb_init_stack_context; entailer!; tauto.
Qed.

Lemma task_suspend_disabled_save_post : forall environment critical saved_local sg view mask saved before,
  UCOS2_state_inv sg before ->
  (EX acquired,
    coq_prop (critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
      interrupt_saved_value mask saved) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       view.(os_execution_invocation) view.(os_execution_origin) saved acquired **
     UCOS2_raw_rep sg acquired ** os_execution_view_resources environment.(task_stack_call_external) view)) |--
  task_suspend_save_post environment critical saved_local sg (TaskSuspendDisabled view) mask saved before.
Proof.
  intros environment critical saved_local sg view mask saved before Hvalid.
  Intros acquired; Intros.
  assert (Hinterval : critical_region_interval critical sg view.(os_execution_invocation) before acquired) by tauto.
  sep_apply_l_atomic (critical_region_interval_open_invariant critical sg view.(os_execution_invocation)
    before acquired Hinterval Hvalid).
  unfold task_suspend_save_post; Exists (TaskSuspendDisabled view) acquired.
  unfold task_suspend_save_observation, task_suspend_masked, task_suspend_view,
    task_suspend_call_resources; entailer!.
Qed.

Lemma task_suspend_task_restore_post : forall environment critical saved_local sg call saved released,
  task_tcb_init_continuation_restore_output environment critical saved_local sg call saved released **
    unmap_table_rep sg |--
  task_suspend_restore_post environment critical saved_local sg (TaskSuspendTask call) saved released.
Proof.
  intros; unfold task_tcb_init_continuation_restore_output; Intros returned current.
  unfold task_suspend_restore_post; Exists (TaskSuspendTask returned) current.
  unfold task_suspend_restore_observation, task_suspend_closed; entailer!; tauto.
Qed.

Lemma task_suspend_disabled_restore_post : forall environment critical saved_local sg view saved released,
  UCOS2_state_inv sg released ->
  (EX current,
    coq_prop (critical_region_interval critical sg view.(os_execution_invocation) released current) &&
    (interrupt_platform_running environment.(task_stack_call_platform) view.(os_execution_invocation)
       view.(os_execution_origin) (armv7a_irq_fiq_mask saved) **
     critical_region_outside critical sg view.(os_execution_invocation) current **
     os_execution_view_resources environment.(task_stack_call_external) view)) |--
  task_suspend_restore_post environment critical saved_local sg (TaskSuspendDisabled view) saved released.
Proof.
  intros environment critical saved_local sg view saved released Hvalid.
  Intros current; Intros.
  destruct (critical_region_interval_transports_resources critical sg view.(os_execution_invocation)
    released current H Hvalid) as [Hcurrent _].
  unfold task_suspend_restore_post; Exists (TaskSuspendDisabled view) current.
  unfold task_suspend_restore_observation, task_suspend_closed, sched_disabled_closed; entailer!.
Qed.

Lemma task_suspend_masked_task_input : forall environment critical saved_local sg call saved acquired released,
  task_suspend_masked environment critical saved_local sg (TaskSuspendTask call) saved acquired released --||--
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released **
    unmap_table_rep sg.
Proof.
  intros; unfold task_suspend_masked, task_suspend_view, os_sched_execution_view,
    task_suspend_call_resources, task_tcb_init_continuation_restore_input; split; entailer!.
Qed.

Lemma task_suspend_used_lookup_frame : forall tasks tid target slot node,
  tasks.(inUsedTaskStates) tid = Some target ->
  (glob_task_set_usedtask tasks tid (task_suspend target)).(inUsedTaskStates) slot = Some node ->
  exists old, tasks.(inUsedTaskStates) slot = Some old /\
    old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr).
Proof.
  intros tasks tid target slot node Htarget Hnode.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
    exists target; repeat split; assumption || reflexivity.
  - exists node; repeat split; assumption || reflexivity.
Qed.

Lemma task_suspend_preserves_stack_coverage : forall tasks tid target active,
  tasks.(inUsedTaskStates) tid = Some target -> task_stack_live_coverage tasks active ->
  task_stack_live_coverage (glob_task_set_usedtask tasks tid (task_suspend target)) active.
Proof.
  intros tasks tid target active Htarget Hcoverage.
  eapply task_stack_live_coverage_used_map_frame with (before := tasks);
    [|reflexivity|exact Hcoverage].
  intros slot node Hnode.
  destruct (task_suspend_used_lookup_frame tasks tid target slot node Htarget Hnode)
    as [old [Hold [Hg Hsp]]]; exists old; auto.
Qed.

Lemma task_suspend_continuation_capsules : forall environment saved_local before tid target,
  before.(TskState).(inUsedTaskStates) tid = Some target ->
  task_tcb_init_continuation_capsules environment saved_local before |--
  task_tcb_init_continuation_capsules environment saved_local (task_suspend_state before tid target).
Proof.
  intros environment saved_local before tid target Htarget.
  unfold task_tcb_init_continuation_capsules.
  change (store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) before.(TskState)
      (task_create_continuation_local saved_local)) before.(TskState).(parkedTaskStacks) |--
    store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
      (glob_task_set_usedtask before.(TskState) tid (task_suspend target))
      (task_create_continuation_local saved_local)) before.(TskState).(parkedTaskStacks)).
  apply kernel_saved_continuation_map_reindex.
  intros key payload node Hstack Hnode Hg.
  eapply task_suspend_used_lookup_frame; eassumption.
Qed.

Lemma task_suspend_call_resources_updated : forall environment saved_local sg caller before tid target,
  before.(TskState).(inUsedTaskStates) tid = Some target ->
  task_suspend_call_resources environment saved_local sg caller before |--
  task_suspend_call_resources environment saved_local sg caller (task_suspend_state before tid target).
Proof.
  intros environment saved_local sg [call|view] before tid target Htarget;
    unfold task_suspend_call_resources; [|entailer!].
  Intros.
  sep_apply_l_atomic (task_suspend_continuation_capsules environment saved_local before tid target Htarget).
  entailer!.
  apply task_suspend_preserves_stack_coverage; assumption.
Qed.

Lemma task_suspend_protected_preserves_caller_source : forall sg request priority acquired released caller,
  UCOS2_state_inv sg acquired ->
  task_suspend_protected sg request priority acquired (OS_ERR_NONE, true) released ->
  task_suspend_caller_source sg caller acquired -> task_suspend_caller_source sg caller released.
Proof.
  intros sg request priority acquired released caller Hvalid Hstep Hsource.
  pose proof (task_suspend_protected_preserves_idle_ready sg request priority acquired
    (OS_ERR_NONE, true) released Hvalid) as Hidle.
  destruct (task_suspend_protected_success sg request priority acquired true released Hstep)
    as [tid [target [Htable [Htarget [Hself ->]]]]].
  destruct caller as [call|view]; unfold task_suspend_caller_source in *.
  - destruct Hsource as [[Horigin [Hactive Hcurrent]] [Havailable [Hlayout Hready]]].
    split.
    + split; [exact Horigin|]; split; [|exact Hcurrent].
      eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Htarget|reflexivity|exact Hactive].
    + split; [exact Havailable|]; split; [exact Hlayout|].
      apply Hidle; assumption.
  - exact Hsource.
Qed.

Lemma task_suspend_caller_source_scheduler_pre : forall environment critical saved_local sg caller mask state,
  task_suspend_scheduler_clients critical caller -> task_suspend_caller_source sg caller state ->
  task_suspend_closed environment critical saved_local sg caller mask state |--
  task_suspend_scheduler_pre environment critical saved_local sg caller mask state.
Proof.
  intros environment critical saved_local sg [call|view] mask state Hclients Hsource.
  - unfold task_suspend_closed, task_tcb_init_continuation_save_input, task_create_continuation_input.
    Intros.
    assert (Hvalid : UCOS2_state_inv sg state) by tauto.
    destruct Hsource as [Htask [Havailable [Hlayout Hidle]]].
    assert (Hready : state.(SchedState).(readyList) <> []).
    { destruct Hvalid as [_ [_ [Hsched _]]].
      eapply sched_idle_ready_nonempty; [exact (proj1 Hsched)|exact Hidle]. }
    assert (Hbinding : os_sched_current_storage_binding sg call state).
    { apply kernel_call_task_source_current_storage; assumption. }
    assert (Hparked : state.(TskState).(parkedTaskStacks)
      (task_stack_key call.(os_sched_call_stack)) = None).
    { unfold kernel_call_stack_available in Havailable.
      destruct Htask as [Horigin _]; rewrite Horigin in Havailable; exact Havailable. }
    assert (Hcut : os_sched_call_cut sg call state) by
      (unfold os_sched_call_cut; auto).
    unfold task_suspend_scheduler_pre, os_sched_continuation_call_pre.
    entailer!.
    unfold os_sched_continuation_pre.
    sep_apply_r_atomic (proj1 (task_tcb_init_continuation_save_input_closed_world
      environment critical saved_local sg call mask state)).
    unfold task_tcb_init_continuation_save_input, task_create_continuation_input.
    entailer!.
  - unfold task_suspend_closed, task_suspend_scheduler_pre, task_suspend_caller_source in *;
      entailer!.
Qed.

Lemma task_suspend_argument_error_eq__entry_resolution : forall sg request,
  valid_stable_glob_vars sg ->
  sg.(osKernelConfig).(cfgArgumentChecks) = true ->
  task_suspend_argument_error sg request =
    if Z.eqb request 63 then Some OS_ERR_TASK_SUSPEND_IDLE
    else if (Z.leb 63 request && negb (Z.eqb request 255))%bool
      then Some OS_ERR_PRIO_INVALID else None.
Proof.
  intros sg request Hvalid Hchecks.
  destruct Hvalid as (_ & _ & _ & _ & _ & Hlowest & Hidle & _ & _ & Hself & _).
  unfold task_suspend_argument_error.
  rewrite Hchecks, Hidle, Hlowest, Hself; reflexivity.
Qed.
Lemma task_suspend_request_promotion_eq__entry_resolution : forall request,
  0 <= request <= 255 -> unsigned_last_nbits request 32 = request.
Proof.
  intros request Hrange; apply unsigned_last_nbits_eq; simpl; lia.
Qed.
Lemma task_suspend_resolved_priority_in_range__entry_resolution : forall sg request priority,
  task_suspend_entry_facts sg request ->
  (request = sg.(osPrioSelf) -> task_priority_in_range sg priority) ->
  task_priority_in_range sg (task_suspend_resolved_priority sg request priority).
Proof.
  intros sg request priority (Hvalid & Hchecks & Hrange & Hnone & Halign) Hpriority.
  assert (Hself : sg.(osPrioSelf) = 255) by
    (unfold valid_stable_glob_vars in Hvalid; tauto).
  assert (Hlowest : sg.(osLowestPrio) = 63) by
    (unfold valid_stable_glob_vars in Hvalid; tauto).
  unfold task_suspend_argument_none in Hnone.
  rewrite (task_suspend_argument_error_eq__entry_resolution sg request Hvalid Hchecks) in Hnone.
  unfold task_suspend_resolved_priority; rewrite Hself.
  destruct (Z.eqb request 255) eqn:Hrequest.
  - apply Hpriority; apply Z.eqb_eq in Hrequest; lia.
  - destruct (Z.eqb request 63); [discriminate|].
    simpl in Hnone.
    destruct (Z.leb 63 request) eqn:Hbelow; [discriminate|].
    apply Z.leb_gt in Hbelow.
    unfold task_priority_in_range; rewrite Hlowest; lia.
Qed.
Lemma task_suspend_resolved_priority_in_range__lookup_errors :
  forall sg request state pointer priority residual,
  task_suspend_entry_facts sg request ->
  task_suspend_current_read_view sg request state pointer priority residual ->
  task_priority_in_range sg (task_suspend_resolved_priority sg request priority).
Proof.
  intros sg request state pointer priority residual
    [Hstable [Hchecks [Hrequest [Hnone Haligned]]]] [_ [_ [Hself _]]].
  unfold task_suspend_resolved_priority.
  destruct (Z.eqb request sg.(osPrioSelf)) eqn:Htest.
  - apply Hself; apply Z.eqb_eq; exact Htest.
  - unfold task_suspend_argument_none, task_suspend_argument_error in Hnone.
    rewrite Hchecks in Hnone.
    destruct (Z.eqb request sg.(osTaskIdlePrio)); [discriminate|].
    rewrite Htest in Hnone; simpl in Hnone.
    rewrite Bool.andb_true_r in Hnone.
    destruct (Z.leb sg.(osLowestPrio) request) eqn:Hbound; [discriminate|].
    apply Z.leb_gt in Hbound; unfold task_priority_in_range; lia.
Qed.
Lemma task_suspend_table_task_lookup__lookup_errors : forall sg state selected tid,
  UCOS2_state_inv sg state -> task_priority_in_range sg selected ->
  state.(TskState).(prioTbl) selected = PTTask tid ->
  exists target, state.(TskState).(inUsedTaskStates) tid = Some target /\
    task_slot_in_range sg tid /\ task_priority_in_range sg target.(curPrio).
Proof.
  intros sg state selected tid Hvalid Hrange Htable.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  assert (Hslots : task_mutex_priotbl_consistency sg state.(TskState) state.(EventState)).
  { destruct Hvalid as [_ [_ [_ [_ [Hcross _]]]]]; exact (proj1 Hcross). }
  pose proof (proj1 (proj2 Hslots) selected Hrange) as Hlookup.
  rewrite Htable in Hlookup; destruct Hlookup as [target Htarget].
  exists target; split; [exact Htarget|]; split.
  - apply (proj2 (proj1 (proj1 Htasks) tid)); left; exists target; exact Htarget.
  - unfold task_in_range in Htasks.
    destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
    exact (Hpriority tid target Htarget).
Qed.
Lemma ptr_array_missing_i_in_range__lookup_errors : forall address index lo hi values,
  PtrArray.missing_i address index lo hi values |-- coq_prop (lo <= index < hi).
Proof.
  intros address index lo hi values; revert lo.
  induction values as [|value values IH]; intro lo.
  - rewrite PtrArray.missing_i_empty; entailer!.
  - rewrite PtrArray.missing_i_unfold; Split; Intros.
    + prop_apply PtrArray.seg_length; entailer!; lia.
    + prop_apply IH; entailer!; lia.
Qed.
Lemma task_suspend_restore_post_unscheduled_call_post__lookup_errors :
  forall environment critical saved_local sg caller mask before request frame saved
    acquired_call acquired pointer priority residual released result,
  task_suspend_acquired_facts critical sg caller request mask before saved
    acquired_call acquired pointer priority residual ->
  task_suspend_step sg request priority acquired result 0 released ->
  task_suspend_restore_post environment critical saved_local sg acquired_call saved released ** frame |--
  task_suspend_call_post environment critical saved_local sg caller mask before request frame result.
Proof.
  intros environment critical saved_local sg caller mask before request frame saved
    acquired_call acquired pointer priority residual released result
    [Hentry [_ [_ [Hsave [_ Hread]]]]] [error [Hresult Hstep]].
  assert (Hnone : task_suspend_argument_error sg request = None).
  { destruct Hentry as [_ [_ [_ [Hnone _]]]]; exact Hnone. }
  assert (Hmask : armv7a_irq_fiq_mask saved = mask).
  { destruct caller, acquired_call; cbn [task_suspend_save_observation] in Hsave;
      unfold interrupt_saved_value in Hsave; tauto. }
  unfold task_suspend_call_post; rewrite Hnone.
  unfold task_suspend_restore_post; Intros returned current.
  Exists saved acquired_call acquired pointer priority residual released returned current false error.
  cbn [task_suspend_tail_post]; rewrite Hmask.
  entailer!.
Qed.
Lemma task_priority_y_in_range__fields_bitmap : forall sg priority,
  valid_stable_glob_vars sg -> task_priority_in_range sg priority ->
  0 <= tcb_y_of_prio priority < 8.
Proof.
  intros sg priority Hsg Hpriority.
  assert (Hlowest : sg.(osLowestPrio) = 63) by
    (unfold valid_stable_glob_vars in Hsg; tauto).
  unfold task_priority_in_range in Hpriority.
  unfold tcb_y_of_prio; split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.
Lemma uchar_array_missing_i_replace_equiv__fields_bitmap :
  forall values base index lo hi value,
  lo <= index ->
  UCharArray.missing_i base index lo hi (replace_Znth (index - lo) value values)
    --||-- UCharArray.missing_i base index lo hi values.
Proof.
  induction values as [|head rest IH]; intros base index lo hi value Hindex.
  - unfold UCharArray.missing_i.
    cbn [replace_Znth replace_nth store_array_missing_i_rec].
    reflexivity.
  - destruct (Z.eq_dec index lo) as [->|Hneq].
    + replace (lo - lo) with 0 by lia.
      cbn [replace_Znth replace_nth Z.to_nat UCharArray.missing_i
        store_array_missing_i_rec].
      split; Split; Intros; try lia; Left; entailer!.
    + rewrite replace_Znth_cons by lia.
      unfold UCharArray.missing_i in *.
      cbn [store_array_missing_i_rec].
      replace (index - lo - 1) with (index - (lo + 1)) by lia.
      rewrite (IH base index (lo + 1) hi value ltac:(lia)).
      split; Split; Intros; try lia; Right; entailer!.
Qed.
Lemma os_sched_rows_length_eq__fields_bitmap : forall state,
  Zlength (os_sched_rows state) = 8.
Proof. reflexivity. Qed.
Lemma os_sched_rows_Znth_eq__fields_bitmap : forall state index,
  0 <= index < 8 ->
  Znth index (os_sched_rows state) 0 =
    Ucos2Verify.lib.sched.encode_ready_tbl_at_or
      (readyList (SchedState state)) (TskState state) index.
Proof. intros; apply Ucos2Verify.lib.sched.sched_row_values_Znth; assumption. Qed.
Lemma task_suspend_cleared_row_in_range__fields_bitmap : forall state target,
  0 <= task_suspend_cleared_row state target < 256.
Proof.
  intros state target; unfold task_suspend_cleared_row.
  pose proof (unsigned_Lastnbits_range
    (Z.land (Ucos2Verify.lib.sched.encode_ready_tbl_at_or
      (readyList (SchedState state)) (TskState state) (tcb_y_of_prio (curPrio target)))
      (Z.lnot (tcb_bit_x_of_prio (curPrio target)))) 8 ltac:(lia)) as Hrange.
  rewrite unsigned_last_nbits_land_distr in Hrange by lia.
  rewrite (unsigned_last_nbits_eq
    (Ucos2Verify.lib.sched.encode_ready_tbl_at_or
      (readyList (SchedState state)) (TskState state) (tcb_y_of_prio (curPrio target)))
    8 (Ucos2Verify.lib.sched.encode_ready_tbl_or_in_range _ _ _)) in Hrange.
  exact Hrange.
Qed.

(** Whole-call refinement.  Save/Restore keep the actual returned context:
    same-call does not identify its resource fragments.  The Task effects
    are the checked modular/segmented histories, not a stronger CPU law.
    Disabled callers retain the original interval contract. *)
Definition task_suspend_save_effect environment critical sg original returned mask saved before acquired : Prop :=
  match original, returned with
  | TaskSuspendTask call, TaskSuspendTask next =>
      os_sched_continuation_save_effect environment critical sg call mask saved before next acquired
  | TaskSuspendDisabled view, TaskSuspendDisabled next =>
      next = view /\ critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
      interrupt_saved_value mask saved
  | _, _ => False
  end.

Definition task_suspend_restore_effect environment critical sg original returned released current : Prop :=
  match original, returned with
  | TaskSuspendTask call, TaskSuspendTask next =>
      os_sched_continuation_restore_effect environment critical sg call released next current
  | TaskSuspendDisabled view, TaskSuspendDisabled next =>
      next = view /\ critical_region_interval critical sg view.(os_execution_invocation) released current
  | _, _ => False
  end.

Definition task_suspend_save_history_post environment critical saved_local sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_suspend_save_observation critical sg original returned mask saved before acquired /\
      task_suspend_save_effect environment critical sg original returned mask saved before acquired) &&
    task_suspend_masked environment critical saved_local sg returned saved acquired acquired.

Definition task_suspend_restore_history_post environment critical saved_local sg original saved released : Assertion :=
  EX returned current,
    coq_prop (task_suspend_restore_observation critical sg original returned released current /\
      task_suspend_restore_effect environment critical sg original returned released current) &&
    task_suspend_closed environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current.

Lemma task_suspend_save_history_post_weaken : forall environment critical saved_local sg caller mask saved before,
  task_suspend_save_history_post environment critical saved_local sg caller mask saved before |--
  task_suspend_save_post environment critical saved_local sg caller mask saved before.
Proof.
  intros; unfold task_suspend_save_history_post, task_suspend_save_post.
  Intros returned acquired; Exists returned acquired; entailer!; tauto.
Qed.

Lemma task_suspend_restore_history_post_weaken : forall environment critical saved_local sg caller saved released,
  task_suspend_restore_history_post environment critical saved_local sg caller saved released |--
  task_suspend_restore_post environment critical saved_local sg caller saved released.
Proof.
  intros; unfold task_suspend_restore_history_post, task_suspend_restore_post.
  Intros returned current; Exists returned current; entailer!; tauto.
Qed.

Lemma task_suspend_task_save_history_post : forall environment critical saved_local sg call mask saved before,
  os_sched_continuation_save_history_output environment critical saved_local sg call mask saved before **
    unmap_table_rep sg |--
  task_suspend_save_history_post environment critical saved_local sg (TaskSuspendTask call) mask saved before.
Proof.
  intros; unfold os_sched_continuation_save_history_output; Intros returned acquired.
  unfold task_suspend_save_history_post; Exists (TaskSuspendTask returned) acquired.
  unfold task_suspend_save_observation, task_suspend_save_effect, task_suspend_masked,
    task_suspend_view, os_sched_execution_view, task_suspend_call_resources,
    task_tcb_init_stack_context; entailer!; tauto.
Qed.

Lemma task_suspend_task_restore_history_post : forall environment critical saved_local sg call saved released,
  os_sched_continuation_restore_history_output environment critical saved_local sg call saved released **
    unmap_table_rep sg |--
  task_suspend_restore_history_post environment critical saved_local sg (TaskSuspendTask call) saved released.
Proof.
  intros; unfold os_sched_continuation_restore_history_output; Intros returned current.
  unfold task_suspend_restore_history_post; Exists (TaskSuspendTask returned) current.
  unfold task_suspend_restore_observation, task_suspend_restore_effect,
    task_suspend_closed; entailer!; tauto.
Qed.

Lemma task_suspend_disabled_save_history_post : forall environment critical saved_local sg view mask saved before,
  task_suspend_save_post environment critical saved_local sg (TaskSuspendDisabled view) mask saved before |--
  task_suspend_save_history_post environment critical saved_local sg (TaskSuspendDisabled view) mask saved before.
Proof.
  intros; unfold task_suspend_save_post; Intros returned acquired.
  destruct returned as [call|next]; cbn [task_suspend_save_observation] in *; [entailer!|].
  unfold task_suspend_save_history_post; Exists (TaskSuspendDisabled next) acquired.
  cbn [task_suspend_save_observation task_suspend_save_effect]; entailer!.
Qed.

Lemma task_suspend_disabled_restore_history_post : forall environment critical saved_local sg view saved released,
  task_suspend_restore_post environment critical saved_local sg (TaskSuspendDisabled view) saved released |--
  task_suspend_restore_history_post environment critical saved_local sg (TaskSuspendDisabled view) saved released.
Proof.
  intros; unfold task_suspend_restore_post; Intros returned current.
  destruct returned as [call|next]; cbn [task_suspend_restore_observation] in *; [entailer!|].
  unfold task_suspend_restore_history_post; Exists (TaskSuspendDisabled next) current.
  cbn [task_suspend_restore_observation task_suspend_restore_effect]; entailer!.
Qed.

Definition task_suspend_save_program environment critical sg original mask
  : program UCOS2_Verify_State (TaskSuspendCaller * Z) :=
  fun before result acquired => task_suspend_save_effect environment critical sg
    original (fst result) mask (snd result) before acquired.

Definition task_suspend_restore_program environment critical sg original
  : program UCOS2_Verify_State TaskSuspendCaller :=
  fun released returned current =>
    task_suspend_restore_effect environment critical sg original returned released current.

(** This is the protected source read, including readable free-current
    images.  No current live-task classification is substituted for it. *)
Definition task_suspend_current_read_program sg request : program UCOS2_Verify_State Z :=
  fun acquired priority after =>
    (exists pointer residual, task_suspend_current_read_view sg request acquired pointer priority residual) /\
    after = acquired.

Definition task_suspend_prefix_program environment critical sg original mask request
  : program UCOS2_Verify_State ((Z * bool) * TaskSuspendCaller) :=
  match task_suspend_argument_error sg request with
  | Some error => StateRelMonad.ret ((encode_os_err_code error, false), original)
  | None => StateRelMonad.bind (task_suspend_save_program environment critical sg original mask)
      (fun entered => StateRelMonad.bind (task_suspend_current_read_program sg request)
        (fun priority => StateRelMonad.bind (task_suspend_protected sg request priority)
          (fun result => StateRelMonad.bind
            (task_suspend_restore_program environment critical sg (fst entered))
            (fun returned => StateRelMonad.ret ((encode_os_err_code (fst result), snd result), returned)))))
  end.

Definition task_suspend_schedule_program environment critical sg caller mask
  : program UCOS2_Verify_State TaskSuspendCaller :=
  match caller with
  | TaskSuspendTask call =>
      StateRelMonad.bind (os_sched_continuation_program environment critical sg call mask)
        (fun returned => StateRelMonad.ret (TaskSuspendTask returned))
  | TaskSuspendDisabled view =>
      StateRelMonad.bind (task_suspend_save_program environment critical sg (TaskSuspendDisabled view) mask)
        (fun entered => StateRelMonad.bind
          (update (fun before after => sched_disabled_protected_identity before /\ after = before))
          (fun _ => task_suspend_restore_program environment critical sg (fst entered)))
  end.

Definition task_suspend_tail_program environment critical sg mask
  (result : (Z * bool) * TaskSuspendCaller) : program UCOS2_Verify_State Z :=
  if snd (fst result) then
    StateRelMonad.bind (task_suspend_schedule_program environment critical sg (snd result) mask)
      (fun _ => StateRelMonad.ret (fst (fst result)))
  else StateRelMonad.ret (fst (fst result)).

Definition task_suspend_program environment critical sg original mask request
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind (task_suspend_prefix_program environment critical sg original mask request)
    (task_suspend_tail_program environment critical sg mask).

Definition task_suspend_safe environment critical sg original mask request before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (task_suspend_program environment critical sg original mask request) X.

Definition task_suspend_scheduler_safe environment critical sg caller mask before result
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (StateRelMonad.bind (task_suspend_schedule_program environment critical sg caller mask)
      (fun _ => StateRelMonad.ret result)) X.

Definition task_suspend_return_safe before result (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before) (StateRelMonad.ret result) X.

Lemma task_suspend_history_prefix_program :
  forall environment critical sg original mask request before saved active acquired pointer priority residual
    error scheduled released returned current,
  task_suspend_argument_error sg request = None ->
  task_suspend_save_effect environment critical sg original active mask saved before acquired ->
  task_suspend_current_read_view sg request acquired pointer priority residual ->
  task_suspend_protected sg request priority acquired (error, scheduled) released ->
  task_suspend_restore_effect environment critical sg active returned released current ->
  task_suspend_prefix_program environment critical sg original mask request
    before ((encode_os_err_code error, scheduled), returned) current.
Proof.
  intros environment critical sg original mask request before saved active acquired pointer priority residual
    error scheduled released returned current Hnone Hsave Hread Hprotected Hrestore.
  unfold task_suspend_prefix_program; rewrite Hnone.
  exists (active, saved), acquired; split; [exact Hsave|].
  exists priority, acquired; split.
  - split; [exists pointer, residual; exact Hread|reflexivity].
  - exists (error, scheduled), released; split; [exact Hprotected|].
    exists returned, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma task_suspend_prefix_safe_continuation :
  forall environment critical sg original mask request before result scheduled returned current X,
  task_suspend_prefix_program environment critical sg original mask request before ((result, scheduled), returned) current ->
  task_suspend_safe environment critical sg original mask request before X ->
  safeExec (fun state => state = current)
    (task_suspend_tail_program environment critical sg mask ((result, scheduled), returned)) X.
Proof.
  intros environment critical sg original mask request before result scheduled returned current X Hprefix Hsafe.
  eapply (highstepbind_derive
    (task_suspend_prefix_program environment critical sg original mask request)
    (task_suspend_tail_program environment critical sg mask)
    (fun state => state = before) ((result, scheduled), returned) (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma task_suspend_argument_safe_return :
  forall environment critical sg original mask request before error X,
  task_suspend_argument_error sg request = Some error ->
  task_suspend_safe environment critical sg original mask request before X ->
  safeExec (fun state => state = before) (StateRelMonad.ret (encode_os_err_code error)) X.
Proof.
  intros environment critical sg original mask request before error X Herror Hsafe.
  apply (task_suspend_prefix_safe_continuation environment critical sg original mask request before
    (encode_os_err_code error) false original before X); [|exact Hsafe].
  unfold task_suspend_prefix_program; rewrite Herror; split; reflexivity.
Qed.

Lemma task_suspend_step_safe_continuation :
  forall environment critical sg original mask request before saved active acquired pointer priority residual
    result self released returned current X,
  task_suspend_acquired_facts critical sg original request mask before saved active acquired pointer priority residual ->
  task_suspend_save_effect environment critical sg original active mask saved before acquired ->
  task_suspend_step sg request priority acquired result self released ->
  task_suspend_restore_effect environment critical sg active returned released current ->
  task_suspend_safe environment critical sg original mask request before X ->
  (self = 1 -> task_suspend_scheduler_safe environment critical sg returned mask current result X) /\
  (self <> 1 -> task_suspend_return_safe current result X).
Proof.
  intros environment critical sg original mask request before saved active acquired pointer priority residual
    result self released returned current X Hfacts Hsave [error [-> Hstep]] Hrestore Hsafe.
  destruct Hfacts as [Hentry [_ [_ [_ [_ Hread]]]]].
  destruct Hentry as [_ [_ [_ [Hnone _]]]].
  pose proof (task_suspend_history_prefix_program environment critical sg original mask request before saved
    active acquired pointer priority residual error (Z.eqb self 1) released returned current
    Hnone Hsave Hread Hstep Hrestore) as Hprefix.
  pose proof (task_suspend_prefix_safe_continuation environment critical sg original mask request before
    (encode_os_err_code error) (Z.eqb self 1) returned current X Hprefix Hsafe) as Htail.
  cbn [task_suspend_tail_program fst snd] in Htail.
  split; intro Hself.
  - subst self; exact Htail.
  - rewrite (proj2 (Z.eqb_neq _ _) Hself) in Htail; exact Htail.
Qed.

Definition task_suspend_scheduler_history_post environment critical saved_local sg caller mask before : Assertion :=
  match caller with
  | TaskSuspendTask call => os_sched_continuation_history_return_post environment critical saved_local
      kernel_program_inv sg call mask before
  | TaskSuspendDisabled view => sched_disabled_contextual_post environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical sg view mask before
  end.

(** The two resource conjuncts describe the same heap: X is attached to
    the actual returned context/state, and the entire old post is retained. *)
Definition task_suspend_scheduler_refined_post environment critical saved_local sg caller mask before result
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (task_suspend_schedule_program environment critical sg caller mask before returned current /\
      safeExec (fun state => state = current) (StateRelMonad.ret result) X) &&
    (task_suspend_closed environment critical saved_local sg returned mask current &&
     task_suspend_scheduler_post environment critical saved_local sg caller mask before).

Lemma task_suspend_scheduler_result_safe_return :
  forall environment critical sg caller mask before returned current result X,
  task_suspend_schedule_program environment critical sg caller mask before returned current ->
  task_suspend_scheduler_safe environment critical sg caller mask before result X ->
  safeExec (fun state => state = current) (StateRelMonad.ret result) X.
Proof.
  intros environment critical sg caller mask before returned current result X Hprogram Hsafe.
  eapply (highstepbind_derive (task_suspend_schedule_program environment critical sg caller mask)
    (fun _ => StateRelMonad.ret result) (fun state => state = before) returned (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma task_suspend_scheduler_history_post_safe_return :
  forall environment critical saved_local sg caller mask before result X,
  task_suspend_scheduler_safe environment critical sg caller mask before result X ->
  task_suspend_scheduler_history_post environment critical saved_local sg caller mask before |--
  task_suspend_scheduler_refined_post environment critical saved_local sg caller mask before result X.
Proof.
  intros environment critical saved_local sg [call|view] mask before result X Hsafe;
    unfold task_suspend_scheduler_refined_post; cbn [task_suspend_scheduler_history_post].
  - unfold os_sched_continuation_history_return_post at 1; Intros returned current.
    assert (Hprogram : task_suspend_schedule_program environment critical sg
      (TaskSuspendTask call) mask before (TaskSuspendTask returned) current).
    { cbn [task_suspend_schedule_program]; exists returned, current; split.
      - apply os_sched_continuation_program_iff; tauto.
      - split; reflexivity. }
    pose proof (task_suspend_scheduler_result_safe_return environment critical sg
      (TaskSuspendTask call) mask before (TaskSuspendTask returned) current result X Hprogram Hsafe) as Hreturn.
    Exists (TaskSuspendTask returned) current.
    apply _derivable1_andp_intros; [entailer!|].
    apply _derivable1_andp_intros.
    + cbn [task_suspend_closed]; rewrite task_tcb_init_continuation_save_input_closed_world; entailer!.
    + cbn [task_suspend_scheduler_post]; unfold os_sched_continuation_return_post.
      Exists returned current; entailer!; tauto.
  - unfold sched_disabled_contextual_post at 1; Intros saved acquired current.
    assert (Hprogram : task_suspend_schedule_program environment critical sg
      (TaskSuspendDisabled view) mask before (TaskSuspendDisabled view) current).
    { cbn [task_suspend_schedule_program].
      exists (TaskSuspendDisabled view, saved), acquired; split.
      - cbn [task_suspend_save_program task_suspend_save_effect fst snd]; split; [reflexivity|tauto].
      - exists tt, acquired; split.
        + split; [tauto|reflexivity].
        + cbn [task_suspend_restore_program task_suspend_restore_effect fst]; split; [reflexivity|tauto]. }
    pose proof (task_suspend_scheduler_result_safe_return environment critical sg
      (TaskSuspendDisabled view) mask before (TaskSuspendDisabled view) current result X Hprogram Hsafe) as Hreturn.
    Exists (TaskSuspendDisabled view) current.
    apply _derivable1_andp_intros; [entailer!|].
    apply _derivable1_andp_intros.
    + cbn [task_suspend_closed]; entailer!; tauto.
    + cbn [task_suspend_scheduler_post]; unfold sched_disabled_contextual_post.
      Exists saved acquired current; entailer!.
Qed.

Definition task_suspend_refined_tail_post environment critical saved_local sg caller mask before (scheduled : bool) result
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  if scheduled then task_suspend_scheduler_refined_post environment critical saved_local sg caller mask before result X
  else coq_prop (safeExec (fun state => state = before) (StateRelMonad.ret result) X) &&
    task_suspend_closed environment critical saved_local sg caller mask before.

Definition task_suspend_refined_call_post environment critical saved_local sg original mask before request
  (frame : Assertion) (result : Z) (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  match task_suspend_argument_error sg request with
  | Some error => coq_prop (result = encode_os_err_code error /\
      safeExec (fun state => state = before) (StateRelMonad.ret result) X) && frame
  | None => EX saved acquired_call acquired pointer priority residual released checkpoint_call checkpoint scheduled error,
      coq_prop (task_suspend_save_observation critical sg original acquired_call mask saved before acquired /\
        task_suspend_current_read_view sg request acquired pointer priority residual /\
        result = encode_os_err_code error /\
        task_suspend_protected sg request priority acquired (error, scheduled) released /\
        task_suspend_restore_observation critical sg acquired_call checkpoint_call released checkpoint) &&
      (task_suspend_refined_tail_post environment critical saved_local sg checkpoint_call mask checkpoint scheduled result X ** frame)
  end.

Lemma task_suspend_refined_tail_post_weaken :
  forall environment critical saved_local sg caller mask before scheduled result X,
  task_suspend_refined_tail_post environment critical saved_local sg caller mask before scheduled result X |--
  task_suspend_tail_post environment critical saved_local sg caller mask before scheduled.
Proof.
  intros; destruct scheduled; cbn [task_suspend_refined_tail_post task_suspend_tail_post].
  - unfold task_suspend_scheduler_refined_post; Intros returned current; entailer!.
  - entailer!.
Qed.

Lemma task_suspend_refined_call_post_weaken :
  forall environment critical saved_local sg caller mask before request frame result X,
  task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame result X |--
  task_suspend_call_post environment critical saved_local sg caller mask before request frame result.
Proof.
  intros; unfold task_suspend_refined_call_post, task_suspend_call_post.
  destruct (task_suspend_argument_error sg request); [entailer!; tauto|].
  Intros saved active acquired pointer priority residual released returned current scheduled error.
  Exists saved active acquired pointer priority residual released returned current scheduled error.
  sep_apply_l_atomic (task_suspend_refined_tail_post_weaken environment critical saved_local sg
    returned mask current scheduled result X); entailer!.
Qed.

Lemma task_suspend_restore_history_post_unscheduled_call_post :
  forall environment critical saved_local sg caller request mask before saved acquired_call acquired
    pointer priority residual released result frame X,
  task_suspend_acquired_facts critical sg caller request mask before saved
    acquired_call acquired pointer priority residual ->
  task_suspend_save_effect environment critical sg caller acquired_call mask saved before acquired ->
  task_suspend_step sg request priority acquired result 0 released ->
  task_suspend_safe environment critical sg caller mask request before X ->
  task_suspend_restore_history_post environment critical saved_local sg acquired_call saved released ** frame |--
  task_suspend_refined_call_post environment critical saved_local sg caller mask before request frame result X.
Proof.
  intros environment critical saved_local sg caller request mask before saved acquired_call acquired
    pointer priority residual released result frame X Hfacts Heffect [error [-> Hstep]] Hsafe.
  destruct Hfacts as [Hentry [_ [_ [Hsave [_ Hread]]]]].
  destruct Hentry as [_ [_ [_ [Hnone _]]]].
  destruct (task_suspend_save_observation_same_call _ _ _ _ _ _ _ _ Hsave) as [_ [_ Hmask]].
  unfold task_suspend_restore_history_post; Intros returned current.
  assert (Hprefix : task_suspend_prefix_program environment critical sg caller mask request
    before ((encode_os_err_code error, false), returned) current).
  { eapply task_suspend_history_prefix_program; eauto; tauto. }
  pose proof (task_suspend_prefix_safe_continuation environment critical sg caller mask request before
    (encode_os_err_code error) false returned current X Hprefix Hsafe) as Hreturn.
  unfold task_suspend_refined_call_post; rewrite Hnone.
  Exists saved acquired_call acquired pointer priority residual released returned current false error.
  cbn [task_suspend_refined_tail_post]; rewrite Hmask; entailer!; tauto.
Qed.
