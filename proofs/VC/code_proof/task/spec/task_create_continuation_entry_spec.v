Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Registration consumes a real current execution owner and the full
    current world. It changes only the existing invocation ledger; the
    live-task map, parked payloads, and every descriptor's local owner are
    preserved. The source stage is supplied by one of the actual entry
    producers below and retained beside the public precondition.

    This does not infer current/readiness from the CPU resource. No
    priority, ISR, or scheduler-lock error branch is removed. *)
Lemma task_create_continuation_register_entry_pre :
  forall environment critical saved_local sg args name call mask state
    region task_return lower old_frame upper,
  task_create_call_stage call state ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) sg (task_stack_call_active_key call)
    call mask state ** task_stack_storage region (lower ++ old_frame ++ upper) |--
  let registered := replace_TskS
    (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state in
  coq_prop (task_create_source_entry sg args name call registered) &&
    task_create_continuation_pre environment critical saved_local sg region args task_return
      lower old_frame upper name call mask registered.
Proof.
  intros environment critical saved_local sg args name call mask state
    region task_return lower old_frame upper Hstage Hinv Hname Hbuffer.
  cbv zeta.
  set (registered := replace_TskS
    (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state).
  unfold kernel_continuation_call_closed, kernel_continuation_inv.
  rewrite kernel_program_inv_split_unmap; Intros.
  assert (Hobserve : UCOS2_inv sg state |--
    coq_prop (UCOS2_state_inv sg state) && UCOS2_inv sg state)
    by (unfold UCOS2_inv; entailer!).
  sep_apply_l_atomic Hobserve; Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by assumption.
  assert (Hcovered : task_stack_live_coverage state.(TskState) (task_stack_call_active_key call))
    by assumption.
  assert (Hlive : task_invocation_origin_live state.(TskState) call.(os_sched_call_origin))
    by (apply task_create_call_origin_live; exact (proj1 Hstage)).
  pose proof (task_create_registered_stack_entry sg args name state call Hvalid
    (proj1 Hstage) Hinv Hname) as Hentry.
  fold registered in Hentry.
  assert (Hregistered_stage : task_create_call_stage call registered) by exact Hstage.
  assert (Hsource : task_create_source_entry sg args name call registered)
    by exact (conj Hentry Hregistered_stage).
  assert (Hcoverage : task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call))
    by exact Hcovered.
  assert (Hmap :
    store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
        state.(TskState) (task_create_continuation_local saved_local))
      state.(TskState).(parkedTaskStacks) |--
    store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
        registered.(TskState) (task_create_continuation_local saved_local))
      registered.(TskState).(parkedTaskStacks)).
  { apply kernel_saved_continuation_map_used_map_eq; reflexivity. }
  sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state call.(os_sched_call_origin) Hlive).
  fold registered.
  sep_apply_l_atomic Hmap.
  eapply derivable1_trans with (y :=
    kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
      (task_create_continuation_local saved_local) sg (task_stack_call_active_key call)
      call mask registered ** task_stack_storage region (lower ++ old_frame ++ upper)).
  - unfold kernel_continuation_call_closed, kernel_continuation_inv.
    rewrite kernel_program_inv_split_unmap; entailer!.
  - sep_apply_l_atomic (proj2 (task_create_continuation_input_closed_world
      environment critical saved_local sg call mask registered)).
    unfold task_create_continuation_pre; entailer!.
Qed.

(** A boot call uses the startup CPU/stack owner already supplied by its
    platform contract. OSRunning=false determines its actual source
    stage. Registration and the caller's real buffer now produce the
    current public pre directly, with the same generic parked map. *)
Lemma task_create_continuation_boot_entry_pre :
  forall environment critical saved_local sg args name call mask state
    region task_return lower old_frame upper,
  call.(os_sched_call_origin) = BootInvocation ->
  state.(SchedState).(isRunning) = false ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) sg None call mask state **
    task_stack_storage region (lower ++ old_frame ++ upper) |--
  let registered := replace_TskS (task_begin_invocation BootInvocation state.(TskState)) state in
  coq_prop (task_create_source_entry sg args name call registered) &&
    task_create_continuation_pre environment critical saved_local sg region args task_return
      lower old_frame upper name call mask registered.
Proof.
  intros environment critical saved_local sg args name call mask state
    region task_return lower old_frame upper Horigin Hrunning Hinv Hname Hbuffer.
  assert (Hstage : task_create_call_stage call state).
  { unfold task_create_call_stage; rewrite Horigin; split; [exact Hrunning|exact I]. }
  pose proof (task_create_continuation_register_entry_pre environment critical saved_local
    sg args name call mask state region task_return lower old_frame upper
    Hstage Hinv Hname Hbuffer) as Hentry.
  unfold task_stack_call_active_key in Hentry; rewrite Horigin in Hentry.
  exact Hentry.
Qed.

(** Initial None entry follows the actual TaskRestore endpoint. The
    selector/install supplies current, generation and readiness; the take
    supplies absence. The existing first-call ABI only converts the
    already restored execution owner. It is not applied to a completed
    API or to an arbitrary Some continuation. All other saved locals are
    retained in the same map and the caller buffer remains disjoint.

    The explicit pure inputs are current selector/take observations. This
    consumer does not assert that every foreign source path has already
    been connected to the generic-map install producer. *)
Lemma task_create_continuation_selected_initial_entry_pre :
  forall environment
    (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    critical saved_local sg args name selected node state
    region task_return lower old_frame upper,
  state.(SchedState).(isRunning) = true ->
  armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0
    selected.(armv7a_continuation_fragments) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key selected.(armv7a_continuation_stack)) = None ->
  sched_current_ready_at state.(TskState) state.(SchedState)
    selected.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  armv7a_task_restored_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) selected **
  kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) sg
    (Some (task_stack_key selected.(armv7a_continuation_stack))) state **
  task_stack_storage region (lower ++ old_frame ++ upper) |--
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  let registered := armv7a_initial_call_registered selected state in
  coq_prop (task_create_source_entry sg args name call registered) &&
    task_create_continuation_pre environment critical saved_local sg region args task_return
      lower old_frame upper name call
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) registered.
Proof.
  intros environment entry critical saved_local sg args name selected node state
    region task_return lower old_frame upper Hrunning Hbinding Hfragments Habsent
    Hready Hgeneration Hname Hbuffer.
  cbv zeta.
  set (call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments)).
  assert (Hcurrent : task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { split; [exact (proj1 (proj2 Hready))|].
    exists node; split; [exact (proj1 Hready)|exact Hgeneration]. }
  assert (Hstage : task_create_call_stage call state).
  { unfold task_create_call_stage, call, armv7a_initial_call; cbn [os_sched_call_origin os_sched_call_stack].
    split; [exact (conj Hrunning Hcurrent)|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Habsent|].
    intros; exists node; split; assumption. }
  pose proof (armv7a_initial_frame_no_call selected Hbinding) as Hnone.
  unfold armv7a_task_restored_execution; rewrite Hnone.
  sep_apply_l_atomic (armv7a_initial_call_resources _ _ _
    environment.(task_stack_call_continuations) entry selected
    state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) Hbinding Hfragments).
  eapply derivable1_trans with (y :=
    kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
      (task_create_continuation_local saved_local) sg (task_stack_call_active_key call)
      call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) state **
    task_stack_storage region (lower ++ old_frame ++ upper)).
  - unfold kernel_continuation_call_closed, kernel_call_execution_owned, os_sched_context_resources,
      task_stack_call_active_key, call, armv7a_initial_call; entailer!.
  - exact (task_create_continuation_register_entry_pre environment critical saved_local sg args name
      call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) state
      region task_return lower old_frame upper Hstage eq_refl Hname Hbuffer).
Qed.

(** A later API uses the existing completed-return / next-entry source
    event. Its actual CPU-owner exchange frames the full generic map and
    real buffer, then the same registration producer supplies the current
    public pre. The observed boundary preserves heap bytes.

    [Hstage] concerns the preceding API's actual returned state. The
    current TaskCreate post alone does not provide it; its source return
    proof must do so. Locked/self-suspended and ISR stages keep their
    original conditional readiness, with no promise of a future return. *)
Lemma task_create_continuation_sequential_entry_pre :
  forall environment
    (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform))
    critical saved_local sg args name previous mask state
    region task_return lower old_frame upper before after (frame : Assertion),
  task_create_call_stage previous state ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  kernel_sequential_call_source boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) before after ->
  (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
     (task_create_continuation_local saved_local) sg (task_stack_call_active_key previous)
     previous mask state ** task_stack_storage region (lower ++ old_frame ++ upper) ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := replace_TskS
    (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (coq_prop (task_create_source_entry sg args name call registered) &&
    (task_create_continuation_pre environment critical saved_local sg region args task_return
       lower old_frame upper name call mask registered ** frame)) after.
Proof.
  intros environment boundary critical saved_local sg args name previous mask state
    region task_return lower old_frame upper before after frame
    Hstage Hname Hbuffer Hsource Hbefore call registered.
  assert (Hopen :
    kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
      (task_create_continuation_local saved_local) sg (task_stack_call_active_key previous)
      previous mask state ** task_stack_storage region (lower ++ old_frame ++ upper) ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) previous mask **
    (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_inv
       (task_create_continuation_local saved_local) sg (task_stack_call_active_key previous) state **
     task_stack_storage region (lower ++ old_frame ++ upper) ** frame)).
  { unfold kernel_continuation_call_closed; entailer!. }
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _
    Hsource (Hopen before Hbefore)) as [Hmemory Hreturned].
  fold call in Hreturned; split; [exact Hmemory|].
  match type of Hreturned with ?P after => match goal with |- ?Q after =>
    assert (Hregister : P |-- Q) end end.
  { eapply derivable1_trans with (y :=
      kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
        (task_create_continuation_local saved_local) sg (task_stack_call_active_key call)
        call mask state ** task_stack_storage region (lower ++ old_frame ++ upper) ** frame).
    - unfold kernel_continuation_call_closed.
      change (task_stack_call_active_key call) with (task_stack_call_active_key previous); entailer!.
    - sep_apply_l_atomic (task_create_continuation_register_entry_pre
        environment critical saved_local sg args name call mask state
        region task_return lower old_frame upper Hstage eq_refl Hname Hbuffer).
      cbv zeta; Intros; entailer!. }
  exact (Hregister after Hreturned).
Qed.
