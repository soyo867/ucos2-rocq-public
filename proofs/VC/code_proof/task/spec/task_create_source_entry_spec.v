Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The source API stage, separate from global validity and CPU authority.
    Boot and the ISR early-error path remain supported. Readiness is used
    only when BOTH source scheduling guards are enabled. A locked task
    can suspend itself, return from the suppressed scheduler, and call
    Create while its current TCB is no longer ready. Absence belongs to the actual taken running stack,
    not to the coverage exemption. No Sem-specific non-idle/wait condition
    is imposed on TaskCreate. *)
Definition task_create_call_stage call state : Prop :=
  task_create_call_origin state call.(os_sched_call_origin) /\
  match call.(os_sched_call_origin) with
  | BootInvocation => True
  | RunningInvocation slot generation =>
      slot = call.(os_sched_call_stack).(stackLeaseSlot) /\
      generation = call.(os_sched_call_stack).(stackLeaseGeneration) /\
      state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
      (os_sched_selection_enabled state = true ->
       exists node, sched_current_ready_at state.(TskState) state.(SchedState) slot node /\
         node.(taskGeneration) = generation)
  end.

Definition task_create_source_entry sg args name call state : Prop :=
  task_create_stack_entry sg args name call state /\ task_create_call_stage call state.

(** Ordinary entry identity is already established by registration and
    the selected/sequential entry producers below. This projection does
    not assert readiness at a later checkpoint or exclude Boot/ISR calls. *)
Lemma task_create_source_entry_running_source : forall sg args name call state,
  task_create_source_entry sg args name call state ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_task_source call state.
Proof.
  intros sg args name call state [[Hvalid [Hactive Hrest]] [Horigin Hstage]] Hrunning.
  destruct call.(os_sched_call_origin) as [|slot generation] eqn:Hcall.
  - unfold task_create_call_origin in Horigin; congruence.
  - destruct Hstage as [Hslot [Hgeneration Hrest_stage]].
    subst slot generation.
    unfold kernel_call_task_source; rewrite Hcall.
    split; [reflexivity|]. split; [exact Hactive|].
    exact (proj1 (proj2 Horigin)).
Qed.

(** The existing fresh-invocation registration establishes the actual
    unreserved Create entry. It does not establish running/current/ready;
    those come from the source producers below. No C field is changed. *)
Lemma task_create_registered_stack_entry : forall sg args name state call,
  UCOS2_state_inv sg state ->
  task_create_call_origin state call.(os_sched_call_origin) ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  task_create_stack_entry sg args name call
    (replace_TskS (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state).
Proof.
  intros sg args name state call Hvalid Horigin Hinv Hname.
  assert (Hlive : task_invocation_origin_live state.(TskState) call.(os_sched_call_origin))
    by (apply task_create_call_origin_live; exact Horigin).
  unfold task_create_stack_entry; split.
  - apply UCOS2_begin_task_invocation_preserves_validity; assumption.
  - split.
    + rewrite Hinv; apply task_begin_invocation_active; exact Hlive.
    + split; [|exact Hname].
      unfold task_create_stack_no_reservation; intros priority entry Hentry.
      rewrite Hinv; eapply task_begin_invocation_unreserved with (sg := sg); [| |exact Hentry].
      all: pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto.
Qed.

(** Boot's explicit startup CPU/stack owner is consumed at its current
    fresh invocation number. The existing initializer supplies the owned
    kernel_stack_inv (possibly with active=None); registration only updates
    the already existing ghost call ledger. This is not a BSP proof or a
    new CPU axiom. The boot call's real stack remains externally supplied. *)
Lemma task_create_boot_entry_world : forall environment sg args name call mask state,
  call.(os_sched_call_origin) = BootInvocation ->
  state.(SchedState).(isRunning) = false ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg None
    call mask state |--
  let registered := replace_TskS (task_begin_invocation BootInvocation state.(TskState)) state in
  coq_prop (task_create_source_entry sg args name call registered) &&
    kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg None
      call mask registered.
Proof.
  intros environment sg args name call mask state Horigin Hrunning Hinv Hname.
  cbv zeta.
  set (registered := replace_TskS (task_begin_invocation BootInvocation state.(TskState)) state).
  unfold kernel_stack_call_closed, kernel_stack_inv; rewrite !kernel_program_inv_split_unmap.
  Intros.
  assert (Hobserve : UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) && UCOS2_inv sg state)
    by (unfold UCOS2_inv; entailer!).
  sep_apply_l_atomic Hobserve; Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by assumption.
  assert (Hcall_origin : task_create_call_origin state call.(os_sched_call_origin)).
  { rewrite Horigin; exact Hrunning. }
  pose proof (task_create_registered_stack_entry sg args name state call Hvalid Hcall_origin Hinv Hname)
    as Hentry; rewrite Horigin in Hentry; fold registered in Hentry.
  assert (Hsource : task_create_source_entry sg args name call registered).
  { unfold task_create_source_entry, task_create_call_stage; split; [exact Hentry|].
    rewrite Horigin; split; [exact Hrunning|exact I]. }
  sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state BootInvocation I).
  change (armv7a_task_stack_continuations environment.(task_stack_call_continuations)
    registered.(TskState) registered.(TskState).(parkedTaskStacks)) with
    (armv7a_task_stack_continuations environment.(task_stack_call_continuations)
      state.(TskState) state.(TskState).(parkedTaskStacks)).
  entailer!.
Qed.

(** Initial task entry uses the actual selected-source post: ready/current
    and generation are proved by the C selector and install stores, while
    the initial-call ABI supplies execution authority only. The same owned
    strong map survives ghost registration; no weak-map strengthening.
    The real taken-key absence and descriptor fragment bounds are source
    facts from the preceding take, not new public API requirements. *)
Lemma task_create_selected_initial_entry_world : forall environment
  (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg args name focus incoming selected node state,
  state.(SchedState).(isRunning) = true ->
  armv7a_initial_frame_binding selected ->
  selected.(armv7a_continuation_call) = None ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0
    selected.(armv7a_continuation_fragments) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) = None ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  os_sched_source_selected_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg focus incoming selected node state ** unmap_table_rep sg |--
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  let registered := armv7a_initial_call_registered selected state in
  coq_prop (task_create_source_entry sg args name call registered) &&
    kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
      (task_stack_call_active_key call) call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) registered.
Proof.
  intros environment entry sg args name focus incoming selected node state Hrunning Hbinding Hnone
    Hfragments Habsent Hname.
  cbv zeta.
  set (call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments)).
  set (registered := armv7a_initial_call_registered selected state).
  unfold os_sched_source_selected_post; Intros.
  assert (Hlease : selected.(armv7a_continuation_stack) = incoming) by tauto.
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) node)
    by tauto.
  assert (Hgen : node.(taskGeneration) = incoming.(stackLeaseGeneration)) by tauto.
  assert (Hcovered : task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) by tauto.
  assert (Hcurrent : task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { rewrite Hlease; split; [exact (proj1 (proj2 Hready))|].
    exists node; split; [exact (proj1 Hready)|exact Hgen]. }
  assert (Horigin : task_create_call_origin state call.(os_sched_call_origin)).
  { unfold call, armv7a_initial_call; cbn [os_sched_call_origin].
    exact (conj Hrunning Hcurrent). }
  assert (Hobserve : UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) && UCOS2_inv sg state)
    by (unfold UCOS2_inv; entailer!).
  sep_apply_l_atomic Hobserve; Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by assumption.
  pose proof (task_create_registered_stack_entry sg args name state call Hvalid Horigin eq_refl Hname)
    as Hentry.
  change (task_create_stack_entry sg args name call registered) in Hentry.
  assert (Hsource : task_create_source_entry sg args name call registered).
  { unfold task_create_source_entry, task_create_call_stage; split; [exact Hentry|]. split; [exact Horigin|].
    unfold call, armv7a_initial_call; cbn [os_sched_call_origin os_sched_call_stack].
    split; [reflexivity|]. split; [reflexivity|]. split.
    - rewrite Hlease; exact Habsent.
    - intros; exists node; rewrite Hlease; split; [exact Hready|exact Hgen]. }
  unfold armv7a_task_restored_execution; rewrite Hnone.
  pose proof (armv7a_initial_call_register_resources _ _ _
    environment.(task_stack_call_continuations) entry sg state selected
    selected.(armv7a_continuation_fragments) Hbinding Hfragments Hcurrent) as Hregister.
  cbv zeta in Hregister; sep_apply_l_atomic Hregister.
  Intros.
  sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ environment.(task_stack_call_continuations)
    state.(TskState) focus state.(TskState).(parkedTaskStacks)).
  unfold kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
  fold call registered.
  change (armv7a_task_stack_continuations environment.(task_stack_call_continuations)
    registered.(TskState) registered.(TskState).(parkedTaskStacks)) with
    (armv7a_task_stack_continuations environment.(task_stack_call_continuations)
      state.(TskState) state.(TskState).(parkedTaskStacks)).
  assert (Hcoverage : task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call)).
  { unfold task_stack_call_active_key, call, armv7a_initial_call; cbn [os_sched_call_origin].
    rewrite Hlease; exact Hcovered. }
  entailer!.
Qed.
