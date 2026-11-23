Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_stack_spec.
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

(** This selected first-entry consumer retains the pending caller's exact
    focused map. The executing child and [focus] are distinct parameters:
    the new child does not rename or consume the earlier dormant call.
    The existing initial-entry producer supplies the executing authority;
    readiness/current come from the actual scheduler selected post. *)
Lemma task_create_selected_initial_entry_focused_world : forall environment
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
  coq_prop (task_create_source_entry sg args name call registered /\
    task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call
       (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
   kernel_program_inv sg registered **
   armv7a_task_call_stacks environment.(task_stack_call_continuations)
     registered.(TskState) focus registered.(TskState).(parkedTaskStacks)).
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
  rewrite kernel_program_inv_split_unmap.
  fold call registered.
  change (armv7a_task_call_stacks environment.(task_stack_call_continuations)
    registered.(TskState) focus registered.(TskState).(parkedTaskStacks)) with
    (armv7a_task_call_stacks environment.(task_stack_call_continuations)
      state.(TskState) focus state.(TskState).(parkedTaskStacks)).
  assert (Hcoverage : task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call)).
  { unfold task_stack_call_active_key, call, armv7a_initial_call; cbn [os_sched_call_origin].
    rewrite Hlease; exact Hcovered. }
  entailer!.
Qed.

(** The same pending map survives a later completed-call / next-call entry.
    This is the existing externally observed sequential boundary, followed
    by the OS ghost registration already used by the ordinary entry proof.
    It neither interprets arbitrary application code nor re-focuses a
    parked continuation. *)
Lemma task_create_sequential_entry_focused_world : forall environment
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  sg args name previous mask state focus before after (frame : Assertion),
  task_create_call_stage previous state ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key previous) ->
  kernel_sequential_call_source boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) before after ->
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) previous mask **
   kernel_program_inv sg state **
   armv7a_task_call_stacks environment.(task_stack_call_continuations)
     state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := replace_TskS
    (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (coq_prop (task_create_source_entry sg args name call registered /\
     task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call)) &&
   (kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call mask **
    kernel_program_inv sg registered **
    armv7a_task_call_stacks environment.(task_stack_call_continuations)
      registered.(TskState) focus registered.(TskState).(parkedTaskStacks) ** frame)) after.
Proof.
  intros environment boundary sg args name previous mask state focus before after frame
    Hstage Hname Hcoverage Hsource Hbefore call registered.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hbefore with ?P before => assert (Hexpose : P |--
      coq_prop (UCOS2_state_inv sg state) && TT) end.
    { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hbefore)). }
  assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin))
    by (apply task_create_call_origin_live; exact (proj1 Hstage)).
  destruct (kernel_sequential_call_register_focused_world _ _ _
    environment.(task_stack_call_continuations) boundary sg previous mask state focus before after frame
    Hlive Hsource Hbefore) as [Hmemory Hafter].
  fold call registered in Hafter.
  assert (Horigin : task_create_call_origin state call.(os_sched_call_origin)) by exact (proj1 Hstage).
  pose proof (task_create_registered_stack_entry sg args name state call Hvalid Horigin eq_refl Hname)
    as Hentry.
  change (task_create_stack_entry sg args name call registered) in Hentry.
  assert (Hsource_entry : task_create_source_entry sg args name call registered)
    by exact (conj Hentry Hstage).
  assert (Hcovered : task_stack_live_coverage registered.(TskState) (task_stack_call_active_key call))
    by exact Hcoverage.
  split; [exact Hmemory|]. exact (conj (conj Hsource_entry Hcovered) Hafter).
Qed.
