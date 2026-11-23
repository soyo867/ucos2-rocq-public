Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition task_tcb_init_stack_covered_capsules environment state : Assertion :=
  armv7a_task_stack_continuations environment.(task_stack_call_continuations)
    state.(TskState) state.(TskState).(parkedTaskStacks).

Definition task_tcb_init_stack_covered_save_input environment critical sg call mask state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask **
   critical_region_outside critical sg call.(os_sched_call_invocation) state **
   task_tcb_init_stack_covered_capsules environment state).

(** These are source endpoint views, not new Save/Restore ABI guarantees.
    Only a checked source branch can supply the current indexed resources. *)
Definition task_tcb_init_stack_covered_save_post environment critical sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg original returned mask saved before acquired /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment returned ** UCOS2_inv sg acquired **
     task_tcb_init_stack_covered_capsules environment acquired).

Definition task_tcb_init_stack_covered_restore_post environment critical sg original mask released : Assertion :=
  EX returned current,
    coq_prop (kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients)
      sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      released false returned.(os_sched_call_origin) current /\
      task_tcb_init_stack_same_call returned original) &&
    task_tcb_init_stack_covered_save_input environment critical sg returned mask current.

Definition task_create_stack_covered_success_post environment critical sg original mask : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original) &&
    (task_tcb_init_stack_covered_save_input environment critical sg returned mask current **
     unmap_table_rep sg).

(** The current table is part of the returning heap, not a frame retaining
    the pre-call table across a context switch. This definition does not
    assert that a switch or original-call return must occur. *)
Definition os_sched_covered_call_post environment critical sg original mask before : Assertion :=
  EX entry returned current,
    coq_prop (critical_region_interval critical sg original.(os_sched_call_invocation) before entry /\
      os_sched_c_return environment.(task_stack_call_external) critical sg entry original returned current) &&
    (task_tcb_init_stack_covered_save_input environment critical sg returned mask current **
     unmap_table_rep sg).

(** Package the already owned platform resource only after the actual
    bytes and matching live SP have been established. In particular this
    lemma cannot turn running CPU authority into a dormant continuation. *)
Lemma armv7a_task_stack_entry_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks saved,
  armv7a_continuation_binding saved -> armv7a_task_frame_slice saved ->
  task_stack_live_sp tasks (task_stack_key saved.(armv7a_continuation_stack))
    saved.(armv7a_continuation_sp) ->
  armv7a_task_continuation_resource abi saved |--
  armv7a_task_stack_entry abi tasks (task_stack_key saved.(armv7a_continuation_stack))
    (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)).
Proof. intros; unfold armv7a_task_stack_entry; Exists saved; entailer!. Qed.

Lemma task_tcb_init_stack_covered_save_input_forget : forall environment critical sg call mask state,
  task_tcb_init_stack_covered_save_input environment critical sg call mask state |--
  task_tcb_init_stack_save_input environment critical sg call mask state.
Proof.
  intros; unfold task_tcb_init_stack_covered_save_input, task_tcb_init_stack_save_input,
    task_tcb_init_stack_covered_capsules, task_tcb_init_stack_capsules; reflexivity.
Qed.

Lemma task_create_stack_covered_success_post_forget :
  forall environment critical sg region args task_return lower old_frame upper original mask,
  task_create_stack_covered_success_post environment critical sg original mask |--
  task_create_stack_post environment critical sg region args task_return lower old_frame upper original mask 0.
Proof.
  intros; unfold task_create_stack_covered_success_post; Intros returned current.
  unfold task_tcb_init_stack_covered_save_input; Intros.
  unfold task_create_stack_post; Exists returned current.
  destruct (Z.eq_dec 0 0); [|contradiction].
  unfold task_tcb_init_stack_save_input, task_tcb_init_stack_covered_capsules,
    task_tcb_init_stack_capsules.
  entailer!; tauto.
Qed.

Lemma task_create_stack_covered_return_without_schedule : forall environment critical sg original returned mask current,
  task_tcb_init_stack_same_call returned original ->
  task_tcb_init_stack_covered_save_input environment critical sg returned mask current **
    unmap_table_rep sg |--
  task_create_stack_covered_success_post environment critical sg original mask.
Proof. intros; unfold task_create_stack_covered_success_post; Exists returned current; entailer!. Qed.

Lemma os_sched_covered_call_post_returns_create : forall environment critical sg original mask before,
  os_sched_covered_call_post environment critical sg original mask before |--
  task_create_stack_covered_success_post environment critical sg original mask.
Proof.
  intros; unfold os_sched_covered_call_post; Intros entry returned current.
  assert (Hreturn : os_sched_c_return environment.(task_stack_call_external)
    critical sg entry original returned current) by tauto.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hreturn) as Hsame.
  unfold task_create_stack_covered_success_post; Exists returned current.
  unfold task_tcb_init_stack_same_call; entailer!.
Qed.

Lemma task_tcb_init_stack_covered_save_post_forget : forall environment critical sg original mask saved before,
  task_tcb_init_stack_covered_save_post environment critical sg original mask saved before |--
  task_tcb_init_stack_save_output environment critical sg original mask saved before.
Proof.
  intros; change (task_tcb_init_stack_save_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) critical
    environment.(task_stack_call_continuations) sg original mask saved before |--
    task_tcb_init_stack_save_output environment critical sg original mask saved before).
  apply task_tcb_init_stack_registered_save_output.
Qed.

Lemma task_tcb_init_stack_covered_restore_post_forget : forall environment critical sg original mask released,
  task_tcb_init_stack_covered_restore_post environment critical sg original mask released |--
  task_tcb_init_stack_restore_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) critical
    environment.(task_stack_call_continuations) sg original mask released.
Proof.
  intros; unfold task_tcb_init_stack_covered_restore_post; Intros returned current.
  unfold task_tcb_init_stack_covered_save_input; Intros.
  unfold task_tcb_init_stack_restore_post; Exists returned current.
  unfold task_tcb_init_stack_covered_capsules.
  unfold task_tcb_init_stack_same_call in *; entailer!; tauto.
Qed.

(** Exact original-call indexing needed by Create witness 11. The premise
    is the strong source-produced returning heap, not the old os_sched_post
    that has forgotten its parked continuation table. *)
Lemma task_create_stack_covered_scheduled_return :
  forall environment critical sg region args task_return lower old_frame upper original scheduled mask before,
  task_tcb_init_stack_same_call scheduled original ->
  os_sched_covered_call_post environment critical sg scheduled mask before |--
  task_create_stack_post environment critical sg region args task_return lower old_frame upper original mask 0.
Proof.
  intros environment critical sg region args task_return lower old_frame upper original scheduled mask before Hsame.
  sep_apply_l_atomic (os_sched_covered_call_post_returns_create environment critical sg scheduled mask before).
  assert (Hreindex : task_create_stack_covered_success_post environment critical sg scheduled mask |--
    task_create_stack_covered_success_post environment critical sg original mask).
  { unfold task_create_stack_covered_success_post; Intros returned current; Exists returned current.
    unfold task_tcb_init_stack_same_call in *; entailer!; intuition congruence. }
  sep_apply_l_atomic Hreindex; apply task_create_stack_covered_success_post_forget.
Qed.

(** Real MRS/CPSID/DSB/BX with no IRQ between those instructions. Strong
    entries and coverage are retained as the actual disjoint resource of
    this local source branch; no such framing is claimed for an IRQ. *)
Lemma task_tcb_init_stack_covered_uninterrupted_save :
  forall environment critical arch
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call mask state registers before final_registers acquired after (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (task_tcb_init_stack_covered_save_input environment critical sg call mask state ** frame) before ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (task_tcb_init_stack_covered_save_post environment critical sg call mask
     final_registers.(kernel_save_r0) state ** frame) after.
Proof.
  intros environment critical arch suffix sg call mask state registers before final_registers
    acquired after frame Hreturn Hcpsr Hmask Hbefore Hrun.
  assert (Hopen : task_tcb_init_stack_covered_save_input environment critical sg call mask state ** frame |--
    coq_prop (UCOS2_state_inv sg state /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call
       (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
     (UCOS2_inv sg state ** task_tcb_init_stack_covered_capsules environment state ** frame))).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask.
    unfold task_tcb_init_stack_covered_save_input, critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hbefore) as [[Hvalid Hcoverage] Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  assert (Hsource : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hrun). }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ suffix sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired after _ Hsaved Howned Hrun)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  split; [exact Hsource|]. subst acquired.
  assert (Hcall : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call call mask final_registers.(kernel_save_r0) state state).
  { split; [constructor|]. repeat (split; [reflexivity|]).
    rewrite Hr0; split; [exact Hcpsr|exact Hmask]. }
  match type of Hafter with ?P after =>
    assert (Hpost : P |-- task_tcb_init_stack_covered_save_post environment critical sg call mask
      final_registers.(kernel_save_r0) state ** frame)
  end.
  { unfold task_tcb_init_stack_covered_save_post, task_tcb_init_stack_context;
      Exists call state; entailer!. }
  exact (Hpost after Hafter).
Qed.

(** Real local Restore transports the SAME released strong table. General
    interrupted returns must instead produce their own current table. *)
Lemma task_tcb_init_stack_covered_uninterrupted_restore :
  forall environment critical arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call saved entry released cursor before written_cursor middle final_cursor after (frame : Assertion),
  task_stack_live_coverage released.(TskState) (task_stack_call_active_key call) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg released **
   task_tcb_init_stack_covered_capsules environment released ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (task_tcb_init_stack_covered_save_input environment critical sg call
     (armv7a_irq_fiq_mask saved) released ** frame) after.
Proof.
  intros environment critical arch restore sg call saved entry released cursor before written_cursor
    middle final_cursor after frame Hcoverage Hr0 Hmask Hbefore Hprefix Hsuffix.
  match type of Hbefore with ?P before =>
    assert (Horder : P |-- critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
      os_sched_context_resources environment.(task_stack_call_external) call **
      (UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released ** frame))
  end.
  { unfold task_tcb_init_stack_context; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call saved entry
    cursor before written_cursor middle final_cursor after _ Hr0 Hmask (Horder before Hbefore) Hprefix Hsuffix)
    as [Hrun [Hreturn [Hmemory Hafter]]].
  split; [exact Hrun|]. split; [exact Hreturn|].
  match type of Hafter with ?P after =>
    assert (Hpost : P |-- task_tcb_init_stack_covered_save_input environment critical sg call
      (armv7a_irq_fiq_mask saved) released ** frame)
  end.
  { unfold task_tcb_init_stack_covered_save_input, critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  exact (Hpost after Hafter).
Qed.

(** Complete the actual no-switch branch from the masked prefix endpoint.
    This is not a switch/return theorem and does not impose scheduler
    safety on unstarted calls that bypass OS_Sched in the C source. *)
Lemma os_sched_covered_uninterrupted_nonswitch_return :
  forall environment critical arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call saved entry cursor before written_cursor middle final_cursor after (frame : Assertion),
  os_sched_requests_switch entry = false ->
  task_stack_live_coverage entry.(TskState) (task_stack_call_active_key call) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg (os_sched_prefix_state entry) **
   task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state entry) **
   unmap_table_rep sg ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  (os_sched_covered_call_post environment critical sg call (armv7a_irq_fiq_mask saved) entry ** frame) after.
Proof.
  intros environment critical arch restore sg call saved entry cursor before written_cursor middle
    final_cursor after frame Hnoswitch Hcoverage Hr0 Hmask Hbefore Hprefix Hsuffix.
  assert (Horder : critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
      task_tcb_init_stack_context environment call ** UCOS2_inv sg (os_sched_prefix_state entry) **
      task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state entry) **
      unmap_table_rep sg ** frame |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
      task_tcb_init_stack_context environment call ** UCOS2_inv sg (os_sched_prefix_state entry) **
      task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state entry) **
      (unmap_table_rep sg ** frame)) by entailer!.
  destruct (task_tcb_init_stack_covered_uninterrupted_restore environment critical arch restore sg call
    saved entry (os_sched_prefix_state entry) cursor before written_cursor middle final_cursor after
    _ Hcoverage Hr0 Hmask (Horder before Hbefore) Hprefix Hsuffix) as [Hrun [Hreturn Hafter]].
  split; [exact Hrun|].
  assert (Hpost : task_tcb_init_stack_covered_save_input environment critical sg call
      (armv7a_irq_fiq_mask saved) (os_sched_prefix_state entry) ** (unmap_table_rep sg ** frame) |--
    os_sched_covered_call_post environment critical sg call (armv7a_irq_fiq_mask saved) entry ** frame).
  { assert (Hinterval : critical_region_interval critical sg call.(os_sched_call_invocation) entry entry)
      by constructor.
    assert (Hreturn_source : os_sched_c_return environment.(task_stack_call_external) critical sg
      entry call call (os_sched_prefix_state entry)).
    { unfold os_sched_c_return; rewrite Hnoswitch; auto. }
    unfold os_sched_covered_call_post; Exists entry call (os_sched_prefix_state entry); entailer!. }
  exact (Hpost after Hafter).
Qed.

(** The protected publication producer now returns the strong SAME-map
    entries. Actual free-root observation and the two acquisition
    intervals identify the allocation; the five source stores and the
    initialized buffer produce coverage, rather than assuming it of the
    future child. The incoming current table is never weakened first. *)
Lemma task_tcb_init_stack_covered_publication_source :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    critical sg region args task_return lower upper initial_name invocation origin initial
    acquired current slot rest image active allocation_heap (frame : Assertion) before,
  let actual := task_create_tcb_args args
    (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_entry sg actual invocation origin initial ->
  critical_region_interval critical sg invocation initial acquired ->
  task_tcb_init_detach_observation actual invocation origin acquired slot rest image ->
  critical_region_interval critical sg invocation
    (task_tcb_init_detached_state actual invocation origin acquired slot rest image) current ->
  pointer_load sg.(g_OSTCBFreeList) (task_slot_addr sg slot) allocation_heap ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_stack_live_coverage current.(TskState) active ->
  (task_tcb_init_publication_tail_storage sg actual current slot image **
   task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
   armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) ** frame) before ->
  exists allocation after,
    allocation.(privateSlot) = slot /\
    allocation.(privateGeneration) = acquired.(TskState).(taskLifecycle).(taskNextGeneration) /\
    let publication := {| stack_publication_region := region;
      stack_publication_args := args; stack_publication_return := task_return;
      stack_publication_lower := lower; stack_publication_upper := upper;
      stack_publication_name := initial_name; stack_publication_invocation := invocation;
      stack_publication_origin := origin; stack_publication_acquired := acquired;
      stack_publication_slot := slot; stack_publication_image := image;
      stack_publication_lease := task_stack_lease_of_allocation region allocation |} in
    task_tcb_init_publication_tail_fragment sg actual.(initPrio) (task_slot_addr sg slot) before after /\
    kernel_client_step (task_create_stack_publication_client publication) sg current
      (task_create_stack_publication_state sg publication current) /\
    task_stack_live_coverage (task_create_stack_publication_state sg publication current).(TskState) active /\
    (UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
     armv7a_task_stack_continuations abi
       (task_create_stack_publication_state sg publication current).(TskState)
       (task_create_stack_publication_state sg publication current).(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi critical sg region args task_return lower upper initial_name
    invocation origin initial acquired current slot rest image active allocation_heap frame before actual
    Hentry Hfirst Hdetach Hopen Hpointer Hlayout Hcoverage Hbefore.
  pose proof (task_tcb_init_acquire_entry critical sg actual invocation origin initial acquired Hentry Hfirst)
    as Hacquired.
  destruct (task_tcb_init_acquire_commit critical sg actual invocation origin acquired slot rest image current
    Hacquired Hdetach Hopen) as [Hvalid [Hcommit Hactive]].
  destruct (task_create_stack_commit_allocation_binding region actual invocation origin acquired current slot Hcommit)
    as [allocation [Hslot [Hgeneration Hcreation]]].
  destruct (task_tcb_init_detached_flags_defined sg actual invocation origin acquired slot rest image Hacquired Hdetach)
    as [flags Hflags].
  assert (Hname : sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name current.(NameState)
      (task_tcb_init_commit_node actual acquired slot image).(tcbTaskName) chars).
  { intros Hnames.
    destruct (proj2 (proj2 (proj2 (proj2 Hacquired))) Hnames) as [chars Hread].
    pose proof (critical_region_interval_preserves_name_state critical sg invocation
      (task_tcb_init_detached_state actual invocation origin acquired slot rest image) current Hopen) as Hnames_frame.
    exists chars; rewrite task_tcb_init_commit_node_name, <- Hnames_frame; exact Hread. }
  pose proof (proj1 (task_tcb_init_entry_priority_in_range sg actual invocation origin acquired Hacquired)) as Hpriority.
  assert (Hfocus : task_tcb_init_publication_tail_storage sg actual current slot image **
      task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
      armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) ** frame |--
    task_tcb_init_publication_tail_storage sg actual current slot image **
      (task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
       armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) ** frame))
    by entailer!.
  destruct (task_tcb_init_publication_tail_store_execution sg actual invocation origin acquired current slot image
    _ before Hvalid Hcommit Hpriority (proj1 Hpointer) (Hfocus before Hbefore)) as [after [Hrun Hafter]].
  set (publication := {| stack_publication_region := region;
    stack_publication_args := args; stack_publication_return := task_return;
    stack_publication_lower := lower; stack_publication_upper := upper;
    stack_publication_name := initial_name; stack_publication_invocation := invocation;
    stack_publication_origin := origin; stack_publication_acquired := acquired;
    stack_publication_slot := slot; stack_publication_image := image;
    stack_publication_lease := task_stack_lease_of_allocation region allocation |}).
  assert (Hinput : task_create_stack_publication_input sg publication current).
  { split; [exact Hlayout|]. split; [reflexivity|]. split; [exact Hcommit|].
    split; [exact Hcreation|]. split; [exists flags; exact Hflags|exact Hname]. }
  pose proof (task_create_publication_covered_stack_merge external platform port abi sg
    publication current active Hvalid Hinput Hcoverage) as Hmerge; cbv zeta in Hmerge.
  assert (Hclose : task_create_publication_storage sg actual invocation acquired current slot image **
      (task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
       armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) ** frame) |--
    coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current
      (task_create_stack_publication_state sg publication current) /\
      task_stack_live_coverage (task_create_stack_publication_state sg publication current).(TskState) active) &&
    (UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
     armv7a_task_stack_continuations abi
       (task_create_stack_publication_state sg publication current).(TskState)
       (task_create_stack_publication_state sg publication current).(TskState).(parkedTaskStacks) ** frame)).
  { unfold task_create_stack_publication_args, task_create_stack_publication_words in Hmerge.
    cbn [publication stack_publication_region stack_publication_args stack_publication_return
      stack_publication_lower stack_publication_upper stack_publication_name stack_publication_invocation
      stack_publication_origin stack_publication_acquired stack_publication_slot stack_publication_image
      stack_publication_lease] in Hmerge.
    fold actual in Hmerge; sepcon_assoc_change; sep_apply_l_atomic Hmerge; Intros; entailer!. }
  destruct (Hclose after Hafter) as [[Hstep Hcovered] Hresources].
  exists allocation, after; split; [exact Hslot|]. split; [exact Hgeneration|].
  fold publication; split; [exact Hrun|]. split; [exact Hstep|]. split; assumption.
Qed.

(** The live-current OSCtxSw memory branch: actual frame stores, actual
    OSTCBCur load, and actual TCB-SP store. The complete old strong map is
    reindexed using that store. No dormant CPU resource is manufactured:
    the resulting descriptor facts are ready for the separate platform
    running-to-dormant exchange. The free/retired-current branch is not
    collapsed into this live-node case. *)
Lemma task_stack_live_save_source :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg tasks node call old_sp cpsr registers lr prefix suffix first old_words (frame : Assertion) before,
  tasks.(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  tasks.(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  task_stack_live_coverage tasks (Some (task_stack_key call.(os_sched_call_stack))) ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) call.(os_sched_call_fragments) **
   task_public_storage sg tasks ** armv7a_task_stack_continuations abi tasks tasks.(parkedTaskStacks) **
   sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := glob_task_set_usedtask tasks call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp)) in
  exists written after,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp)) written after /\
    armv7a_continuation_binding saved /\ armv7a_task_frame_slice saved /\
    task_stack_live_sp updated (task_stack_key call.(os_sched_call_stack)) saved.(armv7a_continuation_sp) /\
    task_stack_live_coverage updated (Some (task_stack_key call.(os_sched_call_stack))) /\
    armv7a_continuation_restore_reads saved after /\
    (task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) ** task_public_storage sg updated **
     armv7a_task_stack_continuations abi updated updated.(parkedTaskStacks) **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame) after.
Proof.
  intros external platform port abi sg tasks node call old_sp cpsr registers lr prefix suffix first old_words
    frame before Hnode Hgen Hnone Hcoverage Hfragments Hlength Hcpsr Hlr Hranges Hsprange Hsp Haddress Hbefore.
  cbv zeta.
  set (fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix).
  set (saved := armv7a_task_save_image call old_sp cpsr registers lr fragments).
  set (updated := glob_task_set_usedtask tasks call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp))).
  assert (Horder : task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      call.(os_sched_call_fragments) ** task_public_storage sg tasks **
      armv7a_task_stack_continuations abi tasks tasks.(parkedTaskStacks) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame |--
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) **
    (task_public_storage sg tasks ** armv7a_task_stack_continuations abi tasks tasks.(parkedTaskStacks) **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame)).
  { rewrite Hfragments; entailer!. }
  destruct (armv7a_task_save_fragment_execution call old_sp cpsr registers lr prefix suffix first old_words
    _ before Hlength Hcpsr Hlr Hranges Hsp (Horder before Hbefore))
    as [written [Hstores [Hwritten [Hreads Hslice]]]].
  fold fragments in Hwritten, Hslice; fold saved in Hwritten, Hslice.
  assert (Hcurrent : pointer_load sg.(g_OSTCBCur)
    (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written).
  { match type of Hwritten with ?P written =>
      assert (Hload : P |-- sg.(g_OSTCBCur) # Ptr |->
        task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** TT)
    end.
    { entailer!; intros ? ?; exact I. }
    eapply framed_pointer_store_load; exact (Hload written Hwritten). }
  match type of Hwritten with ?P written =>
    assert (Hsplit : P |-- task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) # Ptr |->_ **
      (task_public_storage_without_field sg tasks call.(os_sched_call_stack).(stackLeaseSlot)
         node (TCBCommonField TCBStkPtr) **
       task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
         saved.(armv7a_continuation_fragments) **
       armv7a_task_stack_continuations abi tasks tasks.(parkedTaskStacks) **
       sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame))
  end.
  { sep_apply_l_atomic (task_public_storage_split_saved_sp sg tasks
      call.(os_sched_call_stack).(stackLeaseSlot) node Hnode).
    cbn [tcb_layout_cell tcb_cell].
    rewrite Haddress.
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) node.(tcbStkPtr)); entailer!. }
  destruct (framed_pointer_store_execution
    (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp)
    _ written Hsprange (Hsplit written Hwritten)) as [after [Hstore Hafter]].
  match type of Hafter with ?P after =>
    assert (Hmerge : P |-- task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** task_public_storage sg updated **
      armv7a_task_stack_continuations abi updated updated.(parkedTaskStacks) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame)
  end.
  { rewrite <- Haddress at 1.
    sep_apply_l_atomic (task_public_storage_merge_saved_sp sg tasks
      call.(os_sched_call_stack).(stackLeaseSlot) node saved.(armv7a_continuation_sp)).
    sep_apply_l_atomic (armv7a_task_stack_continuations_save_sp external platform port abi tasks
      node saved.(armv7a_continuation_sp) call.(os_sched_call_stack) tasks.(parkedTaskStacks) Hnode Hgen Hnone).
    unfold updated; cbn [glob_task_set_usedtask parkedTaskStacks]; entailer!. }
  pose proof (Hmerge after Hafter) as Hresources.
  assert (Hbinding : armv7a_continuation_binding saved) by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hlive_sp : task_stack_live_sp updated (task_stack_key call.(os_sched_call_stack))
    saved.(armv7a_continuation_sp)).
  { intros other Hother Hothergen; cbn [updated glob_task_set_usedtask inUsedTaskStates task_stack_key fst] in Hother.
    rewrite Z.eqb_refl in Hother; injection Hother as Hother; subst other; reflexivity. }
  assert (Hcovered : task_stack_live_coverage updated (Some (task_stack_key call.(os_sched_call_stack)))).
  { apply task_stack_save_sp_preserves_coverage; assumption. }
  assert (Hafter_reads : armv7a_continuation_restore_reads saved after).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    assert (Hfocus : task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** task_public_storage sg updated **
        armv7a_task_stack_continuations abi updated updated.(parkedTaskStacks) **
        sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame |--
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      (task_public_storage sg updated ** armv7a_task_stack_continuations abi updated updated.(parkedTaskStacks) **
       sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame)) by entailer!.
    exact (Hfocus after Hresources). }
  exists written, after; fold fragments saved updated.
  split; [exact Hstores|]. split; [exact Hcurrent|]. split; [exact Hstore|].
  split; [exact Hbinding|]. split; [exact Hslice|]. split; [exact Hlive_sp|].
  split; [exact Hcovered|]. split; assumption.
Qed.
