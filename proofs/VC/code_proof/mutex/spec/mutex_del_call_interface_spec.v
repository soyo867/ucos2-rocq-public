Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Annotation handle only: no new platform law or desired OS conclusion.
    Boot and running origins are both admitted. An ISR early-error caller
    supplies its own real execution/stack owner; it is not identified with
    the suspended task by this record. *)
Record MutexDelCallEnvironment : Type := {
  mutex_del_call_external : OsSchedExternalResources;
  mutex_del_call_platform : InterruptPlatformResources;
  mutex_del_call_port : OsIntExitPlatformResources;
  mutex_del_call_continuations : Armv7aContinuationABI
    mutex_del_call_external mutex_del_call_platform mutex_del_call_port
}.

Definition mutex_del_interface_capsules environment state : Assertion :=
  armv7a_task_continuations environment.(mutex_del_call_continuations)
    state.(TskState).(parkedTaskStacks).

Definition mutex_del_interface_context environment call : Assertion :=
  os_sched_context_resources environment.(mutex_del_call_external) call.

Definition mutex_del_interface_world environment sg state : Assertion :=
  kernel_client_heap_world environment.(mutex_del_call_continuations) sg state.

(** One program owner, including the single table, plus the currently
    owned CPU/stack and whole parked map. These are present resources of a
    modular C entry, not a promise about future acquisitions or returns. *)
Definition mutex_del_interface_closed environment critical sg call mask state : Assertion :=
  kernel_program_closed environment.(mutex_del_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) mask state **
  mutex_del_interface_context environment call ** mutex_del_interface_capsules environment state.

Definition mutex_del_interface_same_call returned original : Prop :=
  returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = original.(os_sched_call_stack).

Definition mutex_del_interface_save_pre environment critical sg call mask state : Assertion :=
  mutex_del_interface_closed environment critical sg call mask state.

(** This is a source-facing view, not an assertion that every old weak
    Save contract implements it. The local producer below is checked;
    arbitrary returning IRQ/switch chains remain a separate source cut. *)
Definition mutex_del_interface_save_post environment critical sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source environment.(mutex_del_call_external)
      environment.(mutex_del_call_port) critical sg original returned mask saved before acquired) &&
    (critical_region_masked environment.(mutex_del_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
     mutex_del_interface_context environment returned ** mutex_del_interface_world environment sg acquired).

Definition mutex_del_interface_restore_pre environment critical sg call saved acquired released : Assertion :=
  critical_region_masked environment.(mutex_del_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
  mutex_del_interface_context environment call ** mutex_del_interface_world environment sg released.

(** [released] is history, NOT the normally returned heap's state. The
    actual source trace may change the OS state and the whole map. This
    interface does not claim caller readiness, owner-use or slot lifetime. *)
Definition mutex_del_interface_restore_post environment critical sg original mask released : Assertion :=
  EX returned current,
    coq_prop (kernel_resumption_task_source_trace environment.(mutex_del_call_external)
      environment.(mutex_del_call_port) critical.(critical_region_clients)
      sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      released false returned.(os_sched_call_origin) current /\
      mutex_del_interface_same_call returned original) &&
    mutex_del_interface_closed environment critical sg returned mask current.

Lemma mutex_del_interface_closed_owned : forall environment critical sg call mask state,
  mutex_del_interface_closed environment critical sg call mask state --||--
  kernel_call_execution_owned environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) call mask ** mutex_del_interface_world environment sg state.
Proof.
  intros; unfold mutex_del_interface_closed, mutex_del_interface_context,
    mutex_del_interface_world, kernel_client_heap_world, mutex_del_interface_capsules.
  rewrite kernel_program_closed_equiv; unfold kernel_call_execution_owned; split; entailer!.
Qed.

(** Consumes the existing actual first-task-entry producer and its
    physical stack partition. Registration changes no parked-map entry.
    It neither creates the table nor proves arbitrary application callers. *)
Lemma mutex_del_interface_initial_entry : forall environment critical sg
  (entry_abi : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations)) state initial fragments,
  armv7a_initial_frame_binding initial ->
  task_stack_fragments_in_range initial.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 fragments ->
  task_current_at state initial.(armv7a_continuation_stack).(stackLeaseSlot)
    initial.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  let call := armv7a_initial_call initial state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  mutex_del_interface_world environment sg state **
    armv7a_initial_execution environment.(mutex_del_call_continuations) initial **
    task_stack_fragments_rep initial.(armv7a_continuation_stack).(stackLeaseRegion) fragments |--
  coq_prop (kernel_call_task_source call (armv7a_initial_call_registered initial state)) &&
    mutex_del_interface_closed environment critical sg call
      (armv7a_irq_fiq_mask initial.(armv7a_continuation_cpsr))
      (armv7a_initial_call_registered initial state).
Proof.
  intros environment critical sg entry_abi state initial fragments Hbinding Hrange Hcurrent call.
  unfold mutex_del_interface_world, kernel_client_heap_world.
  pose proof (mutex_del_initial_call_program_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) sg entry_abi state initial fragments
    Hbinding Hrange Hcurrent) as Hentry.
  cbv zeta in Hentry; sep_apply_l_atomic Hentry.
  rewrite mutex_del_interface_closed_owned.
  unfold mutex_del_interface_world, kernel_client_heap_world, call.
  cbn [armv7a_initial_call_registered replace_TskS TskState task_begin_invocation parkedTaskStacks].
  entailer!.
Qed.

(** The existing actual C initializer/guard producer accepts all original
    NULL/type/ISR branches. CPU, stack and capsules are a REAL private
    frame through this local fragment, not manufactured from its outcome.
    This theorem does not erase IRQs between unmasked C instructions. *)
Lemma mutex_del_interface_entry_prefix : forall environment critical sg call mask state
  pe eid observed perr old_error cpu_sr before (frame : Assertion),
  mutex_del_call_pointer_domain sg state pe eid observed ->
  (mutex_del_interface_closed environment critical sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame) before ->
  exists initialized result after,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) before initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized result after /\
    mutex_del_call_prefix_post sg state pe eid perr old_error result
      ((cpu_sr # UInt |-> 0) **
       (kernel_call_execution_owned environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) call mask **
        mutex_del_interface_capsules environment state ** frame)) after.
Proof.
  intros environment critical sg call mask state pe eid observed perr old_error cpu_sr before frame Hdomain Hpre.
  assert (Hopen : mutex_del_interface_closed environment critical sg call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      (kernel_call_execution_owned environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) call mask ** mutex_del_interface_capsules environment state ** frame)).
  { rewrite mutex_del_interface_closed_owned.
    unfold mutex_del_interface_world, kernel_client_heap_world, mutex_del_interface_capsules; entailer!. }
  eapply mutex_del_call_entry_prefix_source; [exact Hdomain|exact (Hopen before Hpre)].
Qed.

Lemma mutex_del_interface_uninterrupted_save : forall environment critical arch
  (suffix : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg call state mask registers before final_registers acquired after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (mutex_del_interface_save_pre environment critical sg call mask state ** frame) before ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (mutex_del_interface_save_post environment critical sg call mask
    final_registers.(kernel_save_r0) state ** frame) after.
Proof.
  intros environment critical arch suffix sg call state mask registers before final_registers acquired after
    frame Hreturn Hvalid Hmask Hpre Hsuffix.
  assert (Hopen : mutex_del_interface_save_pre environment critical sg call mask state ** frame |--
    mutex_del_call_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      sg call mask state ** (mutex_del_interface_capsules environment state ** frame)).
  { unfold mutex_del_interface_save_pre; rewrite mutex_del_interface_closed_owned.
    unfold mutex_del_interface_world, kernel_client_heap_world, mutex_del_interface_capsules,
      mutex_del_call_owned; entailer!. }
  destruct (mutex_del_call_uninterrupted_save environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch suffix sg call state mask registers before
    final_registers acquired after _ Hreturn Hvalid Hmask (Hopen before Hpre) Hsuffix)
    as [Hrun [Hstate [Hlr Hafter]]].
  split; [exact Hrun|]. subst acquired.
  destruct (kernel_call_save_uninterrupted_return_values _ _ _ _ _ _ _ Hrun) as [Hr0 _].
  assert (Hsource : kernel_call_save_source environment.(mutex_del_call_external)
    environment.(mutex_del_call_port) critical sg call call mask final_registers.(kernel_save_r0) state state).
  { split; [constructor|]. repeat (split; [reflexivity|]).
    rewrite Hr0; split; [exact Hvalid|exact Hmask]. }
  assert (Hclose : mutex_del_call_masked environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical sg call final_registers.(kernel_save_r0) state state **
      (mutex_del_interface_capsules environment state ** frame) |--
    mutex_del_interface_save_post environment critical sg call mask final_registers.(kernel_save_r0) state ** frame).
  { unfold mutex_del_interface_save_post; Exists call state.
    unfold mutex_del_call_masked, mutex_del_interface_context, mutex_del_interface_world,
      kernel_client_heap_world, mutex_del_interface_capsules; entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma mutex_del_interface_uninterrupted_restore : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg call saved acquired released cursor before written_cursor middle final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (mutex_del_interface_restore_pre environment critical sg call saved acquired released ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (mutex_del_interface_restore_post environment critical sg call (armv7a_irq_fiq_mask saved) released ** frame) after.
Proof.
  intros environment critical arch restore sg call saved acquired released cursor before written_cursor middle
    final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix.
  assert (Hopen : mutex_del_interface_restore_pre environment critical sg call saved acquired released ** frame |--
    critical_region_masked environment.(mutex_del_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(mutex_del_call_external) call **
    (mutex_del_interface_world environment sg released ** frame)).
  { unfold mutex_del_interface_restore_pre, mutex_del_interface_context; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch restore sg call saved acquired cursor before
    written_cursor middle final_cursor after _ Hr0 Hmask (Hopen before Hpre) Hprefix Hsuffix)
    as [Hrun [Hreturn [Hmemory Hafter]]].
  split; [exact Hrun|]. split; [exact Hreturn|].
  assert (Htrace : kernel_resumption_task_source_trace environment.(mutex_del_call_external)
    environment.(mutex_del_call_port) critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    released false call.(os_sched_call_origin) released) by constructor.
  assert (Hclose : kernel_call_execution_owned environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) call (armv7a_irq_fiq_mask saved) **
      (mutex_del_interface_world environment sg released ** frame) |--
    mutex_del_interface_restore_post environment critical sg call (armv7a_irq_fiq_mask saved) released ** frame).
  { unfold mutex_del_interface_restore_post; Exists call released.
    rewrite mutex_del_interface_closed_owned; unfold mutex_del_interface_same_call; entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma mutex_del_interface_restore_current : forall environment critical sg original mask released,
  mutex_del_interface_restore_post environment critical sg original mask released |--
  EX returned current,
    coq_prop (mutex_del_interface_same_call returned original /\
      critical_region_interval critical sg original.(os_sched_call_invocation) released current) &&
    (kernel_program_closed environment.(mutex_del_call_platform) critical sg
       original.(os_sched_call_invocation) original.(os_sched_call_origin) mask current **
     mutex_del_interface_context environment returned ** mutex_del_interface_capsules environment current).
Proof.
  intros; unfold mutex_del_interface_restore_post; Intros returned current.
  match goal with H : _ /\ mutex_del_interface_same_call returned original |- _ =>
    destruct H as [Hsource Hsame]
  end.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsource)) as Hinterval.
  Exists returned current; unfold mutex_del_interface_closed.
  destruct Hsame as [Hi [Ho Hs]]; rewrite Hi, Ho; unfold mutex_del_interface_same_call; entailer!.
Qed.
