Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This caller-specific input adds the actual initialized buffer to the
    unchanged generic TCBInit input.  The callee has not allocated a slot
    or generation yet.  No future publication, ready task, or parked frame
    is an input fact.  Its full C-call proof is separate from the protected
    publication source consumer below. *)
Definition task_tcb_init_stack_pre platform critical sg region args task_return lower upper
  initial_name invocation origin mask initial : Assertion :=
  coq_prop (task_create_stack_layout TaskStackNoVFP region args lower upper) &&
  (task_tcb_init_pre platform critical sg
     (task_create_tcb_args args (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name)
     invocation origin mask initial **
   task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper)).

(** Source consumer at the second protected TCBInit publication.  The
    earlier real free-root load fixes the concrete slot pointer.  The two
    actual critical intervals and detach observation produce the allocation
    identity; none is recovered from the later ready table.

    The five public stores run on the SAME heap as the caller's current
    StackInit buffer.  Only after these stores is the protected world closed
    with that buffer and its initial continuation entry.  The final Restore
    must consume this produced world, not the old raw-publication snapshot.
    Earlier link stores, hooks, and any later return interval are not hidden
    in this fragment. *)
Lemma task_tcb_init_stack_publication_source :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    critical sg region args task_return lower upper initial_name invocation origin initial
    acquired current slot rest image allocation_heap (frame : Assertion) before,
  let actual := task_create_tcb_args args
    (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_entry sg actual invocation origin initial ->
  critical_region_interval critical sg invocation initial acquired ->
  task_tcb_init_detach_observation actual invocation origin acquired slot rest image ->
  critical_region_interval critical sg invocation
    (task_tcb_init_detached_state actual invocation origin acquired slot rest image) current ->
  pointer_load sg.(g_OSTCBFreeList) (task_slot_addr sg slot) allocation_heap ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  (task_tcb_init_publication_tail_storage sg actual current slot image **
   task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
   armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) ** frame) before ->
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
    (UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
     armv7a_task_continuations abi
       (task_create_stack_publication_state sg publication current).(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi critical sg region args task_return lower upper initial_name
    invocation origin initial acquired current slot rest image allocation_heap frame before actual
    Hentry Hfirst Hdetach Hopen Hpointer Hlayout Hbefore.
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
      (task_tcb_init_detached_state actual invocation origin acquired slot rest image) current Hopen) as Hname_frame.
    exists chars; rewrite task_tcb_init_commit_node_name, <- Hname_frame; exact Hread. }
  pose proof (proj1 (task_tcb_init_entry_priority_in_range sg actual invocation origin acquired Hacquired)) as Hpriority.
  assert (Hfocus : task_tcb_init_publication_tail_storage sg actual current slot image **
      task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
      armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) ** frame |--
    task_tcb_init_publication_tail_storage sg actual current slot image **
      (task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
       armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) ** frame)) by entailer!.
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
  pose proof (task_create_stack_publication_source_post external platform port abi sg publication current Hvalid Hinput)
    as Hpost; cbv zeta in Hpost.
  assert (Hclose : task_create_publication_storage sg actual invocation acquired current slot image **
      (task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
       armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
      armv7a_task_continuations abi
        (task_create_stack_publication_state sg publication current).(TskState).(parkedTaskStacks) ** frame).
  { unfold task_create_stack_publication_resources in Hpost.
    unfold task_create_stack_publication_args, task_create_stack_publication_words in Hpost.
    cbn [publication stack_publication_region stack_publication_args stack_publication_return
      stack_publication_lower stack_publication_upper stack_publication_name stack_publication_invocation
      stack_publication_origin stack_publication_acquired stack_publication_slot stack_publication_image
      stack_publication_lease task_create_stack_publication_args task_create_stack_publication_words] in Hpost.
    fold actual in Hpost; sepcon_assoc_change; sep_apply_l_atomic Hpost; Intros; entailer!. }
  exists allocation, after; split; [exact Hslot|]. split; [exact Hgeneration|].
  fold publication; split; [exact Hrun|]. split.
  - split; [exact Hinput|reflexivity].
  - exact (Hclose after Hafter).
Qed.

(** Source-facing Save view for a stack-aware creation call.  The map is
    indexed by the ACTUAL acquired state, not by the earlier snapshot.
    This definition is not installed as a universal CPU ABI postcondition:
    a concrete returning source branch must produce it with its heap. *)
Definition task_tcb_init_stack_save_post external platform port critical
  (continuations : Armv7aContinuationABI external platform port)
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source external port critical sg original returned
      mask saved before acquired /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) saved acquired **
     os_sched_context_resources external returned ** UCOS2_inv sg acquired **
     armv7a_task_stack_continuations continuations acquired.(TskState)
       acquired.(TskState).(parkedTaskStacks)).

(** Restore's released publication snapshot is a history index.  Its
    normally returned physical resources belong to [current], after the
    actual returning source interval.  A caller cannot obtain the old
    released map, initial frame, or ready node from this postcondition. *)
Definition task_tcb_init_stack_restore_post external platform port critical
  (continuations : Armv7aContinuationABI external platform port)
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (kernel_resumption_task_source_trace external port critical.(critical_region_clients)
      sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      released false returned.(os_sched_call_origin) current /\
      returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack) /\
      UCOS2_state_inv sg current /\
      task_stack_live_coverage current.(TskState) (task_stack_call_active_key returned)) &&
    (kernel_call_execution_owned external platform returned mask **
     critical_region_outside critical sg returned.(os_sched_call_invocation) current **
     armv7a_task_stack_continuations continuations current.(TskState)
       current.(TskState).(parkedTaskStacks)).

(** The actual local Restore branch supplies the source-facing return
    view. Equality with [released] follows only for this explicit absence
    of intervening IRQ steps, never for the general return interface. *)
Lemma task_tcb_init_stack_uninterrupted_restore_post :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    sg call saved entry released cursor before written_cursor middle final_cursor after (frame : Assertion),
  UCOS2_state_inv sg released ->
  task_stack_live_coverage released.(TskState) (task_stack_call_active_key call) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry ** os_sched_context_resources external call **
   UCOS2_inv sg released **
   armv7a_task_stack_continuations continuations released.(TskState)
     released.(TskState).(parkedTaskStacks) ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (task_tcb_init_stack_restore_post external platform port critical continuations sg call
     (armv7a_irq_fiq_mask saved) released ** frame) after.
Proof.
  intros external platform port critical arch continuations restore sg call saved entry released
    cursor before written_cursor middle final_cursor after frame Hvalid Hcoverage Hr0 Hmask Hbefore Hprefix Hsuffix.
  match type of Hbefore with ?P before =>
    assert (Horder : P |--
      critical_region_masked platform critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) saved entry ** os_sched_context_resources external call **
      (UCOS2_inv sg released **
       armv7a_task_stack_continuations continuations released.(TskState)
         released.(TskState).(parkedTaskStacks) ** frame))
  end.
  { entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch
    restore sg call saved entry cursor before written_cursor middle final_cursor after _ Hr0 Hmask
    (Horder before Hbefore) Hprefix Hsuffix) as [Hrun [Hreturn [Hmemory Hafter]]].
  split; [exact Hrun|]. split; [exact Hreturn|].
  assert (Htrace : kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    released false call.(os_sched_call_origin) released) by constructor.
  match type of Hafter with ?P after =>
    assert (Hpost : P |-- task_tcb_init_stack_restore_post external platform port critical continuations
      sg call (armv7a_irq_fiq_mask saved) released ** frame)
  end.
  { unfold task_tcb_init_stack_restore_post; Exists call released.
    unfold critical_region_outside; rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running; unfold UCOS2_inv; entailer!. }
  exact (Hpost after Hafter).
Qed.

(** Concrete local MRS -> CPSID/DSB/BX branch.  All caller-owned resources,
    including the unpublished initialized buffer, are the same [frame]
    through these actual local instructions.  This branch does not erase
    an IRQ: interrupted executions use the selected-return producer and
    their actual acquired map instead. *)
Lemma task_tcb_init_stack_uninterrupted_save_post :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg call mask state registers before final_registers acquired after (frame : Assertion),
  UCOS2_state_inv sg state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_call_execution_owned external platform call mask **
   critical_region_outside critical sg call.(os_sched_call_invocation) state **
   armv7a_task_stack_continuations continuations state.(TskState)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (task_tcb_init_stack_save_post external platform port critical continuations sg call mask
     final_registers.(kernel_save_r0) state ** frame) after.
Proof.
  intros external platform port critical arch continuations suffix sg call mask state registers
    before final_registers acquired after frame Hvalid Hcoverage Hreturn Hcpsr Hmask Hbefore Hrun.
  assert (Hopen : kernel_call_execution_owned external platform call mask **
      critical_region_outside critical sg call.(os_sched_call_invocation) state **
      armv7a_task_stack_continuations continuations state.(TskState)
        state.(TskState).(parkedTaskStacks) ** frame |--
    kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (UCOS2_inv sg state **
     armv7a_task_stack_continuations continuations state.(TskState)
       state.(TskState).(parkedTaskStacks) ** frame)).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask.
    unfold critical_region_outside; rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running; unfold UCOS2_inv; entailer!. }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hcpsr|reflexivity]. }
  assert (Hsource : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hrun). }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired after _ Hsaved
    (Hopen before Hbefore) Hrun) as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  split; [exact Hsource|]. subst acquired.
  assert (Hcall : kernel_call_save_source external port critical sg call call mask
    final_registers.(kernel_save_r0) state state).
  { split; [constructor|]. repeat (split; [reflexivity|]).
    rewrite Hr0; split; [exact Hcpsr|exact Hmask]. }
  match type of Hafter with ?P after =>
    assert (Hpost : P |-- task_tcb_init_stack_save_post external platform port critical
      continuations sg call mask final_registers.(kernel_save_r0) state ** frame)
  end.
  { unfold task_tcb_init_stack_save_post; Exists call state; entailer!. }
  exact (Hpost after Hafter).
Qed.

(** The second real Save consumer transports the original detached
    allocation identity and exposes the resources at THIS acquired cut.
    The current map comes from the source-facing Save post, never from
    the first acquisition or from a pure client certificate. *)
Lemma task_tcb_init_stack_save_commit_resources :
  forall external platform port critical
    (continuations : Armv7aContinuationABI external platform port)
    sg args original mask saved first slot rest image,
  task_tcb_init_entry sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first ->
  task_tcb_init_detach_observation args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first slot rest image ->
  task_tcb_init_stack_save_post external platform port critical continuations sg original mask saved
    (task_tcb_init_detached_state args original.(os_sched_call_invocation)
      original.(os_sched_call_origin) first slot rest image) |--
  EX returned current,
    coq_prop (task_tcb_init_commit_binding args original.(os_sched_call_invocation)
      original.(os_sched_call_origin) first current slot /\
      critical_region_interval critical sg original.(os_sched_call_invocation)
        (task_tcb_init_detached_state args original.(os_sched_call_invocation)
          original.(os_sched_call_origin) first slot rest image) current /\
      returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      task_stack_live_coverage current.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved current **
     os_sched_context_resources external returned ** UCOS2_inv sg current **
     armv7a_task_stack_continuations continuations current.(TskState)
       current.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port critical continuations sg args original mask saved first slot rest image
    Hentry Hdetach.
  unfold task_tcb_init_stack_save_post; Intros returned current.
  assert (Hsource : kernel_call_save_source external port critical sg original returned mask saved
    (task_tcb_init_detached_state args original.(os_sched_call_invocation)
      original.(os_sched_call_origin) first slot rest image) current) by tauto.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsource) as Hinterval.
  destruct (task_tcb_init_acquire_commit critical sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first slot rest image current Hentry Hdetach Hinterval)
    as [Hvalid [Hcommit Hactive]].
  pose proof Hsource as [_ [Hinvocation [Horigin _]]].
  Exists returned current; rewrite Hinvocation, Horigin; entailer!.
Qed.

(** Handover is completed before the actual final Restore MSR.  The
    caller's buffer and the publication heap are consumed into the new
    protected world before its saved/inside tokens are released.  This
    endpoint is BEFORE possible IRQ work at the BX cursor: it asserts no
    stale map, readiness or initial-frame ownership at the later C return. *)
Lemma task_tcb_init_stack_publication_restore_prefix :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    sg publication current call saved cursor before written_cursor after (frame : Assertion),
  UCOS2_state_inv sg current ->
  task_create_stack_publication_input sg publication current ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_create_stack_publication_resources external platform port continuations sg publication current **
   critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved current **
   os_sched_context_resources external call ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor after ->
  kernel_client_step (task_create_stack_publication_client publication) sg current
    (task_create_stack_publication_state sg publication current) /\
  written_cursor = kernel_restore_write_cpsr cursor /\
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask saved) **
   UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
   armv7a_task_continuations continuations
     (task_create_stack_publication_state sg publication current).(TskState).(parkedTaskStacks) **
   frame) after.
Proof.
  intros external platform port critical arch continuations restore sg publication current
    call saved cursor before written_cursor after frame Hvalid Hinput Hr0 Hmask Hbefore Hrun.
  assert (Hhandover : task_create_stack_publication_resources external platform port continuations
      sg publication current **
      critical_region_masked platform critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) saved current ** os_sched_context_resources external call ** frame |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved current ** os_sched_context_resources external call **
    (UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
     armv7a_task_continuations continuations
       (task_create_stack_publication_state sg publication current).(TskState).(parkedTaskStacks) ** frame)).
  { pose proof (task_create_stack_publication_source_post external platform port
      continuations sg publication current Hvalid Hinput) as Hclose.
    cbv zeta in Hclose; sep_apply_l_atomic Hclose; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region external platform critical arch restore
    sg call saved current cursor before written_cursor after _ Hr0 Hmask
    (Hhandover before Hbefore) Hrun) as [Hcursor [Hmemory Hafter]].
  split; [split; [exact Hinput|reflexivity]|].
  split; [exact Hcursor|]. split; [exact Hmemory|].
  match type of Hafter with ?P after =>
    assert (Horder : P |--
      kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask saved) **
      UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
      armv7a_task_continuations continuations
        (task_create_stack_publication_state sg publication current).(TskState).(parkedTaskStacks) ** frame)
  end.
  { entailer!. }
  exact (Horder after Hafter).
Qed.

(** The real NULL free-root observation selects return code 66.  In this
    explicitly uninterrupted Restore branch there has been no allocation
    or publication, so the very same initialized caller buffer is returned.
    An IRQ between MSR and BX requires the separate returning source chain;
    it is not erased by this local rule. *)
Lemma task_tcb_init_stack_no_free_uninterrupted_return :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    sg region args task_return lower upper initial_name call mask initial acquired saved
    cursor before written_cursor middle final_cursor after (frame : Assertion),
  let actual := task_create_tcb_args args
    (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_entry sg actual call.(os_sched_call_invocation) call.(os_sched_call_origin) initial ->
  critical_region_interval critical sg call.(os_sched_call_invocation) initial acquired ->
  pointer_load sg.(g_OSTCBFreeList) 0 before ->
  interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
   UCOS2_inv sg acquired **
   task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
   armv7a_task_continuations continuations acquired.(TskState).(parkedTaskStacks) ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  task_tcb_init_result critical sg actual call.(os_sched_call_invocation)
    call.(os_sched_call_origin) initial 66 acquired /\
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (task_tcb_init_post platform critical sg actual call.(os_sched_call_invocation)
     call.(os_sched_call_origin) mask initial 66 **
   task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
   armv7a_task_continuations continuations acquired.(TskState).(parkedTaskStacks) **
   os_sched_context_resources external call ** frame) after.
Proof.
  intros external platform port critical arch continuations restore sg region args task_return
    lower upper initial_name call mask initial acquired saved cursor before written_cursor middle
    final_cursor after frame actual Hentry Hinterval Hnull Hsaved Hr0 Hmask Hbefore Hprefix Hsuffix.
  pose proof (task_tcb_init_acquire_entry critical sg actual call.(os_sched_call_invocation)
    call.(os_sched_call_origin) initial acquired Hentry Hinterval) as Hacquired.
  match type of Hbefore with ?P before =>
    assert (Hroot : P |-- sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_root sg acquired ** TT)
  end.
  { unfold UCOS2_inv; Intros.
    sep_apply_l_atomic (task_tcb_init_raw_split_free_root sg acquired).
    entailer!; intros ? ?; exact I. }
  pose proof (framed_pointer_store_load _ _ _ before (Hroot before Hbefore)) as Hload.
  assert (Hzero : task_tcb_init_free_root sg acquired = 0)
    by (eapply pointer_load_deterministic; eassumption).
  assert (Hresult : task_tcb_init_result critical sg actual call.(os_sched_call_invocation)
    call.(os_sched_call_origin) initial 66 acquired).
  { apply TaskTCBInitNoFree; [exact Hinterval| |exact (proj1 (proj2 (proj2 (proj2 Hacquired))))|exact (proj1 Hacquired)].
    eapply task_tcb_init_free_root_zero__publication_and_returns; [exact (proj1 Hacquired)|exact Hzero]. }
  match type of Hbefore with ?P before =>
    assert (Horder : P |--
      critical_region_masked platform critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
      (UCOS2_inv sg acquired **
       task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
       armv7a_task_continuations continuations acquired.(TskState).(parkedTaskStacks) ** frame))
  end.
  { entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch
    restore sg call saved acquired cursor before written_cursor middle final_cursor after _ Hr0 Hmask
    (Horder before Hbefore) Hprefix Hsuffix) as [Hrun [Hreturn [Hmemory Hafter]]].
  split; [exact Hresult|]. split; [exact Hrun|]. split; [exact Hreturn|].
  match type of Hafter with ?P after =>
    assert (Hpost : P |-- task_tcb_init_post platform critical sg actual call.(os_sched_call_invocation)
      call.(os_sched_call_origin) mask initial 66 **
      task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
      armv7a_task_continuations continuations acquired.(TskState).(parkedTaskStacks) **
      os_sched_context_resources external call ** frame)
  end.
  { unfold task_tcb_init_post, kernel_call_execution_owned; Exists acquired.
    unfold critical_region_outside; rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; rewrite (proj2 Hsaved); entailer!. }
  exact (Hpost after Hafter).
Qed.

(** The last actual selection of a normally returning Save must return
    the current complete capsule map, not just the pending caller's focused
    entry.  Install/take consumes the selected slot and its physical frame;
    the restore exchange and masked suffix transport the remaining map on
    the same successive heaps.  No pre-interruption map equality, ready
    coverage law, hook behavior or existence of a returning execution is
    assumed.  [Some original] and PC/LR equations identify this continuation
    as a returning Save, excluding a newly created task's first entry. *)
Lemma task_tcb_init_selected_save_resources :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg handler original transfer return_pc (frame : Assertion) heap,
  os_int_exit_destination_binding external transfer ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
   armv7a_task_continuations continuations
     transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) heap ->
  exists installed saved,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    armv7a_continuation_binding saved /\
    saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) /\
    (forall registers restored final_registers acquired after,
      saved.(armv7a_continuation_call) = Some original ->
      saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
      saved.(armv7a_continuation_lr) = return_pc ->
      registers.(kernel_save_cpsr) = saved.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 saved.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = saved.(armv7a_continuation_lr) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
        registers.(kernel_save_r0) ->
      armv7a_continuation_restore_reads saved installed ->
      armv7a_restore_transition continuations handler saved installed restored ->
      armv7a_save_suffix_transition suffix registers (os_int_exit_installed_state transfer)
        restored final_registers acquired after ->
      acquired = os_int_exit_installed_state transfer /\
      final_registers.(kernel_save_return_word) = Some return_pc /\
      final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
      (critical_region_masked platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
       UCOS2_inv sg acquired **
       armv7a_task_continuations continuations acquired.(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame) after).
Proof.
  intros external platform port critical arch continuations suffix sg handler original
    transfer return_pc frame heap Hdestination Haddress Hpre.
  destruct (armv7a_install_take_task_continuation external platform port continuations
    sg transfer _ heap Hdestination Haddress Hpre)
    as [installed [saved [Hinstall [Hbinding [Hstack [Hfragments [Hcurrent Howned]]]]]]].
  exists installed, saved; split; [exact Hinstall|]. split; [exact Hbinding|].
  split; [exact Hstack|].
  intros registers restored final_registers acquired after
    Hcall Hpc Hlr Hcpsr Hr0 Hregisterlr Hsaved Hreads Hrestore Hsuffix.
  assert (Hrestore_input : UCOS2_inv sg (os_int_exit_installed_state transfer) **
      armv7a_task_continuations continuations
        (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) **
      armv7a_task_continuation_resource continuations saved **
      (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation continuations saved **
    (UCOS2_inv sg (os_int_exit_installed_state transfer) **
     armv7a_task_continuations continuations
       (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) ** frame)).
  { unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!. }
  destruct (armv7a_restore_call_resources external platform port continuations handler saved original
    _ installed restored Hcall Hreads (Hrestore_input installed Howned) Hrestore)
    as [Hmemory Hreturned].
  match type of Hreturned with ?P restored =>
    assert (Hsuffix_input : P |--
      kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved original)
        (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
      (UCOS2_inv sg (os_int_exit_installed_state transfer) **
       armv7a_task_continuations continuations
         (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame))
  end.
  { rewrite Hcpsr; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg
    (armv7a_continuation_resumed_call saved original) registers (os_int_exit_installed_state transfer)
    restored final_registers acquired after _ Hsaved (Hsuffix_input restored Hreturned) Hsuffix)
    as [Hstate [Hmemory_after [Hreturn [Hresult Hafter]]]].
  split; [exact Hstate|]. split; [rewrite Hreturn, Hregisterlr; exact (f_equal Some Hlr)|].
  split; [exact Hresult|]. subst acquired.
  match type of Hafter with ?P after =>
    assert (Hpack : P |-- critical_region_masked platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) final_registers.(kernel_save_r0) (os_int_exit_installed_state transfer) **
      os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
      UCOS2_inv sg (os_int_exit_installed_state transfer) **
      armv7a_task_continuations continuations
        (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame)
  end.
  { cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
  exact (Hpack after Hafter).
Qed.
