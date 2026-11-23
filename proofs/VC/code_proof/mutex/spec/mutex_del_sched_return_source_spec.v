Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These creator steps only change Event or the interrupt counter. In
    particular a reused ECB cannot overwrite the suspended caller's TCB SP. *)
Lemma mutex_del_creator_interrupt_task_frame : forall creator sg cut state next returned,
  mutex_del_creator_interrupt_effect creator sg cut state next returned ->
  returned.(TskState) = state.(TskState).
Proof.
  intros creator sg cut state next returned Hstep; destruct Hstep; try reflexivity.
  destruct H.
  - destruct H; eapply event_create_allocate_critical_task_frame; eassumption.
  - change (initialized.(TskState) = state.(TskState)).
    exact (proj1 (proj2 (proj2 (event_create_private_stores_published_frame _ _ _ _ _ H1)))).
Qed.

(** Run the physical registry once, transporting its real saved-SP field
    alongside the same abstract and source traces. Task publication uses
    allocation disjointness; creator steps preserve the existing TCB fields. *)
Lemma mutex_del_creator_trace_saved_pointer : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients actor creator
  sg observer focus payload lease sp cut before next after (frame : Assertion),
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  task_saved_pointer_at state lease sp ->
  (mutex_del_stack_registry abi sg focus payload cut state ** frame) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer None
      origin state false returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    task_saved_pointer_at returned lease sp /\
    (mutex_del_stack_registry abi sg focus payload next returned ** frame) after.
Proof.
  intros external platform port abi clients actor creator sg observer focus payload lease sp cut before next after
    frame Hinclude Hforeign Hargs Htrace.
  induction Htrace; intros state origin Hcut Hpointer Hpre.
  - exists state, origin; split; [constructor|]. split; [constructor|].
    split; [exact Hcut|]. split; assumption.
  - assert (Hopen : mutex_del_stack_registry abi sg focus payload cut state ** frame |--
      coq_prop (mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState)) &&
      (kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
        sg focus payload cut state ** event_private_pool_rep sg state.(EventState) ** frame)).
    { unfold mutex_del_stack_registry; entailer!. }
    destruct (Hopen before Hpre) as [[Hhistory Htypes] Howned].
    pose proof (proj1 (mutex_del_creator_pool_resources_valid external platform port abi sg focus payload cut state
      frame before Howned)) as Hvalid.
    assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
    { pose proof Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
    destruct (event_private_pool_call_stack_step external platform port Z abi
      (mutex_del_creator_pool_cursor abi focus payload) focus payload
      (mutex_del_creator_interrupt_step creator) (mutex_del_creator_interrupt_effect creator)
      (mutex_del_creator_pool_extension external platform port abi focus payload creator Hargs)
      sg cut before middle_cut middle state frame H Howned) as [middle_state [Hstep Hmiddle]].
    assert (Hmiddle_pointer : task_saved_pointer_at middle_state lease sp).
    { destruct Hstep.
      - exact Hpointer.
      - exact Hpointer.
      - eapply task_publication_preserves_saved_pointer; eassumption.
      - unfold task_saved_pointer_at in *.
        rewrite (mutex_del_creator_interrupt_task_frame _ _ _ _ _ _ H0); exact Hpointer. }
    assert (Hreachable : mutex_program_selected_reachable sg middle_state).
    { eapply mutex_program_source_step_reachable; [exact Hhistory|].
      eapply mutex_del_creator_interrupt_state_source; exact Hstep. }
    pose proof (mutex_del_creator_step_preserves_private_non_mutex creator sg cut state middle_cut
      middle_state Hvalid Htypes Hstep) as Hnonmutex_middle.
    assert (Hclose : kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
        sg focus payload middle_cut middle_state ** event_private_pool_rep sg middle_state.(EventState) ** frame |--
      mutex_del_stack_registry abi sg focus payload middle_cut middle_state ** frame).
    { unfold mutex_del_stack_registry; entailer!. }
    destruct (kernel_client_heap_state_step_source external port Z
      (mutex_del_creator_source_client actor creator) sg observer None (mutex_del_creator_interrupt_effect creator)
      ltac:(constructor; constructor) ltac:(intros; constructor; constructor)
      ltac:(intros; constructor; constructor)
      (mutex_del_creator_interrupt_extension_source external port actor creator sg observer Hforeign Hnames)
      cut state middle_cut middle_state origin Hcut Hstep)
      as [Hcompatible [stopped [middle_origin Hsource]]].
    pose proof (mutex_del_creator_source_trace_nonstopping external port actor creator sg observer None
      origin state stopped middle_origin middle_state Hsource) as ->.
    destruct (IHHtrace middle_state middle_origin Hcompatible Hmiddle_pointer (Hclose middle Hmiddle))
      as [returned [returned_origin [Hstates [Htail_source [Hnext [Hreturned_pointer Hpost]]]]]].
    exists returned, returned_origin; split; [econstructor; eassumption|]. split.
    + replace false with (orb false false) by reflexivity.
      eapply kernel_resumption_task_source_trace_trans; [|exact Htail_source].
      eapply kernel_resumption_task_source_trace_inclusion; eassumption.
    + split; [exact Hnext|]. split; assumption.
Qed.

(** The actual registry endpoint owns the current private pool and source
    history. OSIntExit then selects the original suspended Del call, executes
    the cache stores and frame reads, and its final OS_Sched Restore returns
    that same current owner. Event is unchanged only across this final tail;
    the preceding foreign registry may allocate, initialize or publish objects.
    Selection is a source-branch observation, never a public Del precondition. *)
Lemma mutex_del_selected_irq_sched_return : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg state handler original suspended saved acquired call_before before (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let checkpoint := os_int_exit_ready_checkpoint true state in
  let cached := replace_SchedS (sched_install_selected checkpoint.(SchedState)) checkpoint in
  let current := os_int_exit_wrapper_restored_state cached original.(os_sched_call_stack) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  state.(SchedState).(isRunning) = true ->
  os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  checkpoint.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg checkpoint checkpoint ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state **
   (interrupt_platform_running environment.(mutex_del_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(mutex_del_call_port) handler **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame))) before ->
  exists prepared installed selected,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    kernel_heap_execution [] prepared prepared /\
    kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg checkpoint checkpoint /\
    sched_install_heap_fragment sg prepared installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    (forall irq_return cursor written middle final_cursor after,
      armv7a_restore_transition abi handler selected installed irq_return ->
      cursor.(kernel_restore_r0) = saved ->
      cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
      armv7a_restore_prefix_transition restore cursor irq_return written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
      kernel_call_task_source (armv7a_continuation_resumed_call selected original) current /\
      (os_sched_stack_return_post (mutex_del_runtime_sched_environment environment)
         mutex_del_stack_resources sg original (armv7a_irq_fiq_mask saved) call_before **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) after /\
      (mutex_del_source_return environment environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved) **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) after).
Proof.
  intros environment critical arch restore sg state handler original suspended saved acquired call_before
    before frame abi focus payload checkpoint cached current Horigin Hbinding Hcall Hslice Hmask Hactive
    Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_program_selected_reachable sg state /\
      mutex_del_private_types_non_mutex state.(EventState)) &&
    (kernel_client_call_stack_world abi sg focus payload state **
     (interrupt_platform_running environment.(mutex_del_call_platform)
        handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources environment.(mutex_del_call_port) handler **
      (interrupt_platform_saved environment.(mutex_del_call_platform)
         (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
       critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
       (event_private_pool_rep sg state.(EventState) ** frame))))) end.
  { unfold mutex_del_stack_registry; cbn [kernel_client_call_stack_resources]; entailer!. }
  destruct (Hopen before Hpre) as [[Hhistory Htypes] Howned].
  assert (Htransport : event_private_pool_rep sg state.(EventState) |--
    event_private_pool_rep sg current.(EventState)) by reflexivity.
  assert (Hreachable : mutex_program_selected_reachable sg current).
  { eapply mutex_program_source_step_reachable; [exact Hhistory|].
    apply MutexOwnerSourceFrame; reflexivity. }
  destruct (sched_selected_irq_return_resources (mutex_del_runtime_sched_environment environment)
    critical arch restore (fun sg state => event_private_pool_rep sg state.(EventState))
    sg state handler original suspended saved acquired before frame Htransport Horigin Hbinding Hcall
    Hslice Hmask Hactive Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Howned)
    as [prepared [installed [selected [Hprefix [Hempty [Hhooked [Hinstall
      [Hcpsr [Hregisters [Hsame [Hactive_now [Hready_now Hreturn]]]]]]]]]]]].
  exists prepared, installed, selected.
  split; [exact Hprefix|]. split; [exact Hempty|]. split; [exact Hhooked|].
  split; [exact Hinstall|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix.
  destruct (Hreturn irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix)
    as [Hexecution [Hordinary Hreturned]].
  assert (Hminimal : (os_sched_stack_return_post (mutex_del_runtime_sched_environment environment)
    mutex_del_stack_resources sg original (armv7a_irq_fiq_mask saved) call_before **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) after).
  { match type of Hreturned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post.
      Exists (armv7a_continuation_resumed_call selected original) current.
      unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources; entailer!. }
    exact (Hclose after Hreturned). }
  split; [exact Hexecution|]. split; [exact Hordinary|]. split; [exact Hminimal|].
  assert (Hstage : mutex_del_call_stage (armv7a_continuation_resumed_call selected original) current).
  { unfold mutex_del_call_stage; rewrite (proj1 (proj2 Hsame)), Horigin.
    split; [exact Hordinary|]. intros _.
    rewrite (proj2 (proj2 Hsame)); exact Hready_now. }
  match type of Hreturned with ?P after => match goal with |- ?Q after => assert (Hpublic : P |-- Q) end end.
  { unfold mutex_del_source_return, mutex_del_source_return_at, mutex_del_runtime_return_at.
    Exists (armv7a_continuation_resumed_call selected original) current environment.
    unfold mutex_del_callsite_environment, kernel_stack_call_closed, kernel_stack_inv,
      mutex_del_stack_resources; entailer!. }
  exact (Hpublic after Hreturned).
Qed.

(** The same physical creator/IRQ registry both transports the current pool
    and establishes the original invocation's saved pointer and active status.
    Its actual selected-return branch consumes those results directly. *)
Lemma mutex_del_creator_trace_sched_return : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  actor creator sg state source_origin handler original suspended saved acquired
  before registry_heap (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  (forall action, mutex_del_creator_source_client actor creator action ->
    critical.(critical_region_clients) action) ->
  actor <> Some original.(os_sched_call_invocation) -> mutex_del_creator_arguments creator ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
    KernelClientHeapClosed before KernelClientHeapClosed registry_heap ->
  (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state **
   (interrupt_platform_running environment.(mutex_del_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(mutex_del_call_port) handler **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** frame))) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg
      KernelClientHeapClosed state KernelClientHeapClosed returned /\
    kernel_resumption_task_source_trace environment.(mutex_del_call_external)
      environment.(mutex_del_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None source_origin state false returned_origin returned /\
    (forall
      (Hrunning : returned.(SchedState).(isRunning) = true)
      (Hswitch : os_int_exit_requests_switch true returned = true)
      (Hnonempty : returned.(SchedState).(readyList) <> [])
      (Hhigh : (os_int_exit_ready_checkpoint true returned).(SchedState).(highRdyTid) =
        Some original.(os_sched_call_stack).(stackLeaseSlot))
      (Hhook : kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg
        (os_int_exit_ready_checkpoint true returned) (os_int_exit_ready_checkpoint true returned))
      (Haddress : tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
        TCBStkPtr = task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)),
      exists prepared installed selected,
        os_int_exit_source_switch_prefix_execution sg registry_heap prepared /\
        sched_install_heap_fragment sg prepared installed
          (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        (forall irq_return cursor written middle final_cursor after,
          armv7a_restore_transition abi handler selected installed irq_return ->
          cursor.(kernel_restore_r0) = saved ->
          cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
          armv7a_restore_prefix_transition restore cursor irq_return written middle ->
          armv7a_restore_suffix_transition restore written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
          (mutex_del_source_return environment environment.(mutex_del_call_external)
             environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved) **
           (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
              handler.(os_int_exit_handler_fragments) ** frame)) after)).
Proof.
  intros environment critical arch restore actor creator sg state source_origin handler original suspended saved
    acquired before registry_heap frame abi focus payload Hinclude Hforeign Hargs Horigin Hbinding Hcall
    Hslice Hmask Hactive Hpointer Htrace Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hobserve : P |--
      coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold mutex_del_stack_registry; cbn [kernel_client_call_stack_resources].
      unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap.
      unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  destruct (mutex_del_creator_trace_saved_pointer _ _ _ abi critical.(critical_region_clients) actor creator
    sg original.(os_sched_call_invocation) focus payload suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) KernelClientHeapClosed before KernelClientHeapClosed registry_heap
    _ Hinclude Hforeign Hargs Htrace state source_origin I Hpointer Hpre)
    as [returned [returned_origin [Hstates [Hsource [Hcut [Hsaved_pointer Hreturned]]]]]].
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsource)) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg original.(os_sched_call_invocation)
    state returned Hinterval Hvalid) as [Hreturned_valid [Hcreation Hactive_preserved]].
  exists returned, returned_origin; split; [exact Hstates|]. split; [exact Hsource|].
  intros Hrunning Hswitch Hnonempty Hhigh Hhook Haddress.
  destruct (mutex_del_selected_irq_sched_return environment critical arch restore sg returned handler
    original suspended saved acquired state registry_heap frame Horigin Hbinding Hcall Hslice Hmask
    (Hactive_preserved _ Hactive) Hsaved_pointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hreturned)
    as [prepared [installed [selected [Hprefix [Hempty [Hhooked [Hinstall [Hcpsr [Hregisters Hreturn]]]]]]]]].
  exists prepared, installed, selected; split; [exact Hprefix|]. split; [exact Hinstall|].
  intros irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix.
  destruct (Hreturn irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix)
    as [Hexecution [Hordinary [Hminimal Hpost]]].
  split; assumption.
Qed.
