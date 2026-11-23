Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_irq_sched_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A foreign running task is not an all-parked handler world. Consume its
    actual IRQ frame save and SP/nesting writes first, then ONE registry
    heap/state/source trace. The earlier pending call's active registration
    and saved SP follow that trace; they are not supplied again at its end.
    A false-stop result identifies the returning branch, not termination of
    every trace. The selector/install consumer below this cut still has to
    select and restore the original task on its actual heap. *)
Lemma task_create_foreign_irq_registry_source : forall environment critical Extra
  extra_resources extra_step extra_effect sg entry node handler foreign_saved publication
  original suspended (frame : Assertion) before saved_heap,
  let abi := environment.(task_stack_call_continuations) in
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let parked := armv7a_irq_live_parked_state entry call foreign_saved.(armv7a_continuation_sp)
    foreign_saved.(armv7a_continuation_fragments) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  armv7a_task_frame_slice foreign_saved ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    foreign_saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    foreign_saved.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut initial next returned, extra_effect sg cut initial next returned ->
    UCOS2_state_inv sg initial ->
    task_saved_pointer_at initial suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None extra_effect ->
  (os_int_exit_frame_save_pre environment.(task_stack_call_external)
     environment.(task_stack_call_platform) handler **
   (kernel_program_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
      entry.(TskState).(parkedTaskStacks) ** frame)) before ->
  armv7a_save_transition abi handler foreign_saved before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes foreign_saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) foreign_saved.(armv7a_continuation_sp))
      saved_heap registry_heap /\
    (forall closed_heap,
      kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
        KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
          KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          original.(os_sched_call_invocation) None original.(os_sched_call_origin)
          parked stopped returned_origin returned /\
        task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
          suspended.(armv7a_continuation_sp) /\
        (stopped = false -> task_invocation_active returned.(TskState)
          original.(os_sched_call_invocation) original.(os_sched_call_origin)) /\
        (kernel_client_call_stack_world abi sg focus payload returned **
         (interrupt_platform_running environment.(task_stack_call_platform)
            handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
          os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) closed_heap).
Proof.
  intros environment critical Extra extra_resources extra_step extra_effect sg entry node handler foreign_saved
    publication original suspended frame before saved_heap abi call focus payload parked Hbinding Hcall Hactive
    Hpointer Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hextension Hextra Henter Hexit Hpublish Hsource Hpre Hsave.
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hdifferent : suspended.(armv7a_continuation_stack).(stackLeaseSlot) <>
    call.(os_sched_call_stack).(stackLeaseSlot)).
  { intros Heq; destruct Hpointer as [old [Hold [Hg Hsp_old]]].
    rewrite Heq in Hold; assert (old = node) by congruence; subst old.
    assert (Hkey : task_stack_key call.(os_sched_call_stack) = armv7a_call_focus_key focus).
    { unfold task_stack_key, armv7a_call_focus_key, focus, armv7a_call_focus.
      cbn; rewrite <- Hlease; unfold task_stack_key; congruence. }
    rewrite Hkey in Hnone; congruence. }
  match type of Hpre with ?P before => assert (Horder : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
      entry.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame)))
    by (rewrite kernel_program_inv_split_unmap; entailer!) end.
  destruct (armv7a_irq_source_save_preserves_pending_call _ _ _ abi sg entry node handler foreign_saved
    publication focus payload (unmap_table_rep sg ** frame) before saved_heap Hslice Hrunning Hnesting
    Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    (Horder before Hpre) Hsave)
    as [registry_heap [Hwrites [Hstores [Hcovered [Hpending [Hjoint [Hmerged Hinterrupted]]]]]]].
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node foreign_saved.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      foreign_saved.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hparked_active : task_invocation_active parked.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { rewrite Htasks; change (task_invocation_active
      (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
        (task_set_saved_sp node foreign_saved.(armv7a_continuation_sp)))
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
    eapply task_set_saved_sp_preserves_invocation_active; eassumption. }
  assert (Hparked_pointer : task_saved_pointer_at parked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { destruct Hpointer as [old [Hold [Hg Hsp_old]]]; exists old; split; [|auto].
    rewrite Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    destruct (Z.eqb _ _) eqn:Heq; [apply Z.eqb_eq in Heq; contradiction|exact Hold]. }
  assert (Hvalid : UCOS2_state_inv sg parked).
  { match type of Hmerged with ?P registry_heap => assert (Hexpose : P |--
      coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose registry_heap Hmerged)). }
  match type of Hmerged with ?P registry_heap => assert (Hregistry : P |--
    kernel_client_call_stack_world abi sg focus payload parked **
    (interrupt_platform_running environment.(task_stack_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) end.
  { unfold kernel_client_call_stack_world, kernel_client_call_stack_facts.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (kernel_client_call_stack_trace_source_resources _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None Hextension Henter Hexit Hpublish Hsource
    KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap _ Htrace
    parked original.(os_sched_call_origin) I (Hregistry registry_heap Hmerged))
    as [returned [stopped [returned_origin [Hstates [Hsources [Hcut Hworld]]]]]].
  destruct (kernel_client_trace_preserves_saved_pointer Extra extra_effect sg
    suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hextra
    KernelClientHeapClosed parked KernelClientHeapClosed returned Hstates Hvalid Hparked_pointer)
    as [Hreturned Hreturned_pointer].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  split; [exact Hreturned_pointer|]. split; [|exact Hworld].
  intro Hnormal.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    parked stopped returned_origin returned Hsources)) as Hinterval.
  rewrite Hnormal in Hinterval.
  destruct (critical_region_interval_transports_resources critical sg original.(os_sched_call_invocation)
    parked returned Hinterval Hvalid) as [_ [_ Hlive]].
  apply Hlive; exact Hparked_active.
Qed.

(** The published TCB's masked endpoint can take an IRQ after Restore's
    MSR. Compose that actual branch through OSIntExit and BX, retaining the
    earlier pending call. The returned creator stage and owned world are
    the inputs of [task_create_nonswitch_sched_preserves_pending_call] and
    [task_create_pending_sched_switch_source]; this cut neither strengthens
    the public callee contract nor excludes other handler/switch paths. *)
Lemma task_create_tcb_restore_irq_preserves_pending_call : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg acquired released node handler suspended publication focus payload
  saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let returned := os_int_exit_counter_state parked.(SchedState).(isRunning) parked in
  let current := os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_create_call_stage call released ->
  armv7a_task_frame_slice suspended ->
  released.(SchedState).(isRunning) = true -> released.(IntrState).(intNesting) = 0 ->
  released.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  released.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  released.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  released.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened released.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  task_stack_live_coverage released.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  interrupt_exit_requests_schedule parked.(SchedState).(isRunning) parked.(IntrState) = false ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
   task_tcb_init_stack_context environment call ** kernel_program_inv sg released **
   armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
  (forall written irq_input saved_heap,
    armv7a_restore_prefix_transition restore cursor before written irq_input ->
    armv7a_save_transition abi handler suspended irq_input saved_heap ->
    exists registry_heap exit_heap,
      written = kernel_restore_write_cpsr cursor /\
      kernel_heap_writes (armv7a_continuation_save_writes suspended)
        irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
      kernel_heap_execution (armv7a_irq_live_entry_writes sg released
        call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
        saved_heap registry_heap /\
      os_int_exit_masked_no_schedule_fragment sg registry_heap exit_heap /\
      armv7a_irq_restore_pointer_reads sg exit_heap
        (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot))
        suspended.(armv7a_continuation_sp) /\
      task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call /\
      task_create_call_stage (armv7a_continuation_resumed_call suspended call) current /\
      task_stack_live_coverage current.(TskState)
        (task_stack_call_active_key (armv7a_continuation_resumed_call suspended call)) /\
      current.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload /\
      (forall irq_return resume_cursor final_cursor after,
        armv7a_restore_transition abi handler suspended exit_heap irq_return ->
        resume_cursor.(kernel_restore_msr_word) = Some
          (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) ->
        resume_cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
        armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
        final_cursor.(kernel_restore_return_word) = Some suspended.(armv7a_continuation_lr) /\
        (kernel_call_execution_owned environment.(task_stack_call_external)
           environment.(task_stack_call_platform) (armv7a_continuation_resumed_call suspended call)
           (armv7a_irq_fiq_mask saved) **
         kernel_program_inv sg current **
         armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
         (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
           handler.(os_int_exit_handler_fragments) ** frame)) after)).
Proof.
  intros environment critical arch restore sg acquired released node handler suspended publication
    focus payload saved cursor before frame call abi parked returned current
    Horigin Hstage Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus
    Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hbranch Hr0 Hmask Hhandler Hpre
    written irq_input saved_heap Hprefix Hsave.
  match type of Hpre with ?P before => assert (Hrelease : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_program_inv sg released **
     armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold task_tcb_init_stack_context; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region _ _ _ _ restore sg call saved acquired
    cursor before written irq_input _ Hr0 Hmask (Hrelease before Hpre) Hprefix)
    as [Hwritten [Hmemory Hreleased]].
  match type of Hreleased with ?P irq_input => assert (Hirq : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg released **
     armv7a_task_call_stacks abi released.(TskState) focus released.(TskState).(parkedTaskStacks) **
     (unmap_table_rep sg ** frame))) end.
  { unfold os_int_exit_frame_save_pre; rewrite Hhandler, kernel_program_inv_split_unmap; entailer!. }
  destruct (armv7a_irq_source_no_schedule_preserves_pending_call _ _ _ abi sg released node handler
    suspended publication focus payload (unmap_table_rep sg ** frame) irq_input saved_heap
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hbranch (Hirq irq_input Hreleased) Hsave)
    as [registry_heap [exit_heap [Hwrites [Hstores [Hexit [Hpointers [Hcovered [Hretained Hresume]]]]]]]].
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hsaved_mask Hobserved]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hready : task_create_irq_caller_stage call released).
  { eapply task_create_call_stage_irq_entry; eassumption. }
  assert (Hready_returned : task_create_irq_caller_stage call returned).
  { apply task_create_irq_counter_exit_preserves_caller_stage.
    eapply task_create_irq_deposit_preserves_caller_stage; eassumption. }
  assert (Hstage_current : task_create_call_stage (armv7a_continuation_resumed_call suspended call) current).
  { unfold current; rewrite Hlease; apply task_create_irq_take_reestablishes_call_stage; assumption. }
  assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call).
  { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    repeat split; assumption || reflexivity. }
  assert (Hactive : task_stack_call_active_key (armv7a_continuation_resumed_call suspended call) =
    Some (task_stack_key suspended.(armv7a_continuation_stack))).
  { unfold task_stack_call_active_key, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin os_sched_call_stack]; rewrite Horigin, Hlease; reflexivity. }
  exists registry_heap, exit_heap.
  split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  split; [exact Hexit|]. split; [exact Hpointers|]. split; [exact Hsame|].
  split; [exact Hstage_current|]. split; [rewrite Hactive; exact Hcovered|].
  split; [exact Hretained|].
  intros irq_return resume_cursor final_cursor after Hrestore Hword Hlr Hsuffix.
  destruct (Hresume irq_return Hrestore) as [Hreturned_memory Howned].
  rewrite Hhandler in Hsaved_mask; rewrite Hsaved_mask in Howned.
  match type of Howned with ?P irq_return => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (armv7a_continuation_resumed_call suspended call)
      (armv7a_irq_fiq_mask (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
        cursor.(kernel_restore_r0))) **
    (kernel_program_inv sg current **
     armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
     (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame))) end.
  { rewrite armv7a_cpsr_restore_mask_eq, Hr0, kernel_program_inv_split_unmap; entailer!. }
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call suspended call)
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))
    resume_cursor irq_return final_cursor after _ Hword (Hsuffix_input irq_return Howned) Hsuffix)
    as [Hcursor [Hfinal_memory Hfinal]].
  split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hfinal.
    match type of Hfinal with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) by entailer! end end.
    exact (Hclose after Hfinal).
Qed.

(** The pending observer and the currently executing foreign call have
    distinct roles.  The latter's source registration is established by
    initial entry or its earlier saved-call producer, not inferred from a
    dormant token.  The actual IRQ save, SP/nesting stores and park produce
    the all-parked registry cut.  Its source origin tracks that interrupted
    task; the handler's own CPU/stack owner stays separately in [frame].
    No premise identifies the final origin with the pending observer. *)
Lemma task_create_foreign_irq_registry_execution_source : forall environment critical Extra
  extra_resources extra_source extra_step extra_effect sg entry node handler foreign_saved publication
  original suspended (frame : Assertion) before saved_heap,
  let abi := environment.(task_stack_call_continuations) in
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let parked := armv7a_irq_live_parked_state entry call foreign_saved.(armv7a_continuation_sp)
    foreign_saved.(armv7a_continuation_fragments) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  armv7a_task_frame_slice foreign_saved ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  entry.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    foreign_saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    foreign_saved.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  kernel_call_task_source call entry ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut initial next returned, extra_effect sg cut initial next returned ->
    UCOS2_state_inv sg initial ->
    task_saved_pointer_at initial suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_execution_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg original.(os_sched_call_invocation) None extra_source extra_effect ->
  (os_int_exit_frame_save_pre environment.(task_stack_call_external)
     environment.(task_stack_call_platform) handler **
   (kernel_program_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
      entry.(TskState).(parkedTaskStacks) ** frame)) before ->
  armv7a_save_transition abi handler foreign_saved before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes foreign_saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) foreign_saved.(armv7a_continuation_sp))
      saved_heap registry_heap /\
    (forall closed_heap,
      kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
        KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
          KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          original.(os_sched_call_invocation) None call.(os_sched_call_origin)
          parked stopped returned_origin returned /\
        task_execution_current returned_origin returned /\
        task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
          suspended.(armv7a_continuation_sp) /\
        (stopped = false -> task_invocation_active returned.(TskState)
          original.(os_sched_call_invocation) original.(os_sched_call_origin)) /\
        (kernel_client_call_stack_world abi sg focus payload returned **
         (interrupt_platform_running environment.(task_stack_call_platform)
            handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
          os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) closed_heap).
Proof.
  intros environment critical Extra extra_resources extra_source extra_step extra_effect sg entry node handler foreign_saved
    publication original suspended frame before saved_heap abi call focus payload parked Hbinding Hcall Hactive
    Hpointer Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hcall_source Hextension Hextra Henter Hexit Hpublish Hsource Hpre Hsave.
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hdifferent : suspended.(armv7a_continuation_stack).(stackLeaseSlot) <>
    call.(os_sched_call_stack).(stackLeaseSlot)).
  { intros Heq; destruct Hpointer as [old [Hold [Hg Hsp_old]]].
    rewrite Heq in Hold; assert (old = node) by congruence; subst old.
    assert (Hkey : task_stack_key call.(os_sched_call_stack) = armv7a_call_focus_key focus).
    { unfold task_stack_key, armv7a_call_focus_key, focus, armv7a_call_focus.
      cbn; rewrite <- Hlease; unfold task_stack_key; congruence. }
    rewrite Hkey in Hnone; congruence. }
  match type of Hpre with ?P before => assert (Horder : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg entry ** armv7a_task_call_stacks abi entry.(TskState) focus
      entry.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame)))
    by (rewrite kernel_program_inv_split_unmap; entailer!) end.
  destruct (armv7a_irq_source_save_preserves_pending_call _ _ _ abi sg entry node handler foreign_saved
    publication focus payload (unmap_table_rep sg ** frame) before saved_heap Hslice Hrunning Hnesting
    Hcurrent Hnode Hid Hgen Hnone Hfocus Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    (Horder before Hpre) Hsave)
    as [registry_heap [Hwrites [Hstores [Hcovered [Hpending [Hjoint [Hmerged Hinterrupted]]]]]]].
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node foreign_saved.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      foreign_saved.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hparked_active : task_invocation_active parked.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { rewrite Htasks; change (task_invocation_active
      (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
        (task_set_saved_sp node foreign_saved.(armv7a_continuation_sp)))
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
    eapply task_set_saved_sp_preserves_invocation_active; eassumption. }
  assert (Hparked_pointer : task_saved_pointer_at parked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { destruct Hpointer as [old [Hold [Hg Hsp_old]]]; exists old; split; [|auto].
    rewrite Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    destruct (Z.eqb _ _) eqn:Heq; [apply Z.eqb_eq in Heq; contradiction|exact Hold]. }
  assert (Hvalid : UCOS2_state_inv sg parked).
  { match type of Hmerged with ?P registry_heap => assert (Hexpose : P |--
      coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose registry_heap Hmerged)). }
  match type of Hmerged with ?P registry_heap => assert (Hregistry : P |--
    kernel_client_call_stack_world abi sg focus payload parked **
    (interrupt_platform_running environment.(task_stack_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) end.
  { unfold kernel_client_call_stack_world, kernel_client_call_stack_facts.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  assert (Hparked_current : kernel_client_heap_source_cut extra_source
    (@KernelClientHeapClosed Extra) call.(os_sched_call_origin) parked).
  { split; [|exact I].
    pose proof (proj1 Hcall_source) as Horigin.
    assert (Hcurrent_pointer : parked.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID)).
    { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
        armv7a_irq_entry_counter_state, os_sched_save_current_sp.
      rewrite Hrunning; cbn [replace_IntrS TskState SchedState].
      rewrite Hnode; reflexivity. }
    unfold task_execution_current; rewrite Horigin, Hcurrent_pointer; exact Hcurrent. }
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (kernel_client_call_stack_trace_execution_resources _ _ _ Extra abi
    extra_resources focus payload extra_source extra_step extra_effect critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None Hextension Henter Hexit Hpublish Hsource
    KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap _ Htrace
    parked call.(os_sched_call_origin) I Hparked_current (Hregistry registry_heap Hmerged))
    as [returned [stopped [returned_origin [Hstates [Hsources [Hcut [Hexecution Hworld]]]]]]].
  destruct (kernel_client_trace_preserves_saved_pointer Extra extra_effect sg
    suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hextra
    KernelClientHeapClosed parked KernelClientHeapClosed returned Hstates Hvalid Hparked_pointer)
    as [Hreturned Hreturned_pointer].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  split; [exact (proj1 Hexecution)|]. split; [exact Hreturned_pointer|]. split; [|exact Hworld].
  intro Hnormal.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None call.(os_sched_call_origin)
    parked stopped returned_origin returned Hsources)) as Hinterval.
  rewrite Hnormal in Hinterval.
  destruct (critical_region_interval_transports_resources critical sg original.(os_sched_call_invocation)
    parked returned Hinterval Hvalid) as [_ [_ Hlive]].
  apply Hlive; exact Hparked_active.
Qed.
