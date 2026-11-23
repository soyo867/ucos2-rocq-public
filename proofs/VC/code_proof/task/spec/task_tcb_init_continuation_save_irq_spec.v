Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_context Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Actual first-level IRQ between MRS and CPSID in OS_CPU_SR_Save.
    MRS fixes the saved R0, the approved register-save relation observes
    that value in the SAME IRQ descriptor, and exact-descriptor take
    restores it before the real CPSID/DSB/BX suffix. Every other entry's
    existing local owner stays in the generic map throughout.

    The interrupted call has not acquired its new Save/inside pair yet.
    The precise IRQ local therefore contains only the descriptor equality;
    any caller-owned private TCB or buffer remains once in [frame]. This
    reuses the current IRQ local/take interfaces without imposing the
    Scheduler PC=LR or mask=192 conditions on an IRQ descriptor.

    The selected registry subfamily starts and ends Closed, with no Extra
    source transition. It covers actual counter-only handler steps; it
    does not invent a publication cut, switch, nested IRQ/FIQ, or a law
    preserving arbitrary locals. Its endpoint is the canonical Save
    output, shared by the actual TCBInit/TaskCreate Save call sites. *)
Lemma task_tcb_init_continuation_mrs_irq_save_output :
  forall environment critical saved_local arch Extra
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (registers_source : Armv7aIRQRegisterSave environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg entry node handler suspended publication registers after_mrs before irq_input saved_heap
    (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let local := task_tcb_init_irq_local saved_local suspended in
  let parked := armv7a_irq_live_parked_state entry call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  kernel_call_save_instruction_step arch SaveReadCPSR registers entry before after_mrs entry irq_input ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  (task_tcb_init_continuation_save_input environment critical saved_local sg call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) entry ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   frame) irq_input ->
  armv7a_irq_register_save registers_source after_mrs.(kernel_save_r0) after_mrs.(kernel_save_lr)
    handler suspended irq_input saved_heap ->
  exists registry_heap,
    nth 0 suspended.(armv7a_continuation_registers) 0 = registers.(kernel_save_cpsr) /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap,
      @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
        KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned,
        @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
          KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          call.(os_sched_call_invocation) None call.(os_sched_call_origin)
          parked false call.(os_sched_call_origin) returned /\
        armv7a_irq_restore_pointer_reads sg closed_heap
          (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) suspended.(armv7a_continuation_sp) /\
        (forall restored cursor final_registers acquired after,
          armv7a_restore_transition abi handler suspended closed_heap restored ->
          cursor.(kernel_save_cpsr) = suspended.(armv7a_continuation_cpsr) ->
          cursor.(kernel_save_r0) = nth 0 suspended.(armv7a_continuation_registers) 0 ->
          cursor.(kernel_save_lr) = suspended.(armv7a_continuation_lr) ->
          armv7a_save_suffix_transition suffix cursor
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
            final_registers acquired after ->
          kernel_save_after_mrs_execution arch cursor
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
            final_registers acquired after /\
          final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
          final_registers.(kernel_save_return_word) = Some suspended.(armv7a_continuation_lr) /\
          (task_tcb_init_continuation_save_output environment critical saved_local sg call
             (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0) entry **
           unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
             handler.(os_int_exit_handler_fragments) ** frame) after)).
Proof.
  intros environment critical saved_local arch Extra suffix registers_source sg entry node handler suspended
    publication registers after_mrs before irq_input saved_heap frame call abi local parked
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hregister_valid Hmrs Hpc Hhandler Henter Hexit Hpublish Hpre Hcapture.
  assert (Hmrs_registers : after_mrs = kernel_save_read_cpsr registers)
    by (inversion Hmrs; reflexivity).
  subst after_mrs.
  destruct (armv7a_irq_register_save_refinement _ _ _ _ registers_source _ _ _ _ _ _ Hcapture)
    as [Hsave [Hr0 Hlr]].
  change (nth 0 suspended.(armv7a_continuation_registers) 0 = registers.(kernel_save_cpsr)) in Hr0.
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [Hsave_source [Hcall [Hbinding [Hsaved_mask [Hsaved_pc Hsave_rest]]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hbound; rewrite Hcall in Hbound; symmetry; exact Hbound. }
  assert (Habsent : entry.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) = None) by (rewrite Hlease; exact Hnone).
  assert (Hcoverage : task_stack_live_coverage entry.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hpre with ?P irq_input => assert (Hobserve : P |-- coq_prop
      (task_stack_live_coverage entry.(TskState) (task_stack_call_active_key call)) && TT) end.
    { unfold task_tcb_init_continuation_save_input, task_create_continuation_input;
        entailer!; intros ? ?; exact I. }
    pose proof (proj1 (Hobserve irq_input Hpre)) as Hcovered.
    unfold task_stack_call_active_key in Hcovered; rewrite Horigin in Hcovered; exact Hcovered. }
  match type of Hpre with ?P irq_input => assert (Hirq_input : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg entry **
     store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) ** local suspended ** (unmap_table_rep sg ** frame))) end.
  { unfold task_tcb_init_continuation_save_input, task_create_continuation_input.
    fold abi; Intros.
    sep_apply_l_atomic (proj1 (task_tcb_init_irq_map_absent _ _ _ abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) saved_local suspended Habsent)).
    unfold os_int_exit_frame_save_pre, local; rewrite task_tcb_init_irq_local_saved_eq.
    rewrite Hhandler; unfold critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  destruct (kernel_irq_save_continuation_resources _ _ _ abi sg entry node handler suspended publication
    local (unmap_table_rep sg ** frame) irq_input saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen
    Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Hirq_input irq_input Hpre) Hsave)
    as [registry_heap [Hsave_call [Hsave_pc [Hsave_mask [Hwrites [Hstores [Hcovered Hparked]]]]]]].
  fold parked in Hcovered, Hparked.
  assert (Hparked_valid : UCOS2_state_inv sg parked).
  { match type of Hparked with ?P registry_heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve registry_heap Hparked)). }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hparked_sched : parked.(SchedState) = entry.(SchedState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  match type of Hparked with ?P registry_heap => assert (Hregistry : P |--
    kernel_client_continuation_world abi local sg parked **
    (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
     frame)) end.
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  exists registry_heap; split; [exact Hr0|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (kernel_client_continuation_trace_resources _ _ _ Extra abi local critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None Henter Hexit Hpublish
    KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap _ Htrace parked
    call.(os_sched_call_origin) I (Hregistry registry_heap Hparked))
    as [returned [Hstates [Hsources [Hobserver Hworld]]]].
  destruct (kernel_client_builtin_closed_trace_task_fields Extra sg _ _ _ _ Hstates eq_refl)
    as [Hclosed [Hreturned_tasks Hreturned_sched]].
  assert (Hreturned_current : returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { rewrite Hreturned_sched, Hparked_sched; exact Hcurrent. }
  assert (Hreturned_node : returned.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))).
  { rewrite Hreturned_tasks, Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hreturned_lookup : returned.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { rewrite Hreturned_tasks, Htasks, Hlease; apply task_stack_park_fragments_lookup. }
  match type of Hworld with ?P closed_heap => assert (Htake_input : P |--
    coq_prop (task_stack_live_coverage returned.(TskState) None) &&
    (UCOS2_inv sg returned ** store_parked_continuations
       (kernel_saved_continuation_entry abi returned.(TskState) (task_tcb_init_irq_local saved_local suspended))
       returned.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      unmap_table_rep sg ** frame))) end.
  { unfold kernel_client_continuation_resources, kernel_client_continuation_world, local;
      rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Htake_input closed_heap Hworld) as [Hreturned_coverage Htake_owned].
  assert (Htake_current : returned.(SchedState).(curTaskID) =
    Some suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Hreturned_current).
  assert (Htake_node : returned.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))) by (rewrite Hlease; exact Hreturned_node).
  assert (Htake_gen : (task_set_saved_sp node suspended.(armv7a_continuation_sp)).(taskGeneration) =
    suspended.(armv7a_continuation_stack).(stackLeaseGeneration)) by (rewrite Hlease; exact Hgen).
  assert (Htake_address : tcb_field_address
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Haddress).
  destruct (task_tcb_init_irq_take_resources _ _ _ abi sg returned saved_local suspended call
    (task_set_saved_sp node suspended.(armv7a_continuation_sp)) _ closed_heap Hcall Htake_current Htake_node
    Htake_gen Hreturned_lookup Htake_address Hreturned_coverage Htake_owned)
    as [Hpointers [Hreads [Hfinal_coverage Htake_resources]]].
  exists returned; split; [exact Hstates|]. split; [exact Hsources|]. split.
  - rewrite Hlease in Hpointers; exact Hpointers.
  - intros restored cursor final_registers acquired after Hrestore Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsuffix.
    match type of Htake_resources with ?P closed_heap => assert (Hrestore_input : P |--
      interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       unmap_table_rep sg ** frame)) end.
    { unfold task_tcb_init_continuation_capsules; fold abi; entailer!. }
    destruct (armv7a_restore_call_resources _ _ _ abi handler suspended call _ closed_heap restored
      Hcall Hreads (Hrestore_input closed_heap Htake_resources) Hrestore) as [Hirq_memory Hrestored].
    assert (Hsaved : interrupt_saved_value (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) cursor.(kernel_save_r0)).
    { rewrite Hcursor_cpsr, Hcursor_r0, Hr0.
      split; [exact Hregister_valid|rewrite Hsaved_mask, Hhandler; reflexivity]. }
    match type of Hrestored with ?P restored => assert (Hsuffix_input : P |--
      kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
        (armv7a_continuation_resumed_call suspended call) (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
       unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame)) end.
    { rewrite Hcursor_cpsr, Hlease; entailer!. }
    destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ suffix sg
      (armv7a_continuation_resumed_call suspended call) cursor
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
      final_registers acquired after _ Hsaved (Hsuffix_input restored Hrestored) Hsuffix)
      as [Hacquired [Hafter_memory [Hreturn_word [Hreturn_r0 Hafter]]]].
    split; [exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hsuffix)|].
    split; [rewrite Hreturn_r0, Hcursor_r0; exact Hr0|].
    split; [rewrite Hreturn_word, Hcursor_lr; reflexivity|].
    assert (Hcurrent_valid : UCOS2_state_inv sg
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { match type of Hafter with ?P after => assert (Hobserve : P |-- coq_prop
        (UCOS2_state_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))) && TT) end.
      { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hobserve after Hafter)). }
    assert (Hpreserved : task_tcb_init_call_preserved sg call.(os_sched_call_invocation) entry
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { eapply task_tcb_init_irq_preserves_call; eassumption. }
    assert (Hsource_preserved : UCOS2_state_inv sg entry -> task_tcb_init_stack_source_preserved call entry
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { intro Hentry_valid.
      pose proof (task_tcb_init_stack_irq_return_preserved environment critical sg call entry node
        suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)
        returned call.(os_sched_call_origin) Horigin Hrunning Hnode Hparked_valid
        Hsources Hreturned_current) as Hfacts.
      exact (proj2 (proj2 Hfacts)). }
    assert (Hsaved_result : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
      final_registers.(kernel_save_r0)).
    { rewrite Hreturn_r0, Hcursor_r0, Hr0; split; [exact Hregister_valid|reflexivity]. }
    assert (Hsame : task_tcb_init_stack_same_call (armv7a_continuation_resumed_call suspended call) call).
    { unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
        cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; auto. }
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
    { unfold task_tcb_init_continuation_save_output.
      Exists (armv7a_continuation_resumed_call suspended call)
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
      assert (Hcoverage_after : task_stack_live_coverage
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState)
        (task_stack_call_active_key (armv7a_continuation_resumed_call suspended call))).
      { unfold task_stack_call_active_key, armv7a_continuation_resumed_call;
          cbn [os_sched_call_origin]; rewrite Horigin.
        rewrite Hlease in Hfinal_coverage; exact Hfinal_coverage. }
      unfold task_tcb_init_stack_context; entailer!. }
    exact (Hpost after Hafter).
Qed.
