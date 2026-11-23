Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_resume_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_restore_phase_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.

(** The second Save starts with the real resumed waiter. Its original MRS
    word, indexed IRQ descriptor and heap are kept together through the
    actual registry and wrapper restore. Built-in counter/publication cuts
    preserve the waiter and its established readiness. Other registered
    operations must prove both field and ready preservation for this
    no-selection family, or use their separate selected-return source. *)
Lemma sem_pend_wait_mrs_irq_save_phase_source :
  forall environment critical arch Extra
  (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (registers_source : Armv7aIRQRegisterSave environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  extra_resources extra_step extra_effect sg entry node handler suspended publication
  registers after_mrs before irq_input saved_heap original initial observed eid timeout waiting (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state entry call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  sem_pend_wait_selected_at (Some environment) critical sg original (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    initial observed eid timeout waiting call entry ->
  (forall cut state next returned previous, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    UCOS2_state_inv sg returned /\ exists current,
      returned.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) current) ->
  (forall cut state next returned previous, extra_effect sg cut state next returned ->
    sem_pend_resume_entry sg state eid original.(os_sched_call_stack).(stackLeaseSlot) previous ->
    exists current, sem_pend_resume_entry sg returned eid original.(os_sched_call_stack).(stackLeaseSlot) current) ->
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
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) suspended.(armv7a_continuation_sp) ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  kernel_call_save_instruction_step arch SaveReadCPSR registers entry before after_mrs entry irq_input ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients) (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical.(critical_region_clients) sg call.(os_sched_call_invocation) None extra_effect ->
  (task_tcb_init_stack_save_input environment critical sg call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) entry ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) irq_input ->
  armv7a_irq_register_save registers_source after_mrs.(kernel_save_r0) after_mrs.(kernel_save_lr)
    handler suspended irq_input saved_heap ->
  exists registry_heap,
    nth 0 suspended.(armv7a_continuation_registers) 0 = registers.(kernel_save_cpsr) /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap,
      kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          call.(os_sched_call_invocation) None call.(os_sched_call_origin) parked stopped returned_origin returned /\
        (stopped = false ->
         returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
         exists selected,
           armv7a_irq_restore_pointer_reads sg closed_heap
             (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
           (forall restored cursor final_registers acquired after,
             armv7a_restore_transition abi handler selected closed_heap restored ->
             cursor.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
             cursor.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
             cursor.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
             armv7a_save_suffix_transition suffix cursor
               (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
               final_registers acquired after ->
             kernel_save_after_mrs_execution arch cursor
               (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
               final_registers acquired after /\
             final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
             final_registers.(kernel_save_return_word) = Some suspended.(armv7a_continuation_lr) /\
             (sem_pend_phase_save_output
                (SemPendWaitPhase original (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
                  initial observed eid timeout waiting)
                environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
                critical sg call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0) entry **
              unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                handler.(os_int_exit_handler_fragments) ** frame) after))).
Proof.
  intros environment critical arch Extra suffix registers_source extra_resources extra_step extra_effect
    sg entry node handler suspended publication registers after_mrs before irq_input saved_heap original initial observed eid timeout waiting frame
    call abi parked focus payload Hselected_wait Hwait_step Hresume_step Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hregister_valid Hmrs Hpc Hhandler
    Hextension Hextra Henter Hexit Hpublish Hsource Hpre Hcapture.
  assert (Hmrs_registers : after_mrs = kernel_save_read_cpsr registers)
    by (inversion Hmrs; reflexivity).
  subst after_mrs.
  destruct (armv7a_irq_register_save_refinement _ _ _ _ registers_source _ _ _ _ _ _ Hcapture)
    as [Hsave [Hr0 Hlr]].
  change (nth 0 suspended.(armv7a_continuation_registers) 0 = registers.(kernel_save_cpsr)) in Hr0.
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended irq_input saved_heap Hsave)
    as [_ [Hcall [Hbinding [Hmask [Hsaved_pc _]]]]].
  destruct Hselected_wait as [Hwait_before [resume_node Hresume_entry]].
  pose proof Hwait_before as [owned [Henv [Hcall_same [Hinitial Hpath]]]].
  pose proof (proj2 (proj2 Hcall_same)) as Hcall_stack.
  assert (Hresume_call : sem_pend_resume_entry sg entry eid call.(os_sched_call_stack).(stackLeaseSlot) resume_node).
  { rewrite Hcall_stack; exact Hresume_entry. }
  assert (Hcoverage : task_stack_live_coverage entry.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hpre with ?P irq_input => assert (Hobserve : P |-- coq_prop
      (task_stack_live_coverage entry.(TskState) (task_stack_call_active_key call)) && TT) end.
    { unfold task_tcb_init_stack_save_input; entailer!; intros ? ?; exact I. }
    pose proof (proj1 (Hobserve irq_input Hpre)) as Hcovered.
    unfold task_stack_call_active_key in Hcovered; rewrite Horigin in Hcovered; exact Hcovered. }
  match type of Hpre with ?P irq_input => assert (Hirq_input : P |--
    os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform) handler **
    (UCOS2_inv sg entry ** armv7a_task_stack_continuations abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) end.
  { unfold task_tcb_init_stack_save_input, task_tcb_init_stack_capsules, os_int_exit_frame_save_pre.
    rewrite Hhandler; unfold critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  destruct (armv7a_irq_source_save_parks_call _ _ _ abi sg entry node handler suspended publication
    (unmap_table_rep sg ** frame) irq_input saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen
    Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage (Hirq_input irq_input Hpre) Hsave)
    as [registry_heap [Hwrites [Hstores [Hcovered Hparked]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hsame; rewrite Hcall in Hsame; symmetry; exact Hsame. }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hpointer : task_saved_pointer_at parked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { unfold task_saved_pointer_at; rewrite Hlease, Htasks.
    exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)); split.
    - cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    - change (node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
        suspended.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp)); auto. }
  assert (Hlookup : parked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { unfold payload, focus; rewrite Htasks, Hlease; apply task_stack_park_fragments_lookup. }
  assert (Hvalid : UCOS2_state_inv sg parked).
  { match type of Hparked with ?P registry_heap => assert (Hobserve : P |--
      coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve registry_heap Hparked)). }
  match type of Hparked with ?P registry_heap => assert (Hregistry : P |--
    kernel_client_call_stack_world abi sg focus payload parked **
    (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) end.
  { unfold kernel_client_call_stack_world, kernel_client_call_stack_facts, focus.
    rewrite kernel_program_inv_split_unmap, Hsaved_pc; entailer!. }
  exists registry_heap; split; [exact Hr0|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (task_create_registered_call_stack_restore _ _ _ Extra abi extra_resources extra_step extra_effect
    critical.(critical_region_clients) sg call suspended Hbinding Hcall Hslice Hextension Hextra Henter Hexit Hpublish
    Hsource KernelClientHeapClosed registry_heap closed_heap parked handler frame
    Hvalid Hpointer Htrace I (Hregistry registry_heap Hparked))
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  assert (Hparked_resume : sem_pend_resume_entry sg parked eid
    original.(os_sched_call_stack).(stackLeaseSlot) (task_set_saved_sp resume_node suspended.(armv7a_continuation_sp))).
  { rewrite <- Hcall_stack; eapply sem_pend_irq_deposit_resume_entry; eassumption. }
  destruct (sem_pend_client_trace_preserves_resume_entry Extra extra_effect sg eid
    original.(os_sched_call_stack).(stackLeaseSlot) Hresume_step KernelClientHeapClosed parked
    KernelClientHeapClosed returned (task_set_saved_sp resume_node suspended.(armv7a_continuation_sp))
    Hstates Hparked_resume) as [returned_node Hreturned_resume].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hreturned_current.
  destruct (Hreturn Hreturned_current Haddress)
    as [selected [Hpointers [Hfocus [Hselected_lease [Hselected_sp [Hcpsr [Hregisters [Hrestored_covered Hresume]]]]]]]].
  exists selected; split; [exact Hpointers|].
  intros restored cursor final_registers acquired after Hrestore Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsuffix.
  destruct (Hresume restored Hrestore) as [Hmemory Hrestored].
  assert (Hsaved : interrupt_saved_value (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) cursor.(kernel_save_r0)).
  { rewrite Hcursor_cpsr, Hcursor_r0, Hcpsr, Hregisters, Hr0.
    split; [exact Hregister_valid|rewrite Hmask, Hhandler; reflexivity]. }
  match type of Hrestored with ?P restored => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (armv7a_continuation_resumed_call selected call) (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) **
    (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     task_tcb_init_stack_capsules environment (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) end.
  { rewrite Hcursor_cpsr, Hcpsr; unfold task_tcb_init_stack_capsules; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ suffix sg
    (armv7a_continuation_resumed_call selected call) cursor
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
    final_registers acquired after _ Hsaved (Hsuffix_input restored Hrestored) Hsuffix)
    as [Hacquired [Hafter_memory [Hreturn_word [Hreturn_r0 Hafter]]]].
  subst acquired.
  split; [exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hsuffix)|].
  split; [rewrite Hreturn_r0, Hcursor_r0, Hregisters; exact Hr0|].
  split; [rewrite Hreturn_word, Hcursor_lr; f_equal; exact (proj2 (proj2 Hfocus))|].
  assert (Hhistory : kernel_call_save_history environment critical sg call entry
    (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { assert (Hsource_pc : suspended.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4)
      by congruence.
    eapply KernelCallSaveIRQ with (save := suffix) (extra_step := extra_step) (extra_effect := extra_effect)
      (suspended := suspended) (selected := selected) (registers := registers)
      (resume_registers := cursor) (stopped := stopped) (returned_origin := returned_origin);
      eassumption || reflexivity. }
  pose proof (kernel_call_save_history_same_call _ _ _ _ _ _ _ Hhistory) as Hsame.
  assert (Hfields : forall previous,
    entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    exists current,
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState).(inUsedTaskStates)
        original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) current).
  { intros previous Hprevious Hprevious_wait.
    destruct (sem_pend_irq_deposit_wait_continuation entry call suspended.(armv7a_continuation_sp)
      suspended.(armv7a_continuation_fragments) original.(os_sched_call_stack).(stackLeaseSlot)
      previous eid original.(os_sched_call_stack).(stackLeaseGeneration) Hrunning Hprevious Hprevious_wait)
      as [deposited [Hdeposited Hdeposited_wait]].
    destruct (sem_pend_client_trace_preserves_wait_continuation Extra extra_effect sg
      original.(os_sched_call_stack).(stackLeaseSlot) eid original.(os_sched_call_stack).(stackLeaseGeneration)
      Hwait_step KernelClientHeapClosed parked KernelClientHeapClosed returned deposited Hstates Hvalid
      Hdeposited Hdeposited_wait) as [_ [current [Hwait_current Hcurrent_wait]]].
    exists current; split; assumption. }
  assert (Hselected_after : sem_pend_wait_selected_at (Some environment) critical sg original
    (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) initial observed eid timeout waiting
    (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { split.
    - exists environment; split; [reflexivity|]. split.
      + unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
      + split; [exact Hinitial|]. inversion Henv; subst owned.
        eapply SemPendWaitSourceTrans; [exact Hpath|].
        eapply SemPendWaitSourceSave; eassumption.
    - exists returned_node; split.
      + match type of Hafter with ?P after => assert (Hvalid_view : P |--
          coq_prop (UCOS2_state_inv sg
            (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))) && TT) end.
        { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
        exact (proj1 (Hvalid_view after Hafter)).
      + exact (proj2 Hreturned_resume). }
  assert (Hvalue : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    final_registers.(kernel_save_r0)).
  { rewrite Hreturn_r0, Hcursor_r0, Hregisters, Hr0; split; [exact Hregister_valid|reflexivity]. }
  unfold armv7a_continuation_resumed_call in Hsame, Hselected_after.
  rewrite Hselected_lease, Horigin in Hsame, Hselected_after.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
  { unfold sem_pend_phase_save_output.
    Exists (armv7a_continuation_resumed_call selected call)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
    unfold sem_pend_stack_save_observation, sem_pend_save_phase_observation,
      sem_pend_optional_stack_resources, task_tcb_init_stack_capsules.
    unfold kernel_call_execution_owned, task_stack_call_active_key, armv7a_continuation_resumed_call.
    cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    rewrite Hselected_lease, Horigin; unfold UCOS2_inv; entailer!; try discriminate. }
  exact (Hpost after Hafter).
Qed.
