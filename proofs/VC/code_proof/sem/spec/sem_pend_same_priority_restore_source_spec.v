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
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_irq_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.

Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_restore_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_nonswitch_phase_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.

(** Publication changes list links and the ready set while retaining the
    current task's priority. This property is needed at the later equal-byte
    branch; equality of OSPrioCur and OSPrioHighRdy alone is insufficient. *)
Lemma sem_pend_publication_preserves_current_cache : forall sg publication state,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  sched_current_consistency (task_create_stack_publication_state sg publication state).(TskState)
    (task_create_stack_publication_state sg publication state).(SchedState).
Proof.
  intros sg publication state Hvalid Hinput Hcache.
  set (args := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node).
  { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfresh : state.(TskState).(inUsedTaskStates) node.(taskID) = None).
  { exact (proj1 (task_private_excludes_public sg state.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) (task_commit_identity_private _ _ _ _ Hidentity))). }
  unfold sched_current_consistency in Hcache |- *.
  change (match state.(SchedState).(curTaskID) with
    | None => state.(SchedState).(curSchedPrio) = None
    | Some tid => exists current,
        (task_commit state.(TskState) args.(initPrio) publication.(stack_publication_invocation)
          node).(inUsedTaskStates) tid = Some current /\
        state.(SchedState).(curSchedPrio) = Some current.(curPrio)
    end).
  destruct state.(SchedState).(curTaskID) as [tid|]; [|exact Hcache].
  destruct Hcache as [old [Hold Hprio]].
  destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node tid old Hfresh Hold)
    as [current [Hcurrent Hfields]].
  exists current; split; [exact Hcurrent|].
  pose proof (f_equal curPrio Hfields) as Hpriority.
  change (current.(curPrio) = old.(curPrio)) in Hpriority.
  rewrite Hpriority; exact Hprio.
Qed.

Lemma sem_pend_irq_deposit_preserves_current_cache : forall state call node sp fragments,
  state.(SchedState).(isRunning) = true ->
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  sched_current_consistency (armv7a_irq_live_parked_state state call sp fragments).(TskState)
    (armv7a_irq_live_parked_state state call sp fragments).(SchedState).
Proof.
  intros * Hrunning Hcurrent Hnode Hcache.
  unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
  destruct Hcache as [old [Hold Hprio]].
  assert (old = node) by congruence; subst old.
  unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
    armv7a_irq_entry_counter_state, os_sched_save_current_sp.
  rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode.
  unfold sched_current_consistency; cbn [replace_TskS replace_IntrS TskState SchedState].
  rewrite Hcurrent; exists (task_set_saved_sp node sp).
  split; [cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity|exact Hprio].
Qed.

(** Only the built-in source actions are proved here. An extension must
    establish its own cache effect on this same state trace. In particular,
    an arbitrary priority-changing client is not silently treated as a
    cache-preserving handler. *)
Lemma sem_pend_client_trace_preserves_current_cache : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg,
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sched_current_consistency state.(TskState) state.(SchedState) ->
    UCOS2_state_inv sg returned /\ sched_current_consistency returned.(TskState) returned.(SchedState)) ->
  forall cut state next returned,
  kernel_client_heap_state_trace extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> sched_current_consistency state.(TskState) state.(SchedState) ->
  UCOS2_state_inv sg returned /\ sched_current_consistency returned.(TskState) returned.(SchedState).
Proof.
  intros Extra extra_effect sg Hextra cut state next returned Htrace.
  induction Htrace; intros Hvalid Hcache; [split; assumption|].
  apply IHHtrace.
  - destruct H.
    + apply os_int_enter_preserves_validity; exact Hvalid.
    + exact Hvalid.
    + eapply task_create_stack_publication_preserves_validity;
        [exact Hvalid|split; [exact H|reflexivity]].
    + exact (proj1 (Hextra _ _ _ _ H Hvalid Hcache)).
  - destruct H.
    + exact Hcache.
    + exact Hcache.
    + eapply sem_pend_publication_preserves_current_cache; eassumption.
    + exact (proj2 (Hextra _ _ _ _ H Hvalid Hcache)).
Qed.

(** Execute the actual last OSIntExit same-priority branch before taking
    the pending frame. Selection writes the high cache and the counter;
    the original SP and descriptor are still obtained from their owner. *)
Lemma sem_pend_same_priority_call_stack_restore : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg original suspended,
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original -> armv7a_task_frame_slice suspended ->
  forall state heap handler (frame : Assertion),
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> [] ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  state.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_client_call_stack_world abi sg focus payload state **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) heap ->
  let current := os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state state)
    original.(os_sched_call_stack) in
  exists exit_heap selected,
    os_int_exit_masked_same_priority_fragment sg heap exit_heap /\
    armv7a_irq_restore_pointer_reads sg exit_heap
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_focus_binding focus selected /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    task_stack_live_coverage current.(TskState) (Some (task_stack_key original.(os_sched_call_stack))) /\
    (forall final, armv7a_restore_transition abi handler selected exit_heap final ->
      final.(ConAssertion.s_mem) = exit_heap.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call selected original)
         (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg current ** armv7a_task_stack_continuations abi current.(TskState)
         current.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) final).
Proof.
  intros external platform port abi sg original suspended focus payload Hbinding Hcall Hslice
    state heap handler frame Hrunning Hschedule Hnonempty Hequal Hpointer Hcurrent Haddress Hpre current.
  match type of Hpre with ?P heap => assert (Hsplit : P |--
    coq_prop (kernel_client_call_stack_facts focus payload state) &&
    (UCOS2_inv sg state ** unmap_table_rep sg **
     (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
      interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame))) end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit heap Hpre) as [Hfacts Hworld].
  destruct (os_int_exit_masked_same_priority_frame_post sg state _ heap Hrunning Hschedule
    Hnonempty Hequal Hworld) as [exit_heap [Hexit Hafter]].
  match type of Hafter with ?P exit_heap => assert (Hmerge : P |--
    kernel_client_call_stack_world abi sg focus payload (os_int_exit_same_priority_state state) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)) end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap.
    unfold kernel_client_call_stack_facts in *.
    unfold os_int_exit_same_priority_state, os_int_exit_selection_state, os_int_exit_counter_state;
      cbn [replace_SchedS replace_IntrS TskState]; entailer!. }
  destruct (task_create_pending_call_stack_restore external platform port abi sg original suspended
    Hbinding Hcall Hslice (os_int_exit_same_priority_state state) exit_heap handler frame
    Hpointer Hcurrent Haddress (Hmerge exit_heap Hafter))
    as [selected [Hpointers [Hfocus [Hlease [Hsp [Hcpsr [Hregs [Hcoverage Hresume]]]]]]]].
  exists exit_heap, selected; split; [exact Hexit|].
  repeat first [assumption | split].
Qed.

(** Actual first Restore, including the last outer OSIntExit selector, then
    the restored BX. The branch's own guards establish zero nesting/locks;
    cache transport uses the registered actions' proved effect interface.
    These are source-family premises, not new OSSemPend admission clauses. *)
Lemma sem_pend_wait_restore_same_priority_phase_source :
  forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step extra_effect sg entry released node handler suspended publication
  saved cursor before original initial observed eid timeout waiting (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) in
  sem_pend_wait_at (Some environment) critical sg original (armv7a_irq_fiq_mask saved)
    initial observed eid timeout waiting call released ->
  sched_current_consistency released.(TskState) released.(SchedState) ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sched_current_consistency state.(TskState) state.(SchedState) ->
    UCOS2_state_inv sg returned /\ sched_current_consistency returned.(TskState) returned.(SchedState)) ->
  (forall cut state next returned previous, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    UCOS2_state_inv sg returned /\ exists current,
      returned.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) current) ->
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  released.(SchedState).(isRunning) = true -> released.(IntrState).(intNesting) = 0 ->
  released.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  released.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  released.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened released.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) suspended.(armv7a_continuation_sp) ->
  task_stack_live_coverage released.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
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
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry ** task_tcb_init_stack_context environment call **
   UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   frame) before ->
  forall written irq_input saved_heap,
  armv7a_restore_prefix_transition restore cursor before written irq_input ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  exists registry_heap,
    written = kernel_restore_write_cpsr cursor /\
    kernel_heap_writes (armv7a_continuation_save_writes suspended) irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg released
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
         returned.(SchedState).(isRunning) = true ->
         interrupt_exit_requests_schedule true returned.(IntrState) = true ->
         returned.(SchedState).(readyList) <> [] ->
         sched_selected_priority returned.(TskState) returned.(SchedState) =
           sched_priority_byte returned.(SchedState).(curSchedPrio) ->
         exists exit_heap selected,
           os_int_exit_masked_same_priority_fragment sg closed_heap exit_heap /\
           armv7a_irq_restore_pointer_reads sg exit_heap
             (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
           (forall irq_return resume_cursor final_cursor after,
             armv7a_restore_transition abi handler selected exit_heap irq_return ->
             resume_cursor.(kernel_restore_msr_word) = Some
               (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) ->
             resume_cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
             armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
             let resumed_state := os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned)
               call.(os_sched_call_stack) in
             resumed_state.(IntrState).(intNesting) = 0 /\
             resumed_state.(IntrState).(lockNesting) = 0 /\
             sched_current_consistency resumed_state.(TskState) resumed_state.(SchedState) /\
             os_sched_selection_enabled resumed_state = true /\
             final_cursor.(kernel_restore_return_word) = Some selected.(armv7a_continuation_lr) /\
             (sem_pend_phase_restore_output
                (SemPendWaitPhase original (armv7a_irq_fiq_mask saved) initial observed eid timeout waiting)
                environment.(task_stack_call_external) environment.(task_stack_call_platform)
                (Some environment) critical sg call (armv7a_irq_fiq_mask saved) released ** unmap_table_rep sg **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after /\
             (forall (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
                         environment.(task_stack_call_platform) critical arch)
                     registers final_registers acquired saved_heap,
                kernel_call_task_source call released ->
                registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
                armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
                armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) resumed_state after
                  final_registers acquired saved_heap ->
                acquired = resumed_state /\ exists prefix_heap,
                  os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
                  forall sched_cursor sched_written sched_middle sched_final final,
                    sched_cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
                    armv7a_irq_fiq_mask sched_cursor.(kernel_restore_current_cpsr) = 192 ->
                    armv7a_restore_prefix_transition restore sched_cursor prefix_heap sched_written sched_middle ->
                    armv7a_restore_suffix_transition restore sched_written sched_middle sched_final final ->
                    kernel_call_restore_uninterrupted_execution arch sched_cursor prefix_heap sched_final final /\
                    (sem_pend_phase_sched_output
                      (SemPendWaitPhase original (armv7a_irq_fiq_mask saved) initial observed eid timeout waiting)
                      environment.(task_stack_call_external) environment.(task_stack_call_platform)
                      (Some environment) critical sg (armv7a_continuation_resumed_call selected call)
                      (armv7a_irq_fiq_mask saved) resumed_state **
                     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                       handler.(os_int_exit_handler_fragments) ** frame) final)))).
Proof.
  intros environment critical arch Extra restore extra_resources extra_step extra_effect sg entry released node
    handler suspended publication saved cursor before original initial observed eid timeout waiting frame
    call abi parked focus payload Hwait Hcache Hcache_step Hwait_step Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hextension Hextra Henter Hexit Hpublish
    Hsource Hpre written irq_input saved_heap Hprefix Hsave.
  assert (Hreleased : UCOS2_state_inv sg released).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg released) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  match type of Hpre with ?P before => assert (Hordered : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry ** task_tcb_init_stack_context environment call **
    UCOS2_inv sg released ** task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (frame)) by entailer! end.
  destruct (task_create_restore_irq_deposit environment critical arch restore sg entry released node
    handler suspended publication saved cursor before written irq_input saved_heap
    (frame)
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    Hr0 Hmask Hhandler (Hordered before Hpre) Hprefix Hsave)
    as [registry_heap [Hwritten [Hwrites [Hstores [Hbinding [Hcall [Hsaved_mask [Hvalid [Hpointer Hregistry]]]]]]]]].
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (kernel_client_call_stack_trace_source_resources _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None Hextension Henter Hexit Hpublish Hsource
    KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap _ Htrace
    parked call.(os_sched_call_origin) I Hregistry)
    as [returned [stopped [returned_origin [Hstates [Hsources [Hcut Hworld]]]]]].
  destruct (kernel_client_trace_preserves_saved_pointer Extra extra_effect sg
    suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hextra
    KernelClientHeapClosed parked KernelClientHeapClosed returned Hstates Hvalid Hpointer)
    as [Hreturned Hpointer_returned].
  assert (Hparked_cache : sched_current_consistency parked.(TskState) parked.(SchedState)).
  { eapply sem_pend_irq_deposit_preserves_current_cache; eassumption. }
  pose proof (proj2 (sem_pend_client_trace_preserves_current_cache Extra extra_effect sg Hcache_step
    KernelClientHeapClosed parked KernelClientHeapClosed returned Hstates Hvalid Hparked_cache))
    as Hreturned_cache.
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hreturned_current Hreturned_running Hschedule Hnonempty Hequal.
  destruct (sem_pend_same_priority_call_stack_restore _ _ _ abi sg call suspended Hbinding Hcall Hslice
    returned closed_heap handler frame Hreturned_running Hschedule Hnonempty Hequal Hpointer_returned
    Hreturned_current Haddress Hworld)
    as [exit_heap [selected [Hexit_source [Hpointers [Hfocus [Hlease [Hselected_sp [Hcpsr [Hregisters [Hcovered Hresume]]]]]]]]]].
  exists exit_heap, selected; split; [exact Hexit_source|]. split; [exact Hpointers|].
  intros irq_return resume_cursor final_cursor after Hrestore Hword Hlr Hsuffix resumed_state.
  destruct (Hresume irq_return Hrestore) as [Hmemory Howned].
  rewrite Hsaved_mask in Howned.
  assert (Hcomputed_mask : armv7a_irq_fiq_mask
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) =
    armv7a_irq_fiq_mask saved) by (rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity).
  rewrite <- Hcomputed_mask in Howned.
  match type of Howned with ?P irq_return => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (armv7a_continuation_resumed_call selected call)
      (armv7a_irq_fiq_mask
        (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
     UCOS2_inv sg (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack)) **
     armv7a_task_stack_continuations abi
       (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack)).(TskState)
       (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack)).(TskState).(parkedTaskStacks) **
     unmap_table_rep sg ** frame))
    by entailer! end.
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call selected call) _ resume_cursor irq_return final_cursor after
    _ Hword (Hsuffix_input irq_return Howned) Hsuffix) as [Hcursor [Hafter_memory Hafter]].
  rewrite Hcomputed_mask in Hafter.
  assert (Hhistory : kernel_call_restore_history environment critical sg call released
    (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack))).
  { eapply KernelCallRestoreIRQSamePriority with (extra_step := extra_step) (extra_effect := extra_effect)
      (suspended := suspended) (selected := selected) (cursor := cursor)
      (written := written) (stopped := stopped) (returned_origin := returned_origin);
      eassumption || reflexivity. }
  pose proof (kernel_call_restore_history_same_call _ _ _ _ _ _ _ Hhistory) as Hsame.
  assert (Hfields : forall previous,
    released.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) previous ->
    exists current,
      (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack)).(TskState).(inUsedTaskStates)
        original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) current).
  { intros previous Hprevious Hprevious_wait.
    destruct (sem_pend_irq_deposit_wait_continuation released call suspended.(armv7a_continuation_sp)
      suspended.(armv7a_continuation_fragments) original.(os_sched_call_stack).(stackLeaseSlot)
      previous eid original.(os_sched_call_stack).(stackLeaseGeneration) Hrunning Hprevious Hprevious_wait)
      as [deposited [Hdeposited Hdeposited_wait]].
    destruct (sem_pend_client_trace_preserves_wait_continuation Extra extra_effect sg
      original.(os_sched_call_stack).(stackLeaseSlot) eid original.(os_sched_call_stack).(stackLeaseGeneration)
      Hwait_step KernelClientHeapClosed parked KernelClientHeapClosed returned deposited Hstates Hvalid
      Hdeposited Hdeposited_wait) as [_ [current [Hwait_current Hcurrent_wait]]].
    exists current; split; assumption. }
  pose proof (sem_pend_wait_at_restore_source environment critical sg original (armv7a_irq_fiq_mask saved)
    initial observed eid timeout waiting call released (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack)) Hwait Hhistory Hfields)
    as Hwait_after.
  assert (Hpreserved : task_tcb_init_stack_return_preserved call released
    (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack))).
  { assert (Hold : task_tcb_init_stack_return_preserved call released
        (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
    { eapply task_tcb_init_stack_irq_return_preserved; try eassumption.
      rewrite <- Hnormal; exact Hsources. }
    exact Hold. }
  assert (Hsource_preserved : UCOS2_state_inv sg released -> kernel_call_task_source call released ->
    kernel_call_task_source (armv7a_continuation_resumed_call selected call)
      (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack))).
  { intros Hreleased_valid Hcall_source.
    unfold armv7a_continuation_resumed_call, kernel_call_task_source;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    rewrite Hlease; exact (proj2 (proj2 Hpreserved) Hcall_source). }
  assert (Hcounts : resumed_state.(IntrState).(intNesting) = 0 /\ resumed_state.(IntrState).(lockNesting) = 0).
  { apply interrupt_exit_requests_schedule_iff in Hschedule.
    destruct Hschedule as [_ [Hcount Hlock]].
    split; [exact Hcount|].
    change ((interrupt_exit_state true returned.(IntrState)).(lockNesting) = 0).
    unfold interrupt_exit_state; destruct (0 <? returned.(IntrState).(intNesting)); exact Hlock. }
  assert (Henabled : os_sched_selection_enabled resumed_state = true).
  { unfold os_sched_selection_enabled; rewrite (proj1 Hcounts), (proj2 Hcounts); reflexivity. }
  assert (Hnoswitch : os_sched_requests_switch resumed_state = false).
  { apply Bool.not_true_is_false; rewrite os_sched_requests_switch_iff.
    intros [_ Hdifferent]; apply Hdifferent.
    unfold sched_selected_priority in Hequal |- *.
    rewrite (encode_ready_grp_ext _ resumed_state.(TskState) returned.(TskState) eq_refl).
    unfold encode_ready_tbl_at_or in Hequal |- *.
    exact Hequal. }
  assert (Hnext_input : (task_tcb_init_stack_covered_save_input environment critical sg
      (armv7a_continuation_resumed_call selected call) (armv7a_irq_fiq_mask saved) resumed_state **
      unmap_table_rep sg ** (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame)) after).
  { assert (Hactive_key : task_stack_call_active_key (armv7a_continuation_resumed_call selected call) =
        Some (task_stack_key call.(os_sched_call_stack))).
    { unfold task_stack_call_active_key, armv7a_continuation_resumed_call;
      cbn [os_sched_call_origin]; rewrite Horigin; reflexivity. }
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hnext : P |-- Q) end end.
    { unfold task_tcb_init_stack_covered_save_input, critical_region_outside.
      rewrite Hactive_key, critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
      unfold UCOS2_inv, task_tcb_init_stack_covered_capsules; entailer!. }
    exact (Hnext after Hafter). }
  assert (Hnext_scheduler : forall (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical arch) registers final_registers acquired saved_heap,
      kernel_call_task_source call released ->
      registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) resumed_state after
        final_registers acquired saved_heap ->
      acquired = resumed_state /\ exists prefix_heap,
        os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
        forall sched_cursor sched_written sched_middle sched_final final,
          sched_cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
          armv7a_irq_fiq_mask sched_cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore sched_cursor prefix_heap sched_written sched_middle ->
          armv7a_restore_suffix_transition restore sched_written sched_middle sched_final final ->
          kernel_call_restore_uninterrupted_execution arch sched_cursor prefix_heap sched_final final /\
          (sem_pend_phase_sched_output
            (SemPendWaitPhase original (armv7a_irq_fiq_mask saved) initial observed eid timeout waiting)
            environment.(task_stack_call_external) environment.(task_stack_call_platform)
            (Some environment) critical sg (armv7a_continuation_resumed_call selected call)
            (armv7a_irq_fiq_mask saved) resumed_state **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack)
             handler.(os_int_exit_handler_fragments) ** frame) final).
  { intros save registers final_registers acquired next_saved_heap Hcall_source Hreturn Hcpsr_valid Hsave_mask Hsave_run.
    destruct (sem_pend_nonswitch_scheduler_phase_source environment critical arch save restore sg
      original (armv7a_irq_fiq_mask saved) initial observed eid timeout waiting
      (armv7a_continuation_resumed_call selected call) resumed_state registers after
      final_registers acquired next_saved_heap
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
      Hwait_after Hreturn Hcpsr_valid Hsave_mask Hnoswitch (fun _ => Hnonempty) Hnext_input Hsave_run)
      as [Hrun [Hacquired [prefix_heap [Hprefix_next Hfinish]]]].
    split; [exact Hacquired|]. exists prefix_heap; split; [exact Hprefix_next|].
    intros sched_cursor sched_written sched_middle sched_final final Hsched_r0 Hsched_mask Hsched_prefix Hsched_suffix.
    destruct (Hfinish sched_cursor sched_written sched_middle sched_final final Hsched_r0 Hsched_mask
      Hsched_prefix Hsched_suffix) as [Hrestore_run [Hwait_current [Hnext_owned Hphase]]].
    split; [exact Hrestore_run|].
    pose proof (Hphase (Hsource_preserved Hreleased Hcall_source) Hreturned_cache Henabled) as Hfinal.
    match type of Hfinal with ?P final => match goal with |- ?Q final =>
      assert (Hreassociate : P |-- Q) by entailer! end end.
    exact (Hreassociate final Hfinal). }
  split; [exact (proj1 Hcounts)|]. split; [exact (proj2 Hcounts)|].
  split; [exact Hreturned_cache|].
  split; [exact Henabled|]. split.
    + rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
    + split; [|exact Hnext_scheduler].
      unfold armv7a_continuation_resumed_call in Hhistory, Hsame, Hsource_preserved, Hwait_after.
    rewrite Hlease, Horigin in Hhistory, Hsame, Hsource_preserved, Hwait_after.
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
    { unfold sem_pend_phase_restore_output.
      Exists (armv7a_continuation_resumed_call selected call)
        (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned) call.(os_sched_call_stack)).
      unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
        sem_pend_restore_phase_pre, sem_pend_optional_stack_resources, task_tcb_init_stack_capsules.
      rewrite mutex_query_closed_equiv.
      unfold kernel_call_execution_owned, task_stack_call_active_key, armv7a_continuation_resumed_call.
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
      rewrite Hlease, Horigin; unfold UCOS2_inv; entailer!; try discriminate. }
    exact (Hpost after Hafter).
Qed.
