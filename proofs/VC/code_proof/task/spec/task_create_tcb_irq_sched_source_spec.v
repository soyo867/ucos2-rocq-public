Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_irq_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_world_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The interrupted caller is parked, so its absent-key API stage is not
    used. Current identity remains live even for a locked self-suspended
    task. Readiness is needed only if the unchanged scheduler lock is zero;
    IRQ entry/exit change nesting but do not enable a locked scheduler. *)
Definition task_create_irq_caller_stage call state : Prop :=
  state.(SchedState).(isRunning) = true /\
  exists node,
    state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) /\
    node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
    (state.(IntrState).(lockNesting) = 0 ->
      sched_current_ready_at state.(TskState) state.(SchedState)
        call.(os_sched_call_stack).(stackLeaseSlot) node).

Lemma task_create_call_stage_irq_entry : forall call state,
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_create_call_stage call state -> state.(IntrState).(intNesting) = 0 ->
  task_create_irq_caller_stage call state.
Proof.
  intros call state Horigin [Hcurrent Hstage] Hnesting.
  rewrite Horigin in Hcurrent, Hstage.
  destruct Hcurrent as [Hrunning [Htid [node [Hnode Hgen]]]].
  destruct Hstage as [_ [_ [_ Hready]]].
  split; [exact Hrunning|]. exists node.
  split; [exact Hnode|]. split; [exact Htid|]. split; [exact Hgen|].
  intros Hlock.
  assert (Henabled : os_sched_selection_enabled state = true)
    by (apply os_sched_selection_enabled_iff; auto).
  destruct (Hready Henabled) as [ready [Hready_node _]].
  assert (ready = node) by (destruct Hready_node as [Hlookup _]; congruence).
  subst ready; exact Hready_node.
Qed.

Lemma task_create_publication_preserves_irq_caller_stage : forall sg publication state call,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  task_create_irq_caller_stage call state ->
  task_create_irq_caller_stage call (task_create_stack_publication_state sg publication state).
Proof.
  intros sg publication state call Hvalid Hinput [Hrunning [old [Hold [Hcurrent [Hgen Hready]]]]].
  set (args := task_create_stack_publication_args publication).
  set (new := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  set (published := task_create_stack_publication_state sg publication state).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) new).
  { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfresh : state.(TskState).(inUsedTaskStates) new.(taskID) = None).
  { exact (proj1 (task_private_excludes_public sg state.(TskState) new.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) (task_commit_identity_private _ _ _ _ Hidentity))). }
  destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) new call.(os_sched_call_stack).(stackLeaseSlot)
    old Hfresh Hold) as [updated [Hupdated Hfields]].
  assert (Hpriority_updated : updated.(curPrio) = old.(curPrio)) by exact (f_equal curPrio Hfields).
  assert (Hgen_updated : updated.(taskGeneration) = old.(taskGeneration))
    by exact (f_equal taskGeneration Hfields).
  split; [exact Hrunning|]. exists updated.
  split; [exact Hupdated|]. split; [exact Hcurrent|]. split; [congruence|].
  intros Hlock.
  destruct (Hready Hlock) as [_ [_ [Hpriority [Hin Heffective]]]].
  assert (Hstatus : updated.(stat) = old.(stat)) by exact (f_equal stat Hfields).
  assert (Hdelay : updated.(dly) = old.(dly)) by exact (f_equal dly Hfields).
  assert (Heffective_updated : is_effectively_ready updated.(stat) updated.(dly) = true).
  { rewrite Hstatus, Hdelay; exact Heffective. }
  assert (Hpost : UCOS2_state_inv sg published).
  { eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
    split; [exact Hinput|reflexivity]. }
  assert (Hmember : In call.(os_sched_call_stack).(stackLeaseSlot) published.(SchedState).(readyList)).
  { exact (proj1 (proj2 (proj2 (proj1 (proj1 (proj2 (proj2 Hpost))))))
      _ _ Hupdated Heffective_updated). }
  unfold sched_current_ready_at; split; [exact Hupdated|]. split; [exact Hcurrent|]. split.
  - change (state.(SchedState).(curSchedPrio) = Some updated.(curPrio)).
    rewrite Hpriority_updated; exact Hpriority.
  - split; assumption.
Qed.


Lemma task_create_irq_counter_exit_preserves_caller_stage : forall call state observed,
  task_create_irq_caller_stage call state ->
  task_create_irq_caller_stage call (os_int_exit_counter_state observed state).
Proof.
  intros call state observed Hstage.
  unfold task_create_irq_caller_stage in *.
  cbn [os_int_exit_counter_state replace_IntrS TskState SchedState IntrState].
  unfold interrupt_exit_state.
  destruct observed, (0 <? state.(IntrState).(intNesting)); exact Hstage.
Qed.

(** This is the registry's existing built-in client family: counter
    Enter/Exit and TCB publication. Extension steps have no constructor in
    this particular source branch. It does not restrict the global client
    registry or claim closure for an unproved arbitrary client. *)
Lemma task_create_builtin_trace_preserves_irq_caller_stage : forall Extra sg call cut state next returned,
  @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg cut state next returned ->
  UCOS2_state_inv sg state -> task_create_irq_caller_stage call state ->
  UCOS2_state_inv sg returned /\ task_create_irq_caller_stage call returned.
Proof.
  intros Extra sg call cut state next returned Htrace.
  induction Htrace; intros Hvalid Hready; [split; assumption|].
  apply IHHtrace.
  - destruct H.
    + apply os_int_enter_preserves_validity; exact Hvalid.
    + exact Hvalid.
    + eapply task_create_stack_publication_preserves_validity;
        [exact Hvalid|split; [exact H|reflexivity]].
    + contradiction.
  - destruct H.
    + unfold task_create_irq_caller_stage in *.
      cbn [os_int_enter_state replace_IntrS TskState SchedState IntrState].
      unfold interrupt_enter_state.
      destruct state.(SchedState).(isRunning), (state.(IntrState).(intNesting) <? 255); exact Hready.
    + apply task_create_irq_counter_exit_preserves_caller_stage; exact Hready.
    + eapply task_create_publication_preserves_irq_caller_stage; eassumption.
    + contradiction.
Qed.

Lemma task_create_irq_deposit_preserves_caller_stage : forall state call node sp fragments,
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  task_create_irq_caller_stage call state ->
  task_create_irq_caller_stage call (armv7a_irq_live_parked_state state call sp fragments).
Proof.
  intros state call node sp fragments Hnode [Hrunning [current [Hcurrent [Htid [Hgen Hready]]]]].
  assert (current = node) by congruence; subst current.
  unfold task_create_irq_caller_stage, armv7a_irq_live_parked_state,
    armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state; rewrite Hrunning.
  unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode.
  split; [exact Hrunning|]. exists (task_set_saved_sp node sp).
  split.
  - cbn [replace_TskS TskState glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity.
  - split; [exact Htid|]. split; [exact Hgen|]. intros Hlock.
    destruct (Hready Hlock) as [_ [_ [Hpriority [Hin Heffective]]]].
    unfold sched_current_ready_at; split.
    + cbn [replace_TskS TskState glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + exact (conj Htid (conj Hpriority (conj Hin Heffective))).
Qed.

Lemma task_create_irq_take_reestablishes_call_stage : forall call selected state,
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  selected.(armv7a_continuation_stack) = call.(os_sched_call_stack) ->
  task_create_irq_caller_stage call state ->
  task_create_call_stage (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state state call.(os_sched_call_stack)).
Proof.
  intros call selected state Horigin Hlease [Hrunning [node [Hnode [Hcurrent [Hgen Hready]]]]].
  unfold task_create_call_stage, armv7a_continuation_resumed_call.
  cbn [os_sched_call_origin os_sched_call_stack]; rewrite Horigin, Hlease.
  split.
  - unfold task_create_call_origin; split; [exact Hrunning|].
    split; [exact Hcurrent|]. exists node; split; [exact Hnode|exact Hgen].
  - split; [reflexivity|]. split; [reflexivity|]. split.
    + unfold os_int_exit_wrapper_restored_state.
      cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
      apply task_stack_take_lookup.
    + intros Henabled; apply os_sched_selection_enabled_iff in Henabled.
      exists node; split; [apply Hready; exact (proj2 Henabled)|exact Hgen].
Qed.

(** The intermediate TCB Restore takes this actual built-in IRQ path,
    then its BX and the next Save keep the returned current world. The
    caller stage is recovered from the same registry state trace; it is
    not supplied by the architecture ABI. Extra source transitions are
    deliberately absent in this branch, so this is not the whole callee. *)
Lemma task_create_tcb_irq_return_sched_save_source : forall environment critical arch Extra
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  extra_resources extra_step sg entry released node handler suspended publication
  saved cursor before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop := fun _ _ _ _ _ => False in
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
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg released **
   task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack)
     handler.(os_int_exit_handler_fragments) ** frame) before ->
    (forall written irq_input saved_heap,
      armv7a_restore_prefix_transition restore cursor before written irq_input ->
      armv7a_save_transition abi handler suspended irq_input saved_heap ->
      exists registry_heap,
        written = kernel_restore_write_cpsr cursor /\
        kernel_heap_writes (armv7a_continuation_save_writes suspended)
          irq_input.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
        kernel_heap_execution (armv7a_irq_live_entry_writes sg released
          call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
          saved_heap registry_heap /\
        (forall closed_heap,
          kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
            KernelClientHeapClosed closed_heap ->
          exists returned stopped returned_origin,
            kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
              KernelClientHeapClosed returned /\
            kernel_resumption_task_source_trace environment.(task_stack_call_external)
              environment.(task_stack_call_port) critical.(critical_region_clients) sg
              call.(os_sched_call_invocation) None call.(os_sched_call_origin)
              parked stopped returned_origin returned /\
            (returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
             exists selected,
               armv7a_irq_restore_pointer_reads sg closed_heap
                 (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
                 selected.(armv7a_continuation_sp) /\
               selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
               selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
               (forall irq_return resume_cursor final_cursor after,
                 armv7a_restore_transition abi handler selected closed_heap irq_return ->
                 resume_cursor.(kernel_restore_msr_word) = Some
                   (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
                     cursor.(kernel_restore_r0)) ->
                 resume_cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
                 armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
                 kernel_call_restore_history environment critical sg call released
                   (armv7a_continuation_resumed_call selected call)
                   (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) /\
                 final_cursor.(kernel_restore_return_word) = Some selected.(armv7a_continuation_lr) /\
                 task_stack_live_coverage
                   (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).(TskState)
                   (Some (task_stack_key call.(os_sched_call_stack))) /\
                 (kernel_call_execution_owned environment.(task_stack_call_external)
                    environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected call)
                    (armv7a_irq_fiq_mask saved) **
                  (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
                   task_tcb_init_stack_covered_capsules environment
                     (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
                   unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                     handler.(os_int_exit_handler_fragments) ** frame)) after /\
                 task_create_call_stage (armv7a_continuation_resumed_call selected call)
                   (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) /\
                 (kernel_stack_call_closed abi kernel_program_inv sg
                    (task_stack_call_active_key (armv7a_continuation_resumed_call selected call))
                    (armv7a_continuation_resumed_call selected call) (armv7a_irq_fiq_mask saved)
                    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
                  (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                    handler.(os_int_exit_handler_fragments) ** frame)) after /\
                 (forall registers final_registers acquired next_heap,
                   registers.(kernel_save_return_word) = None ->
                   valid_os_cpu_sr registers.(kernel_save_cpsr) ->
                   armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
                   armv7a_save_suffix_transition save (kernel_save_read_cpsr registers)
                     (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) after
                     final_registers acquired next_heap ->
                   task_tcb_init_stack_same_call (armv7a_continuation_resumed_call selected call) call /\
                   kernel_call_save_uninterrupted_execution arch registers
                     (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) after
                     final_registers acquired next_heap /\
                   acquired = os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack) /\
                   final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
                   (kernel_stack_call_masked abi kernel_program_inv critical sg
                      (task_stack_call_active_key (armv7a_continuation_resumed_call selected call))
                      (armv7a_continuation_resumed_call selected call) final_registers.(kernel_save_r0)
                      acquired acquired **
                    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                      handler.(os_int_exit_handler_fragments) ** frame)) next_heap))))).

Proof.
  intros environment critical arch Extra restore save extra_resources extra_step sg entry released
    node handler suspended publication saved cursor before frame call abi parked focus payload extra_effect
    Horigin Hstage Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hextension Henter Hexit Hpublish Hpre
    written irq_input saved_heap Hrestore Hsave.
  assert (Hextra : forall cut initial next returned, extra_effect sg cut initial next returned ->
    UCOS2_state_inv sg initial ->
    task_saved_pointer_at initial suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_sp)) by (intros; contradiction).
  assert (Hsource : kernel_client_heap_extension_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
      call.(os_sched_call_invocation) None extra_effect).
  { unfold kernel_client_heap_extension_source; intros; contradiction. }
  assert (Hready : task_create_irq_caller_stage call released).
  { eapply task_create_call_stage_irq_entry; eassumption. }
  destruct (task_create_restore_irq_deposit environment critical arch restore sg entry released node
    handler suspended publication saved cursor before written irq_input saved_heap frame
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hr0 Hmask Hhandler Hpre
    Hrestore Hsave) as [registry_heap [Hwritten [Hwrites [Hstores [Hbinding [Hcall [Hsaved_mask
      [Hvalid [Hpointer Hregistry]]]]]]]]].
  assert (Hparked_ready : task_create_irq_caller_stage call parked).
  { eapply task_create_irq_deposit_preserves_caller_stage; eassumption. }
  exists registry_heap; split; [exact Hwritten|]. split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  assert (Hcut : @kernel_client_heap_observer_cut Extra call.(os_sched_call_invocation) KernelClientHeapClosed)
    by exact I.
  destruct (task_create_registered_call_stack_restore _ _ _ Extra abi extra_resources extra_step extra_effect
    critical.(critical_region_clients) sg call suspended Hbinding Hcall Hslice Hextension Hextra
    Henter Hexit Hpublish Hsource KernelClientHeapClosed registry_heap closed_heap parked handler frame
    Hvalid Hpointer Htrace Hcut Hregistry)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  pose proof (proj2 (task_create_builtin_trace_preserves_irq_caller_stage Extra sg call
    KernelClientHeapClosed parked KernelClientHeapClosed returned Hstates Hvalid Hparked_ready))
    as Hreturned_ready.
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hreturned_current.
  destruct (Hreturn Hreturned_current Haddress)
    as [selected [Hpointers [Hfocus [Hlease [Hselected_sp [Hcpsr [Hregisters [Hcovered Hresume]]]]]]]].
  exists selected; split; [exact Hpointers|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros irq_return resume_cursor final_cursor after Hirq_restore Hword Hlr Hsuffix.
  destruct (Hresume irq_return Hirq_restore) as [Hmemory Howned].
  rewrite Hsaved_mask in Howned.
  match type of Howned with ?P irq_return => assert (Hsuffix_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected call)
      (armv7a_irq_fiq_mask saved) **
    (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     task_tcb_init_stack_covered_capsules environment
       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame))
    by (unfold task_tcb_init_stack_covered_capsules; entailer!)
  end.
  assert (Hcomputed : (kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected call)
      (armv7a_irq_fiq_mask (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
        cursor.(kernel_restore_r0))) **
    (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     task_tcb_init_stack_covered_capsules environment
       (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
     unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) irq_return).
  { rewrite armv7a_cpsr_restore_mask_eq, Hr0; exact (Hsuffix_input irq_return Howned). }
  destruct (armv7a_restore_suffix_transports_owned_execution _ _ _ _ restore
    (armv7a_continuation_resumed_call selected call) _ resume_cursor irq_return final_cursor after
    _ Hword Hcomputed Hsuffix) as [Hcursor [Hmemory_after Hafter]].
  rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hafter.
  assert (Hhistory : kernel_call_restore_history environment critical sg call released
    (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { eapply KernelCallRestoreIRQ with (restore := restore)
      (extra_step := extra_step) (extra_effect := extra_effect)
      (handler := handler) (suspended := suspended) (cursor := cursor)
      (before := before) (written := written) (irq_input := irq_input) (saved_heap := saved_heap)
      (registry_heap := registry_heap) (closed_heap := closed_heap) (returned := returned)
      (stopped := stopped) (returned_origin := returned_origin) (irq_return := irq_return)
      (resume_cursor := resume_cursor) (final_cursor := final_cursor) (after := after);
      try eassumption; try reflexivity. }
  assert (Hstage_returned : task_create_call_stage (armv7a_continuation_resumed_call selected call)
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))).
  { eapply task_create_irq_take_reestablishes_call_stage; eassumption. }
  match type of Hafter with ?P after => assert (Hclose : P |--
    kernel_stack_call_closed abi kernel_program_inv sg
      (task_stack_call_active_key (armv7a_continuation_resumed_call selected call))
      (armv7a_continuation_resumed_call selected call) (armv7a_irq_fiq_mask saved)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold kernel_stack_call_closed, kernel_stack_inv, task_tcb_init_stack_covered_capsules,
      task_stack_call_active_key, armv7a_continuation_resumed_call.
    cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    rewrite Horigin, Hlease, kernel_program_inv_split_unmap; entailer!. }
  pose proof (Hclose after Hafter) as Hclosed.
  split; [exact Hhistory|]. split.
  - rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word]; rewrite Hlr; reflexivity.
  - split; [exact Hcovered|]. split; [exact Hafter|]. split; [exact Hstage_returned|].
    split; [exact Hclosed|].
    intros registers final_registers acquired next_heap Hnext_return Hcpsr_valid Hsaved Hnext.
    pose proof (kernel_call_restore_history_same_call environment critical sg call released
      (armv7a_continuation_resumed_call selected call)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) Hhistory) as Hsame_returned.
    exact (task_create_tcb_return_sched_masked_source environment critical arch save sg call
      (armv7a_continuation_resumed_call selected call) (armv7a_irq_fiq_mask saved)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))
      registers after final_registers acquired next_heap _ Hsame_returned Hnext_return Hcpsr_valid Hsaved
      Hclosed Hnext).
Qed.
