Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_post_wake_source_spec.

Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_foreign_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The original waiting invocation reaches its first physical foreign
    installation from the existing Scheduler input. Its non-readiness
    proves that the PRESENT selector chooses another slot. The actual
    Save/capture owns the saved mask and inside resource in the exact
    parked entry; no separately framed copy of those owners is assumed.

    The same prefix and switch execution extend this invocation's wait
    history. The selected task is still a foreign continuation; initial
    C entry or a later Post entry is a subsequent source event. *)
Lemma sem_pend_wait_saved_foreign_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (initial_entry : Armv7aInitialEntryABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg call mask state eid node registers before final_registers acquired saved_heap
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion)
  public_call wait_mask initial observed timeout waiting,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus call lr lr in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  sem_pend_wait_at (Some environment) critical sg public_call wait_mask initial observed eid timeout
    waiting call state ->
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration) node ->
  ~ In call.(os_sched_call_stack).(stackLeaseSlot) state.(SchedState).(readyList) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  state.(SchedState).(readyList) <> [] -> os_sched_requests_switch state = true ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values ->
  armv7a_irq_fiq_mask cpsr = 192 -> 0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (os_sched_stack_pre environment kernel_program_inv sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      suspended.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call suspended stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected current_node,
        os_sched_destination_binding environment.(task_stack_call_external)
          call fragments updated incoming resumed /\
        incoming.(stackLeaseSlot) <> call.(os_sched_call_stack).(stackLeaseSlot) /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        sched_current_ready_at (os_sched_install_context call fragments incoming updated).(TskState)
          (os_sched_install_context call fragments incoming updated).(SchedState) incoming.(stackLeaseSlot) current_node /\
        current_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
        task_stack_live_coverage (os_sched_install_context call fragments incoming updated).(TskState)
          (Some (task_stack_key incoming)) /\
        (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          let foreign_state := os_sched_install_context call fragments incoming updated in
          os_sched_source_switch_execution environment.(task_stack_call_external) environment.(task_stack_call_platform)
            environment.(task_stack_call_port) abi task_abi sg checkpoint call old_sp cpsr values lr
            suspended incoming selected prefix_heap restored /\
          sem_pend_wait_at (Some environment) critical sg public_call wait_mask initial observed eid timeout
            waiting call foreign_state /\
          foreign_state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
            Some (task_set_saved_sp node suspended.(armv7a_continuation_sp)) /\
          sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration)
            (task_set_saved_sp node suspended.(armv7a_continuation_sp)) /\
          task_invocation_active foreign_state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
          task_saved_pointer_at foreign_state call.(os_sched_call_stack) suspended.(armv7a_continuation_sp) /\
          foreign_state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
            Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments) /\
          armv7a_task_restored_source environment.(task_stack_call_external) selected /\
          (armv7a_task_restored_execution environment.(task_stack_call_external)
             environment.(task_stack_call_platform) environment.(task_stack_call_port) abi selected **
           kernel_program_inv sg foreign_state **
           store_parked_continuations
             (kernel_saved_sched_call_entry abi critical sg call final_registers.(kernel_save_r0) state
               suspended foreign_state.(TskState) focus) foreign_state.(TskState).(parkedTaskStacks) ** frame) restored)).
Proof.
  intros environment critical arch save task_abi initial_entry sg call mask state eid node registers before
    final_registers acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame
    public_call wait_mask initial observed timeout waiting abi focus checkpoint fragments suspended updated
    Hhistory Hsource Hnode Hwait Hblocked Habsent Hnonempty Hswitch Hreturn Hvalid_sr Hmask
    Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32
    Hsp Haddress Hpre Hsave.
  pose proof Hsource as [Horigin [Hactive Hcurrent]].
  assert (Hgen : node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration))
    by exact (proj1 Hwait).
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold os_sched_stack_pre, kernel_stack_call_closed, kernel_stack_inv.
      rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  assert (Hid : node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hlinks.
    destruct Hlinks as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hnode].
    apply Hdomain; eauto. }
  assert (Hcovered : task_stack_live_coverage state.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop
      (task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) && TT) end.
    { unfold os_sched_stack_pre, kernel_stack_call_closed, kernel_stack_inv, task_stack_call_active_key.
      rewrite Horigin; unfold task_stack_key; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  assert (Henabled : os_sched_selection_enabled state = true)
    by exact (proj1 (proj1 (os_sched_requests_switch_iff state) Hswitch)).
  assert (Hready : checkpoint.(SchedState).(readyList) = state.(SchedState).(readyList))
    by exact (proj1 (os_sched_ready_checkpoint_frame state)).
  assert (Hhigh : sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState)).
  { apply os_sched_ready_checkpoint_high_consistency with (sg := sg); [|exact Henabled].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hforeign : checkpoint.(SchedState).(highRdyTid) <> Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold sched_high_ready_consistency in Hhigh; rewrite Hready in Hhigh.
    destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    destruct Hhigh as [Hhead _].
    intro Heq; assert (head = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
    subst head; apply Hblocked; simpl; auto. }
  unfold task_execution_current in Hcurrent; rewrite Horigin in Hcurrent.
  assert (Hinput : os_sched_source_live_save_input sg checkpoint node call old_sp cpsr values lr
    prefix suffix first old_words focus publication).
  { unfold os_sched_source_live_save_input, focus.
    assert (Hcur : checkpoint.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
    { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch; exact Hcurrent. }
    rewrite Hready; repeat first [assumption | reflexivity | split | intro]. }
  assert (Howned : (kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call mask ** kernel_program_inv sg state **
    armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Hopen : P |-- Q) end end.
    { unfold os_sched_stack_pre, kernel_stack_call_closed, kernel_stack_inv; fold abi; Intros.
      sep_apply_l_atomic (armv7a_task_call_stacks_absent _ _ _ abi state.(TskState) focus
        state.(TskState).(parkedTaskStacks) Habsent); entailer!. }
    exact (Hopen before Hpre). }
  destruct (kernel_sched_save_foreign_source _ _ _ abi critical arch save task_abi initial_entry
    sg state call node mask focus old_sp cpsr values lr prefix suffix first old_words publication
    registers final_registers acquired before saved_heap frame Hswitch Hnonempty Hforeign Hinput Hcovered
    Hsource Hreturn Hvalid_sr Hmask Howned Hsave)
    as [Hrun [Hacquired [prefix_heap [written [stored [Hprefix [Hwrites [Hload [Hstore Hselected]]]]]]]]].
  split; [exact Hrun|]. split; [exact Hacquired|].
  exists prefix_heap, written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
  split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hselected captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [resumed [installed [selected [current_node
      [Harch [Hdestination [Hkey [Hlease [Hselected_fragments [Hinstall [Hreads
        [Hparked [Hready_current [Hgen_current [Hcoverage [Hfocus_lookup [Hinitial Hrestore]]]]]]]]]]]]]]]]]].
  set (foreign_state := os_sched_install_context call fragments incoming updated) in *.
  change (sched_current_ready_at foreign_state.(TskState) foreign_state.(SchedState)
    incoming.(stackLeaseSlot) current_node) in Hready_current.
  assert (Hready_list : foreign_state.(SchedState).(readyList) = state.(SchedState).(readyList)).
  { unfold foreign_state, updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState).
    rewrite Hnode; change (checkpoint.(SchedState).(readyList) = state.(SchedState).(readyList)).
    exact Hready. }
  assert (Hother : incoming.(stackLeaseSlot) <> call.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj2 (proj2 Hready_current)))) as Hin.
    rewrite Hready_list in Hin; intro Heq; rewrite Heq in Hin; contradiction. }
  assert (Hlookup : foreign_state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))).
  { unfold foreign_state, updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState).
    rewrite Hnode; cbn [os_sched_install_context replace_SchedS replace_TskS TskState
      glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Hwait_after : sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration)
    (task_set_saved_sp node suspended.(armv7a_continuation_sp))) by exact Hwait.
  assert (Hactive_after : task_invocation_active foreign_state.(TskState)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { unfold foreign_state, updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState).
    rewrite Hnode; change (task_invocation_active (glob_task_set_usedtask state.(TskState)
      call.(os_sched_call_stack).(stackLeaseSlot) (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
      call.(os_sched_call_invocation) call.(os_sched_call_origin)).
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive]. }
  assert (Hpointer : task_saved_pointer_at foreign_state call.(os_sched_call_stack) suspended.(armv7a_continuation_sp)).
  { exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)); repeat split; assumption. }
  exists incoming, resumed, installed, selected, current_node.
  split; [exact Hdestination|]. split; [exact Hother|]. split; [exact Hlease|].
  split; [exact Hselected_fragments|]. split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hready_current|]. split; [exact Hgen_current|]. split; [exact Hcoverage|].
  split; [exact Hinitial|].
  intros restored Hrestored; cbv zeta.
  destruct (Hrestore restored Hrestored) as [Hexecution [Hrestored_source Hafter]].
  assert (Hwait_history : sem_pend_wait_at (Some environment) critical sg public_call wait_mask initial
    observed eid timeout waiting call foreign_state).
  { destruct Hhistory as [owned [Henvironment [Hsame [Hobserved Hpath]]]]; inversion Henvironment; subst owned.
    exists environment; split; [reflexivity|]. split; [exact Hsame|]. split; [exact Hobserved|].
    eapply SemPendWaitSourceTrans; [exact Hpath|].
    eapply SemPendWaitSourceSwitch; [exact Hprefix|exact Hexecution]. }
  exact (conj Hexecution (conj Hwait_history (conj Hlookup (conj Hwait_after (conj Hactive_after
    (conj Hpointer (conj Hparked (conj Hrestored_source Hafter)))))))).
Qed.

