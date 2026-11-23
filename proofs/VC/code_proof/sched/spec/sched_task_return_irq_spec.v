Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Import FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Focus the actual saved entry already owned by this map. The selected
    descriptor and its Scheduler local/receipt come from that entry; the
    operation neither manufactures a continuation nor copies its resources.
    All other entries retain exactly [other]. *)
Lemma kernel_sched_saved_continuation_irq_focus : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg tasks
  original saved acquired receipt other stacks fragments,
  stacks (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (kernel_sched_saved_local_resource_at platform critical sg tasks original saved acquired receipt other)) stacks |--
  EX selected,
    coq_prop (armv7a_continuation_binding selected /\
      selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
      selected.(armv7a_continuation_fragments) = fragments /\
      selected.(armv7a_continuation_call) = Some original /\
      selected.(armv7a_continuation_pc) = selected.(armv7a_continuation_lr) /\
      armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
      original.(os_sched_call_origin) = RunningInvocation
        original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) /\
      task_invocation_active tasks original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
      task_stack_live_sp tasks (task_stack_key original.(os_sched_call_stack)) selected.(armv7a_continuation_sp)) &&
    store_parked_continuations
      (kernel_saved_continuation_entry abi tasks
        (kernel_irq_fields_local other selected
          (kernel_sched_saved_local platform critical sg tasks original saved acquired selected ** receipt))) stacks.
Proof.
  intros external platform port abi critical sg tasks original saved acquired receipt other stacks fragments Hentry.
  intros heap Hmap_owned.
  set (local := kernel_sched_saved_local_resource_at platform critical sg tasks original saved acquired receipt other).
  set (resource := kernel_saved_continuation_entry abi tasks local).
  pose proof (store_parked_continuations_take resource stacks original.(os_sched_call_stack)
    fragments Hentry heap Hmap_owned) as Hparts.
  destruct Hparts as [selected_heap [rest_heap [Hjoin [Hselected_entry Hrest]]]].
  destruct Hselected_entry as [selected [[Hbinding [Hkey [Hpayload [Hslice Hpointer]]]] Howned]].
  assert (Hlocal : local selected =
    kernel_sched_saved_local platform critical sg tasks original saved acquired selected ** receipt).
  { unfold local, kernel_sched_saved_local_resource_at.
    destruct task_stack_key_eq_dec; [reflexivity|contradiction]. }
  rewrite Hlocal in Howned.
  pose proof Howned as Howned_parts.
  destruct Howned_parts as [execution_heap [local_heap [Hlocal_join [Hexecution Hsaved_receipt]]]].
  destruct Hsaved_receipt as [saved_heap [receipt_heap [Hreceipt_join [Hsaved_local Hreceipt]]]].
  destruct Hsaved_local as [[Hcall [Hpc [Hmask [Horigin Hactive]]]] Hsaved_resources].
  assert (Hlease : selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hstack; rewrite Hcall in Hstack; symmetry; exact Hstack. }
  assert (Hfragments : selected.(armv7a_continuation_fragments) = fragments) by congruence.
  set (focused := kernel_irq_fields_local other selected
    (kernel_sched_saved_local platform critical sg tasks original saved acquired selected ** receipt)).
  set (focused_resource := kernel_saved_continuation_entry abi tasks focused).
  assert (Hfocused_entry : focused_resource (task_stack_key original.(os_sched_call_stack))
    (original.(os_sched_call_stack).(stackLeaseRegion), fragments) selected_heap).
  { unfold focused_resource, kernel_saved_continuation_entry.
    exists selected; split.
    - exact (conj Hbinding (conj Hkey (conj Hpayload (conj Hslice Hpointer)))).
    - unfold focused, kernel_irq_fields_local.
      destruct task_stack_key_eq_dec; [|contradiction].
      destruct Howned as [owned_execution [owned_local [Howned_join [Howned_execution Howned_local]]]].
      exists owned_execution, owned_local; split; [exact Howned_join|].
      split; [exact Howned_execution|]. split; [reflexivity|exact Howned_local]. }
  pose proof (kernel_saved_continuation_resource_map_unfocus_absent external platform port abi critical sg
    tasks tasks original saved acquired receipt other (task_stack_take stacks original.(os_sched_call_stack))
    (task_stack_take_lookup stacks original.(os_sched_call_stack)) rest_heap Hrest) as Hunfocused_rest.
  assert (Hnone : task_stack_take stacks original.(os_sched_call_stack)
      (task_stack_key selected.(armv7a_continuation_stack)) = None)
    by (rewrite Hlease; apply task_stack_take_lookup).
  pose proof ((proj1 (kernel_irq_fields_local_map_absent external platform port abi tasks
    (task_stack_take stacks original.(os_sched_call_stack)) other selected
    (kernel_sched_saved_local platform critical sg tasks original saved acquired selected ** receipt) Hnone))
    rest_heap Hunfocused_rest) as Hfocused_rest.
  assert (Hfocused_whole : (focused_resource (task_stack_key original.(os_sched_call_stack))
      (original.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    store_parked_continuations focused_resource (task_stack_take stacks original.(os_sched_call_stack))) heap).
  { exists selected_heap, rest_heap; exact (conj Hjoin (conj Hfocused_entry Hfocused_rest)). }
  pose proof (store_parked_continuations_park focused_resource
    (task_stack_take stacks original.(os_sched_call_stack)) original.(os_sched_call_stack) fragments
    (task_stack_take_lookup stacks original.(os_sched_call_stack)) heap Hfocused_whole) as Hpacked.
  assert (Hmap : forall key,
    task_stack_park_fragments (task_stack_take stacks original.(os_sched_call_stack))
      original.(os_sched_call_stack) fragments key = stacks key).
  { intros key; unfold task_stack_park_fragments, task_stack_take, field_update.
    destruct (task_stack_key_eq_dec key (task_stack_key original.(os_sched_call_stack)))
      as [Heq|Hne]; [subst key; symmetry; exact Hentry|reflexivity]. }
  exists selected; split.
  - exact (conj Hbinding (conj Hlease (conj Hfragments (conj Hcall (conj Hpc
      (conj Hmask (conj Horigin (conj Hactive Hpointer)))))))).
  - exact ((proj1 (@store_map_equiv (TaskID * nat)%type
      (TaskStackRegion * TaskStackFragments)%type focused_resource _ _ Hmap)) heap Hpacked).
Qed.

(** The final actual OSIntExit transfer selects the original parked caller.
    Cache installation and map take use the same fields heap. The observed
    IRQ restore returns to the saved OSCtxSw PC, before CPU Restore; hence
    this is a masked continuation, not a claim of a complete API return.

    The IRQ ABI produces execution ownership at this cut, but does not
    produce the independent opaque [os_sched_arch_resume_source] relation.
    The new task-return history consumes this actual IRQ branch directly. *)
Lemma os_sched_task_irq_selected_masked_return_source : forall environment critical
  sg handler entry transfer original saved acquired receipt other before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let hooked := transfer.(os_int_exit_hooked_state) in
  let local := kernel_sched_saved_local_resource_at environment.(task_stack_call_platform) critical sg
    hooked.(TskState) original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_int_exit_installed_state transfer in
  os_int_exit_transfer_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) None ->
  (UCOS2_fields_inv sg hooked ** store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    selected.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) /\
    selected.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) /\
    selected.(armv7a_continuation_call) = Some original /\
    selected.(armv7a_continuation_pc) = selected.(armv7a_continuation_lr) /\
    armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
    sched_install_heap_fragment sg before installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_irq_restore_pointer_reads sg installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall irq_return,
      armv7a_restore_transition abi handler selected installed irq_return ->
      let returned := armv7a_continuation_resumed_call selected original in
      irq_return.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      task_tcb_init_stack_same_call returned original /\
      kernel_call_task_source returned current /\
      os_sched_task_ready_source environment sg returned current /\
      os_sched_task_current_ready returned current /\
      kernel_call_normal_return original hooked returned current /\
      kernel_call_control_rely sg hooked current /\
      (kernel_continuation_call_masked abi kernel_program_fields_inv other critical sg
        (task_stack_call_active_key returned) returned saved acquired current ** receipt **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) irq_return).
Proof.
  intros environment critical sg handler entry transfer original saved acquired receipt other before frame
    abi hooked local resource current Htransfer Hhigh Hincoming Haddress Hcoverage Hpre.
  assert (Hdestination : os_int_exit_destination_binding environment.(task_stack_call_external) transfer)
    by (unfold os_int_exit_transfer_source in Htransfer; tauto).
  destruct Hdestination as [Hselected [[node [Hnode [Hgen [Hpriority Hsp]]]] [Hlive [Hparked Harch]]]].
  rewrite Hincoming in Hselected, Hnode, Hgen, Hparked.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { destruct Hpre as [fields_map_heap [frame_heap [Hjoin [Hfields_map Hframe]]]].
    destruct Hfields_map as [fields_heap [map_heap [Hfields_join [Hfields Hmap]]]].
    exact (proj1 Hfields). }
  assert (Hindex : forall p, hooked.(SchedState).(highRdyPrio) = Some p -> task_priority_in_range sg p).
  { intros p Hp; assert (p = node.(curPrio)) by (unfold hooked in Hp; congruence); subst p.
    pose proof (proj1 (proj2 Hvalid)) as Htasks.
    assert (Hpriorities : forall tid t, hooked.(TskState).(inUsedTaskStates) tid = Some t ->
      task_priority_in_range sg t.(curPrio)) by (unfold task_in_range in Htasks; tauto).
    eapply Hpriorities; exact Hnode. }
  match type of Hpre with ?P before => assert (Hraw : P |-- UCOS2_fields_raw_rep sg hooked **
    (store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(task_stack_call_platform)
        handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame))) end.
  { unfold UCOS2_fields_inv; entailer!. }
  destruct (sched_install_heap_fields_raw_frame_post sg hooked original.(os_sched_call_stack).(stackLeaseSlot)
    node _ before Hselected Hnode Haddress (Hraw before Hpre)) as [installed [Hinstall Hinstalled]].
  set (cached := replace_SchedS (sched_install_selected hooked.(SchedState)) hooked).
  assert (Hcached_valid : UCOS2_state_inv sg cached)
    by (apply os_int_exit_install_cache_preserves_validity; assumption).
  match type of Hinstalled with ?P installed => assert (Hclose : P |--
    EX selected,
      coq_prop (armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
        selected.(armv7a_continuation_fragments) = transfer.(os_int_exit_incoming_fragments) /\
        selected.(armv7a_continuation_call) = Some original /\
        selected.(armv7a_continuation_pc) = selected.(armv7a_continuation_lr) /\
        armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
        original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
          original.(os_sched_call_stack).(stackLeaseGeneration) /\
        task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
        task_stack_live_sp hooked.(TskState) (task_stack_key original.(os_sched_call_stack)) selected.(armv7a_continuation_sp)) &&
      (UCOS2_fields_inv sg cached ** store_parked_continuations
        (kernel_saved_continuation_entry abi cached.(TskState)
          (kernel_irq_fields_local other selected
            (kernel_sched_saved_local environment.(task_stack_call_platform) critical sg hooked.(TskState)
               original saved acquired selected ** receipt))) cached.(TskState).(parkedTaskStacks) **
       (interrupt_platform_running environment.(task_stack_call_platform)
          handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources environment.(task_stack_call_port) handler ** unmap_table_rep sg ** frame))) end.
  { unfold resource, local.
    sep_apply_l_atomic (kernel_sched_saved_continuation_irq_focus environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port) abi critical sg hooked.(TskState)
      original saved acquired receipt other hooked.(TskState).(parkedTaskStacks)
      transfer.(os_int_exit_incoming_fragments) Hparked).
    Intros selected; Exists selected; unfold UCOS2_fields_inv, cached; entailer!;
    (cbn [replace_SchedS TskState];
    intros heap [map_heap [remaining_heap [Hjoin [[Hfacts Hmap] Hremaining]]]];
    split; [exact Hfacts|];
    match type of Hmap with ?P map_heap =>
      match type of Hremaining with ?Q remaining_heap =>
        match goal with |- ?R heap =>
          assert (Hreorder : P ** Q |-- R) by entailer!;
          apply (Hreorder heap);
          exists map_heap, remaining_heap;
          exact (conj Hjoin (conj Hmap Hremaining))
        end
      end
    end). }
  destruct (Hclose installed Hinstalled) as [selected [[Hbinding [Hlease [Hfragments [Hcall [Hpc
    [Hmask [Horigin [Hactive Hpointer]]]]]]]] Howned]].
  assert (Hselected_sp : selected.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp)).
  { assert (Hnode_sp : node.(tcbStkPtr) = selected.(armv7a_continuation_sp)) by (apply Hpointer; assumption).
    congruence. }
  assert (Hcached_current : cached.(SchedState).(curTaskID) =
    Some selected.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Hselected).
  assert (Hselected_node : cached.(TskState).(inUsedTaskStates) selected.(armv7a_continuation_stack).(stackLeaseSlot) = Some node)
    by (rewrite Hlease; exact Hnode).
  assert (Hselected_gen : node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration))
    by (rewrite Hlease; exact Hgen).
  assert (Hselected_parked : cached.(TskState).(parkedTaskStacks) (task_stack_key selected.(armv7a_continuation_stack)) =
    Some (selected.(armv7a_continuation_stack).(stackLeaseRegion), selected.(armv7a_continuation_fragments)))
    by (rewrite Hlease, Hfragments; exact Hparked).
  assert (Hselected_address : tcb_field_address (task_slot_addr sg selected.(armv7a_continuation_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg selected.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Haddress).
  destruct (kernel_irq_take_fields_local_resources environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi sg cached other selected
    (kernel_sched_saved_local environment.(task_stack_call_platform) critical sg hooked.(TskState)
      original saved acquired selected ** receipt) original node _ installed Hcall Hcached_current Hselected_node
    Hselected_gen Hselected_parked Hselected_address Hcoverage Howned)
    as [Hpointers [Hreads [Hcovered Htaken]]].
  assert (Hcurrent_eq : os_int_exit_wrapper_restored_state cached selected.(armv7a_continuation_stack) = current).
  { unfold current, os_int_exit_installed_state; rewrite Hincoming, Hlease; reflexivity. }
  rewrite Hcurrent_eq in Hcovered, Htaken.
  exists installed, selected; split; [exact Hlease|]. split; [exact Hselected_sp|].
  split; [exact Hfragments|]. split; [exact Hcall|]. split; [exact Hpc|]. split; [exact Hmask|].
  split; [rewrite Hselected_sp, <- Hsp; exact Hinstall|].
  split; [rewrite <- Hlease; exact Hpointers|]. split; [exact Hreads|].
  intros irq_return Hrestore returned.
  match type of Htaken with ?P installed => assert (Hrestore_input : P |--
    interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion) selected.(armv7a_continuation_fragments) **
    armv7a_dormant_continuation abi selected **
    (UCOS2_fields_inv sg current ** store_parked_continuations
       (kernel_saved_continuation_entry abi current.(TskState) other) current.(TskState).(parkedTaskStacks) **
     kernel_sched_saved_local environment.(task_stack_call_platform) critical sg hooked.(TskState)
       original saved acquired selected ** receipt ** unmap_table_rep sg ** frame)) by entailer! end.
  destruct (armv7a_restore_transition_resources environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi handler selected _ installed irq_return
    Hreads (Hrestore_input installed Htaken) Hrestore) as [Hmemory Hrestored].
  rewrite Hcall, Hmask in Hrestored.
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { unfold returned, task_tcb_init_stack_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  assert (Hsource : kernel_call_task_source returned current).
  { unfold returned, kernel_call_task_source, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin os_sched_call_stack os_sched_call_invocation].
    split; [rewrite Hlease; exact Horigin|]. split; [exact Hactive|].
    unfold task_execution_current; rewrite Horigin; exact Hselected. }
  assert (Hready : os_sched_task_ready_source environment sg returned current).
  { unfold current; eapply OsSchedTaskReadyInterruptSelected; [exact Hvalid|exact Hhigh| |].
    - unfold os_int_exit_transfer_source in Htransfer; tauto.
    - unfold returned, armv7a_continuation_resumed_call; cbn; congruence. }
  assert (Hnormal : kernel_call_normal_return original hooked returned current).
  { split; [exact Hsame|]. intro Havailable.
    unfold kernel_call_stack_available; rewrite (proj1 Hsource), (proj2 (proj2 Hsame)).
    unfold current, os_int_exit_installed_state; rewrite Hincoming; apply task_stack_take_lookup. }
  assert (Hkey : task_stack_call_active_key returned = Some (task_stack_key selected.(armv7a_continuation_stack))).
  { unfold returned, task_stack_call_active_key, armv7a_continuation_resumed_call; cbn; rewrite Horigin, Hlease; reflexivity. }
  split; [exact Hmemory|]. split; [exact Hsame|]. split; [exact Hsource|]. split; [exact Hready|].
  split; [eapply os_sched_task_ready_source_current_ready; exact Hready|]. split; [exact Hnormal|].
  split; [split; reflexivity|].
  match type of Hrestored with ?P irq_return => match goal with |- ?Q irq_return => assert (Hmasked : P |-- Q) end end.
  { unfold kernel_continuation_call_masked, kernel_continuation_inv.
    rewrite Hkey, kernel_program_fields_inv_split_unmap.
    unfold kernel_sched_saved_local, kernel_call_execution_owned, critical_region_masked,
      returned, armv7a_continuation_resumed_call; cbn [os_sched_call_invocation os_sched_call_origin]; entailer!. }
  exact (Hmasked irq_return Hrestored).
Qed.
