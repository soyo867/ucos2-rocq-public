Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_irq_source_spec.
Import FlagPendSchedulerResources.
(** Source consumers for the exact saved local owner on normal return.
    No existence of a future selection/return is assumed. Each conclusion
    is conditional on the actual restore transition at the same source cut.
    The receipt was already owned by the selected descriptor; absence in a
    map does not manufacture it. Public API/callee composition is separate. *)

Lemma kernel_saved_sched_continuation_fields_receipt_return_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical arch
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg context outgoing hooked original saved acquired receipt other resumed before (frame : Assertion),
  let local := kernel_sched_saved_local_resource_at platform critical sg hooked.(TskState)
    original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some original /\
      kernel_call_task_source returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
        after.(ConAssertion.s_mem) = restored.(ConAssertion.s_mem) /\
        (kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask saved) **
         kernel_program_fields_inv sg current **
         store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
           current.(TskState).(parkedTaskStacks) ** receipt ** frame) after)).
Proof.
  intros external platform port abi critical arch task_abi restore sg context outgoing hooked original
    saved acquired receipt other resumed before frame local resource current Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (kernel_saved_continuation_fields_install_source external platform port abi task_abi sg context
    outgoing hooked original.(os_sched_call_stack) resumed local before frame
    Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hbinding [Hlease [Hfragments [Hcurrent [Hcovered Hrestore]]]]]]]]].
  fold current in Hcurrent, Hcovered, Hrestore.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hmemory [Hsource Howned]].
  assert (Hlocal : local selected = kernel_sched_saved_local platform critical sg hooked.(TskState)
    original saved acquired selected ** receipt).
  { unfold local; apply kernel_sched_saved_local_resource_at_selected; exact Hlease. }
  rewrite Hlocal in Howned.
  assert (Hfacts : selected.(armv7a_continuation_call) = Some original /\
      armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
      original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
        original.(os_sched_call_stack).(stackLeaseGeneration) /\
      task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { match type of Howned with ?P restored => assert (Hexpose : P |-- coq_prop
      (selected.(armv7a_continuation_call) = Some original /\
       armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
       original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
         original.(os_sched_call_stack).(stackLeaseGeneration) /\
       task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin)) && TT) end.
    { unfold kernel_sched_saved_local; entailer!; try tauto; intros ? ?; exact I. }
    exact (proj1 (Hexpose restored Howned)). }
  destruct Hfacts as [Hcall [Hmask [Horigin Hactive]]].
  assert (Hactive_current : task_invocation_active current.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { exact Hactive. }
  assert (Hselected_current : task_current_at current selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { rewrite Hlease; exact Hcurrent. }
  assert (Hreturned_source : kernel_call_task_source returned current).
  { unfold returned; eapply kernel_selected_saved_call_source; eassumption. }
  assert (Hreturned : returned = armv7a_continuation_resumed_call selected original).
  { unfold returned, kernel_selected_call; rewrite Hcall; reflexivity. }
  split; [exact Hcall|]. split; [exact Hreturned_source|].
  intros cursor written middle final_cursor after Hr0 Hcurrent_mask Hprefix Hsuffix.
  match type of Howned with ?P restored => assert (Hopen : P |--
    critical_region_masked platform critical sg returned.(os_sched_call_invocation)
      returned.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
    (kernel_program_fields_inv sg current **
     store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
       current.(TskState).(parkedTaskStacks) ** receipt ** frame)) end.
  { unfold armv7a_task_restored_execution; rewrite Hcall, Hmask, Hreturned.
    unfold kernel_sched_saved_local, kernel_call_execution_owned, critical_region_masked,
      armv7a_continuation_resumed_call; cbn [os_sched_call_invocation os_sched_call_origin]; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch restore
    sg returned saved acquired cursor restored written middle final_cursor after _ Hr0 Hcurrent_mask
    (Hopen restored Howned) Hprefix Hsuffix) as [Hrun [Hlr [Hheap Hafter]]].
  split; [exact Hrun|]. split; [exact Hlr|]. split; [exact Hheap|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) by entailer! end end.
  exact (Hclose after Hafter).
Qed.

Lemma os_sched_fields_modular_saved_call_receipt_return :
  forall external platform port critical arch
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    sg context outgoing hooked source_tasks original saved acquired receipt other resumed before
    (frame : Assertion),
  let local := kernel_sched_saved_local_resource_at platform critical sg source_tasks original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some original /\
      returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack) /\
      kernel_call_task_source returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
        after.(ConAssertion.s_mem) = restored.(ConAssertion.s_mem) /\
        (kernel_continuation_call_closed abi kernel_program_fields_inv other sg
           (Some (task_stack_key original.(os_sched_call_stack))) returned
           (armv7a_irq_fiq_mask saved) current ** receipt ** frame) after)).
Proof.
  intros external platform port critical arch abi task_abi restore sg context outgoing hooked source_tasks
    original saved acquired receipt other resumed before frame local resource current
    Hactive Hsaved Hdestination Haddress Hcoverage Hpre.
  set (current_local := kernel_sched_saved_local_resource_at platform critical sg hooked.(TskState)
    original saved acquired receipt other).
  set (current_resource := kernel_saved_continuation_entry abi hooked.(TskState) current_local).
  assert (Hentry : forall key payload, resource key payload |-- current_resource key payload).
  { intros key payload; unfold resource, current_resource, kernel_saved_continuation_entry.
    Intros descriptor; Exists descriptor.
    unfold local, current_local, kernel_sched_saved_local_resource_at.
    destruct task_stack_key_eq_dec; [unfold kernel_sched_saved_local; entailer!|entailer!]. }
  assert (Hmap : store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) |--
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks)).
  { unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
    intros key payload Hlookup; apply Hentry. }
  match type of Hpre with ?P before => assert (Hconvert : P |--
    UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
    current_resource (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) end.
  { sep_apply_l_atomic (Hentry (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing)).
    sep_apply_l_atomic Hmap; entailer!. }
  destruct (kernel_saved_sched_continuation_fields_receipt_return_source external platform port abi critical arch
    task_abi restore sg context outgoing hooked original saved acquired receipt other resumed before frame
    Hsaved Hdestination Haddress Hcoverage (Hconvert before Hpre))
    as [installed [selected [Hinstall [Hreads [Hlease Hrestore]]]]].
  fold current current_local in Hrestore.
  assert (Hcovered : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key original.(os_sched_call_stack)))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing))
      original.(os_sched_call_stack)
      (task_stack_park_covers_active hooked.(TskState) context.(os_sched_call_stack) outgoing Hcoverage)). }
  assert (Habsent : current.(TskState).(parkedTaskStacks)
    (task_stack_key original.(os_sched_call_stack)) = None) by apply task_stack_take_lookup.
  assert (Hunfocus : store_parked_continuations
      (kernel_saved_continuation_entry abi current.(TskState) current_local)
      current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) other)
      current.(TskState).(parkedTaskStacks)).
  { unfold current_local; apply kernel_saved_continuation_resource_map_unfocus_absent; exact Habsent. }
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hcall [Hsource Htail]].
  fold returned in Hsource, Htail.
  assert (Hsame : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack)).
  { unfold returned, kernel_selected_call; rewrite Hcall.
    unfold armv7a_continuation_resumed_call; cbn; auto. }
  split; [exact Hcall|]. destruct Hsame as [Hi [Ho Hs]].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|]. split; [exact Hsource|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Htail cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix)
    as [Hrun [Hlr [Hmemory Howned]]].
  split; [exact Hrun|]. split; [exact Hlr|]. split; [exact Hmemory|].
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic Hunfocus.
    unfold kernel_continuation_call_closed, kernel_continuation_inv; entailer!. }
  exact (Hclose after Howned).
Qed.

(** A focused IRQ entry keeps the exact descriptor produced by the save and
    the actual interrupted local resource. All other entries keep [other]
    verbatim, including their initial-entry resources. *)
Definition kernel_irq_fields_local (other : Armv7aContinuation -> Assertion)
  (suspended : Armv7aContinuation) (receipt : Assertion)
  (descriptor : Armv7aContinuation) : Assertion :=
  if task_stack_key_eq_dec (task_stack_key descriptor.(armv7a_continuation_stack))
      (task_stack_key suspended.(armv7a_continuation_stack))
  then coq_prop (descriptor = suspended) && receipt
  else other descriptor.

Lemma kernel_irq_fields_local_selected : forall other suspended receipt,
  kernel_irq_fields_local other suspended receipt suspended --||--
    (coq_prop (suspended = suspended) && receipt).
Proof.
  intros; unfold kernel_irq_fields_local.
  destruct task_stack_key_eq_dec; [split; entailer!|contradiction].
Qed.

Lemma kernel_irq_fields_local_map_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks stacks local suspended receipt,
  stacks (task_stack_key suspended.(armv7a_continuation_stack)) = None ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) stacks --||--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (kernel_irq_fields_local local suspended receipt)) stacks.
Proof.
  intros external platform port abi tasks stacks local suspended receipt Hnone.
  split; (unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono;
    intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor;
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = key) by tauto;
    assert (Hdifferent : task_stack_key descriptor.(armv7a_continuation_stack) <>
      task_stack_key suspended.(armv7a_continuation_stack))
      by (intro Heq; rewrite <- Hkey, Heq, Hnone in Hlookup; discriminate);
    Exists descriptor; unfold kernel_irq_fields_local;
    destruct task_stack_key_eq_dec; [contradiction|entailer!]).
Qed.

Lemma kernel_irq_take_fields_local_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state local suspended receipt call node
  (frame : Assertion) heap,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_fields_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState) (kernel_irq_fields_local local suspended receipt))
     state.(TskState).(parkedTaskStacks) ** frame) heap ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot))
    suspended.(armv7a_continuation_sp) /\
  armv7a_continuation_restore_reads suspended heap /\
  task_stack_live_coverage restored.(TskState) (Some (task_stack_key suspended.(armv7a_continuation_stack))) /\
  (UCOS2_fields_inv sg restored ** store_parked_continuations
     (kernel_saved_continuation_entry abi restored.(TskState) local)
     restored.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
     suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended ** receipt ** frame) heap.
Proof.
  intros external platform port abi sg state local suspended receipt call node frame heap
    Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre restored.
  assert (Hpointers : armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) node.(tcbStkPtr)).
  { match type of Hpre with ?P heap => assert (Horder : P |-- UCOS2_fields_inv sg state **
      (store_parked_continuations
        (kernel_saved_continuation_entry abi state.(TskState) (kernel_irq_fields_local local suspended receipt))
        state.(TskState).(parkedTaskStacks) ** frame)) by entailer! end.
    destruct (Horder heap Hpre) as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
    eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_fields_live; eassumption. }
  match type of Hpre with ?P heap => assert (Htake : P |--
    coq_prop (armv7a_continuation_binding suspended /\ armv7a_task_frame_slice suspended /\
      task_stack_live_sp state.(TskState) (task_stack_key suspended.(armv7a_continuation_stack))
        suspended.(armv7a_continuation_sp)) &&
    (UCOS2_fields_inv sg restored ** store_parked_continuations
       (kernel_saved_continuation_entry abi restored.(TskState) local)
       restored.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
       suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended ** receipt ** frame)) end.
  { rewrite UCOS2_fields_inv_split_parked_stacks; Intros.
    assert (Hvalid : UCOS2_state_inv sg state) by assumption.
    assert (Hconsistent : parked_stacks_consistent state.(TskState)
      (task_stack_take state.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_stack))).
    { apply task_stack_take_preserves_consistency.
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
    sep_apply_l_atomic (store_parked_stacks_take_fragments state.(TskState).(parkedTaskStacks)
      suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_fragments) Hparked).
    sep_apply_l_atomic (store_parked_continuations_take
      (kernel_saved_continuation_entry abi state.(TskState) (kernel_irq_fields_local local suspended receipt))
      state.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_stack)
      suspended.(armv7a_continuation_fragments) Hparked).
    sep_apply_l_atomic (proj2 (kernel_irq_fields_local_map_absent external platform port abi state.(TskState)
      (task_stack_take state.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_stack))
      local suspended receipt (task_stack_take_lookup _ _))).
    unfold kernel_saved_continuation_entry at 2; Intros descriptor.
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) =
      task_stack_key suspended.(armv7a_continuation_stack)) by tauto.
    unfold kernel_irq_fields_local; rewrite Hkey.
    destruct task_stack_key_eq_dec as [Heq|Hne]; [|contradiction].
    Intros; assert (descriptor = suspended) by assumption; subst descriptor.
    sep_apply_l_atomic (UCOS2_fields_inv_merge_updated_parked_stacks sg state _ Hvalid Hconsistent).
    unfold armv7a_task_continuation_resource; rewrite Hcall.
    unfold restored, os_int_exit_wrapper_restored_state;
      cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks]; entailer!. }
  destruct (Htake heap Hpre) as [[Hbinding [Hslice Hlive]] Hresources].
  assert (Hsp : node.(tcbStkPtr) = suspended.(armv7a_continuation_sp)) by (apply Hlive; assumption).
  rewrite Hsp in Hpointers; split; [exact Hpointers|]. split.
  - eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hresources with ?P heap => assert (Horder : P |--
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) **
      (UCOS2_fields_inv sg restored ** store_parked_continuations
         (kernel_saved_continuation_entry abi restored.(TskState) local)
         restored.(TskState).(parkedTaskStacks) ** armv7a_dormant_continuation abi suspended ** receipt ** frame))
      by entailer! end.
    exact (Horder heap Hresources).
  - split; [apply task_stack_take_covers_selected; exact Hcoverage|exact Hresources].
Qed.

Lemma kernel_irq_save_fields_local_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler descriptor publication local
  (interrupted_local frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call descriptor.(armv7a_continuation_sp)
    descriptor.(armv7a_continuation_fragments) in
  armv7a_task_frame_slice descriptor ->
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
    descriptor.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    descriptor.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (os_int_exit_frame_save_pre external platform handler **
   (UCOS2_fields_inv sg entry **
    store_parked_continuations
      (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) ** interrupted_local ** frame)) before ->
  armv7a_save_transition abi handler descriptor before saved_heap ->
  exists final,
    descriptor.(armv7a_continuation_call) = Some call /\
    descriptor.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = handler.(os_int_exit_interrupted_mask) /\
    kernel_heap_writes (armv7a_continuation_save_writes descriptor)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) descriptor.(armv7a_continuation_sp)) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_fields_inv sg parked **
     store_parked_continuations
       (kernel_saved_continuation_entry abi parked.(TskState)
         (kernel_irq_fields_local local descriptor interrupted_local))
       parked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler descriptor publication local interrupted_local
    frame before saved_heap call parked Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hcoverage Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler descriptor before saved_heap Hsave)
    as [Hsource [Hcall [Hbinding Hobservations]]].
  assert (Hlease : descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hstack; rewrite Hcall in Hstack; symmetry; exact Hstack. }
  assert (Habsent : entry.(TskState).(parkedTaskStacks)
    (task_stack_key descriptor.(armv7a_continuation_stack)) = None) by (rewrite Hlease; exact Hnone).
  match type of Hpre with ?P before => assert (Hopen : P |--
    os_int_exit_frame_save_pre external platform handler **
      (UCOS2_fields_inv sg entry **
       store_parked_continuations
         (kernel_saved_continuation_entry abi entry.(TskState)
           (kernel_irq_fields_local local descriptor interrupted_local))
         entry.(TskState).(parkedTaskStacks) **
       kernel_irq_fields_local local descriptor interrupted_local descriptor ** frame)) end.
  { sep_apply_l_atomic (proj1 (kernel_irq_fields_local_map_absent external platform port abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) local descriptor interrupted_local Habsent)).
    sep_apply_r_atomic (proj2 (kernel_irq_fields_local_selected local descriptor interrupted_local)); entailer!. }
  exact (kernel_irq_save_continuation_fields_resources external platform port abi sg entry node handler descriptor
    publication (kernel_irq_fields_local local descriptor interrupted_local) frame before saved_heap
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    (Hopen before Hpre) Hsave).
Qed.

Lemma kernel_irq_restore_fields_local_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state local suspended call node handler
  (interrupted_local frame : Assertion) before after,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_fields_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState)
       (kernel_irq_fields_local local suspended interrupted_local))
     state.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) before ->
  armv7a_restore_transition abi handler suspended before after ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  restored.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) = None /\
  (flag_source_save_input abi (fun sg state => UCOS2_fields_inv sg state)
     local sg
     (Some (task_stack_key suspended.(armv7a_continuation_stack)))
     (armv7a_continuation_resumed_call suspended call)
     (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) restored interrupted_local **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port abi sg state local suspended call node handler interrupted_local frame
    before after Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre Hrestore restored.
  destruct (kernel_irq_take_fields_local_resources external platform port abi sg state local suspended interrupted_local call node
    _ before Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre)
    as [Hpointers [Hreads [Hcovered Htaken]]].
  fold restored in Hcovered, Htaken.
  match type of Htaken with ?P before => assert (Hopen : P |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
      suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    (UCOS2_fields_inv sg restored ** store_parked_continuations
       (kernel_saved_continuation_entry abi restored.(TskState) local)
       restored.(TskState).(parkedTaskStacks) ** interrupted_local ** frame)) by entailer! end.
  destruct (armv7a_restore_transition_resources external platform port abi handler suspended _ before after
    Hreads (Hopen before Htaken) Hrestore) as [Hmemory Hafter].
  rewrite Hcall in Hafter.
  split; [exact Hmemory|]. split.
  - unfold restored, os_int_exit_wrapper_restored_state;
      cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_take_lookup.
  - match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { unfold flag_source_save_input, kernel_continuation_call_closed, kernel_continuation_inv; entailer!. }
    exact (Hclose after Hafter).
Qed.
