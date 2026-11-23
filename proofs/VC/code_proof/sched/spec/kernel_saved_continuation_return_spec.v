Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The local resources of one actual Scheduler save. The CPU authority
    and physical saved frame remain in their existing owners. Registration
    refers to the supplied source cut; intervening clients must transport
    it before this view is used at a later selector. No future execution
    or permanent liveness is inferred from these resources. *)
Definition kernel_sched_saved_local (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) sg tasks call saved acquired
  (descriptor : Armv7aContinuation) : Assertion :=
  coq_prop (descriptor.(armv7a_continuation_call) = Some call /\
    descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) /\
    armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 /\
    call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
      call.(os_sched_call_stack).(stackLeaseGeneration) /\
    task_invocation_active tasks call.(os_sched_call_invocation) call.(os_sched_call_origin)) &&
  (interrupt_platform_saved platform
     (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
   critical_region_inside critical sg call.(os_sched_call_invocation) acquired).

(** A local view for a source-identified saved Scheduler invocation. Other
    entries retain their own local predicate, including initial entry and
    IRQ-interrupted cuts. This is not a global classification by PC/mask:
    the selected key's Scheduler resources must be supplied by its actual
    save producer. All entries still use the same physical parked map. *)
Definition kernel_sched_saved_local_at platform critical sg tasks call saved acquired
  (other : Armv7aContinuation -> Assertion) (descriptor : Armv7aContinuation) : Assertion :=
  if task_stack_key_eq_dec (task_stack_key descriptor.(armv7a_continuation_stack))
      (task_stack_key call.(os_sched_call_stack))
  then kernel_sched_saved_local platform critical sg tasks call saved acquired descriptor
  else other descriptor.

(** Before the physical OSCtxSw stores, its known source image and the
    real preceding Save pair already establish this local view. The
    physical producer carries it through writes and capture as a frame;
    the lemma neither manufactures a dormant owner nor assumes a post. *)
Lemma kernel_sched_saved_image_local_resources : forall platform critical sg state call saved acquired
  old_sp cpsr values lr fragments,
  kernel_call_task_source call state -> armv7a_irq_fiq_mask cpsr = 192 ->
  interrupt_platform_saved platform
    (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
  critical_region_inside critical sg call.(os_sched_call_invocation) acquired |--
  kernel_sched_saved_local platform critical sg state.(TskState) call saved acquired
    (armv7a_task_save_image call old_sp cpsr values lr fragments).
Proof.
  intros platform critical sg state call saved acquired old_sp cpsr values lr fragments
    [Horigin [Hactive Hcurrent]] Hmask.
  unfold kernel_sched_saved_local; cbn [armv7a_task_save_image armv7a_continuation_call
    armv7a_continuation_pc armv7a_continuation_lr armv7a_continuation_cpsr].
  rewrite armv7a_task_saved_cpsr_mask; entailer!.
Qed.

(** The existing real Save/capture producer already supplies this precise
    pair and descriptor observations. This bridge only separates the
    dormant owner from its retained local resources on the same heap. *)
Lemma kernel_saved_sched_call_local_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg tasks call saved acquired descriptor,
  task_invocation_active tasks call.(os_sched_call_invocation) call.(os_sched_call_origin) ->
  kernel_saved_sched_call abi critical sg call saved acquired descriptor |--
  armv7a_task_continuation_resource abi descriptor **
    kernel_sched_saved_local platform critical sg tasks call saved acquired descriptor.
Proof.
  intros external platform port abi critical sg tasks call saved acquired descriptor Hactive.
  unfold kernel_saved_sched_call; Intros.
  assert (Hcall : descriptor.(armv7a_continuation_call) = Some call) by tauto.
  unfold armv7a_task_continuation_resource; rewrite Hcall.
  unfold kernel_sched_saved_local; entailer!; tauto.
Qed.

Lemma kernel_sched_saved_local_at_selected : forall platform critical sg tasks call saved acquired other descriptor,
  descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack) ->
  kernel_sched_saved_local_at platform critical sg tasks call saved acquired other descriptor =
    kernel_sched_saved_local platform critical sg tasks call saved acquired descriptor.
Proof.
  intros; unfold kernel_sched_saved_local_at; rewrite H.
  destruct task_stack_key_eq_dec; [reflexivity|contradiction].
Qed.

(** The actual selected entry has been taken. Changing the local policy
    only at that now-ABSENT key loses no owner and touches no other entry.
    In particular a later ordinary call is not tied to an earlier call's
    saved word or acquired state. This is not a weak-map reconstruction. *)
Lemma kernel_saved_continuation_map_unfocus_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  critical sg source_tasks tasks original saved acquired other stacks,
  stacks (task_stack_key original.(os_sched_call_stack)) = None ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (kernel_sched_saved_local_at platform critical sg source_tasks original saved acquired other)) stacks |--
  store_parked_continuations (kernel_saved_continuation_entry abi tasks other) stacks.
Proof.
  intros external platform port abi critical sg source_tasks tasks original saved acquired other stacks Hnone.
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
  assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = key) by tauto.
  assert (Hne : task_stack_key descriptor.(armv7a_continuation_stack) <>
    task_stack_key original.(os_sched_call_stack)).
  { intro Heq; rewrite Hkey in Heq; rewrite Heq, Hnone in Hlookup; discriminate. }
  Exists descriptor; unfold kernel_sched_saved_local_at.
  destruct task_stack_key_eq_dec; [contradiction|entailer!].
Qed.

(** Consume the actual generic install/TaskRestore result, then the real
    later C Restore. The selected call's registration comes from its local
    source cut and its current-task identity from OSTCBCur installation.
    The remaining generic map is an unchanged frame of the C Restore;
    no local owner is forgotten to obtain an older weak stack invariant.

    The destination is the CURRENT selector binding. Neither eventual
    selection nor an API postcondition is assumed or concluded. The local
    view is indexed by [hooked.TskState]; preserving it through earlier
    client execution remains the responsibility of that actual trace. *)
Lemma kernel_saved_sched_continuation_return_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical arch
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg context outgoing hooked original saved acquired other resumed before (frame : Assertion),
  let local := kernel_sched_saved_local_at platform critical sg hooked.(TskState)
    original saved acquired other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
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
         kernel_program_inv sg current **
         store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
           current.(TskState).(parkedTaskStacks) ** frame) after)).
Proof.
  intros external platform port abi critical arch task_abi restore sg context outgoing hooked original
    saved acquired other resumed before frame local resource current Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (kernel_saved_continuation_install_source external platform port abi task_abi sg context
    outgoing hooked original.(os_sched_call_stack) resumed local before frame
    Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hbinding [Hlease [Hfragments [Hcurrent [Hcovered Hrestore]]]]]]]]].
  fold current in Hcurrent, Hcovered, Hrestore.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hmemory [Hsource Howned]].
  assert (Hlocal : local selected = kernel_sched_saved_local platform critical sg hooked.(TskState)
    original saved acquired selected).
  { unfold local; apply kernel_sched_saved_local_at_selected; exact Hlease. }
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
    (kernel_program_inv sg current **
     store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
       current.(TskState).(parkedTaskStacks) ** frame)) end.
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
