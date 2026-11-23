Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** One entry of the existing parked map carries the local resources of
    the actual saved program point. Physical stack bytes remain exclusively
    in [store_parked_stacks]. [local] is supplied by the source producer;
    it is neither a platform promise nor a second state table. Scheduler
    Save/inside and an interrupted C cut may instantiate it differently.
    In particular no mask, PC=LR, or permanent active-registration premise
    is imposed on every historical descriptor. *)
Definition kernel_saved_continuation_entry {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  (tasks : Glob_TaskAbstractState) (local : Armv7aContinuation -> Assertion)
  (key : TaskID * nat) (payload : TaskStackRegion * TaskStackFragments) : Assertion :=
  EX descriptor,
    coq_prop (armv7a_continuation_binding descriptor /\
      task_stack_key descriptor.(armv7a_continuation_stack) = key /\
      (descriptor.(armv7a_continuation_stack).(stackLeaseRegion),
        descriptor.(armv7a_continuation_fragments)) = payload /\
      armv7a_task_frame_slice descriptor /\
      task_stack_live_sp tasks key descriptor.(armv7a_continuation_sp)) &&
    (armv7a_task_continuation_resource abi descriptor ** local descriptor).

(** Capture consumes the real running authority and retains the actual
    local cut through the existing platform frame rule. The physical save
    producer must already have established the frame reads and live SP. *)
Lemma kernel_saved_continuation_capture_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  tasks local call descriptor (frame : Assertion) before after,
  descriptor.(armv7a_continuation_call) = Some call ->
  armv7a_continuation_binding descriptor -> armv7a_task_frame_slice descriptor ->
  task_stack_live_sp tasks (task_stack_key descriptor.(armv7a_continuation_stack))
    descriptor.(armv7a_continuation_sp) ->
  armv7a_continuation_restore_reads descriptor before ->
  armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 ->
  (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
   external.(os_sched_arch_running) call ** local descriptor ** frame) before ->
  armv7a_task_capture_transition task_abi call descriptor before after ->
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp)
    descriptor.(armv7a_continuation_fragments) /\
  (kernel_saved_continuation_entry abi tasks local
     (task_stack_key descriptor.(armv7a_continuation_stack))
     (descriptor.(armv7a_continuation_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) **
   armv7a_task_switch_control task_abi call ** frame) after.
Proof.
  intros external platform port abi task_abi tasks local call descriptor frame before after
    Hcall Hbinding Hslice Hlive Hreads Hmask Hpre Hcapture.
  match type of Hpre with ?P before => assert (Horder : P |--
    interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
    external.(os_sched_arch_running) call ** (local descriptor ** frame)) by entailer! end.
  destruct (armv7a_task_capture_resources _ _ _ abi task_abi call descriptor _ before after
    Hcall Hreads Hmask (Horder before Hpre) Hcapture) as [Hmemory [Hsource Hafter]].
  split; [exact Hmemory|]. split; [exact Hsource|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold kernel_saved_continuation_entry; Exists descriptor.
    unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Physical park/take and install operate on the same map and heap. The
    selected descriptor's local cut is opened together with its dormant
    owner, then passed through TaskRestore as a disjoint retained frame.
    Installation changes neither live TCB fields nor invocation lifecycle.
    Equal outgoing/incoming keys are handled by the underlying map rule. *)
Lemma kernel_saved_continuation_install_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg call outgoing hooked incoming resumed local before (frame : Assertion),
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context call outgoing incoming hooked in
  os_sched_saved_stack_binding call outgoing hooked ->
  os_sched_destination_binding external call outgoing hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at current incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming)) /\
    (forall restored,
      armv7a_task_restore_transition task_abi call selected installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      armv7a_task_restored_source external selected /\
      (armv7a_task_restored_execution external platform port abi selected ** local selected **
       kernel_program_inv sg current **
       store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
         current.(TskState).(parkedTaskStacks) ** frame) restored).
Proof.
  intros external platform port abi task_abi sg call outgoing hooked incoming resumed local before frame
    resource current Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (os_sched_install_continuation_map_resources external sg call outgoing hooked incoming resumed resource
    _ before Hsaved Hdestination Haddress Hpre) as [installed [sp [Hrun [[Hcurrent Harch] Hinstalled]]]].
  fold current in Hcurrent, Hinstalled.
  match type of Hinstalled with ?P installed => assert (Hextract : P |--
    EX selected,
      coq_prop (armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed /\ armv7a_task_frame_slice selected /\
        task_stack_live_sp hooked.(TskState) (task_stack_key incoming) selected.(armv7a_continuation_sp)) &&
      (UCOS2_inv sg current **
       task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
       local selected ** store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) end.
  { unfold resource at 1; unfold kernel_saved_continuation_entry at 1; Intros selected.
    assert (Hkey : task_stack_key selected.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (selected.(armv7a_continuation_stack).(stackLeaseRegion),
      selected.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hlease : selected.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct selected.(armv7a_continuation_stack), incoming; cbn in *; congruence. }
    assert (Hfragments : selected.(armv7a_continuation_fragments) = resumed) by congruence.
    Exists selected; rewrite Hlease, Hfragments; entailer!; tauto. }
  destruct (Hextract installed Hinstalled) as
    [selected [[Hbinding [Hlease [Hfragments [Hslice Hlive]]]] Howned]].
  pose proof Hdestination as [Hhigh [[node [Hnode [Hgen [Hprio Hsource]]]] Hrest]].
  assert (Hnode_sp : node.(tcbStkPtr) = selected.(armv7a_continuation_sp)) by (apply Hlive; assumption).
  assert (Hload : pointer_load (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) installed).
  { eapply task_stack_framed_live_sp_load with (state := current); [exact Hnode|exact Haddress|].
    match type of Howned with ?P installed => assert (Horder : P |-- UCOS2_inv sg current **
      (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
       local selected ** store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hsp : sp = selected.(armv7a_continuation_sp)).
  { rewrite <- Hnode_sp; eapply pointer_load_deterministic; [exact (proj2 Hrun)|exact Hload]. }
  rewrite Hsp in Hrun.
  assert (Hreads : armv7a_continuation_restore_reads selected installed).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Howned with ?P installed => assert (Horder : P |--
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      (UCOS2_inv sg current ** armv7a_task_continuation_resource abi selected ** local selected **
       store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hcovered : task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) outgoing))
      incoming (task_stack_park_covers_active hooked.(TskState) call.(os_sched_call_stack) outgoing Hcoverage)). }
  exists installed, selected; split; [exact Hrun|]. split; [exact Hreads|]. split; [exact Hbinding|].
  split; [exact Hlease|]. split; [exact Hfragments|]. split; [exact Hcurrent|]. split; [exact Hcovered|].
  intros restored Hrestore.
  match type of Howned with ?P installed => assert (Hrestore_input : P |--
    armv7a_task_switch_control task_abi call **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
    (local selected ** kernel_program_inv sg current **
     store_parked_continuations resource current.(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (armv7a_task_restore_resources _ _ _ abi task_abi call selected _ installed restored
    Hreads (Hrestore_input installed Howned) Hrestore) as [Hmemory [Hresume_source Hrestored]].
  split; [exact Hmemory|]. split; [exact Hresume_source|].
  match type of Hrestored with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
  { change (kernel_saved_continuation_entry abi current.(TskState) local) with resource; entailer!. }
  exact (Hclose restored Hrestored).
Qed.

(** Current execution comes from the actual install. Registration comes
    separately from the saved call's source history, never from a dormant
    token or equal stack address. This rule applies equally to Scheduler
    and IRQ descriptors; it imposes no Scheduler-only PC/mask condition. *)
Lemma kernel_selected_saved_call_source : forall selected previous state,
  armv7a_continuation_binding selected ->
  selected.(armv7a_continuation_call) = Some previous ->
  previous.(os_sched_call_origin) = RunningInvocation previous.(os_sched_call_stack).(stackLeaseSlot)
    previous.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active state.(TskState) previous.(os_sched_call_invocation) previous.(os_sched_call_origin) ->
  task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  kernel_call_task_source (kernel_selected_call selected state) state.
Proof.
  intros selected previous state Hbinding Hcall Horigin Hactive Hcurrent.
  assert (Hlease : selected.(armv7a_continuation_stack) = previous.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hstack; rewrite Hcall in Hstack; symmetry; exact Hstack. }
  unfold kernel_selected_call; rewrite Hcall.
  unfold kernel_call_task_source, armv7a_continuation_resumed_call;
    cbn [os_sched_call_origin os_sched_call_stack os_sched_call_invocation]; rewrite Hlease.
  split; [exact Horigin|]. split; [exact Hactive|].
  unfold task_execution_current; rewrite Horigin.
  rewrite Hlease in Hcurrent; exact (proj1 Hcurrent).
Qed.
