Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Open the actual selected entry without forgetting the pending call.
    Foreign entries may be first-entry frames or suspended calls. Only
    selection of the focus key identifies this particular invocation. *)
Lemma armv7a_task_call_stack_entry_open : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus key payload,
  armv7a_task_call_stack_entry abi tasks focus key payload |--
  EX saved,
    coq_prop (armv7a_continuation_binding saved /\
      task_stack_key saved.(armv7a_continuation_stack) = key /\
      (saved.(armv7a_continuation_stack).(stackLeaseRegion),
        saved.(armv7a_continuation_fragments)) = payload /\
      armv7a_task_frame_slice saved /\
      task_stack_live_sp tasks key saved.(armv7a_continuation_sp) /\
      (key = armv7a_call_focus_key focus -> armv7a_continuation_focus_binding focus saved)) &&
    armv7a_task_continuation_resource abi saved.
Proof.
  intros; unfold armv7a_task_call_stack_entry.
  destruct task_stack_key_eq_dec as [Heq|Hneq].
  - Intros saved.
    assert (Hcall : saved.(armv7a_continuation_call) = Some focus.(armv7a_focus_call))
      by (unfold armv7a_continuation_focus_binding in *; tauto).
    Exists saved; unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!.
  - unfold armv7a_task_stack_entry; Intros saved; Exists saved; entailer!; congruence.
Qed.

(** Actual post-hook OSCtxSw stores and selected-SP load. The resource
    parameter of the existing physical producer is instantiated with the
    call-aware entry; it is never reconstructed from a weaker map.
    Park/take also covers an outgoing/incoming alias. *)
Lemma os_sched_install_take_call_continuation :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg context outgoing hooked incoming resumed focus (frame : Assertion) heap,
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   frame) heap ->
  exists final selected,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected final /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    (task_stack_key incoming = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    task_current_at (os_sched_install_context context outgoing incoming hooked)
      incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage (os_sched_install_context context outgoing incoming hooked).(TskState)
      (Some (task_stack_key incoming)) /\
    (UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
     armv7a_task_call_stacks abi (os_sched_install_context context outgoing incoming hooked).(TskState)
       focus (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
       selected.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi selected ** frame) final.
Proof.
  intros external platform port abi sg context outgoing hooked incoming resumed focus frame heap
    Hsaved Hdestination Haddress Hcoverage Hbefore.
  destruct (os_sched_install_continuation_map_resources external sg context outgoing hooked incoming
    resumed (armv7a_task_call_stack_entry abi hooked.(TskState) focus) frame heap
    Hsaved Hdestination Haddress Hbefore)
    as [final [sp [Hrun [[Hcurrent Hrestore] Hafter]]]].
  set (installed := os_sched_install_context context outgoing incoming hooked).
  assert (Hextract : UCOS2_inv sg installed **
      task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
      armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key incoming)
        (incoming.(stackLeaseRegion), resumed) **
      store_parked_continuations (armv7a_task_call_stack_entry abi hooked.(TskState) focus)
        installed.(TskState).(parkedTaskStacks) ** frame |--
    EX selected,
      coq_prop (armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed /\
        armv7a_task_frame_slice selected /\
        task_stack_live_sp hooked.(TskState) (task_stack_key incoming) selected.(armv7a_continuation_sp) /\
        (task_stack_key incoming = armv7a_call_focus_key focus ->
          armv7a_continuation_focus_binding focus selected)) &&
      (UCOS2_inv sg installed **
       armv7a_task_call_stacks abi installed.(TskState) focus installed.(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) **
       armv7a_task_continuation_resource abi selected ** frame)).
  { sep_apply_l_atomic (armv7a_task_call_stack_entry_open external platform port abi hooked.(TskState)
      focus (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed)).
    Intros selected.
    assert (Hkey : task_stack_key selected.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (selected.(armv7a_continuation_stack).(stackLeaseRegion),
      selected.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hlease : selected.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct selected.(armv7a_continuation_stack), incoming;
        cbn in *; congruence. }
    assert (Hfragments : selected.(armv7a_continuation_fragments) = resumed) by congruence.
    Exists selected; unfold armv7a_task_call_stacks.
    rewrite Hlease, Hfragments; entailer!; tauto. }
  destruct (Hextract final Hafter) as [selected
    [[Hbinding [Hlease [Hfragments [Hslice [Hsp Hfocus]]]]] Hresources]].
  destruct Hdestination as [Hhigh [[node [Hnode [Hgeneration [Hprio Harch]]]] Hother]].
  assert (Hnode_sp : node.(tcbStkPtr) = selected.(armv7a_continuation_sp))
    by (apply Hsp; assumption).
  assert (Hload : pointer_load (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) final).
  { eapply task_stack_framed_live_sp_load with (state := installed).
    - exact Hnode.
    - exact Haddress.
    - assert (Horder : UCOS2_inv sg installed **
        armv7a_task_call_stacks abi installed.(TskState) focus installed.(TskState).(parkedTaskStacks) **
        task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
          selected.(armv7a_continuation_fragments) **
        armv7a_task_continuation_resource abi selected ** frame |--
        UCOS2_inv sg installed **
        (armv7a_task_call_stacks abi installed.(TskState) focus installed.(TskState).(parkedTaskStacks) **
         task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
           selected.(armv7a_continuation_fragments) **
         armv7a_task_continuation_resource abi selected ** frame)) by entailer!.
      exact (Horder final Hresources). }
  assert (Hloaded_sp : sp = selected.(armv7a_continuation_sp)).
  { rewrite <- Hnode_sp; eapply pointer_load_deterministic; [exact (proj2 Hrun)|exact Hload]. }
  assert (Hreads : armv7a_continuation_restore_reads selected final).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    assert (Horder : UCOS2_inv sg installed **
        armv7a_task_call_stacks abi installed.(TskState) focus installed.(TskState).(parkedTaskStacks) **
        task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
          selected.(armv7a_continuation_fragments) **
        armv7a_task_continuation_resource abi selected ** frame |--
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      (UCOS2_inv sg installed **
       armv7a_task_call_stacks abi installed.(TskState) focus installed.(TskState).(parkedTaskStacks) **
       armv7a_task_continuation_resource abi selected ** frame)) by entailer!.
    exact (Horder final Hresources). }
  assert (Hcovered : task_stack_live_coverage installed.(TskState) (Some (task_stack_key incoming))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing))
      incoming (task_stack_park_covers_active hooked.(TskState) context.(os_sched_call_stack) outgoing Hcoverage)). }
  exists final, selected; rewrite Hloaded_sp in Hrun.
  exact (conj Hrun (conj Hreads (conj Hlease (conj Hfragments
    (conj Hfocus (conj Hcurrent (conj Hcovered Hresources))))))).
Qed.

(** Presence plus the real outgoing absence proves it is a different
    key. Only the selected-key comparison is a branch condition. *)
Lemma os_sched_install_other_keeps_call_lookup : forall context outgoing hooked incoming focus payload,
  os_sched_saved_stack_binding context outgoing hooked ->
  hooked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  task_stack_key incoming <> armv7a_call_focus_key focus ->
  (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks)
    (armv7a_call_focus_key focus) = Some payload.
Proof.
  intros context outgoing hooked incoming focus payload Hsaved Hlookup Hother.
  assert (Hnone : hooked.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None)
    by (unfold os_sched_saved_stack_binding in Hsaved; tauto).
  assert (Houtgoing : armv7a_call_focus_key focus <> task_stack_key context.(os_sched_call_stack)) by congruence.
  change ((task_stack_take (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
    context.(os_sched_call_stack) outgoing) incoming) (armv7a_call_focus_key focus) = Some payload).
  rewrite task_stack_take_lookup_other by congruence.
  rewrite task_stack_park_fragments_lookup_other by exact Houtgoing; exact Hlookup.
Qed.

(** Restore the actually selected continuation through the approved TASK
    ABI, not the IRQ handler ABI. The whole call-aware map survives.
    Choosing a foreign task retains the pending lookup; choosing the
    focus recovers that invocation/PC/LR from the consumed entry.
    The hook and preceding physical save must supply this post-hook cut;
    they are not silently assumed stable across an arbitrary call. *)
Lemma armv7a_task_restore_call_map : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg context outgoing hooked incoming resumed node focus (frame : Assertion) heap,
  os_sched_saved_stack_binding context outgoing hooked ->
  hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) ->
  hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) ->
  task_stack_live_binding hooked.(TskState) incoming ->
  (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
    context.(os_sched_call_stack) outgoing) (task_stack_key incoming) =
      Some (incoming.(stackLeaseRegion), resumed) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** frame)) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = incoming /\
    (task_stack_key incoming = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    task_current_at (os_sched_install_context context outgoing incoming hooked)
      incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage (os_sched_install_context context outgoing incoming hooked).(TskState)
      (Some (task_stack_key incoming)) /\
    (forall payload,
      hooked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
      task_stack_key incoming <> armv7a_call_focus_key focus ->
      (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks)
        (armv7a_call_focus_key focus) = Some payload) /\
    (forall restored, armv7a_task_restore_transition task_abi context selected installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      armv7a_task_restored_source external selected /\
      (armv7a_task_restored_execution external platform port abi selected **
       UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
       armv7a_task_call_stacks abi (os_sched_install_context context outgoing incoming hooked).(TskState)
         focus (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) **
       frame) restored /\
      (task_stack_key incoming = armv7a_call_focus_key focus ->
       (kernel_call_execution_owned external platform
          (armv7a_continuation_resumed_call selected focus.(armv7a_focus_call))
          (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
        UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
        armv7a_task_call_stacks abi (os_sched_install_context context outgoing incoming hooked).(TskState)
          focus (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) **
        frame) restored)).
Proof.
  intros external platform port abi task_abi initial sg context outgoing hooked incoming resumed node
    focus frame heap Hsaved Hhigh Hnode Hgen Hprio Hlive Hparked Haddress Hcoverage Hbefore.
  assert (Hnone : hooked.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None)
    by (unfold os_sched_saved_stack_binding in Hsaved; tauto).
  assert (Hdestination : os_sched_destination_binding external context outgoing hooked incoming resumed).
  { match type of Hbefore with ?P heap =>
      assert (Hobserve : P |--
        coq_prop (os_sched_destination_binding external context outgoing hooked incoming resumed) && TT)
    end.
    { unfold armv7a_task_call_stacks.
      sep_apply_l_atomic (store_parked_continuations_switch (armv7a_task_call_stack_entry abi hooked.(TskState) focus)
        hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) incoming outgoing resumed Hnone Hparked).
      sep_apply_l_atomic (armv7a_task_call_stack_entry_forget external platform port abi hooked.(TskState)
        focus (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed)).
      sep_apply_l_atomic (os_sched_destination_from_stack_entry external platform port abi task_abi initial
        context outgoing hooked incoming resumed node Hhigh Hnode Hgen Hprio Hlive Hparked).
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hbefore)). }
  destruct (os_sched_install_take_call_continuation external platform port abi sg context outgoing hooked
    incoming resumed focus _ heap Hsaved Hdestination Haddress Hcoverage Hbefore)
    as [installed [selected [Hrun [Hreads [Hlease [Hfragments [Hfocus [Hcurrent [Hcovered Hinstalled]]]]]]]]].
  exists installed, selected; split; [exact Hrun|]. split; [exact Hlease|].
  split; [exact Hfocus|]. split; [exact Hcurrent|]. split; [exact Hcovered|]. split.
  - intros; eapply os_sched_install_other_keeps_call_lookup; eassumption.
  - intros restored Hrestore.
    match type of Hinstalled with ?P installed =>
      assert (Hinput : P |-- armv7a_task_switch_control task_abi context **
        task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
          selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
        (UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
         armv7a_task_call_stacks abi (os_sched_install_context context outgoing incoming hooked).(TskState)
           focus (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) **
         frame))
    end.
    { entailer!. }
    destruct (armv7a_task_restore_resources _ _ _ abi task_abi context selected _ installed restored
      Hreads (Hinput installed Hinstalled) Hrestore) as [Hmemory [Hsource Hrestored]].
    split; [exact Hmemory|]. split; [exact Hsource|].
    match type of Hrestored with ?P restored =>
      assert (Hclose : P |-- armv7a_task_restored_execution external platform port abi selected **
        UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
        armv7a_task_call_stacks abi (os_sched_install_context context outgoing incoming hooked).(TskState)
          focus (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) **
        frame)
    end.
    { entailer!. }
    pose proof (Hclose restored Hrestored) as Hpost.
    split; [exact Hpost|]. intros Hselected.
    pose proof (Hfocus Hselected) as Hbinding.
    assert (Hcall : selected.(armv7a_continuation_call) = Some focus.(armv7a_focus_call))
      by (unfold armv7a_continuation_focus_binding in Hbinding; tauto).
    unfold armv7a_task_restored_execution in Hpost; rewrite Hcall in Hpost; exact Hpost.
Qed.
