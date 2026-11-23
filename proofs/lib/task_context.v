Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** TCB-resource part of a source context save, NOT an ARM executor.
    GNU ARMv7-A OSCtxSw saves registers, reads the actual OSTCBCur, and
    writes SP to [OSTCBCur] before OSTaskSwHook: none:234, D16:258, D32:261.
    The first-level exception wrapper has the same TCB store; OSIntCtxSw
    itself does not.  No context-switch or callback termination is proved.

    OSTaskDel can already have recycled its own TCB before OS_Sched reaches
    this store (Source/os_task.c:550--557).  Therefore both the used-task
    and the stale FREE storage images must admit the write.  A freed slot
    does not thereby become live again or acquire the old stack's lease. *)
Definition task_set_saved_sp (node : TaskAbstractState) (sp : addr) : TaskAbstractState :=
  {| taskID := node.(taskID); taskGeneration := node.(taskGeneration);
     tcbStkPtr := sp;
     tcbExtPtr := node.(tcbExtPtr); tcbStkBottom := node.(tcbStkBottom);
     tcbStkSize := node.(tcbStkSize); tcbOpt := node.(tcbOpt);
     tcbPublicId := node.(tcbPublicId); tcbFlagNode := node.(tcbFlagNode);
     tcbFlagsRdy := node.(tcbFlagsRdy); tcbTaskName := node.(tcbTaskName);
     tcbReg0 := node.(tcbReg0);
     tcbCtxSwCtr := node.(tcbCtxSwCtr);
     tcbCyclesTot := node.(tcbCyclesTot);
     tcbCyclesStart := node.(tcbCyclesStart);
     tcbStkBase := node.(tcbStkBase);
     tcbStkUsed := node.(tcbStkUsed); tcbPadding42 := node.(tcbPadding42);
     tcbPadding43 := node.(tcbPadding43); tcbEventMultiPtr := node.(tcbEventMultiPtr);
     curPrio := node.(curPrio); stat := node.(stat); statPend := node.(statPend); dly := node.(dly);
     eventPtr := node.(eventPtr); eventMultiWaitEvents := node.(eventMultiWaitEvents);
     eventMultiRdy := node.(eventMultiRdy); msg := node.(msg);
     nextTCB := node.(nextTCB); prevTCB := node.(prevTCB); delReq := node.(delReq) |}.

Definition tcb_saved_sp_image (image : TCBLayoutImage) (sp : addr)
  : TCBLayoutImage :=
  tcb_layout_write image (TCBCommonField TCBStkPtr) (Some sp).

Lemma task_set_saved_sp_put_back : forall node,
  task_set_saved_sp node node.(tcbStkPtr) = node.
Proof. intros []; reflexivity. Qed.

Lemma task_set_saved_sp_last_write : forall node first last,
  task_set_saved_sp (task_set_saved_sp node first) last = task_set_saved_sp node last.
Proof. reflexivity. Qed.

Lemma task_set_saved_sp_value : forall node sp,
  (task_set_saved_sp node sp).(tcbStkPtr) = sp.
Proof. reflexivity. Qed.

Lemma task_set_saved_sp_layout_image_eq : forall sg node sp,
  task_layout_image sg (task_set_saved_sp node sp) =
    tcb_saved_sp_image (task_layout_image sg node) sp.
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |];
    try destruct field; reflexivity.
Qed.

Lemma tcb_saved_sp_image_value : forall image sp,
  tcb_saved_sp_image image sp (TCBCommonField TCBStkPtr) = Some sp.
Proof. intros; apply field_update_same. Qed.

Lemma tcb_saved_sp_image_frame : forall image sp field,
  field <> TCBCommonField TCBStkPtr -> tcb_saved_sp_image image sp field = image field.
Proof. intros; apply field_update_other; assumption. Qed.

Lemma tcb_saved_sp_image_next_flags : forall image sp,
  tcb_saved_sp_image image sp (TCBCommonField TCBNext) = image (TCBCommonField TCBNext) /\
  tcb_saved_sp_image image sp (TCBCommonField TCBFlagsRdy) = image (TCBCommonField TCBFlagsRdy).
Proof. intros; split; reflexivity. Qed.

Lemma task_set_saved_sp_preserves_in_range : forall sg tasks tid node sp,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some node ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_set_saved_sp node sp)).
Proof.
  intros; eapply task_update_preserves_in_range;
    [exact H|exact H0|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity].
Qed.

Lemma task_set_saved_sp_preserves_invocation_active : forall tasks tid node sp invocation origin,
  tasks.(inUsedTaskStates) tid = Some node -> task_invocation_active tasks invocation origin ->
  task_invocation_active
    (glob_task_set_usedtask tasks tid (task_set_saved_sp node sp)) invocation origin.
Proof.
  intros; eapply glob_task_set_usedtask_preserves_invocation_active;
    [exact H|reflexivity|exact H0].
Qed.

Lemma task_set_saved_sp_lifecycle_frame : forall tasks tid node sp,
  (glob_task_set_usedtask tasks tid (task_set_saved_sp node sp)).(taskLifecycle) = tasks.(taskLifecycle).
Proof. reflexivity. Qed.

Lemma task_set_saved_sp_structure_frame : forall node sp,
  (task_set_saved_sp node sp).(taskID) = node.(taskID) /\
  (task_set_saved_sp node sp).(taskGeneration) = node.(taskGeneration) /\
  (task_set_saved_sp node sp).(curPrio) = node.(curPrio) /\
  (task_set_saved_sp node sp).(stat) = node.(stat) /\
  (task_set_saved_sp node sp).(dly) = node.(dly) /\
  (task_set_saved_sp node sp).(nextTCB) = node.(nextTCB) /\
  (task_set_saved_sp node sp).(prevTCB) = node.(prevTCB).
Proof. intros; repeat split; reflexivity. Qed.

Lemma task_public_storage_split_saved_sp : forall sg tasks tid node,
  tasks.(inUsedTaskStates) tid = Some node ->
  task_public_storage sg tasks |--
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) (TCBCommonField TCBStkPtr) (Some node.(tcbStkPtr)) **
  task_public_storage_without_field sg tasks tid node (TCBCommonField TCBStkPtr).
Proof.
  intros sg tasks tid node Hnode.
  exact (task_public_storage_split_field sg tasks tid node
    (TCBCommonField TCBStkPtr) Hnode (tcb_configured_common_field_in _ _ _)).
Qed.

Lemma task_public_storage_merge_saved_sp : forall sg tasks tid node sp,
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) (TCBCommonField TCBStkPtr) (Some sp) **
  task_public_storage_without_field sg tasks tid node (TCBCommonField TCBStkPtr) |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (task_set_saved_sp node sp)).
Proof.
  intros; apply task_public_storage_merge_updated_field;
    [apply tcb_configured_common_field_in|apply task_set_saved_sp_layout_image_eq].
Qed.

(** Numeric offset zero does not identify QCP's opaque named field_address.
    The second theorem explicitly consumes that selected-ABI bridge and an
    actually written pointer cell.  It does not postulate the bridge as an
    axiom or perform the machine instruction from old cell ownership. *)
Lemma tcb_saved_sp_offset_zero : forall multi,
  tcb_layout_field_offset multi (TCBCommonField TCBStkPtr) = 0.
Proof. intros []; reflexivity. Qed.

Lemma tcb_saved_sp_storage_merge : forall multi profile base image sp,
  tcb_layout_cell multi base (TCBCommonField TCBStkPtr) (Some sp) **
  tcb_configured_storage_without_field multi profile base image (TCBCommonField TCBStkPtr) |--
  tcb_configured_storage_rep multi profile base (tcb_saved_sp_image image sp).
Proof.
  intros; apply tcb_configured_storage_merge_updated_field; apply tcb_configured_common_field_in.
Qed.

Lemma tcb_saved_sp_raw_storage_merge : forall multi profile base image sp,
  tcb_field_address base TCBStkPtr = base ->
  base # Ptr |-> sp **
  tcb_configured_storage_without_field multi profile base image (TCBCommonField TCBStkPtr) |--
  tcb_configured_storage_rep multi profile base (tcb_saved_sp_image image sp).
Proof.
  intros multi profile base image sp Haddress; rewrite <- Haddress at 1.
  apply tcb_saved_sp_storage_merge.
Qed.

Lemma task_context_current_saved_sp_storage_merge : forall sg tid image sp,
  tcb_field_address (task_slot_addr sg tid) TCBStkPtr = task_slot_addr sg tid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  task_slot_addr sg tid # Ptr |-> sp **
  tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image (TCBCommonField TCBStkPtr) |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  task_slot_storage_rep sg tid (tcb_saved_sp_image image sp).
Proof.
  intros; sep_apply_l_atomic (tcb_saved_sp_raw_storage_merge
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg tid) image sp H).
  entailer!.
Qed.

(** A saved-SP write does not change parked buffers or publication history.
    The executing instance is absent from the parked map.  An entry at the
    same slot with another generation can remain retired; the consistency
    relation only checks its SP against a matching live generation. *)
Lemma task_set_saved_sp_preserves_parked_stacks_consistency :
  forall tasks node sp outgoing stacks,
  parked_stacks_consistent tasks stacks ->
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskID) = outgoing.(stackLeaseSlot) ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  stacks (task_stack_key outgoing) = None ->
  parked_stacks_consistent
    (glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp)) stacks.
Proof.
  intros tasks node sp outgoing stacks Hconsistent Hnode Hslot Hgeneration Hnone.
  intros slot generation region fragments Hentry.
  destruct (Hconsistent slot generation region fragments Hentry)
    as [Hregion [Hgeometry [Hhistory Hbinding]]].
  split; [exact Hregion|]. split; [exact Hgeometry|]. split; [exact Hhistory|].
  intros updated Hupdated Hgeneration_updated.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hupdated.
  destruct (Z.eqb slot outgoing.(stackLeaseSlot)) eqn:Hsame.
  - apply Z.eqb_eq in Hsame; subst slot.
    injection Hupdated as Hupdated; subst updated.
    change (node.(taskGeneration) = generation) in Hgeneration_updated.
    assert (Hkey : (outgoing.(stackLeaseSlot), generation) = task_stack_key outgoing).
    { unfold task_stack_key; f_equal; congruence. }
    rewrite Hkey, Hnone in Hentry; discriminate.
  - exact (Hbinding updated Hupdated Hgeneration_updated).
Qed.

(** Pure consistency at the park/take endpoint.  Taking an entry cannot
    invalidate this registered subset, even if that key is absent.  Actual
    incoming bytes and restore eligibility therefore still require the
    entry and live-binding premises of the spatial switch rule below. *)
Lemma task_context_live_saved_sp_switch_consistent :
  forall tasks node sp outgoing incoming stacks saved invocation,
  parked_stacks_consistent tasks stacks ->
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskID) = outgoing.(stackLeaseSlot) ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  stacks (task_stack_key outgoing) = None ->
  valid_task_stack_region outgoing.(stackLeaseRegion) ->
  task_publication_happened tasks invocation
    outgoing.(stackLeaseSlot) outgoing.(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp ->
  parked_stacks_consistent
    (glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp))
    (task_stack_take (task_stack_park stacks outgoing saved) incoming).
Proof.
  intros tasks node sp outgoing incoming stacks saved invocation
    Hconsistent Hnode Hslot Hgeneration Hnone Hregion Hhistory Hsp.
  apply task_stack_take_preserves_consistency.
  apply task_stack_park_preserves_consistency with (invocation := invocation).
  - exact (task_set_saved_sp_preserves_parked_stacks_consistency
      tasks node sp outgoing stacks Hconsistent Hnode Hslot Hgeneration Hnone).
  - exact Hregion.
  - exists (task_set_saved_sp node sp); split.
    + cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    + change (node.(taskID) = outgoing.(stackLeaseSlot) /\
        node.(taskGeneration) = outgoing.(stackLeaseGeneration) /\
        task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp).
      exact (conj Hslot (conj Hgeneration Hsp)).
  - exact Hhistory.
Qed.

(** Fragment resource handoff for a LIVE outgoing task and a
    different, already parked incoming task.  The antecedent contains the
    actual SP value written through the observed OSTCBCur, its named-field
    address bridge, and the outgoing fragments AFTER saving has finished
    and any hook has returned those bytes.  No instruction or hook is executed
    by this entailment.  It only combines the existing TCB update and stack
    transfers; the OSTCBCur cell is deliberately unchanged here.

    Actual destination selection, cache stores, register restore, entry
    permissions and continuation/interrupt protocols remain separate.
    Missing intervals remain with their actual external owner, such as
    Flag.  SP lying within the whole region does not prove that its saved
    frame lies within the retained fragments; this is not a restore rule.
    Self-delete/free-slot saving and same-task switching retain their
    separate interfaces; neither is ruled out by a new C guard. *)
Lemma task_context_live_saved_sp_switch_fragments_map_resources :
  forall sg tasks node sp outgoing incoming stacks saved resumed,
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskID) = outgoing.(stackLeaseSlot) ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp ->
  task_stack_live_binding tasks incoming ->
  stacks (task_stack_key outgoing) = None ->
  stacks (task_stack_key incoming) = Some (incoming.(stackLeaseRegion), resumed) ->
  tcb_field_address (task_slot_addr sg outgoing.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg outgoing.(stackLeaseSlot) ->
  let after := glob_task_set_usedtask tasks outgoing.(stackLeaseSlot)
    (task_set_saved_sp node sp) in
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
  task_slot_addr sg outgoing.(stackLeaseSlot) # Ptr |-> sp **
  task_public_storage_without_field sg tasks outgoing.(stackLeaseSlot) node
    (TCBCommonField TCBStkPtr) **
  task_stack_fragments_rep outgoing.(stackLeaseRegion) saved ** store_parked_stacks stacks |--
  coq_prop (task_stack_live_binding after outgoing /\ task_stack_live_binding after incoming) &&
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
   task_public_storage sg after ** task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
   store_parked_stacks (task_stack_take (task_stack_park_fragments stacks outgoing saved) incoming)).
Proof.
  intros sg tasks node sp outgoing incoming stacks saved resumed
    Hnode Hslot Hgeneration Hsp Hincoming Houtside Hparked Haddress after.
  assert (Hkeys : task_stack_key incoming <> task_stack_key outgoing).
  { intro Heq; rewrite Heq, Houtside in Hparked; discriminate. }
  destruct Hincoming as [destination [Hdestination [Hid [Hgeneration_in Hincoming_sp]]]].
  assert (Hslots : incoming.(stackLeaseSlot) <> outgoing.(stackLeaseSlot)).
  { intro Heq; rewrite Heq in Hdestination.
    assert (Hsame : destination = node) by congruence; subst destination.
    apply Hkeys; unfold task_stack_key; f_equal; [exact Heq|congruence]. }
  assert (Houtgoing_after : task_stack_live_binding after outgoing).
  { exists (task_set_saved_sp node sp); split.
    - unfold after; cbn [glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    - change (node.(taskID) = outgoing.(stackLeaseSlot) /\
        node.(taskGeneration) = outgoing.(stackLeaseGeneration) /\
        task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp).
      exact (conj Hslot (conj Hgeneration Hsp)). }
  assert (Hincoming_after : task_stack_live_binding after incoming).
  { exists destination; split.
    - unfold after; cbn [glob_task_set_usedtask inUsedTaskStates].
      rewrite (proj2 (Z.eqb_neq _ _) Hslots); exact Hdestination.
    - exact (conj Hid (conj Hgeneration_in Hincoming_sp)). }
  assert (Hcell : tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg outgoing.(stackLeaseSlot)) (TCBCommonField TCBStkPtr) (Some sp) =
    task_slot_addr sg outgoing.(stackLeaseSlot) # Ptr |-> sp).
  { change ((tcb_field_address (task_slot_addr sg outgoing.(stackLeaseSlot)) TCBStkPtr
      # Ptr |-> sp) = (task_slot_addr sg outgoing.(stackLeaseSlot) # Ptr |-> sp)).
    rewrite Haddress; reflexivity. }
  rewrite <- Hcell.
  eapply derivable1_trans with (y :=
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
       (task_slot_addr sg outgoing.(stackLeaseSlot)) (TCBCommonField TCBStkPtr) (Some sp) **
     task_public_storage_without_field sg tasks outgoing.(stackLeaseSlot) node
       (TCBCommonField TCBStkPtr)) **
    (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
     (task_stack_fragments_rep outgoing.(stackLeaseRegion) saved ** store_parked_stacks stacks))).
  - entailer!.
  - eapply derivable1_trans with (y :=
      task_public_storage sg after **
      (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
       (task_stack_fragments_rep outgoing.(stackLeaseRegion) saved ** store_parked_stacks stacks))).
    + apply derivable1_sepcon_mono.
      * apply task_public_storage_merge_saved_sp.
      * apply derivable1_refl.
    + eapply derivable1_trans with (y :=
        task_public_storage sg after **
        (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
         (task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
          store_parked_stacks (task_stack_take (task_stack_park_fragments stacks outgoing saved) incoming)))).
      * apply derivable1_sepcon_mono; [apply derivable1_refl|].
        apply derivable1_sepcon_mono; [apply derivable1_refl|].
        apply store_parked_stacks_switch_fragments; [exact Houtside|].
        unfold task_stack_park_fragments.
        rewrite field_update_other by exact Hkeys; exact Hparked.
      * entailer!.
Qed.

(** The original whole-buffer subinterface is a specialization only at an
    explicit complete-fragment embedding.  It reuses the same TCB-cell
    proof, and cannot turn an arbitrary fragmented entry into a buffer. *)
Lemma task_context_live_saved_sp_switch_map_resources :
  forall sg tasks node sp outgoing incoming stacks saved resumed,
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskID) = outgoing.(stackLeaseSlot) ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp ->
  task_stack_live_binding tasks incoming ->
  stacks (task_stack_key outgoing) = None ->
  stacks (task_stack_key incoming) = Some (incoming.(stackLeaseRegion),
    task_stack_complete_fragments incoming.(stackLeaseRegion) resumed) ->
  tcb_field_address (task_slot_addr sg outgoing.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg outgoing.(stackLeaseSlot) ->
  let after := glob_task_set_usedtask tasks outgoing.(stackLeaseSlot)
    (task_set_saved_sp node sp) in
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
  task_slot_addr sg outgoing.(stackLeaseSlot) # Ptr |-> sp **
  task_public_storage_without_field sg tasks outgoing.(stackLeaseSlot) node
    (TCBCommonField TCBStkPtr) **
  task_stack_storage outgoing.(stackLeaseRegion) saved ** store_parked_stacks stacks |--
  coq_prop (task_stack_live_binding after outgoing /\ task_stack_live_binding after incoming) &&
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
   task_public_storage sg after ** task_stack_storage incoming.(stackLeaseRegion) resumed **
   store_parked_stacks (task_stack_take (task_stack_park stacks outgoing saved) incoming)).
Proof.
  intros sg tasks node sp outgoing incoming stacks saved resumed
    Hnode Hslot Hgeneration Hsp Hincoming Houtside Hparked Haddress after.
  pose proof (task_context_live_saved_sp_switch_fragments_map_resources
    sg tasks node sp outgoing incoming stacks
    (task_stack_complete_fragments outgoing.(stackLeaseRegion) saved)
    (task_stack_complete_fragments incoming.(stackLeaseRegion) resumed)
    Hnode Hslot Hgeneration Hsp Hincoming Houtside Hparked Haddress) as Htransfer.
  cbv zeta in Htransfer.
  sep_apply_l_atomic (proj2
    (task_stack_fragments_rep_complete outgoing.(stackLeaseRegion) saved)).
  sep_apply_l_atomic Htransfer.
  Intros.
  sep_apply_l_atomic (proj1
    (task_stack_fragments_rep_complete incoming.(stackLeaseRegion) resumed)).
  entailer!.
Qed.

(** The context endpoint records the transferred map in the existing Task
    component.  The used-TCB update still precedes this resource handoff;
    neither setter executes a save, hook, cache write or register restore. *)
Definition task_context_live_saved_sp_switch_fragments_state
  (tasks : Glob_TaskAbstractState) (node : TaskAbstractState) (sp : addr)
  (outgoing incoming : TaskStackLease) (saved : TaskStackFragments)
  : Glob_TaskAbstractState :=
  glob_task_set_parked_stacks
    (glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp))
    (task_stack_take (task_stack_park_fragments tasks.(parkedTaskStacks) outgoing saved) incoming).

Definition task_context_live_saved_sp_switch_state
  (tasks : Glob_TaskAbstractState) (node : TaskAbstractState) (sp : addr)
  (outgoing incoming : TaskStackLease) (saved : list (option Z))
  : Glob_TaskAbstractState :=
  task_context_live_saved_sp_switch_fragments_state tasks node sp outgoing incoming
    (task_stack_complete_fragments outgoing.(stackLeaseRegion) saved).

Lemma task_context_live_saved_sp_switch_fragments_state_consistent :
  forall tasks node sp outgoing incoming saved invocation,
  parked_stacks_consistent tasks tasks.(parkedTaskStacks) ->
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskID) = outgoing.(stackLeaseSlot) ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  tasks.(parkedTaskStacks) (task_stack_key outgoing) = None ->
  valid_task_stack_region outgoing.(stackLeaseRegion) ->
  task_stack_fragments_in_range outgoing.(stackLeaseRegion).(stackRegionWords) 0 saved ->
  task_publication_happened tasks invocation
    outgoing.(stackLeaseSlot) outgoing.(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp ->
  let after := task_context_live_saved_sp_switch_fragments_state tasks node sp outgoing incoming saved in
  parked_stacks_consistent after after.(parkedTaskStacks).
Proof.
  intros tasks node sp outgoing incoming saved invocation
    Hconsistent Hnode Hslot Hgeneration Hnone Hregion Hgeometry Hhistory Hsp after.
  eapply parked_stacks_consistent_task_map_frame with
    (before := glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp)).
  - reflexivity.
  - intros observer observed_slot generation Hobserved; exact Hobserved.
  - apply task_stack_take_preserves_consistency.
    apply task_stack_park_fragments_preserves_consistency with (invocation := invocation).
    + exact (task_set_saved_sp_preserves_parked_stacks_consistency tasks node sp outgoing
        tasks.(parkedTaskStacks) Hconsistent Hnode Hslot Hgeneration Hnone).
    + exact Hregion.
    + exact Hgeometry.
    + exists (task_set_saved_sp node sp); split.
      * cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
      * exact (conj Hslot (conj Hgeneration Hsp)).
    + exact Hhistory.
Qed.

(** Only the retained fragments are transferred.  Any lent interval stays
    absent from the parked entry until its actual owner returns it.  Even
    with the pure consistency theorem above, this endpoint does not prove
    that the saved register frame is present, nor that restore can run. *)
Lemma task_context_live_saved_sp_switch_fragments_resources :
  forall sg tasks node sp outgoing incoming saved resumed,
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskID) = outgoing.(stackLeaseSlot) ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp ->
  task_stack_live_binding tasks incoming ->
  tasks.(parkedTaskStacks) (task_stack_key outgoing) = None ->
  tasks.(parkedTaskStacks) (task_stack_key incoming) = Some (incoming.(stackLeaseRegion), resumed) ->
  tcb_field_address (task_slot_addr sg outgoing.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg outgoing.(stackLeaseSlot) ->
  let after := task_context_live_saved_sp_switch_fragments_state tasks node sp outgoing incoming saved in
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
  task_slot_addr sg outgoing.(stackLeaseSlot) # Ptr |-> sp **
  task_public_storage_without_field sg tasks outgoing.(stackLeaseSlot) node
    (TCBCommonField TCBStkPtr) **
  task_stack_fragments_rep outgoing.(stackLeaseRegion) saved **
  store_parked_stacks tasks.(parkedTaskStacks) |--
  coq_prop (task_stack_live_binding after outgoing /\ task_stack_live_binding after incoming) &&
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
   task_public_storage sg after ** task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
   store_parked_stacks after.(parkedTaskStacks)).
Proof.
  intros sg tasks node sp outgoing incoming saved resumed
    Hnode Hslot Hgeneration Hsp Hincoming Houtside Hparked Haddress after.
  exact (task_context_live_saved_sp_switch_fragments_map_resources sg tasks node sp outgoing incoming
    tasks.(parkedTaskStacks) saved resumed Hnode Hslot Hgeneration Hsp Hincoming
    Houtside Hparked Haddress).
Qed.

Lemma task_context_live_saved_sp_switch_state_parked_stacks :
  forall tasks node sp outgoing incoming saved,
  (task_context_live_saved_sp_switch_state tasks node sp outgoing incoming saved).(parkedTaskStacks) =
    task_stack_take (task_stack_park tasks.(parkedTaskStacks) outgoing saved) incoming.
Proof. reflexivity. Qed.

Lemma task_context_live_saved_sp_switch_state_saved_task :
  forall tasks node sp outgoing incoming saved,
  (task_context_live_saved_sp_switch_state tasks node sp outgoing incoming saved).(inUsedTaskStates)
    outgoing.(stackLeaseSlot) = Some (task_set_saved_sp node sp).
Proof.
  intros; unfold task_context_live_saved_sp_switch_state,
    task_context_live_saved_sp_switch_fragments_state;
    cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates].
  rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma task_context_live_saved_sp_switch_state_lifecycle_frame :
  forall tasks node sp outgoing incoming saved,
  (task_context_live_saved_sp_switch_state tasks node sp outgoing incoming saved).(taskLifecycle) =
    tasks.(taskLifecycle).
Proof. reflexivity. Qed.

Lemma task_context_live_saved_sp_switch_state_consistent :
  forall tasks node sp outgoing incoming saved invocation,
  parked_stacks_consistent tasks tasks.(parkedTaskStacks) ->
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskID) = outgoing.(stackLeaseSlot) ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  tasks.(parkedTaskStacks) (task_stack_key outgoing) = None ->
  valid_task_stack_region outgoing.(stackLeaseRegion) ->
  task_publication_happened tasks invocation
    outgoing.(stackLeaseSlot) outgoing.(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp ->
  let after := task_context_live_saved_sp_switch_state tasks node sp outgoing incoming saved in
  parked_stacks_consistent after after.(parkedTaskStacks).
Proof.
  intros tasks node sp outgoing incoming saved invocation
    Hconsistent Hnode Hslot Hgeneration Hnone Hregion Hhistory Hsp after.
  eapply parked_stacks_consistent_task_map_frame with
    (before := glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp)).
  - reflexivity.
  - intros observer observed_slot generation Hobserved; exact Hobserved.
  - exact (task_context_live_saved_sp_switch_consistent tasks node sp outgoing incoming
      tasks.(parkedTaskStacks) saved invocation Hconsistent Hnode Hslot Hgeneration Hnone
      Hregion Hhistory Hsp).
Qed.

(** State-bound complete-buffer specialization.  The incoming lookup must
    explicitly contain the complete-fragment embedding: an arbitrary
    fragmented entry cannot yield a whole buffer.  The actual Task map,
    not an unrelated map parameter, supplies and receives these resources. *)
Lemma task_context_live_saved_sp_switch_resources :
  forall sg tasks node sp outgoing incoming saved resumed,
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskID) = outgoing.(stackLeaseSlot) ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range outgoing.(stackLeaseRegion) sp ->
  task_stack_live_binding tasks incoming ->
  tasks.(parkedTaskStacks) (task_stack_key outgoing) = None ->
  tasks.(parkedTaskStacks) (task_stack_key incoming) = Some (incoming.(stackLeaseRegion),
    task_stack_complete_fragments incoming.(stackLeaseRegion) resumed) ->
  tcb_field_address (task_slot_addr sg outgoing.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg outgoing.(stackLeaseSlot) ->
  let after := task_context_live_saved_sp_switch_state tasks node sp outgoing incoming saved in
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
  task_slot_addr sg outgoing.(stackLeaseSlot) # Ptr |-> sp **
  task_public_storage_without_field sg tasks outgoing.(stackLeaseSlot) node
    (TCBCommonField TCBStkPtr) **
  task_stack_storage outgoing.(stackLeaseRegion) saved **
  store_parked_stacks tasks.(parkedTaskStacks) |--
  coq_prop (task_stack_live_binding after outgoing /\ task_stack_live_binding after incoming) &&
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg outgoing.(stackLeaseSlot) **
   task_public_storage sg after ** task_stack_storage incoming.(stackLeaseRegion) resumed **
   store_parked_stacks after.(parkedTaskStacks)).
Proof.
  intros sg tasks node sp outgoing incoming saved resumed
    Hnode Hslot Hgeneration Hsp Hincoming Houtside Hparked Haddress after.
  exact (task_context_live_saved_sp_switch_map_resources sg tasks node sp outgoing incoming
    tasks.(parkedTaskStacks) saved resumed Hnode Hslot Hgeneration Hsp Hincoming
    Houtside Hparked Haddress).
Qed.

(** Update the EXISTING free image if present.  The None case is only a
    totalization of this pure transformer, not a new C branch and not a
    license to write an absent allocation.  The raw spatial rule above is
    independent of used/free classification.  Its caller must tie the
    observed OSTCBCur address to the actual current allocation state. *)
Definition task_free_saved_sp_storage
  (storage : TaskID -> option TCBLayoutImage) (tid : TaskID) (sp : addr)
  : TaskID -> option TCBLayoutImage :=
  field_update Z.eq_dec storage tid (option_map (fun image => tcb_saved_sp_image image sp) (storage tid)).

Definition task_save_free_sp (tasks : Glob_TaskAbstractState) (tid : TaskID) (sp : addr)
  : Glob_TaskAbstractState :=
  let life := tasks.(taskLifecycle) in glob_task_set_lifecycle tasks
    {| taskFreeStorage := task_free_saved_sp_storage life.(taskFreeStorage) tid sp;
       taskReservations := life.(taskReservations); taskActiveOrder := life.(taskActiveOrder);
       taskNextGeneration := life.(taskNextGeneration); taskInvocations := life.(taskInvocations);
       taskRetiredInvocations := life.(taskRetiredInvocations);
       taskNextInvocation := life.(taskNextInvocation); taskPublications := life.(taskPublications) |}.

Lemma task_save_free_sp_parked_stacks_frame : forall tasks tid sp,
  (task_save_free_sp tasks tid sp).(parkedTaskStacks) = tasks.(parkedTaskStacks).
Proof. reflexivity. Qed.

Lemma task_free_saved_sp_storage_target : forall storage tid sp image,
  storage tid = Some image ->
  task_free_saved_sp_storage storage tid sp tid = Some (tcb_saved_sp_image image sp).
Proof. intros; unfold task_free_saved_sp_storage; rewrite field_update_same, H; reflexivity. Qed.

Lemma task_free_saved_sp_storage_other : forall storage tid sp other,
  other <> tid -> task_free_saved_sp_storage storage tid sp other = storage other.
Proof. intros; apply field_update_other; assumption. Qed.

Lemma task_free_saved_sp_storage_domain : forall storage tid sp slot,
  (exists image, task_free_saved_sp_storage storage tid sp slot = Some image) <->
  (exists image, storage slot = Some image).
Proof.
  intros storage tid sp slot; destruct (Z.eq_dec slot tid) as [->|Hother].
  - unfold task_free_saved_sp_storage; rewrite field_update_same.
    destruct (storage tid) as [image|]; simpl.
    + split; intros; eexists; reflexivity.
    + split; intros [image Himage]; discriminate.
  - rewrite task_free_saved_sp_storage_other by exact Hother; reflexivity.
Qed.

Lemma task_free_saved_sp_storage_image_cases : forall storage tid sp slot after,
  task_free_saved_sp_storage storage tid sp slot = Some after ->
  exists before, storage slot = Some before /\
    (after = before \/ after = tcb_saved_sp_image before sp).
Proof.
  intros storage tid sp slot after Hafter; destruct (Z.eq_dec slot tid) as [->|Hother].
  - unfold task_free_saved_sp_storage in Hafter; rewrite field_update_same in Hafter.
    destruct (storage tid) as [before|] eqn:Hbefore; simpl in Hafter; [|discriminate].
    injection Hafter as Hafter; subst after; exists before; split; [reflexivity|right; reflexivity].
  - rewrite task_free_saved_sp_storage_other in Hafter by exact Hother.
    exists after; split; [exact Hafter|left; reflexivity].
Qed.

Lemma task_free_saved_sp_storage_preserves_links : forall sg ids storage tid sp,
  task_free_links sg storage ids ->
  task_free_links sg (task_free_saved_sp_storage storage tid sp) ids.
Proof.
  intros sg ids; induction ids as [|head rest IH]; intros storage tid sp Hlinks; [exact I|].
  destruct Hlinks as [image [Himage [Hnext Hrest]]].
  destruct (Z.eq_dec head tid) as [->|Hother].
  - exists (tcb_saved_sp_image image sp); split.
    + apply task_free_saved_sp_storage_target; exact Himage.
    + split; [exact Hnext|apply IH; exact Hrest].
  - exists image; split.
    + rewrite task_free_saved_sp_storage_other by exact Hother; exact Himage.
    + split; [exact Hnext|apply IH; exact Hrest].
Qed.

Lemma task_save_free_sp_preserves_reuse_closure : forall tasks tid sp,
  task_free_reuse_closure tasks ->
  task_free_reuse_closure (task_save_free_sp tasks tid sp).
Proof.
  intros tasks tid sp Hreuse slot after Hafter.
  destruct (task_free_saved_sp_storage_image_cases
    tasks.(taskLifecycle).(taskFreeStorage) tid sp slot after Hafter)
    as [before [Hbefore [Heq|Heq]]]; subst after;
    destruct (Hreuse slot before Hbefore) as [flags Hflags]; exists flags; exact Hflags.
Qed.

Lemma task_save_free_sp_preserves_pool_partition : forall sg tasks tid sp,
  task_pool_partition sg tasks ->
  task_pool_partition sg (task_save_free_sp tasks tid sp).
Proof.
  intros sg tasks tid sp [Hcover [Hused [Hprivate [Hnodup [Hstorage Hunique]]]]].
  split; [exact Hcover|]. split; [exact Hused|]. split; [exact Hprivate|].
  split; [exact Hnodup|]. split; [|exact Hunique].
  intro slot; change (In slot tasks.(unUsedTaskStates) <-> exists image,
    task_free_saved_sp_storage tasks.(taskLifecycle).(taskFreeStorage) tid sp slot = Some image).
  rewrite task_free_saved_sp_storage_domain; exact (Hstorage slot).
Qed.

Lemma task_save_free_sp_preserves_in_range : forall sg tasks tid sp,
  task_in_range sg tasks -> task_in_range sg (task_save_free_sp tasks tid sp).
Proof.
  intros sg tasks tid sp
    [Hpool [Hactive [Hlinks [Hreservations [Hgenerations [Hregistered [Hunique [Hpriority [Hreuse Hregisters]]]]]]]]].
  split; [apply task_save_free_sp_preserves_pool_partition; exact Hpool|].
  split; [exact Hactive|].
  split; [apply task_free_saved_sp_storage_preserves_links; exact Hlinks|].
  split; [exact Hreservations|]. split; [exact Hgenerations|]. split; [exact Hregistered|].
  split; [exact Hunique|]. split; [exact Hpriority|].
  split; [apply task_save_free_sp_preserves_reuse_closure; exact Hreuse|exact Hregisters].
Qed.

Lemma task_save_free_sp_creation_frame : forall tasks tid sp invocation,
  task_creation_frame invocation tasks (task_save_free_sp tasks tid sp).
Proof. reflexivity. Qed.

Lemma task_save_free_sp_private_storage_eq : forall sg tasks tid sp invocation,
  task_private_storage sg (task_save_free_sp tasks tid sp) invocation =
  task_private_storage sg tasks invocation.
Proof.
  intros; apply task_creation_frame_private_storage; apply task_save_free_sp_creation_frame.
Qed.

Lemma task_save_free_sp_invocation_active_iff : forall tasks tid sp invocation origin,
  task_invocation_active (task_save_free_sp tasks tid sp) invocation origin <->
  task_invocation_active tasks invocation origin.
Proof. reflexivity. Qed.

Lemma task_save_free_sp_public_fields_frame : forall tasks tid sp,
  (task_save_free_sp tasks tid sp).(inUsedTaskStates) = tasks.(inUsedTaskStates) /\
  (task_save_free_sp tasks tid sp).(unUsedTaskStates) = tasks.(unUsedTaskStates) /\
  (task_save_free_sp tasks tid sp).(prioTbl) = tasks.(prioTbl) /\
  (task_save_free_sp tasks tid sp).(taskLifecycle).(taskNextGeneration) =
    tasks.(taskLifecycle).(taskNextGeneration) /\
  (task_save_free_sp tasks tid sp).(taskLifecycle).(taskPublications) =
    tasks.(taskLifecycle).(taskPublications).
Proof. intros; repeat split; reflexivity. Qed.

(** Concrete free-head convenience rules, applicable immediately after
    recycling the executing task.  The arbitrary-slot rules below do not
    require that an intervening execution preserves this head position. *)
Lemma task_free_head_split_saved_sp : forall sg tasks tid rest image,
  tasks.(unUsedTaskStates) = tid :: rest ->
  tasks.(taskLifecycle).(taskFreeStorage) tid = Some image ->
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) |--
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) (TCBCommonField TCBStkPtr) (image (TCBCommonField TCBStkPtr)) **
  tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image (TCBCommonField TCBStkPtr) **
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) rest.
Proof.
  intros sg tasks tid rest image Hhead Himage.
  rewrite Hhead, task_free_storage_open_head; Intros current.
  assert (Heq : current = image) by congruence; subst current.
  unfold task_slot_storage_rep.
  sep_apply_l_atomic (tcb_configured_storage_split_field
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg tid) image
    (TCBCommonField TCBStkPtr) (tcb_configured_common_field_in _ _ _)).
  entailer!.
Qed.

Lemma task_free_head_merge_saved_sp : forall sg tasks tid rest image sp,
  tasks.(unUsedTaskStates) = tid :: rest ->
  tasks.(taskLifecycle).(taskFreeStorage) tid = Some image -> ~ In tid rest ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) (TCBCommonField TCBStkPtr) (Some sp) **
  tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image (TCBCommonField TCBStkPtr) **
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) rest |--
  task_free_storage_rep sg
    (task_save_free_sp tasks tid sp).(taskLifecycle).(taskFreeStorage)
    (task_save_free_sp tasks tid sp).(unUsedTaskStates).
Proof.
  intros sg tasks tid rest image sp Hhead Himage Hnotin.
  assert (Htail : task_free_storage_rep sg
    (task_free_saved_sp_storage tasks.(taskLifecycle).(taskFreeStorage) tid sp) rest =
    task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) rest).
  { apply task_free_storage_rep_ext; intros slot Hin.
    apply task_free_saved_sp_storage_other; intro Heq; subst slot; contradiction. }
  pose proof (task_free_saved_sp_storage_target
    tasks.(taskLifecycle).(taskFreeStorage) tid sp image Himage) as Hwritten.
  cbn [task_save_free_sp glob_task_set_lifecycle taskLifecycle taskFreeStorage unUsedTaskStates].
  rewrite Hhead, task_free_storage_open_head, Htail.
  sep_apply_l_atomic (tcb_saved_sp_storage_merge
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg tid) image sp).
  Exists (tcb_saved_sp_image image sp); entailer!.
Qed.

(** Focus one member of the ACTUAL free list.  This residual is the existing
    storage representation on the remaining list, not another map or a
    second ownership ledger.  NoDup ensures exactly one slot is removed;
    the ordinary pool-partition invariant already supplies that fact. *)
Definition task_free_storage_without_slot (sg : StableGlobVars)
  (storage : TaskID -> option TCBLayoutImage) (ids : list TaskID) (tid : TaskID)
  : Assertion :=
  task_free_storage_rep sg storage (remove Z.eq_dec tid ids).

Lemma task_free_storage_split_slot : forall sg ids storage tid image,
  NoDup ids -> In tid ids -> storage tid = Some image ->
  task_free_storage_rep sg storage ids |--
  task_slot_storage_rep sg tid image ** task_free_storage_without_slot sg storage ids tid.
Proof.
  intros sg ids; induction ids as [|head rest IH]; intros storage tid image Hnodup Hin Himage.
  - contradiction.
  - inversion Hnodup as [|head' rest' Hnotin Hrest]; subst.
    destruct (Z.eq_dec tid head) as [Heq|Hother].
    + subst head.
      assert (Hremove : remove Z.eq_dec tid (tid :: rest) = rest).
      { transitivity (remove Z.eq_dec tid rest).
        - apply List.remove_cons.
        - apply List.notin_remove; exact Hnotin. }
      assert (Hresidual : task_free_storage_without_slot sg storage (tid :: rest) tid =
        task_free_storage_rep sg storage rest).
      { exact (f_equal (task_free_storage_rep sg storage) Hremove). }
      rewrite Hresidual; cbn [task_free_storage_rep]; Intros current.
      assert (Heq : current = image) by congruence; subst current; entailer!.
    + assert (Hinrest : In tid rest) by (destruct Hin as [Heq|Hin]; [congruence|exact Hin]).
      assert (Hremove : remove Z.eq_dec tid (head :: rest) = head :: remove Z.eq_dec tid rest).
      { change ((if Z.eq_dec tid head then remove Z.eq_dec tid rest
          else head :: remove Z.eq_dec tid rest) = head :: remove Z.eq_dec tid rest).
        destruct (Z.eq_dec tid head); [contradiction|reflexivity]. }
      assert (Hresidual : task_free_storage_without_slot sg storage (head :: rest) tid =
        (EX current, coq_prop (storage head = Some current) &&
          task_slot_storage_rep sg head current) **
        task_free_storage_without_slot sg storage rest tid).
      { exact (f_equal (task_free_storage_rep sg storage) Hremove). }
      rewrite Hresidual; cbn [task_free_storage_rep]; Intros current.
      sep_apply_l_atomic (IH storage tid image Hrest Hinrest Himage).
      Exists current; entailer!.
Qed.

Lemma task_free_storage_merge_slot : forall sg ids storage tid image,
  NoDup ids -> In tid ids -> storage tid = Some image ->
  task_slot_storage_rep sg tid image ** task_free_storage_without_slot sg storage ids tid |--
  task_free_storage_rep sg storage ids.
Proof.
  intros sg ids; induction ids as [|head rest IH]; intros storage tid image Hnodup Hin Himage.
  - contradiction.
  - inversion Hnodup as [|head' rest' Hnotin Hrest]; subst.
    destruct (Z.eq_dec tid head) as [Heq|Hother].
    + subst head.
      assert (Hremove : remove Z.eq_dec tid (tid :: rest) = rest).
      { transitivity (remove Z.eq_dec tid rest).
        - apply List.remove_cons.
        - apply List.notin_remove; exact Hnotin. }
      assert (Hresidual : task_free_storage_without_slot sg storage (tid :: rest) tid =
        task_free_storage_rep sg storage rest).
      { exact (f_equal (task_free_storage_rep sg storage) Hremove). }
      rewrite Hresidual; cbn [task_free_storage_rep]; Exists image; entailer!.
    + assert (Hinrest : In tid rest) by (destruct Hin as [Heq|Hin]; [congruence|exact Hin]).
      assert (Hremove : remove Z.eq_dec tid (head :: rest) = head :: remove Z.eq_dec tid rest).
      { change ((if Z.eq_dec tid head then remove Z.eq_dec tid rest
          else head :: remove Z.eq_dec tid rest) = head :: remove Z.eq_dec tid rest).
        destruct (Z.eq_dec tid head); [contradiction|reflexivity]. }
      assert (Hresidual : task_free_storage_without_slot sg storage (head :: rest) tid =
        (EX current, coq_prop (storage head = Some current) &&
          task_slot_storage_rep sg head current) **
        task_free_storage_without_slot sg storage rest tid).
      { exact (f_equal (task_free_storage_rep sg storage) Hremove). }
      rewrite Hresidual; cbn [task_free_storage_rep]; Intros current.
      sep_apply_l_atomic (IH storage tid image Hrest Hinrest Himage).
      Exists current; entailer!.
Qed.

Lemma task_free_saved_sp_residual_frame : forall sg ids storage tid sp,
  task_free_storage_without_slot sg (task_free_saved_sp_storage storage tid sp) ids tid =
  task_free_storage_without_slot sg storage ids tid.
Proof.
  intros; unfold task_free_storage_without_slot.
  apply task_free_storage_rep_ext; intros slot Hin.
  apply task_free_saved_sp_storage_other.
  exact (proj2 (in_remove Z.eq_dec ids slot tid Hin)).
Qed.

Lemma task_free_storage_merge_saved_sp_image : forall sg ids storage tid image sp,
  NoDup ids -> In tid ids -> storage tid = Some image ->
  task_slot_storage_rep sg tid (tcb_saved_sp_image image sp) **
  task_free_storage_without_slot sg storage ids tid |--
  task_free_storage_rep sg (task_free_saved_sp_storage storage tid sp) ids.
Proof.
  intros sg ids storage tid image sp Hnodup Hin Himage.
  rewrite <- (task_free_saved_sp_residual_frame sg ids storage tid sp).
  apply task_free_storage_merge_slot; [exact Hnodup|exact Hin|].
  apply task_free_saved_sp_storage_target; exact Himage.
Qed.

Definition task_free_storage_without_saved_sp (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (tid : TaskID) (image : TCBLayoutImage) : Assertion :=
  tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image (TCBCommonField TCBStkPtr) **
  task_free_storage_without_slot sg tasks.(taskLifecycle).(taskFreeStorage)
    tasks.(unUsedTaskStates) tid.

Lemma task_free_storage_split_saved_sp : forall sg tasks tid image,
  NoDup tasks.(unUsedTaskStates) -> In tid tasks.(unUsedTaskStates) ->
  tasks.(taskLifecycle).(taskFreeStorage) tid = Some image ->
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) |--
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) (TCBCommonField TCBStkPtr) (image (TCBCommonField TCBStkPtr)) **
  task_free_storage_without_saved_sp sg tasks tid image.
Proof.
  intros sg tasks tid image Hnodup Hin Himage.
  sep_apply_l_atomic (task_free_storage_split_slot sg tasks.(unUsedTaskStates)
    tasks.(taskLifecycle).(taskFreeStorage) tid image Hnodup Hin Himage).
  unfold task_slot_storage_rep, task_free_storage_without_saved_sp.
  sep_apply_l_atomic (tcb_configured_storage_split_field
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg tid) image
    (TCBCommonField TCBStkPtr) (tcb_configured_common_field_in _ _ _)).
  entailer!.
Qed.

Lemma task_free_storage_merge_saved_sp : forall sg tasks tid image sp,
  NoDup tasks.(unUsedTaskStates) -> In tid tasks.(unUsedTaskStates) ->
  tasks.(taskLifecycle).(taskFreeStorage) tid = Some image ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) (TCBCommonField TCBStkPtr) (Some sp) **
  task_free_storage_without_saved_sp sg tasks tid image |--
  task_free_storage_rep sg
    (task_save_free_sp tasks tid sp).(taskLifecycle).(taskFreeStorage)
    (task_save_free_sp tasks tid sp).(unUsedTaskStates).
Proof.
  intros sg tasks tid image sp Hnodup Hin Himage.
  unfold task_free_storage_without_saved_sp.
  sep_apply_l_atomic (tcb_saved_sp_storage_merge
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg tid) image sp).
  apply task_free_storage_merge_saved_sp_image; assumption.
Qed.

(** The source-facing form keeps the same observed OSTCBCur pointer and
    consumes the actual [base] store with its ABI bridge.  The target may
    be anywhere in the current free list; no old-head fact is imported. *)
Lemma task_context_current_free_saved_sp_merge : forall sg tasks tid image sp,
  NoDup tasks.(unUsedTaskStates) -> In tid tasks.(unUsedTaskStates) ->
  tasks.(taskLifecycle).(taskFreeStorage) tid = Some image ->
  tcb_field_address (task_slot_addr sg tid) TCBStkPtr = task_slot_addr sg tid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  task_slot_addr sg tid # Ptr |-> sp **
  task_free_storage_without_saved_sp sg tasks tid image |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  task_free_storage_rep sg
    (task_save_free_sp tasks tid sp).(taskLifecycle).(taskFreeStorage)
    (task_save_free_sp tasks tid sp).(unUsedTaskStates).
Proof.
  intros sg tasks tid image sp Hnodup Hin Himage Haddress.
  assert (Hcell :
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg tid) (TCBCommonField TCBStkPtr) (Some sp) =
    task_slot_addr sg tid # Ptr |-> sp).
  { change ((tcb_field_address (task_slot_addr sg tid) TCBStkPtr # Ptr |-> sp) =
      (task_slot_addr sg tid # Ptr |-> sp)).
    rewrite Haddress; reflexivity. }
  rewrite <- Hcell.
  eapply derivable1_trans with (y :=
    (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid) **
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg tid) (TCBCommonField TCBStkPtr) (Some sp) **
      task_free_storage_without_saved_sp sg tasks tid image)).
  - entailer!.
  - apply derivable1_sepcon_mono; [apply derivable1_refl|].
    apply task_free_storage_merge_saved_sp; assumption.
Qed.

(** No theorem above chooses an executing generation from address equality,
    restores a retired invocation, or grants stack ownership to a reused
    slot.  Stack contents, current-instance/retirement authority, the incoming
    restore, interrupt masks, and the address bridge belong to their actual
    platform/context protocol.  An intermediate private slot must use the
    existing task_private_storage_merge_updated_field with its own
    reservation/allocation evidence; it cannot use the used/free consumers. *)
