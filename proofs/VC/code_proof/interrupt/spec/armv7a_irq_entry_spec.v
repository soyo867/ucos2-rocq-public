Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Import UCOS2_C_Rules ListNotations KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected ARMv7-A/GNU non-VFP first-level exception path:
    OSIntNesting byte store, then LDR OSTCBCur and STR SP,[TCB].
    Reuse the actual task-context store transformer. These are memory
    effects at the masked cut, not an ARM instruction-semantics proof.
    This lemma handles a LIVE interrupted TCB; the kernel also has a
    source-supported free-current path during self-delete, not excluded
    from the general context model by this local result. *)
Lemma armv7a_irq_store_live_sp_raw_post : forall sg entry slot node sp heap,
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  0 <= sp < 4294967296 ->
  UCOS2_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg slot) sp) heap final /\
    UCOS2_raw_rep sg (os_sched_save_current_sp entry slot sp) final.
Proof.
  intros sg entry slot node sp heap Hnode Haddress Hsp Hraw.
  assert (Hsched : sched_raw_rep sg entry.(TskState) entry.(SchedState) =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) slot (task_set_saved_sp node sp))
      entry.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros tid Hin; symmetry.
    eapply glob_task_set_usedtask_observation; [exact Hnode|reflexivity]. }
  assert (Hevent : event_raw_rep sg entry.(TskState) entry.(EventState) =
    event_raw_rep sg (glob_task_set_usedtask entry.(TskState) slot (task_set_saved_sp node sp))
      entry.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hnode|reflexivity]. }
  let residual := constr:(task_public_storage_without_field sg entry.(TskState) slot node
    (TCBCommonField TCBStkPtr) **
    (sched_raw_rep sg entry.(TskState) entry.(SchedState) **
     UCOS2_raw_rep_missing_task_storage_sched sg entry)) in
  assert (Hsplit : UCOS2_raw_rep sg entry |-- task_slot_addr sg slot # Ptr |->_ ** residual).
  { unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
    sep_apply_l_atomic (task_public_storage_split_saved_sp sg entry.(TskState) slot node Hnode).
    cbn [tcb_layout_cell tcb_cell]; rewrite Haddress.
    sep_apply_l_atomic (store_ptr_undef_store_ptr (task_slot_addr sg slot) node.(tcbStkPtr)); entailer!. }
  destruct (framed_pointer_store_execution (task_slot_addr sg slot) sp _ heap Hsp (Hsplit heap Hraw))
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|].
  assert (Hmerge : task_slot_addr sg slot # Ptr |-> sp **
    (task_public_storage_without_field sg entry.(TskState) slot node (TCBCommonField TCBStkPtr) **
     (sched_raw_rep sg entry.(TskState) entry.(SchedState) **
      UCOS2_raw_rep_missing_task_storage_sched sg entry)) |--
    UCOS2_raw_rep sg (os_sched_save_current_sp entry slot sp)).
  { unfold os_sched_save_current_sp; rewrite Hnode.
    unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
    cbn [replace_TskS TskState SchedState IntrState EventState TickState FlagState MemoryState
      TimerState StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
    rewrite <- Hsched, <- Hevent.
    assert (Hcell : task_slot_addr sg slot # Ptr |-> sp |--
      tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg slot)
        (TCBCommonField TCBStkPtr) (Some sp)).
    { cbn [tcb_layout_cell tcb_cell]; rewrite Haddress; reflexivity. }
    sep_apply_l_atomic Hcell.
    sep_apply_l_atomic (task_public_storage_merge_saved_sp sg entry.(TskState) slot node sp).
    entailer!. }
  exact (Hmerge final Hpost).
Qed.

Definition armv7a_irq_live_entry_state (entry : UCOS2_Verify_State)
  (slot : TaskID) (sp : Z) : UCOS2_Verify_State :=
  os_sched_save_current_sp (armv7a_irq_entry_counter_state entry) slot sp.

Definition armv7a_irq_live_entry_writes (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (slot : TaskID) (sp : Z) : list (Mem.addr * Mem.byte) :=
  armv7a_irq_entry_counter_heap_writes sg entry ++ pointer_store_writes (task_slot_addr sg slot) sp.

(** The actual source branch has OSRunning=1 and the incremented register
    equal to one, hence entry nesting zero. Neither readiness nor non-Idle
    is required. Counter and TCB stores act on the SAME physical heap in
    source order; post-state representation is derived, not assumed. *)
Lemma armv7a_irq_live_entry_heap_post : forall sg entry slot node sp heap,
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some slot ->
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  0 <= sp < 4294967296 -> UCOS2_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry slot sp) heap final /\
    UCOS2_raw_rep sg (armv7a_irq_live_entry_state entry slot sp) final /\
    (armv7a_irq_live_entry_state entry slot sp).(IntrState).(intNesting) = 1 /\
    (armv7a_irq_live_entry_state entry slot sp).(TskState).(inUsedTaskStates) slot =
      Some (task_set_saved_sp node sp).
Proof.
  intros sg entry slot node sp heap Hrunning Hnesting Hcurrent Hnode Haddress Hsp Hraw.
  destruct (armv7a_irq_entry_counter_heap_raw_post sg entry heap Hraw)
    as [middle [Hcount Hmiddle]].
  assert (Hlookup : (armv7a_irq_entry_counter_state entry).(TskState).(inUsedTaskStates) slot = Some node).
  { unfold armv7a_irq_entry_counter_state; rewrite Hrunning; exact Hnode. }
  destruct (armv7a_irq_store_live_sp_raw_post sg (armv7a_irq_entry_counter_state entry)
    slot node sp middle Hlookup Haddress Hsp Hmiddle) as [final [Hstore Hfinal]].
  exists final; split.
  - unfold armv7a_irq_live_entry_writes; eapply heap_execution_append; eassumption.
  - split; [exact Hfinal|]. split.
    + unfold armv7a_irq_live_entry_state, os_sched_save_current_sp; rewrite Hlookup.
      cbn [replace_TskS IntrState]; unfold armv7a_irq_entry_counter_state.
      rewrite Hrunning; cbn [replace_IntrS IntrState intNesting]; rewrite Hnesting; reflexivity.
    + unfold armv7a_irq_live_entry_state; apply os_sched_save_current_sp_live_value; exact Hlookup.
Qed.

Lemma armv7a_irq_live_entry_preserves_validity : forall sg entry node sp lease,
  UCOS2_state_inv sg entry ->
  entry.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node ->
  node.(taskID) = lease.(stackLeaseSlot) -> node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key lease) = None ->
  UCOS2_state_inv sg (armv7a_irq_live_entry_state entry lease.(stackLeaseSlot) sp).
Proof.
  intros sg entry node sp lease Hvalid Hnode Hid Hgeneration Hnone.
  unfold armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state.
  destruct entry.(SchedState).(isRunning); unfold os_sched_save_current_sp;
    cbn [replace_IntrS TskState]; rewrite Hnode.
  - apply (os_sched_save_live_sp_preserves_validity sg
      (replace_IntrS
        {| intNesting := (entry.(IntrState).(intNesting) + 1) mod 256;
           lockNesting := entry.(IntrState).(lockNesting) |} entry) node sp lease);
      assumption.
  - apply (os_sched_save_live_sp_preserves_validity sg entry node sp lease); assumption.
Qed.

Lemma armv7a_irq_live_entry_saved_stack_binding : forall entry node sp call saved publication,
  entry.(SchedState).(isRunning) = true ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0 saved ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) sp ->
  os_sched_saved_stack_binding call saved
    (armv7a_irq_live_entry_state entry call.(os_sched_call_stack).(stackLeaseSlot) sp).
Proof.
  intros entry node sp call saved publication Hrunning Hnode Hid Hgeneration Hnone
    Hregion Hgeometry Hhistory Hsp.
  unfold os_sched_saved_stack_binding; cbv zeta.
  unfold armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state.
  rewrite Hrunning; unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode.
  split; [exact Hregion|]. split; [exact Hgeometry|].
  split; [exists publication; exact Hhistory|]. split; [|exact Hnone].
  intros current Hcurrent Hcurrentgen.
  cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates] in Hcurrent.
  rewrite Z.eqb_refl in Hcurrent; injection Hcurrent as Hcurrent; subst current.
  exact (conj Hid (conj Hgeneration Hsp)).
Qed.

Definition armv7a_irq_live_parked_state (entry : UCOS2_Verify_State)
  (call : OsSchedCallContext) (sp : Z) (saved : TaskStackFragments) : UCOS2_Verify_State :=
  let stored := armv7a_irq_live_entry_state entry call.(os_sched_call_stack).(stackLeaseSlot) sp in
  replace_TskS (glob_task_set_parked_stacks stored.(TskState)
    (task_stack_park_fragments stored.(TskState).(parkedTaskStacks)
      call.(os_sched_call_stack) saved)) stored.

(** Physical consumer of the memory-effect producer: the saved frame bytes
    are supplied by the external register-save boundary, kept disjoint
    through the actual counter/SP stores, then transferred to the existing
    parked owner exactly once. This does not manufacture handler CPU/stack
    ownership or prove the external register-save operation itself. *)
Lemma armv7a_irq_live_entry_parks_stack : forall sg entry node sp call saved publication heap,
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0 saved ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) sp ->
  (UCOS2_inv sg entry **
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) saved) heap ->
  exists final,
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot) sp) heap final /\
    UCOS2_inv sg (armv7a_irq_live_parked_state entry call sp saved) final.
Proof.
  intros sg entry node sp call saved publication heap Hrunning Hnesting Hcurrent Hnode
    Hid Hgeneration Hnone Haddress Hregion Hgeometry Hhistory Hsp
    [owned [frame [Hjoin [[Hvalid Hraw] Hsaved]]]].
  assert (Hword : 0 <= sp < 4294967296).
  { destruct Hregion as [_ [Hbase [_ Hend]]]; destruct Hsp as [[Hlower Hupper] _]; lia. }
  destruct (armv7a_irq_live_entry_heap_post sg entry _ node sp owned
    Hrunning Hnesting Hcurrent Hnode Haddress Hword Hraw)
    as [updated [Hrun [Hupdated Hrest]]].
  pose proof (armv7a_irq_live_entry_preserves_validity sg entry node sp call.(os_sched_call_stack)
    Hvalid Hnode Hid Hgeneration Hnone) as Hupdatedvalid.
  pose proof (armv7a_irq_live_entry_saved_stack_binding entry node sp call saved publication
    Hrunning Hnode Hid Hgeneration Hnone Hregion Hgeometry Hhistory Hsp) as Hbinding.
  set (stored := armv7a_irq_live_entry_state entry call.(os_sched_call_stack).(stackLeaseSlot) sp) in *.
  assert (Hconsistent : parked_stacks_consistent stored.(TskState)
    (task_stack_park_fragments stored.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) saved)).
  { apply os_sched_park_saved_context_preserves_consistency; [|exact Hbinding].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hupdatedvalid; tauto. }
  assert (Hstorednone : stored.(TskState).(parkedTaskStacks)
    (task_stack_key call.(os_sched_call_stack)) = None).
  { unfold os_sched_saved_stack_binding in Hbinding; tauto. }
  assert (Hpark : UCOS2_inv sg stored **
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) saved |--
    UCOS2_inv sg (armv7a_irq_live_parked_state entry call sp saved)).
  { rewrite UCOS2_inv_split_parked_stacks; Intros.
    sep_apply_l_atomic (store_parked_stacks_park_fragments stored.(TskState).(parkedTaskStacks)
      call.(os_sched_call_stack) saved Hstorednone).
    sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg stored _ Hupdatedvalid Hconsistent).
    entailer!. }
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  apply (Hpark final); exists updated, frame; split; [exact Hfinal|].
  split; [split; assumption|exact Hsaved].
Qed.
