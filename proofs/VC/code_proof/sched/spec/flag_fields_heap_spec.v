Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.event Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_new_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Physical IRQ and scheduler operations with the six-field Flag owner.
    The original state transformers, source relations and port premises
    are reused. No padding owner is produced or removed, and physical
    parked fragments remain the existing task-stack map. *)

Definition UCOS2_fields_raw_rep_missing_parked_stacks (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  task_public_storage sg s.(TskState) **
  UCOS2_fields_raw_rep_missing_module sg s TaskModule.

Local Lemma UCOS2_fields_raw_rep_split_parked_stacks : forall sg s,
  UCOS2_fields_raw_rep sg s --||--
    store_parked_stacks s.(TskState).(parkedTaskStacks) **
    UCOS2_fields_raw_rep_missing_parked_stacks sg s.
Proof.
  intros sg s.
  rewrite (UCOS2_fields_raw_rep_split_module sg s TaskModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold task_shared_rep, UCOS2_fields_raw_rep_missing_parked_stacks.
  split; entailer!.
Qed.

Lemma UCOS2_fields_inv_split_parked_stacks : forall sg s,
  UCOS2_fields_inv sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
      (store_parked_stacks s.(TskState).(parkedTaskStacks) **
       UCOS2_fields_raw_rep_missing_parked_stacks sg s).
Proof.
  intros; unfold UCOS2_fields_inv.
  rewrite UCOS2_fields_raw_rep_split_parked_stacks; split; reflexivity.
Qed.

Local Lemma UCOS2_fields_raw_rep_missing_parked_stacks_replace_eq : forall sg s stacks,
  UCOS2_fields_raw_rep_missing_parked_stacks sg
    (replace_TskS (glob_task_set_parked_stacks s.(TskState) stacks) s) =
  UCOS2_fields_raw_rep_missing_parked_stacks sg s.
Proof.
  intros sg s stacks; unfold UCOS2_fields_raw_rep_missing_parked_stacks,
    UCOS2_fields_raw_rep_missing_module, UCOS2_raw_rep_missing_two, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep
    replace_TskS TskState SchedState IntrState EventState TickState
    FlagState MemoryState TimerState StatsState ControlState NameState].
  rewrite (sched_raw_rep_change_task_index sg
    (glob_task_set_parked_stacks s.(TskState) stacks)
    s.(TskState) s.(SchedState) eq_refl).
  rewrite (event_raw_rep_change_task_index sg
    (glob_task_set_parked_stacks s.(TskState) stacks)
    s.(TskState) s.(EventState)); [reflexivity|].
  apply event_wait_priority_agreement_encodes; intros eid e tid Hget Hin; reflexivity.
Qed.

Lemma UCOS2_fields_inv_merge_updated_parked_stacks : forall sg s stacks,
  UCOS2_state_inv sg s ->
  parked_stacks_consistent s.(TskState) stacks ->
  store_parked_stacks stacks ** UCOS2_fields_raw_rep_missing_parked_stacks sg s |--
    UCOS2_fields_inv sg
      (replace_TskS (glob_task_set_parked_stacks s.(TskState) stacks) s).
Proof.
  intros sg s stacks Hvalid Hstacks.
  pose proof (UCOS2_replace_parked_stacks_preserves_validity sg s stacks Hvalid Hstacks)
    as Hpost.
  rewrite UCOS2_fields_inv_split_parked_stacks,
    UCOS2_fields_raw_rep_missing_parked_stacks_replace_eq; simpl; entailer!.
Qed.

(** ADD/STRB retains the original byte-wrap semantics, including nesting
    255. The first-level source protocol is supplied only at its consumer. *)
Lemma armv7a_irq_entry_counter_fields_raw_post : forall sg entry heap,
  UCOS2_fields_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg entry) heap final /\
    UCOS2_fields_raw_rep sg (armv7a_irq_entry_counter_state entry) final.
Proof.
  intros sg entry heap Hraw.
  unfold armv7a_irq_entry_counter_heap_writes, armv7a_irq_entry_counter_state.
  destruct entry.(SchedState).(isRunning) eqn:Hrunning.
  - assert (Hsplit : UCOS2_fields_raw_rep sg entry |--
      sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) **
      (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
       UCOS2_fields_raw_rep_missing_module sg entry InterruptModule)).
    { rewrite (UCOS2_fields_raw_rep_split_module sg entry InterruptModule ltac:(discriminate)).
      cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!. }
    assert (Hbyte : 0 <= (entry.(IntrState).(intNesting) + 1) mod 256 < 256)
      by (apply Z.mod_pos_bound; lia).
    destruct (kernel_heap_framed_uchar_store _ _ _ _ _ Hbyte (Hsplit heap Hraw))
      as [final [Hrun Hpost]].
    exists final; split; [exact Hrun|].
    assert (Hmerge :
      sg.(g_OSIntNesting) # UChar |-> ((entry.(IntrState).(intNesting) + 1) mod 256) **
      (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
       UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
      UCOS2_fields_raw_rep sg (replace_IntrS
        {| intNesting := (entry.(IntrState).(intNesting) + 1) mod 256;
           lockNesting := entry.(IntrState).(lockNesting) |} entry)).
    { rewrite (UCOS2_fields_raw_rep_split_module sg _ InterruptModule ltac:(discriminate)).
      change (sg.(g_OSIntNesting) # UChar |-> ((entry.(IntrState).(intNesting) + 1) mod 256) **
        (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
         UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
        interrupt_inv sg
          {| intNesting := (entry.(IntrState).(intNesting) + 1) mod 256;
             lockNesting := entry.(IntrState).(lockNesting) |} **
        UCOS2_fields_raw_rep_missing_module sg entry InterruptModule).
      assert (Hpack :
        sg.(g_OSIntNesting) # UChar |-> ((entry.(IntrState).(intNesting) + 1) mod 256) **
        (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
         UCOS2_fields_raw_rep_missing_module sg entry InterruptModule) |--
        store_int_state sg
          {| intNesting := (entry.(IntrState).(intNesting) + 1) mod 256;
             lockNesting := entry.(IntrState).(lockNesting) |} **
        UCOS2_fields_raw_rep_missing_module sg entry InterruptModule).
      { unfold store_int_state; cbn; entailer!. }
      intros h Hcells; destruct (Hpack h Hcells) as [c [r [Hjoin [Hc Hr]]]].
      exists c, r; split; [exact Hjoin|]. split.
      - apply interrupt_inv_merge_counters; exact Hc.
      - exact Hr. }
    exact (Hmerge final Hpost).
  - exists heap; split; [split; [constructor|split; reflexivity]|exact Hraw].
Qed.

(** The live TCB SP store retains the same priority-indexed Scheduler
    and Event resources, every other module, and the six-field Flag map. *)
Lemma armv7a_irq_store_live_sp_fields_raw_post : forall sg entry slot node sp heap,
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  0 <= sp < 4294967296 ->
  UCOS2_fields_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg slot) sp) heap final /\
    UCOS2_fields_raw_rep sg (os_sched_save_current_sp entry slot sp) final.
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
     (flag_fields_configured_rep sg entry.(FlagState) **
      UCOS2_raw_rep_missing_task_storage_sched_flag sg entry))) in
  assert (Hsplit : UCOS2_fields_raw_rep sg entry |-- task_slot_addr sg slot # Ptr |->_ ** residual).
  { rewrite UCOS2_fields_raw_rep_split_task_storage_sched_flag.
    unfold UCOS2_raw_rep_missing_task_storage_sched_flag.
    sep_apply_l_atomic (task_public_storage_split_saved_sp sg entry.(TskState) slot node Hnode).
    cbn [tcb_layout_cell tcb_cell]; rewrite Haddress.
    sep_apply_l_atomic (store_ptr_undef_store_ptr (task_slot_addr sg slot) node.(tcbStkPtr)); entailer!. }
  destruct (framed_pointer_store_execution (task_slot_addr sg slot) sp _ heap Hsp (Hsplit heap Hraw))
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|].
  assert (Hmerge : task_slot_addr sg slot # Ptr |-> sp **
    (task_public_storage_without_field sg entry.(TskState) slot node (TCBCommonField TCBStkPtr) **
     (sched_raw_rep sg entry.(TskState) entry.(SchedState) **
      (flag_fields_configured_rep sg entry.(FlagState) **
      UCOS2_raw_rep_missing_task_storage_sched_flag sg entry))) |--
    UCOS2_fields_raw_rep sg (os_sched_save_current_sp entry slot sp)).
  { unfold os_sched_save_current_sp; rewrite Hnode.
    rewrite UCOS2_fields_raw_rep_split_task_storage_sched_flag.
    unfold UCOS2_raw_rep_missing_task_storage_sched_flag.
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

(** The supplied saved fragments stay disjoint through the actual
    counter/SP writes, then enter the physical map exactly once. *)
Lemma armv7a_irq_live_entry_fields_parks_stack : forall sg entry node sp call saved publication heap,
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
  (UCOS2_fields_inv sg entry **
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) saved) heap ->
  exists final,
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot) sp) heap final /\
    UCOS2_fields_inv sg (armv7a_irq_live_parked_state entry call sp saved) final.
Proof.
  intros sg entry node sp call saved publication heap Hrunning Hnesting Hcurrent Hnode
    Hid Hgeneration Hnone Haddress Hregion Hgeometry Hhistory Hsp
    [owned [frame [Hjoin [[Hvalid Hraw] Hsaved]]]].
  assert (Hword : 0 <= sp < 4294967296).
  { destruct Hregion as [_ [Hbase [_ Hend]]]; destruct Hsp as [[Hlower Hupper] _]; lia. }
  destruct (armv7a_irq_entry_counter_fields_raw_post sg entry owned Hraw)
    as [middle [Hcount Hmiddle]].
  assert (Hlookup : (armv7a_irq_entry_counter_state entry).(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { unfold armv7a_irq_entry_counter_state; rewrite Hrunning; exact Hnode. }
  destruct (armv7a_irq_store_live_sp_fields_raw_post sg (armv7a_irq_entry_counter_state entry)
    _ node sp middle Hlookup Haddress Hword Hmiddle) as [updated [Hstore Hupdated]].
  assert (Hrun : kernel_heap_execution
    (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot) sp)
    owned updated).
  { unfold armv7a_irq_live_entry_writes; eapply heap_execution_append; eassumption. }
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
  assert (Hpark : UCOS2_fields_inv sg stored **
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) saved |--
    UCOS2_fields_inv sg (armv7a_irq_live_parked_state entry call sp saved)).
  { rewrite UCOS2_fields_inv_split_parked_stacks; Intros.
    sep_apply_l_atomic (store_parked_stacks_park_fragments stored.(TskState).(parkedTaskStacks)
      call.(os_sched_call_stack) saved Hstorednone).
    sep_apply_l_atomic (UCOS2_fields_inv_merge_updated_parked_stacks sg stored _ Hupdatedvalid Hconsistent).
    entailer!. }
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  apply (Hpark final); exists updated, frame; split; [exact Hfinal|].
  split; [split; assumption|exact Hsaved].
Qed.

Lemma armv7a_irq_fields_raw_current_pointer_load : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  pointer_load sg.(g_OSTCBCur) (encode_task_link sg state.(SchedState).(curTaskID)) heap.
Proof.
  intros sg state heap Hraw.
  assert (Hfocus : UCOS2_fields_raw_rep sg state |--
    sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) ** TT).
  { rewrite (UCOS2_fields_raw_rep_split_module sg state SchedModule ltac:(discriminate)).
    cbn [UCOS2_module_rep]; unfold sched_raw_rep, sched_physical_rep; entailer!; intros ? ?; exact I. }
  eapply framed_pointer_store_load; exact (Hfocus heap Hraw).
Qed.

Lemma armv7a_irq_fields_raw_live_stack_pointer_load : forall sg state slot node heap,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  UCOS2_fields_raw_rep sg state heap ->
  pointer_load (task_slot_addr sg slot) node.(tcbStkPtr) heap.
Proof.
  intros sg state slot node heap Hnode Haddress Hraw.
  assert (Hfocus : UCOS2_fields_raw_rep sg state |--
    task_slot_addr sg slot # Ptr |-> node.(tcbStkPtr) ** TT).
  { rewrite (UCOS2_fields_raw_rep_split_module sg state TaskModule ltac:(discriminate)).
    cbn [UCOS2_module_rep]; unfold task_shared_rep.
    sep_apply_l_atomic (task_public_storage_split_saved_sp sg state.(TskState) slot node Hnode).
    cbn [tcb_layout_cell tcb_cell]; rewrite Haddress; entailer!; intros ? ?; exact I. }
  eapply framed_pointer_store_load; exact (Hfocus heap Hraw).
Qed.

Lemma armv7a_irq_restore_pointer_reads_fields_live : forall sg state slot node heap,
  state.(SchedState).(curTaskID) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  UCOS2_fields_raw_rep sg state heap ->
  armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg slot) node.(tcbStkPtr).
Proof.
  intros sg state slot node heap Hcurrent Hnode Haddress Hraw; split.
  - pose proof (armv7a_irq_fields_raw_current_pointer_load sg state heap Hraw) as Hread.
    rewrite Hcurrent in Hread; exact Hread.
  - eapply armv7a_irq_fields_raw_live_stack_pointer_load; eassumption.
Qed.

(** The two selector cache stores use an intermediate physical
    representation: ready tables, Task storage and every non-cache cell
    retain their real input bytes until reassembly. *)
Definition os_int_exit_selection_fields_rep (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (high pointer : Z) : Assertion :=
  sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) high **
  sg.(g_OSTCBHighRdy) # Ptr |-> pointer **
  sched_physical_without_high sg state.(SchedState) **
  UCOS2_fields_raw_rep_missing_module sg state SchedModule.

Local Lemma os_int_exit_selection_fields_rep_entry : forall sg state,
  UCOS2_fields_raw_rep sg state ** unmap_table_rep sg --||--
  os_int_exit_selection_fields_rep sg state
    (sched_priority_byte state.(SchedState).(highRdyPrio))
    (encode_task_link sg state.(SchedState).(highRdyTid)).
Proof.
  intros; rewrite (UCOS2_fields_raw_rep_split_module sg state SchedModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold os_int_exit_selection_fields_rep, sched_new_rep, sched_raw_rep,
    sched_physical_rep, sched_physical_without_high.
  rewrite sched_rows_array_equiv; split; entailer!.
Qed.

Local Lemma os_int_exit_selection_fields_rep_high_load : forall sg state high pointer heap,
  os_int_exit_selection_fields_rep sg state high pointer heap ->
  uchar_load sg.(g_OSPrioHighRdy) high heap.
Proof.
  intros sg state high pointer heap Hrep.
  assert (Hfocus : os_int_exit_selection_fields_rep sg state high pointer |--
    sg.(g_OSPrioHighRdy) # UChar |-> high ** TT).
  { unfold os_int_exit_selection_fields_rep, sched_new_rep; entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hfocus heap Hrep).
Qed.

Local Lemma os_int_exit_selection_fields_rep_current_load : forall sg state high pointer heap,
  os_int_exit_selection_fields_rep sg state high pointer heap ->
  uchar_load sg.(g_OSPrioCur) (sched_priority_byte state.(SchedState).(curSchedPrio)) heap.
Proof.
  intros sg state high pointer heap Hrep.
  assert (Hfocus : os_int_exit_selection_fields_rep sg state high pointer |--
    sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) ** TT).
  { unfold os_int_exit_selection_fields_rep, sched_physical_without_high; entailer!; intros ? ?; exact I. }
  eapply framed_uchar_store_load; exact (Hfocus heap Hrep).
Qed.

Local Lemma os_int_exit_selection_fields_rep_table_load : forall sg state high pointer heap,
  os_int_exit_selection_fields_rep sg state high pointer heap ->
  pointer_load
    (sg.(g_OSTCBPrioTbl) + sched_selected_priority state.(TskState) state.(SchedState) * sizeof(PTR))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) heap.
Proof.
  intros sg state high pointer heap Hrep.
  assert (Hfocus : os_int_exit_selection_fields_rep sg state high pointer |--
    (sg.(g_OSTCBPrioTbl) + sched_selected_priority state.(TskState) state.(SchedState) * sizeof(PTR))
      # Ptr |-> sched_selected_pointer sg state.(TskState) state.(SchedState) ** TT).
  { unfold os_int_exit_selection_fields_rep, UCOS2_fields_raw_rep_missing_module,
      UCOS2_raw_rep_missing_two, UCOS2_selected_rep;
      cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
    unfold task_shared_rep, task_public_storage.
    sep_apply_l_atomic (store_prio_tbl_split_selection sg state.(TskState) state.(SchedState)).
    entailer!; intros ? ?; exact I. }
  eapply framed_pointer_store_load; exact (Hfocus heap Hrep).
Qed.

Local Lemma os_int_exit_selection_heap_fields_rep_post : forall sg state high pointer heap,
  os_int_exit_selection_fields_rep sg state high pointer heap ->
  exists final, os_int_exit_selection_heap_fragment sg heap final /\
    os_int_exit_selection_fields_rep sg state
      (sched_selected_priority state.(TskState) state.(SchedState))
      (sched_selected_pointer sg state.(TskState) state.(SchedState)) final.
Proof.
  intros sg state high pointer heap Hrep.
  assert (Hsplit : os_int_exit_selection_fields_rep sg state high pointer |--
    sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList)) high **
    (sg.(g_OSTCBHighRdy) # Ptr |-> pointer **
     sched_physical_without_high sg state.(SchedState) ** UCOS2_fields_raw_rep_missing_module sg state SchedModule)).
  { unfold os_int_exit_selection_fields_rep; entailer!. }
  destruct (sched_new_heap_fragment_frame_post _ _ _ _ _ heap (Hsplit heap Hrep))
    as [middle [Hnew Hmiddle]].
  rewrite sched_new_priority_eq_selected in Hmiddle.
  assert (Hmid : os_int_exit_selection_fields_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState)) pointer middle).
  { assert (Hmerge : sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList))
      (sched_selected_priority state.(TskState) state.(SchedState)) **
      (sg.(g_OSTCBHighRdy) # Ptr |-> pointer ** sched_physical_without_high sg state.(SchedState) **
        UCOS2_fields_raw_rep_missing_module sg state SchedModule) |--
      os_int_exit_selection_fields_rep sg state (sched_selected_priority state.(TskState) state.(SchedState)) pointer).
    { unfold os_int_exit_selection_fields_rep; entailer!. }
    exact (Hmerge middle Hmiddle). }
  pose proof (os_int_exit_selection_fields_rep_high_load _ _ _ _ _ Hmid) as Hp.
  pose proof (os_int_exit_selection_fields_rep_table_load _ _ _ _ _ Hmid) as Hptr.
  assert (Hwrite : os_int_exit_selection_fields_rep sg state
      (sched_selected_priority state.(TskState) state.(SchedState)) pointer |--
    sg.(g_OSTCBHighRdy) # Ptr |->_ **
    (sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList))
      (sched_selected_priority state.(TskState) state.(SchedState)) **
     sched_physical_without_high sg state.(SchedState) ** UCOS2_fields_raw_rep_missing_module sg state SchedModule)).
  { unfold os_int_exit_selection_fields_rep; sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSTCBHighRdy) pointer).
    entailer!. }
  destruct (framed_pointer_store_execution _ _ _ middle (proj1 Hptr) (Hwrite middle Hmid))
    as [final [Hrun Hpost]].
  exists final; split.
  - exists middle, (sched_selected_priority state.(TskState) state.(SchedState)),
      (sched_selected_pointer sg state.(TskState) state.(SchedState)).
    split; [exact Hnew|]. split; [exact Hp|]. split; [exact Hptr|exact Hrun].
  - assert (Hmerge : sg.(g_OSTCBHighRdy) # Ptr |-> sched_selected_pointer sg state.(TskState) state.(SchedState) **
      (sched_new_rep sg (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
        (sched_row_values state.(TskState) state.(SchedState).(readyList))
        (sched_selected_priority state.(TskState) state.(SchedState)) **
       sched_physical_without_high sg state.(SchedState) ** UCOS2_fields_raw_rep_missing_module sg state SchedModule) |--
      os_int_exit_selection_fields_rep sg state
        (sched_selected_priority state.(TskState) state.(SchedState))
        (sched_selected_pointer sg state.(TskState) state.(SchedState))).
    { unfold os_int_exit_selection_fields_rep; entailer!. }
    exact (Hmerge final Hpost).
Qed.

Local Lemma os_int_exit_selection_fields_rep_merge : forall sg state,
  valid_stable_glob_vars sg -> sched_ready_structure sg state.(TskState) state.(SchedState) ->
  task_current_prio_registered state.(TskState) -> state.(SchedState).(readyList) <> [] ->
  os_int_exit_selection_fields_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) |--
  UCOS2_fields_raw_rep sg (os_int_exit_selection_state state) ** unmap_table_rep sg.
Proof.
  intros sg state Hsg Hready Hregistered Hnonempty.
  destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
  destruct (proj1 Hready head ltac:(rewrite Hlist; left; reflexivity)) as [node [Hnode Hrest]].
  pose proof (proj1 (sched_selection_written_head_eq_from_structure sg state.(TskState) state.(SchedState)
    head tail node Hsg Hready Hregistered Hlist Hnode)) as Hphysical.
  rewrite (UCOS2_fields_raw_rep_split_module sg (os_int_exit_selection_state state) SchedModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  change (os_int_exit_selection_fields_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) |--
    (sched_raw_rep sg state.(TskState) (sched_refresh_high state.(TskState) state.(SchedState)) **
      UCOS2_fields_raw_rep_missing_module sg state SchedModule) ** unmap_table_rep sg).
  assert (Hsplit : os_int_exit_selection_fields_rep sg state
    (sched_selected_priority state.(TskState) state.(SchedState))
    (sched_selected_pointer sg state.(TskState) state.(SchedState)) |--
    sched_selection_written_rep sg state.(TskState) state.(SchedState) **
    (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_fields_raw_rep_missing_module sg state SchedModule ** unmap_table_rep sg)).
  { unfold os_int_exit_selection_fields_rep, sched_new_rep, sched_selection_written_rep, sched_cache_cells.
    rewrite sched_rows_array_equiv; entailer!. }
  sep_apply_l_atomic Hsplit.
  sep_apply_l_atomic Hphysical.
  unfold sched_raw_rep.
  assert (Hreadyframe : (sched_refresh_high state.(TskState) state.(SchedState)).(readyList) =
    state.(SchedState).(readyList)) by reflexivity.
  rewrite Hreadyframe; entailer!.
Qed.

Lemma os_int_exit_selection_fields_raw_frame_post : forall sg state (frame : Assertion) heap,
  valid_stable_glob_vars sg -> sched_ready_in_range sg state.(TskState) state.(SchedState) ->
  task_current_prio_registered state.(TskState) -> state.(SchedState).(readyList) <> [] ->
  (UCOS2_fields_raw_rep sg state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_int_exit_selection_heap_fragment sg heap final /\
    uchar_load sg.(g_OSPrioHighRdy) (sched_selected_priority state.(TskState) state.(SchedState)) final /\
    uchar_load sg.(g_OSPrioCur) (sched_priority_byte state.(SchedState).(curSchedPrio)) final /\
    (UCOS2_fields_raw_rep sg (os_int_exit_selection_state state) ** unmap_table_rep sg ** frame) final.
Proof.
  intros sg state frame heap Hsg Hready Hregistered Hnonempty
    [owned [rest [Hjoin [Hrep Hframe]]]].
  apply sched_ready_in_range_implies_structure in Hready.
  destruct (os_int_exit_selection_heap_fields_rep_post _ _ _ _ _
    (proj1 (os_int_exit_selection_fields_rep_entry sg state) owned Hrep)) as [after [Hsource Hpost]].
  destruct (os_int_exit_selection_heap_fragment_frame sg owned after rest heap Hsource Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  split; [eapply uchar_load_frame; [eapply os_int_exit_selection_fields_rep_high_load; exact Hpost|exact Hfinal]|].
  split; [eapply uchar_load_frame; [eapply os_int_exit_selection_fields_rep_current_load; exact Hpost|exact Hfinal]|].
  exists after, rest; split; [exact Hfinal|]. split; [|exact Hframe].
  eapply os_int_exit_selection_fields_rep_merge; eassumption.
Qed.

(** Selected-profile scheduling increments the real global counter.
    The original masked UInt effect and modulo arithmetic are unchanged. *)
Lemma os_sched_profile_global_fields_raw_post : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  exists final, os_sched_profile_global_fragment sg heap final /\
    UCOS2_fields_raw_rep sg (os_sched_profile_global_state state) final.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_fields_raw_rep sg state |--
    sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
    (sched_physical_without_counter sg state.(SchedState) **
     sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_fields_raw_rep_missing_module sg state SchedModule)).
  { rewrite (UCOS2_fields_raw_rep_split_module sg state SchedModule ltac:(discriminate)); cbn [UCOS2_module_rep].
    unfold sched_raw_rep; sep_apply_l_atomic (sched_physical_split_counter sg state.(SchedState)); entailer!. }
  assert (Hload : pointer_load sg.(g_OSCtxSwCtr) state.(SchedState).(ctxSwCtr) heap).
  { destruct (Hsplit heap Hraw) as [cell [rest [Hjoin [Hcell Hrest]]]].
    eapply pointer_load_frame; [apply sched_profile_uint_load; exact Hcell|exact Hjoin]. }
  assert (Hforget : sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
    (sched_physical_without_counter sg state.(SchedState) **
     sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_fields_raw_rep_missing_module sg state SchedModule) |--
    sg.(g_OSCtxSwCtr) # UInt |->_ **
    (sched_physical_without_counter sg state.(SchedState) **
     sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_fields_raw_rep_missing_module sg state SchedModule)).
  { sep_apply_l_atomic (store_uint_undef_store_uint sg.(g_OSCtxSwCtr) state.(SchedState).(ctxSwCtr));
      entailer!. }
  destruct (sched_profile_uint_store_frame_post _ (kernel_u32 (state.(SchedState).(ctxSwCtr) + 1)) _ heap
    (kernel_u32_in_range _) (Hforget heap (Hsplit heap Hraw))) as [final [Hrun Hpost]].
  exists final; split; [exists state.(SchedState).(ctxSwCtr); split; assumption|].
  assert (Hmerge : sg.(g_OSCtxSwCtr) # UInt |-> kernel_u32 (state.(SchedState).(ctxSwCtr) + 1) **
    (sched_physical_without_counter sg state.(SchedState) **
     sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_fields_raw_rep_missing_module sg state SchedModule) |-- UCOS2_fields_raw_rep sg (os_sched_profile_global_state state)).
  { rewrite (UCOS2_fields_raw_rep_split_module sg (os_sched_profile_global_state state) SchedModule ltac:(discriminate)).
    cbn [UCOS2_module_rep]. unfold os_sched_profile_global_state.
    change (sg.(g_OSCtxSwCtr) # UInt |-> kernel_u32 (state.(SchedState).(ctxSwCtr) + 1) **
      (sched_physical_without_counter sg state.(SchedState) **
       sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
       sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
       UCOS2_fields_raw_rep_missing_module sg state SchedModule) |--
      sched_raw_rep sg state.(TskState) (sched_increment_switch_counter state.(SchedState)) **
      UCOS2_fields_raw_rep_missing_module sg state SchedModule).
    unfold sched_raw_rep; cbn [sched_increment_switch_counter readyList].
    sep_apply_l_atomic (sched_physical_merge_incremented_counter sg state.(SchedState)); entailer!. }
  exact (Hmerge final Hpost).
Qed.

Local Lemma sched_install_cache_fields_raw_post : forall sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  exists final,
    sched_install_cache_fragment sg heap final (encode_task_link sg state.(SchedState).(highRdyTid)) /\
    UCOS2_fields_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state) final.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_fields_raw_rep sg state |--
    sched_install_cache_rep sg state.(SchedState)
      (sched_priority_byte state.(SchedState).(curSchedPrio))
      (encode_task_link sg state.(SchedState).(curTaskID)) **
    (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_fields_raw_rep_missing_module sg state SchedModule)).
  { rewrite (UCOS2_fields_raw_rep_split_module sg state SchedModule ltac:(discriminate)); cbn [UCOS2_module_rep].
    unfold sched_raw_rep; rewrite sched_install_cache_rep_entry; entailer!. }
  destruct (sched_install_cache_rep_post _ _ _ _ _ heap (Hsplit heap Hraw))
    as [final [Hrun Hfinal]].
  exists final; split; [exact Hrun|].
  assert (Hmerge : sched_install_cache_rep sg state.(SchedState)
      (sched_priority_byte state.(SchedState).(highRdyPrio))
      (encode_task_link sg state.(SchedState).(highRdyTid)) **
    (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_fields_raw_rep_missing_module sg state SchedModule) |--
    UCOS2_fields_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state)).
  { rewrite (UCOS2_fields_raw_rep_split_module sg (replace_SchedS (sched_install_selected state.(SchedState)) state)
      SchedModule ltac:(discriminate)); cbn [UCOS2_module_rep].
    change (sched_install_cache_rep sg state.(SchedState)
      (sched_priority_byte state.(SchedState).(highRdyPrio))
      (encode_task_link sg state.(SchedState).(highRdyTid)) **
      (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
       sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
       UCOS2_fields_raw_rep_missing_module sg state SchedModule) |--
      sched_raw_rep sg state.(TskState) (sched_install_selected state.(SchedState)) **
      UCOS2_fields_raw_rep_missing_module sg state SchedModule).
    rewrite sched_install_cache_rep_merge.
    unfold sched_raw_rep; cbn [sched_install_selected readyList]; entailer!. }
  exact (Hmerge final Hfinal).
Qed.

Local Lemma sched_install_heap_fields_raw_post : forall sg state slot node heap,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  UCOS2_fields_raw_rep sg state heap ->
  exists final,
    sched_install_heap_fragment sg heap final (task_slot_addr sg slot) node.(tcbStkPtr) /\
    UCOS2_fields_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state) final.
Proof.
  intros sg state slot node heap Hhigh Hnode Haddress Hraw.
  destruct (sched_install_cache_fields_raw_post sg state heap Hraw) as [final [Hrun Hfinal]].
  exists final; split; [split|exact Hfinal].
  - rewrite Hhigh in Hrun; exact Hrun.
  - eapply (armv7a_irq_fields_raw_live_stack_pointer_load sg
      (replace_SchedS (sched_install_selected state.(SchedState)) state) slot node final);
      [exact Hnode|exact Haddress|exact Hfinal].
Qed.

Lemma sched_install_heap_fields_raw_frame_post : forall sg state slot node (frame : Assertion) heap,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  (UCOS2_fields_raw_rep sg state ** frame) heap ->
  exists final,
    sched_install_heap_fragment sg heap final (task_slot_addr sg slot) node.(tcbStkPtr) /\
    (UCOS2_fields_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state) ** frame) final.
Proof.
  intros sg state slot node frame heap Hhigh Hnode Haddress
    [owned [rest [Hjoin [Hraw Hframe]]]].
  destruct (sched_install_heap_fields_raw_post sg state slot node owned Hhigh Hnode Haddress Hraw)
    as [after [Hrun Hafter]].
  destruct (sched_install_heap_fragment_frame _ _ _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

Local Lemma os_sched_install_fields_heap_take_destination :
  forall external sg context saved hooked incoming resumed heap,
  os_sched_saved_stack_binding context saved hooked ->
  os_sched_destination_binding external context saved hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (UCOS2_fields_inv sg hooked **
    task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved) heap ->
  exists final sp,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot)) sp /\
    (coq_prop (task_current_at (os_sched_install_context context saved incoming hooked)
        incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
      external.(os_sched_arch_restore_source) incoming sp resumed) &&
     (UCOS2_fields_inv sg (os_sched_install_context context saved incoming hooked) **
      task_stack_fragments_rep incoming.(stackLeaseRegion) resumed)) final.
Proof.
  intros external sg context saved hooked incoming resumed heap Hsaved
    [Hhigh [[node [Hnode [Hgeneration [Hpriority Harch]]]] [Hlive Hparked]]]
    Haddress Hbefore.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { destruct Hbefore as [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]]; exact Hvalid. }
  assert (Hraw : (UCOS2_fields_raw_rep sg hooked **
    task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved) heap).
  { assert (Hforget : UCOS2_fields_inv sg hooked **
        task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved |--
      UCOS2_fields_raw_rep sg hooked **
        task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved).
    { unfold UCOS2_fields_inv; entailer!. }
    exact (Hforget heap Hbefore). }
  destruct (sched_install_heap_fields_raw_frame_post sg hooked incoming.(stackLeaseSlot) node _ heap
    Hhigh Hnode Haddress Hraw) as [final [Hrun Hfinal]].
  assert (Hindex : forall p, hooked.(SchedState).(highRdyPrio) = Some p -> task_priority_in_range sg p).
  { intros p Hp; assert (p = node.(curPrio)) by congruence; subst p.
    pose proof (proj1 (proj2 Hvalid)) as Htasks.
    assert (Hpriorities : forall tid t, hooked.(TskState).(inUsedTaskStates) tid = Some t ->
      task_priority_in_range sg t.(curPrio)) by (unfold task_in_range in Htasks; tauto).
    eapply Hpriorities; exact Hnode. }
  assert (Hcached : UCOS2_state_inv sg
    (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked)).
  { apply os_int_exit_install_cache_preserves_validity; assumption. }
  assert (Hnone : hooked.(TskState).(parkedTaskStacks)
    (task_stack_key context.(os_sched_call_stack)) = None).
  { unfold os_sched_saved_stack_binding in Hsaved; tauto. }
  assert (Hconsistent : parked_stacks_consistent hooked.(TskState)
    (task_stack_take (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) saved) incoming)).
  { apply task_stack_take_preserves_consistency.
    apply os_sched_park_saved_context_preserves_consistency; [|exact Hsaved].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Htake : UCOS2_fields_raw_rep sg
      (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked) **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved |--
    UCOS2_fields_inv sg (os_sched_install_context context saved incoming hooked) **
      task_stack_fragments_rep incoming.(stackLeaseRegion) resumed).
  { assert (Hsplit : forall state, UCOS2_fields_raw_rep sg state --||--
      store_parked_stacks state.(TskState).(parkedTaskStacks) **
      UCOS2_fields_raw_rep_missing_parked_stacks sg state).
    { intros; apply UCOS2_fields_raw_rep_split_parked_stacks. }
    rewrite (Hsplit (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked)).
    sep_apply_l_atomic (store_parked_stacks_switch_fragments hooked.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) incoming saved resumed Hnone Hparked).
    sep_apply_l_atomic (UCOS2_fields_inv_merge_updated_parked_stacks sg
      (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked)
      (task_stack_take (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
        context.(os_sched_call_stack) saved) incoming) Hcached Hconsistent).
    unfold os_sched_install_context; entailer!. }
  assert (Hcurrent : task_current_at (os_sched_install_context context saved incoming hooked)
    incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)).
  { split; [exact Hhigh|]; exists node; split; assumption. }
  exists final, node.(tcbStkPtr); split; [exact Hrun|].
  split; [split; assumption|exact (Htake final Hfinal)].
Qed.

Lemma os_sched_install_fields_heap_take_destination_frame :
  forall external sg context saved hooked incoming resumed (frame : Assertion) heap,
  os_sched_saved_stack_binding context saved hooked ->
  os_sched_destination_binding external context saved hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  ((UCOS2_fields_inv sg hooked **
    task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved) ** frame) heap ->
  exists final sp,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot)) sp /\
    (coq_prop (task_current_at (os_sched_install_context context saved incoming hooked)
        incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
      external.(os_sched_arch_restore_source) incoming sp resumed) &&
     ((UCOS2_fields_inv sg (os_sched_install_context context saved incoming hooked) **
       task_stack_fragments_rep incoming.(stackLeaseRegion) resumed) ** frame)) final.
Proof.
  intros external sg context saved hooked incoming resumed frame heap Hsaved Hdestination Haddress
    [owned [rest [Hjoin [Hbefore Hframe]]]].
  destruct (os_sched_install_fields_heap_take_destination external sg context saved hooked incoming resumed
    owned Hsaved Hdestination Haddress Hbefore) as [after [sp [Hrun [Hfacts Hafter]]]].
  destruct (sched_install_heap_fragment_frame _ _ _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final, sp; split; [exact Hwhole|]. split; [exact Hfacts|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** These are local heap/source-fragment interfaces. Their consumers
    must still supply the original actual transitions, bindings, geometry,
    coverage and port contracts. They establish no public entry domain,
    registered-client closure, arbitrary-interference frame rule, or
    whole-C scheduler acceptance. *)
