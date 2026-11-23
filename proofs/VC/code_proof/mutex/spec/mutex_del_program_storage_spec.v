Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** All rules below operate on the actually acquired MASKED program heap.
    OSUnMapTbl is part of that shared owner, not another private copy.
    None of these rules is an unmasked Save/Restore execution theorem. *)
Lemma mutex_del_program_prepare_disabled : forall sg eid entry event mutex,
  mutex_del_parent_entry sg eid entry event mutex -> mutex.(mfPCP) = 255 ->
  kernel_program_inv sg entry |--
    mutex_del_parent_prepared sg eid entry entry event mutex ** unmap_table_rep sg.
Proof.
  intros sg eid entry event mutex Hentry Hpcp.
  rewrite kernel_program_inv_split_unmap.
  unfold UCOS2_inv; Intros.
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry event mutex Hentry Hpcp).
  entailer!.
Qed.

Lemma mutex_del_program_prepare_unowned : forall sg eid entry event mutex,
  mutex_del_parent_entry sg eid entry event mutex -> mutex.(mfPCP) <> 255 ->
  encode_event_ptr_value sg event = 0 ->
  mutex_del_released_resources sg entry mutex.(mfPCP) ** unmap_table_rep sg |--
    mutex_del_parent_prepared sg eid entry (mutex_del_released_state entry mutex.(mfPCP))
      event mutex ** unmap_table_rep sg.
Proof.
  intros sg eid entry event mutex Hentry Hpcp Hptr.
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry event mutex Hentry Hpcp Hptr).
  entailer!.
Qed.

(** Both actual native helper return shapes share the same untouched table
    owner; the proof invokes the original skip/update resource merges. *)
Lemma mutex_del_program_prepare_owner : forall sg entry eid event mutex owner node priority,
  mutex_del_parent_entry sg eid entry event mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority ->
  ((if Z.eq_dec node.(curPrio) priority then
      mutex_del_priority_input sg entry mutex.(mfPCP) owner node
    else mutex_del_priority_output sg entry mutex.(mfPCP) owner node priority) **
    mutex_del_priority_frame sg entry owner) ** unmap_table_rep sg |--
  mutex_del_parent_prepared sg eid entry
    (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority)
    event mutex ** unmap_table_rep sg.
Proof.
  intros sg entry eid event mutex owner node priority Hentry Howner Henabled Hnode Hpointer Hscan.
  pose proof Hentry as [Hvalid [He [Ht [Hm Huse]]]].
  assert (Hprepare : mutex_del_prepare sg mutex entry
    (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority)).
  { unfold mutex_del_prepare; destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)).
    - unfold mutex_pcp_enabled in Henabled; contradiction.
    - rewrite Howner; exists node, priority; repeat split; assumption || reflexivity. }
  destruct (Z.eq_dec node.(curPrio) priority) as [Hequal|Hdifferent].
  - sep_apply_l_atomic (mutex_del_owner_priority_skip_merge sg entry eid event mutex owner node priority
      Hvalid Huse He Ht Hm Howner Henabled Hnode Hpointer Hscan Hequal).
    unfold mutex_del_parent_prepared; entailer!.
  - sep_apply_l_atomic (mutex_del_owner_priority_update_merge sg entry eid event mutex owner node priority
      Hvalid Huse He Ht Hm Howner Henabled Hnode Hpointer Hscan Hdifferent).
    unfold mutex_del_parent_prepared; entailer!.
Qed.

(** This is exactly r29 which32's original conclusion with the actual
    missing table in the premise. The frozen, table-less VC is NOT changed
    or asserted here. The EventGrp address is the generated arrow term. *)
Lemma mutex_del_program_prepared_loop_entry : forall pe eid sg mutex current prepared entry,
  mutex_del_parent_layout sg -> valid_event_id sg eid -> pe = event_addr sg eid ->
  mutex_del_parent_prepared sg eid entry prepared current mutex ** unmap_table_rep sg |--
    mutex_del_parent_loop_rest sg eid entry prepared prepared current current mutex [] **
    (&(pe # "os_event" ->ₛ "OSEventGrp")) # UChar |->
      encode_event_wait_grp current.(waitList) prepared.(TskState).
Proof.
  intros pe eid sg mutex current prepared entry Hlayout Hid ->.
  destruct Hlayout as [_ [Htable _]].
  pose proof (proj1 (proj2 (Htable eid Hid))) as Hgroup; rewrite Hgroup.
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10).
  unfold mutex_del_parent_prepared; Intros_p Hfacts.
  destruct Hfacts as [Hentry Hprepare].
  pose proof Hentry as [_ [Hlookup _]].
  assert (Hcurrent : mutex_query_lookup prepared eid current).
  { unfold mutex_query_lookup in *.
    rewrite (mutex_del_prepare_event_state_eq sg mutex entry prepared Hprepare); exact Hlookup. }
  sep_apply_l_atomic (mutex_del_wake_guard_split sg eid mutex prepared).
  Intros found; unfold mutex_del_wake_guard_rep; Intros_p Hguard.
  destruct Hguard as [Hphase Hfound].
  assert (found = current) by (unfold mutex_query_lookup in Hcurrent; congruence).
  subst found.
  assert (Hloop : mutex_del_parent_loop_facts sg eid entry prepared prepared current current mutex []).
  { unfold mutex_del_parent_loop_facts.
    split; [exact Hentry|]. split; [exact Hprepare|].
    split; [constructor|]. split; assumption. }
  unfold mutex_del_parent_loop_rest; entailer!.
Qed.

(** Existing EventTaskRdy contracts take the ONE table as part of their
    precondition and return it through mutex_del_wake_merge. There is no
    separate table frame while that callee owns its array. *)
Lemma mutex_del_program_wake_result : forall sg eid mutex state event tid old priority,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_task_rdy_entry sg state.(TskState) eid event tid old ->
  event_task_rdy_post sg state.(TskState) eid event tid old 0 16 2
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
  mutex_del_wake_frame sg state eid tid |--
    coq_prop (mutex_del_wake_state_inv sg eid mutex
      (event_wake_state sg state eid event tid old PendMutex 0 PendAbort)) &&
    kernel_program_rep sg (event_wake_state sg state eid event tid old PendMutex 0 PendAbort).
Proof.
  intros sg eid mutex state event tid old priority Hphase He Hcall.
  sep_apply_l_atomic (mutex_del_wake_merge sg eid mutex state event tid old priority Hphase He Hcall).
  unfold mutex_del_wake_rep, kernel_program_rep; entailer!.
Qed.

(** Literal Type/Ptr/Cnt/free-root stores have already occurred in this
    premise. Reassemble their updated physical cells, then return the same
    unchanged table to the updated program owner. *)
Lemma mutex_del_program_recycle_fields_merge : forall sg eid mutex state event,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  ((event_pool_addr sg eid + 0) # UChar |-> 0 **
   (event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
   (event_pool_addr sg eid + 8) # UShort |-> 0 **
   (event_pool_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState) **
   sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
   mutex_del_parent_event_rest sg state eid event) ** unmap_table_rep sg |--
  kernel_program_inv sg (mutex_del_recycle_state sg eid event state).
Proof.
  intros sg eid mutex state event Hphase He Hempty.
  rewrite kernel_program_inv_split_unmap.
  sep_apply_l_atomic (mutex_del_parent_recycle_fields_merge sg state eid event).
  sep_apply_l_atomic (mutex_del_wake_recycle_merge_inv sg eid mutex state event
    (event_image sg state.(TskState) event) Hphase He Hempty); entailer!.
Qed.

(** Resource packaging at the masked Restore call, not a rule that an
    arbitrary ISR preserves a privately framed table. The common source
    ABI must transfer this complete program owner on interruption. *)
Lemma mutex_del_program_restore_pre_equiv : forall platform critical sg invocation origin
  mask saved before entry checkpoint,
  mutex_del_parent_restore_pre platform critical sg invocation origin mask saved before entry checkpoint **
    unmap_table_rep sg --||--
  coq_prop (mutex_del_parent_save_facts critical sg invocation mask saved before entry) &&
    (critical_region_masked platform critical sg invocation origin saved entry **
     kernel_program_inv sg checkpoint).
Proof.
  intros; unfold mutex_del_parent_restore_pre.
  rewrite kernel_program_inv_split_unmap; split; entailer!.
Qed.

Lemma mutex_del_program_restore_consequence : forall platform critical sg invocation origin
  mask saved checkpoint,
  UCOS2_state_inv sg checkpoint -> interrupt_saved_value mask saved ->
  (interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
   critical_region_outside critical sg invocation checkpoint) ** unmap_table_rep sg |--
  kernel_program_closed platform critical sg invocation origin mask checkpoint.
Proof.
  intros platform critical sg invocation origin mask saved checkpoint Hvalid [_ Hmask].
  rewrite Hmask; unfold kernel_program_closed; entailer!.
Qed.
