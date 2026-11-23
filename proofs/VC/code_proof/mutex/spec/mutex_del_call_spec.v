Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From AUXLib Require Import ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import CArch.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected nested-priority Delete first clears the enabled ceiling
    cell, scans the remaining aliases, and only then relocates the owner.
    This intermediate heap is NOT a stable kernel invariant: its old
    current priority may name the cell just cleared. The unchanged resources
    stay indexed by the acquired entry until the actual later stores occur. *)
Definition mutex_del_released_table (entry : UCOS2_Verify_State)
  (ceiling : Priority) : Priority -> PrioTblEntry :=
  update_prio_tbl entry.(TskState).(prioTbl) ceiling PTFree.

Definition mutex_del_priority_values (sg : StableGlobVars)
  (table : Priority -> PrioTblEntry) : list Z :=
  map (fun p => prio_tbl_entry_to_addr sg (table p)) (Zrange 0 64).

Definition mutex_del_released_resources (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (ceiling : Priority) : Assertion :=
  store_prio_tbl sg (mutex_del_released_table entry ceiling) **
  UCOS2_raw_rep_missing_priority_table sg entry.

Lemma mutex_del_priority_values_length : forall sg table,
  Zlength (mutex_del_priority_values sg table) = 64.
Proof. intros; reflexivity. Qed.

Lemma mutex_del_priority_values_lookup : forall sg table p,
  0 <= p < 64 ->
  Znth p (mutex_del_priority_values sg table) 0 = prio_tbl_entry_to_addr sg (table p).
Proof. intros; apply prio_table_values_Znth; assumption. Qed.

Lemma mutex_del_released_resources_merge_cell : forall sg entry ceiling,
  0 <= ceiling < 64 ->
  (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)) # Ptr |-> 0 **
    store_prio_tbl_missing_i sg entry.(TskState).(prioTbl) ceiling **
    UCOS2_raw_rep_missing_priority_table sg entry |--
  mutex_del_released_resources sg entry ceiling.
Proof.
  intros sg entry ceiling Hrange; unfold mutex_del_released_resources,
    mutex_del_released_table.
  pose proof (store_prio_tbl_merge_updated_cell sg
    entry.(TskState).(prioTbl) ceiling PTFree Hrange) as Hmerge.
  cbn [prio_tbl_entry_to_addr] in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

(** Native helper resources are extracted from the already released heap;
    the high-ready cache and unrelated globals remain untouched.  This
    residual owns neither the selected TCB nor any ready/current cell. *)
Definition mutex_del_priority_frame (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (owner : TaskID) : Assertion :=
  store_map_missing_i (used_task_rep sg) entry.(TskState).(inUsedTaskStates) owner **
  task_free_storage_rep sg entry.(TskState).(taskLifecycle).(taskFreeStorage)
    entry.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error entry.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg entry.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> entry.(TskState).(taskCount) **
  task_reg_allocator_rep sg entry.(TskState) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte entry.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg entry.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> entry.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if entry.(SchedState).(isRunning) then 1 else 0) **
  UCOS2_raw_rep_missing_task_storage_sched sg entry.

Definition mutex_del_priority_input (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (ceiling : Priority)
  (owner : TaskID) (node : TaskAbstractState) : Assertion :=
  tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (mutex_del_priority_values sg (mutex_del_released_table entry ceiling)) **
  UCharArray.full sg.(g_OSRdyTbl) 8
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
  sg.(g_OSRdyGrp) # UChar |->
    encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg entry.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte entry.(SchedState).(curSchedPrio).

(** A concrete task pointer cannot equal the reserved-table tag. The proof
    must obtain this fact from actual typed storage plus the source ABI,
    not assume that the abstract PTReserved and PTTask constructors alone
    make their C encodings distinct. Only the already owned cell is reused. *)
Lemma mutex_del_pointer_cell_not_reserved : forall pointer value,
  pointer # Ptr |-> value |--
  coq_prop (pointer <> 1) && pointer # Ptr |-> value.
Proof.
  intros pointer value; unfold store_ptr; Intros.
  entailer!.
  unfold isvalidptr in H; destruct H as [[_ [_ Haligned]] _].
  pose proof (Arch32.ptr_aligned_aligned_4 pointer Haligned) as Hmod.
  intro E; subst pointer; discriminate.
Qed.

Lemma mutex_del_task_storage_pointer_not_reserved : forall sg owner node,
  tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner ->
  used_task_rep sg owner node |--
    coq_prop (task_slot_addr sg owner <> 1) && used_task_rep sg owner node.
Proof.
  intros sg owner node Haddress; unfold used_task_rep, task_slot_storage_rep.
  pose proof (tcb_configured_common_field_in sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) TCBStkPtr) as Hin.
  pose proof (tcb_configured_storage_split_field
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg owner) (task_layout_image sg node) (TCBCommonField TCBStkPtr) Hin) as Hsplit.
  pose proof (tcb_configured_storage_merge_field
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg owner) (task_layout_image sg node) (TCBCommonField TCBStkPtr) Hin) as Hmerge.
  assert (Hcell : tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg owner) (TCBCommonField TCBStkPtr)
    (task_layout_image sg node (TCBCommonField TCBStkPtr)) =
    (task_slot_addr sg owner) # Ptr |-> node.(tcbStkPtr)).
  { cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell].
    rewrite Haddress; reflexivity. }
  rewrite Hcell in Hsplit, Hmerge.
  match goal with |- _ |-- ?Post =>
    match type of Hsplit with _ |-- ?Opened => assert (Hfinish : Opened |-- Post) end
  end.
  { sep_apply_l_atomic (mutex_del_pointer_cell_not_reserved (task_slot_addr sg owner) node.(tcbStkPtr)).
    Intros; sep_apply_l_atomic Hmerge; entailer!. }
  intros heap Howned; apply (Hfinish heap); exact (Hsplit heap Howned).
Qed.

(** A real missing-owner frame: neither the focused TCB nor the released
    priority table is duplicated here. Parked stacks and all unrelated
    modules stay in the global residual. *)
Definition mutex_del_owner_frame (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (owner : TaskID) : Assertion :=
  store_map_missing_i (used_task_rep sg) entry.(TskState).(inUsedTaskStates) owner **
  task_free_storage_rep sg entry.(TskState).(taskLifecycle).(taskFreeStorage)
    entry.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error entry.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg entry.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> entry.(TskState).(taskCount) **
  task_reg_allocator_rep sg entry.(TskState) **
  sched_raw_rep sg entry.(TskState) entry.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg entry.

Lemma mutex_del_released_resources_split_owner : forall sg entry ceiling owner node,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_del_released_resources sg entry ceiling |--
  used_task_rep sg owner node ** store_prio_tbl sg (mutex_del_released_table entry ceiling) **
    mutex_del_owner_frame sg entry owner.
Proof.
  intros sg entry ceiling owner node Hnode.
  unfold mutex_del_released_resources, UCOS2_raw_rep_missing_priority_table,
    task_public_storage_without_prio_tbl, store_used_task_map, mutex_del_owner_frame.
  sep_apply_l_atomic (store_map_split (used_task_rep sg) owner node
    entry.(TskState).(inUsedTaskStates) Hnode); entailer!.
Qed.

Lemma mutex_del_released_resources_merge_owner : forall sg entry ceiling owner node,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  used_task_rep sg owner node ** store_prio_tbl sg (mutex_del_released_table entry ceiling) **
    mutex_del_owner_frame sg entry owner |-- mutex_del_released_resources sg entry ceiling.
Proof.
  intros sg entry ceiling owner node Hnode.
  unfold mutex_del_released_resources, UCOS2_raw_rep_missing_priority_table,
    task_public_storage_without_prio_tbl, store_used_task_map, mutex_del_owner_frame.
  entailer!.
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) owner node
    entry.(TskState).(inUsedTaskStates) Hnode); entailer!.
Qed.

Lemma mutex_del_table_task_encoding : forall sg table owner p,
  task_slot_addr sg owner <> 0 -> task_slot_addr sg owner <> 1 ->
  0 <= p < 64 ->
  (Znth p (mutex_del_priority_values sg table) 0 = task_slot_addr sg owner <->
   table p = PTTask owner).
Proof.
  intros sg table owner p Hnonzero Hreserved Hrange.
  rewrite mutex_del_priority_values_lookup by assumption.
  destruct (table p) as [| |tid] eqn:Hentry; cbn [prio_tbl_entry_to_addr].
  - split; intros; congruence.
  - split; intros; congruence.
  - split.
    + intro E; apply task_slot_addr_injective in E; subst tid; reflexivity.
    + intro E; injection E as E; subst tid; reflexivity.
Qed.

Lemma mutex_del_live_task_pointer_nonzero : forall sg entry owner node,
  UCOS2_state_inv sg entry -> entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_slot_addr sg owner <> 0.
Proof.
  intros sg entry owner node [Hprofile [Htasks _]] Hnode.
  pose proof (proj1 (proj1 Htasks)) as Hpool.
  assert (Hslot : task_slot_in_range sg owner).
  { apply (proj2 (Hpool owner)); left; exists node; exact Hnode. }
  pose proof (proj1 Hprofile) as Hstable.
  assert (Hin : In sg.(g_OSTCBTbl) (stable_global_addresses sg))
    by (unfold stable_global_addresses; simpl; tauto).
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable Hin) as Hbase.
  assert (Hsize : task_object_size sg.(osKernelConfig) = 64).
  { apply task_object_size_tcb64; unfold selected_kernel_profile in Hprofile; tauto. }
  rewrite task_slot_addr_object_size, Hsize; unfold task_slot_in_range in Hslot; lia.
Qed.

(** This consumes exactly the source helper's result on the physical table
    AFTER the NULL store. The permanent slot gives a real scan hit, excludes
    the helper's literal fallback, and proves that relocation cannot write
    another task's slot or the released ceiling. Suspended and noncurrent
    owners remain in the domain; no ready/last-held-lock premise is added. *)
Lemma mutex_del_owner_scan_properties : forall sg entry eid event mutex owner priority,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  task_slot_addr sg owner <> 1 ->
  (forall node, entry.(TskState).(inUsedTaskStates) owner = Some node ->
    mutex_effective_priority_result
      (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
      (task_slot_addr sg owner) node.(curPrio) priority) ->
  exists node base,
    entry.(TskState).(inUsedTaskStates) owner = Some node /\
    task_base_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner base /\
    task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority /\
    node.(curPrio) <= priority <= base /\
    task_priority_in_range sg priority /\ priority <> mutex.(mfPCP) /\
    entry.(TskState).(prioTbl) priority = PTTask owner.
Proof.
  intros sg entry eid event mutex owner priority Hvalid Hevent Htype Hmutex Howner
    Henabled Hnotreserved Hscan.
  destruct Hvalid as [Hprofile [Htasks [Hready [Hevents [Hcross Hrest]]]]].
  destruct Hcross as [Htables [Hsnapshots Hother]].
  destruct (Hsnapshots eid event mutex owner Hevent Htype Hmutex Howner)
    as [node [base [snapshot [Hnode [Hbase Hsnapshot]]]]].
  destruct Htables as [Hcreators [Hslots Halias]].
  destruct (Halias owner node Hnode) as [otherbase [_ [Hcurrent Hclaims]]].
  assert (Hvalid : UCOS2_state_inv sg entry).
  { split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hready|].
    split; [exact Hevents|]; split; [|exact Hrest].
    split; [split; [exact Hcreators|]; split; assumption|].
    split; assumption. }
  pose proof (mutex_del_live_task_pointer_nonzero sg entry owner node Hvalid Hnode) as Hnonzero.
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hreleased : task_base_priority sg
    (mutex_del_released_table entry mutex.(mfPCP)) owner base).
  { unfold mutex_del_released_table; eapply mutex_owner_release_preserves_base_priority;
      eauto; right; reflexivity. }
  assert (Heffective : task_effective_priority sg
    (mutex_del_released_table entry mutex.(mfPCP)) owner priority).
  { eapply mutex_effective_priority_result_implies_task_effective_priority
      with (witness := base)
        (entries := mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
        (pointer := task_slot_addr sg owner) (fallback := node.(curPrio)).
    - exact Hlowest.
    - intros p Hp; apply mutex_del_table_task_encoding; assumption.
    - exact (proj1 Hreleased).
    - exact (Hscan node Hnode). }
  pose proof (mutex_release_slot_effective_priority_monotone sg
    entry.(TskState).(prioTbl) owner node.(curPrio) priority mutex.(mfPCP) PTFree
    Hcurrent (or_intror eq_refl) Heffective) as Hmonotone.
  pose proof (task_effective_priority_le_base sg _ owner base priority Hreleased Heffective) as Hbound.
  pose proof (proj1 Heffective) as Hhit.
  unfold mutex_del_released_table in Hhit.
  apply task_priority_alias_remove_iff in Hhit; [|discriminate].
  destruct Hhit as [Hnotceiling [Hrange Horiginal]].
  exists node, base; split; [exact Hnode|]; split; [exact Hreleased|].
  split; [exact Heffective|]; split; [split; assumption|].
  split; [exact Hrange|]; split; assumption.
Qed.

Lemma mutex_del_released_resources_split_priority : forall sg entry ceiling owner node,
  selected_kernel_profile sg ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_del_released_resources sg entry ceiling |--
    mutex_del_priority_input sg entry ceiling owner node **
    mutex_del_priority_frame sg entry owner.
Proof.
  intros sg entry ceiling owner node Hprofile Hnode.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  sep_apply_l_atomic (mutex_del_released_resources_split_owner sg entry ceiling owner node Hnode).
  unfold mutex_del_owner_frame, sched_raw_rep, sched_physical_rep,
    mutex_del_priority_input, mutex_del_priority_frame.
  rewrite used_task_rep_tcb64, <- task_slot_addr_tcb64 by assumption.
  rewrite sched_rows_array_equiv.
  unfold store_prio_tbl, mutex_del_priority_values; entailer!.
Qed.

Lemma mutex_del_priority_input_fields : forall sg node,
  mutex_priority_image_fields (task_tcb64_image sg node) node.(curPrio)
    (tcb_x_of_prio node.(curPrio)) (tcb_y_of_prio node.(curPrio))
    (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio)).
Proof. intros; repeat split; reflexivity. Qed.

(** The relocation helper writes the scan hit back unchanged.  Its target
    is a real surviving alias, not the ceiling cell just cleared. *)
Lemma mutex_del_priority_values_rewrite_alias : forall sg table owner priority,
  0 <= priority < 64 -> table priority = PTTask owner ->
  replace_Znth priority (task_slot_addr sg owner) (mutex_del_priority_values sg table) =
    mutex_del_priority_values sg table.
Proof.
  intros sg table owner priority Hrange Halias.
  assert (Hvalue : task_slot_addr sg owner =
    Znth priority (mutex_del_priority_values sg table) 0).
  { rewrite mutex_del_priority_values_lookup by exact Hrange.
    rewrite Halias; reflexivity. }
  rewrite Hvalue; apply replace_Znth_Znth.
Qed.

Definition mutex_del_current_priority (entry : UCOS2_Verify_State)
  (owner : TaskID) (priority : Priority) : option Priority :=
  match entry.(SchedState).(curTaskID) with
  | Some current => if Z.eq_dec owner current then Some priority
                    else entry.(SchedState).(curSchedPrio)
  | None => entry.(SchedState).(curSchedPrio)
  end.

Lemma mutex_del_priority_current_eq : forall sg entry owner priority,
  task_slot_addr sg owner <> 0 ->
  mutex_priority_current (task_slot_addr sg owner)
    (encode_task_link sg entry.(SchedState).(curTaskID))
    (sched_priority_byte entry.(SchedState).(curSchedPrio)) priority =
  sched_priority_byte (mutex_del_current_priority entry owner priority).
Proof.
  intros sg entry owner priority Hnonnull.
  unfold mutex_priority_current, mutex_del_current_priority, encode_task_link.
  destruct entry.(SchedState).(curTaskID) as [current|].
  - destruct (Z.eq_dec owner current) as [->|Hneq].
    + destruct (Z.eq_dec (task_slot_addr sg current) (task_slot_addr sg current));
        [reflexivity|contradiction].
    + destruct (Z.eq_dec (task_slot_addr sg owner) (task_slot_addr sg current)) as [Heq|];
        [apply task_slot_addr_injective in Heq; contradiction|reflexivity].
  - destruct (Z.eq_dec (task_slot_addr sg owner) 0); [contradiction|reflexivity].
Qed.

Lemma mutex_del_noncurrent_priority_frame : forall entry owner priority,
  entry.(SchedState).(curTaskID) <> Some owner ->
  mutex_del_current_priority entry owner priority = entry.(SchedState).(curSchedPrio).
Proof.
  intros entry owner priority Hother; unfold mutex_del_current_priority.
  destruct entry.(SchedState).(curTaskID) as [current|]; [|reflexivity].
  destruct (Z.eq_dec owner current); [subst; contradiction|reflexivity].
Qed.

Lemma mutex_del_ready_observation_iff : forall sg tasks scheduler owner node,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) owner = Some node -> task_priority_in_range sg node.(curPrio) ->
  sched_ready_structure sg tasks scheduler ->
  (mutex_priority_was_ready (sched_row_values tasks scheduler.(readyList))
    (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)) = true <->
   In owner scheduler.(readyList)).
Proof.
  intros sg tasks scheduler owner node Hsg Hunique Hnode Hpriority
    [Hmembers [Hsorted Hnodup]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold valid_stable_glob_vars in Hsg; tauto).
  assert (Hy : 0 <= node.(curPrio) / 8 < 8).
  { unfold task_priority_in_range in Hpriority.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  unfold mutex_priority_was_ready, tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio.
  rewrite sched_row_values_Znth by exact Hy.
  rewrite Bool.negb_true_iff, Z.eqb_neq.
  split.
  - intro Hbit; destruct (in_dec Z.eq_dec owner scheduler.(readyList)) as [Hin|Habsent];
      [exact Hin|exfalso].
    apply Hbit; rewrite Z.land_comm; apply sched_bit_disjoint_tbl_or.
    + exact (proj1 Hpriority).
    + reflexivity.
    + intros slot found Hin Hfound.
      destruct (Hmembers slot Hin) as [other [Hother Hrange]].
      assert (found = other) by congruence; subst; exact (proj1 Hrange).
    + intros slot found Hin Hfound Heq.
      assert (slot = owner) by (eapply Hunique; eauto); subst; contradiction.
  - intros Hin Hzero.
    pose proof (encode_ready_tbl_or_permutation _ _ tasks (node.(curPrio) / 8)
      (remove_Z_eqb_perm_cons owner scheduler.(readyList) Hin Hnodup)) as Hperm.
    rewrite Hperm in Hzero.
    cbn [encode_ready_tbl_at_or fold_right] in Hzero.
    rewrite Hnode, Z.eqb_refl in Hzero.
    pose proof (f_equal (fun bits => Z.testbit bits (node.(curPrio) mod 8)) Hzero) as Htest.
    cbn beta in Htest.
    rewrite Z.land_spec, Z.lor_spec, Z.shiftl_1_l, Z.pow2_bits_eqb,
      Z.eqb_refl, Z.testbit_0_l in Htest; [discriminate|apply Z.mod_pos_bound; lia].
Qed.

Definition mutex_del_relocated_ready (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (scheduler : SchedAbstractState)
  (owner : TaskID) (node : TaskAbstractState) (priority : Priority) : list TaskID :=
  if mutex_priority_was_ready (sched_row_values tasks scheduler.(readyList))
       (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio))
  then insert_sorted_by
    (sched_task_key sg (glob_task_set_usedtask tasks owner (mutex_priority_task node priority)))
    owner (remove_Z_eqb owner scheduler.(readyList))
  else scheduler.(readyList).

Lemma mutex_del_relocated_ready_membership : forall sg tasks scheduler owner node priority slot,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) owner = Some node -> task_priority_in_range sg node.(curPrio) ->
  sched_ready_structure sg tasks scheduler ->
  (In slot (mutex_del_relocated_ready sg tasks scheduler owner node priority) <->
   In slot scheduler.(readyList)).
Proof.
  intros sg tasks scheduler owner node priority slot Hsg Hunique Hnode Hpriority Hready.
  unfold mutex_del_relocated_ready.
  destruct (mutex_priority_was_ready _ _ _) eqn:Hwas; [|reflexivity].
  apply (proj1 (mutex_del_ready_observation_iff sg tasks scheduler owner node
    Hsg Hunique Hnode Hpriority Hready)) in Hwas.
  rewrite insert_sorted_by_in; simpl; split.
  - intros [<-|Hin]; [exact Hwas|eapply remove_Z_eqb_in; exact Hin].
  - intro Hin; destruct (Z.eq_dec slot owner) as [->|Hneq]; [left; reflexivity|].
    right; apply remove_Z_eqb_in_neq; assumption.
Qed.

Lemma mutex_del_ready_insert_encoding : forall tasks key owner node ids,
  tasks.(inUsedTaskStates) owner = Some node ->
  encode_ready_grp (insert_sorted_by key owner ids) tasks =
    Z.lor (encode_ready_grp ids tasks) (tcb_bit_y_of_prio node.(curPrio)) /\
  forall row, encode_ready_tbl_at_or (insert_sorted_by key owner ids) tasks row =
    if Z.eqb row (tcb_y_of_prio node.(curPrio))
    then Z.lor (encode_ready_tbl_at_or ids tasks row) (tcb_bit_x_of_prio node.(curPrio))
    else encode_ready_tbl_at_or ids tasks row.
Proof.
  intros tasks key owner node ids Hnode.
  pose proof (insert_sorted_by_perm Z key owner ids) as Hperm; split.
  - transitivity (encode_ready_grp (owner :: ids) tasks).
    { symmetry; exact (encode_ready_grp_permutation _ _ tasks Hperm). }
    cbn [encode_ready_grp]; rewrite Hnode; apply Z.lor_comm.
  - intro row; transitivity (encode_ready_tbl_at_or (owner :: ids) tasks row).
    { symmetry; exact (encode_ready_tbl_or_permutation _ _ tasks row Hperm). }
    cbn [encode_ready_tbl_at_or fold_right]; rewrite Hnode.
    unfold tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio.
    rewrite Z.eqb_sym; destruct (Z.eqb row (node.(curPrio) / 8));
      [apply Z.lor_comm|reflexivity].
Qed.

Lemma mutex_del_ready_insert_row_values : forall tasks key owner node ids,
  tasks.(inUsedTaskStates) owner = Some node -> 0 <= tcb_y_of_prio node.(curPrio) < 8 ->
  sched_row_values tasks (insert_sorted_by key owner ids) =
  replace_Znth (tcb_y_of_prio node.(curPrio))
    (Z.lor (Znth (tcb_y_of_prio node.(curPrio)) (sched_row_values tasks ids) 0)
      (tcb_bit_x_of_prio node.(curPrio))) (sched_row_values tasks ids).
Proof.
  intros tasks key owner node ids Hnode Hrow.
  rewrite sched_row_values_Znth by exact Hrow.
  destruct (mutex_del_ready_insert_encoding tasks key owner node ids Hnode) as [_ Hencoding].
  unfold sched_row_values.
  change (map (encode_ready_tbl_at_or (insert_sorted_by key owner ids) tasks) (Zrange 0 8) =
    replace_Znth (tcb_y_of_prio node.(curPrio))
      (Z.lor (encode_ready_tbl_at_or ids tasks (tcb_y_of_prio node.(curPrio)))
        (tcb_bit_x_of_prio node.(curPrio)))
      (map (encode_ready_tbl_at_or ids tasks) (Zrange 0 8))).
  rewrite <- map_Zrange_update by exact Hrow.
  apply map_ext; intro row; rewrite Hencoding.
  destruct (Z.eq_dec row (tcb_y_of_prio node.(curPrio))) as [->|Hneq].
  - rewrite Z.eqb_refl; reflexivity.
  - apply Z.eqb_neq in Hneq; rewrite Hneq; reflexivity.
Qed.

(** This is the exact bitmap result of the native helper.  A non-ready
    owner stays absent, including a suspended owner; a ready owner moves
    its bit without changing membership.  No high-ready refresh is used. *)
Lemma mutex_del_relocated_ready_encoding : forall sg tasks scheduler owner node priority,
  valid_stable_glob_vars sg -> task_in_range sg tasks -> sched_in_range sg tasks scheduler ->
  tasks.(inUsedTaskStates) owner = Some node -> 0 <= priority < 64 ->
  let updated := glob_task_set_usedtask tasks owner (mutex_priority_task node priority) in
  let ready := mutex_del_relocated_ready sg tasks scheduler owner node priority in
  encode_ready_grp ready updated =
    mutex_priority_group (sched_row_values tasks scheduler.(readyList))
      (encode_ready_grp scheduler.(readyList) tasks) (tcb_y_of_prio node.(curPrio))
      (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio)) priority /\
  sched_row_values updated ready =
    mutex_priority_rows (sched_row_values tasks scheduler.(readyList))
      (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)) priority.
Proof.
  intros sg tasks scheduler owner node priority Hsg Htasks Hsched Hnode Hpriority; cbn zeta.
  assert (Hunique : task_priority_unique tasks) by (unfold task_in_range in Htasks; tauto).
  assert (Hold : task_priority_in_range sg node.(curPrio)).
  { unfold task_in_range in Htasks; intuition eauto. }
  pose proof (sched_ready_in_range_implies_structure sg tasks scheduler (proj1 Hsched)) as Hstructure.
  assert (Hy : 0 <= tcb_y_of_prio node.(curPrio) < 8).
  { assert (Hlowest : sg.(osLowestPrio) = 63)
      by (unfold valid_stable_glob_vars in Hsg; tauto).
    unfold tcb_y_of_prio, task_priority_in_range in *.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hnewrow : 0 <= tcb_y_of_prio priority < 8).
  { unfold tcb_y_of_prio; split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hnew : (glob_task_set_usedtask tasks owner (mutex_priority_task node priority)).(inUsedTaskStates)
    owner = Some (mutex_priority_task node priority)) by (simpl; rewrite Z.eqb_refl; reflexivity).
  unfold mutex_del_relocated_ready, mutex_priority_group, mutex_priority_rows.
  destruct (mutex_priority_was_ready _ _ _) eqn:Hwas.
  - pose proof (proj1 (mutex_del_ready_observation_iff sg tasks scheduler owner node
      Hsg Hunique Hnode Hold Hstructure) Hwas) as Hin.
    pose proof (sched_remove_ready_member_row_values sg tasks scheduler owner node
      (mutex_priority_task node priority) Hsg Htasks Hsched Hnode Hin Hy) as Hremovedrows.
    destruct (sched_remove_ready_member_encoding sg tasks scheduler owner node
      (mutex_priority_task node priority) Hsg Htasks Hsched Hnode Hin) as [Hremovedgroup _].
    cbn [sched_remove_ready_task sched_set_ready readyList] in Hremovedgroup, Hremovedrows.
    destruct (mutex_del_ready_insert_encoding _
      (sched_task_key sg (glob_task_set_usedtask tasks owner (mutex_priority_task node priority)))
      owner (mutex_priority_task node priority)
      (remove_Z_eqb owner scheduler.(readyList)) Hnew) as [Hgroup _].
    split.
    + rewrite Hgroup, Hremovedgroup.
      unfold ready_group_after_relocation, mutex_priority_cleared_row,
        tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio, tcb_bit_y_of_prio.
      rewrite sched_row_values_Znth by exact Hy; reflexivity.
    + rewrite (mutex_del_ready_insert_row_values _
        (sched_task_key sg (glob_task_set_usedtask tasks owner (mutex_priority_task node priority)))
        owner (mutex_priority_task node priority)
        (remove_Z_eqb owner scheduler.(readyList)) Hnew Hnewrow).
      change (replace_Znth (tcb_y_of_prio priority)
        (Z.lor (Znth (tcb_y_of_prio priority)
          (sched_row_values (glob_task_set_usedtask tasks owner (mutex_priority_task node priority))
            (sched_remove_ready_task scheduler owner).(readyList)) 0)
          (tcb_bit_x_of_prio priority))
        (sched_row_values (glob_task_set_usedtask tasks owner (mutex_priority_task node priority))
          (sched_remove_ready_task scheduler owner).(readyList)) =
        replace_Znth (tcb_y_of_prio priority)
          (Z.lor (Znth (tcb_y_of_prio priority)
            (mutex_priority_removed_rows (sched_row_values tasks scheduler.(readyList))
              (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio))) 0)
            (tcb_bit_x_of_prio priority))
          (mutex_priority_removed_rows (sched_row_values tasks scheduler.(readyList))
            (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)))).
      cbn [sched_remove_ready_task sched_set_ready readyList]; rewrite Hremovedrows.
      unfold mutex_priority_removed_rows; rewrite Hwas.
      unfold mutex_priority_cleared_row; rewrite sched_row_values_Znth by exact Hy; reflexivity.
  - assert (Habsent : ~ In owner scheduler.(readyList)).
    { intro Hin; apply (proj2 (mutex_del_ready_observation_iff sg tasks scheduler owner node
        Hsg Hunique Hnode Hold Hstructure)) in Hin; congruence. }
    destruct (sched_encoding_priority_ext scheduler.(readyList)
      (glob_task_set_usedtask tasks owner (mutex_priority_task node priority)) tasks
      ltac:(intros slot Hin; simpl; destruct (Z.eqb slot owner) eqn:E; [|reflexivity];
        apply Z.eqb_eq in E; subst slot; contradiction)) as [Hgroup Hrows].
    split; [exact Hgroup|]. unfold sched_row_values; apply map_ext; exact Hrows.
Qed.

Definition mutex_del_relocated_tasks (entry : UCOS2_Verify_State) (ceiling : Priority)
  (owner : TaskID) (node : TaskAbstractState) (priority : Priority) : Glob_TaskAbstractState :=
  let updated := glob_task_set_usedtask entry.(TskState) owner (mutex_priority_task node priority) in
  {| inUsedTaskStates := updated.(inUsedTaskStates);
     unUsedTaskStates := updated.(unUsedTaskStates);
     tcbListHead := updated.(tcbListHead);
     prioTbl := mutex_del_released_table entry ceiling;
     taskRegNextID := updated.(taskRegNextID);
     parkedTaskStacks := updated.(parkedTaskStacks);
     taskLifecycle := updated.(taskLifecycle);
     taskCount := updated.(taskCount) |}.

Definition mutex_del_relocated_sched (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (owner : TaskID) (node : TaskAbstractState) (priority : Priority) : SchedAbstractState :=
  {| readyList := mutex_del_relocated_ready sg entry.(TskState) entry.(SchedState) owner node priority;
     curTaskID := entry.(SchedState).(curTaskID);
     curSchedPrio := mutex_del_current_priority entry owner priority;
     highRdyTid := entry.(SchedState).(highRdyTid);
     highRdyPrio := entry.(SchedState).(highRdyPrio);
     ctxSwCtr := entry.(SchedState).(ctxSwCtr);
     isRunning := entry.(SchedState).(isRunning) |}.

(** Raw source stage after PCP release and optional owner relocation, before
    Event removal.  The still-live Mutex record can still claim the now-free
    ceiling, so this intermediate state is deliberately not a full invariant. *)
Definition mutex_del_relocated_state (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (ceiling : Priority) (owner : TaskID) (node : TaskAbstractState) (priority : Priority)
  : UCOS2_Verify_State :=
  replace_SchedS (mutex_del_relocated_sched sg entry owner node priority)
    (replace_TskS (mutex_del_relocated_tasks entry ceiling owner node priority) entry).

Definition mutex_del_priority_output (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (ceiling : Priority) (owner : TaskID) (node : TaskAbstractState) (priority : Priority) : Assertion :=
  tcb64_storage_rep (task_slot_addr sg owner)
    (mutex_priority_image (task_tcb64_image sg node) priority) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (replace_Znth priority (task_slot_addr sg owner)
      (mutex_del_priority_values sg (mutex_del_released_table entry ceiling))) **
  UCharArray.full sg.(g_OSRdyTbl) 8
    (mutex_priority_rows (sched_row_values entry.(TskState) entry.(SchedState).(readyList))
      (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)) priority) **
  sg.(g_OSRdyGrp) # UChar |->
    mutex_priority_group (sched_row_values entry.(TskState) entry.(SchedState).(readyList))
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
      (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio))
      (tcb_bit_y_of_prio node.(curPrio)) priority **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg entry.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> mutex_priority_current (task_slot_addr sg owner)
    (encode_task_link sg entry.(SchedState).(curTaskID))
    (sched_priority_byte entry.(SchedState).(curSchedPrio)) priority.

Lemma mutex_del_relocated_tasks_lookup : forall entry ceiling owner node priority,
  (mutex_del_relocated_tasks entry ceiling owner node priority).(inUsedTaskStates) owner =
    Some (mutex_priority_task node priority).
Proof. intros; simpl; rewrite Z.eqb_refl; reflexivity. Qed.

Lemma mutex_del_relocated_tasks_priority_unique : forall entry ceiling owner node priority,
  task_current_prio_registered entry.(TskState) -> task_priority_unique entry.(TskState) ->
  entry.(TskState).(prioTbl) priority = PTTask owner ->
  task_priority_unique (mutex_del_relocated_tasks entry ceiling owner node priority).
Proof.
  intros entry ceiling owner node priority Hregistered Hunique Halias tid1 tid2 t1 t2 H1 H2 Hp.
  cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates] in H1, H2.
  destruct (Z.eqb tid1 owner) eqn:E1; destruct (Z.eqb tid2 owner) eqn:E2.
  - apply Z.eqb_eq in E1, E2; congruence.
  - injection H1 as H1; subst t1; cbn [mutex_priority_task curPrio] in Hp.
    specialize (Hregistered tid2 t2 H2); rewrite <- Hp, Halias in Hregistered.
    apply Z.eqb_eq in E1; congruence.
  - injection H2 as H2; subst t2; cbn [mutex_priority_task curPrio] in Hp.
    specialize (Hregistered tid1 t1 H1); rewrite Hp, Halias in Hregistered.
    apply Z.eqb_eq in E2; congruence.
  - eapply Hunique; eassumption.
Qed.

(** The owner-use source protocol, not non-readiness, justifies the Event
    frame.  These helpers never update another Event's waiting bitmap. *)
Lemma mutex_del_relocated_event_encoding : forall entry ceiling owner node priority,
  (forall eid event, entry.(EventState).(inUsedEventStates) eid = Some event ->
    ~ In owner event.(waitList)) ->
  event_raw_encoding_agrees entry.(TskState)
    (mutex_del_relocated_tasks entry ceiling owner node priority) entry.(EventState).
Proof.
  intros entry ceiling owner node priority Habsent.
  apply event_wait_priority_agreement_encodes; intros eid event slot Hevent Hin.
  cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot owner) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E; subst slot; exfalso; exact (Habsent eid event Hevent Hin).
Qed.

Lemma mutex_del_relocated_other_modules_eq : forall sg entry ceiling owner node priority,
  (forall eid event, entry.(EventState).(inUsedEventStates) eid = Some event ->
    ~ In owner event.(waitList)) ->
  UCOS2_raw_rep_missing_task_storage_sched sg entry =
  UCOS2_raw_rep_missing_task_storage_sched sg
    (mutex_del_relocated_state sg entry ceiling owner node priority).
Proof.
  intros sg entry ceiling owner node priority Habsent.
  unfold UCOS2_raw_rep_missing_task_storage_sched.
  cbn [mutex_del_relocated_state replace_TskS replace_SchedS
    TskState SchedState IntrState EventState TickState FlagState MemoryState TimerState
    StatsState ControlState NameState mutex_del_relocated_tasks glob_task_set_usedtask parkedTaskStacks].
  rewrite (event_raw_rep_change_task_index sg entry.(TskState)
    (mutex_del_relocated_tasks entry ceiling owner node priority) entry.(EventState)
    (mutex_del_relocated_event_encoding entry ceiling owner node priority Habsent)).
  reflexivity.
Qed.

(** Consume the complete native RdyAtPrio Ensure and its disjoint caller
    frame.  The result is the one source-stage raw heap, not a post-validity
    premise or a fabricated full invariant while the Event is still live. *)
Lemma mutex_del_priority_output_merge_raw : forall sg entry ceiling owner node priority,
  UCOS2_state_inv sg entry ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> 0 <= priority < 64 ->
  mutex_del_released_table entry ceiling priority = PTTask owner ->
  (forall eid event, entry.(EventState).(inUsedEventStates) eid = Some event ->
    ~ In owner event.(waitList)) ->
  mutex_del_priority_output sg entry ceiling owner node priority **
    mutex_del_priority_frame sg entry owner |--
  UCOS2_raw_rep sg (mutex_del_relocated_state sg entry ceiling owner node priority).
Proof.
  intros sg entry ceiling owner node priority Hvalid Hnode Hpriority Halias Habsent.
  pose proof Hvalid as [Hprofile [Htasks [Hsched Hrest]]].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (mutex_del_live_task_pointer_nonzero sg entry owner node Hvalid Hnode) as Hnonnull.
  destruct (mutex_del_relocated_ready_encoding sg entry.(TskState) entry.(SchedState)
    owner node priority (proj1 Hprofile) Htasks Hsched Hnode Hpriority) as [Hgroup Hrows].
  set (updated := mutex_del_relocated_tasks entry ceiling owner node priority).
  set (ready := mutex_del_relocated_ready sg entry.(TskState) entry.(SchedState) owner node priority).
  destruct (sched_encoding_priority_ext ready updated
    (glob_task_set_usedtask entry.(TskState) owner (mutex_priority_task node priority))
    ltac:(intros; reflexivity)) as [Hgroup_index Hrows_index].
  assert (Hrow_values : sched_row_values updated ready =
    sched_row_values (glob_task_set_usedtask entry.(TskState) owner
      (mutex_priority_task node priority)) ready).
  { unfold sched_row_values; apply map_ext; exact Hrows_index. }
  fold ready in Hgroup, Hrows.
  rewrite <- Hgroup_index in Hgroup; rewrite <- Hrow_values in Hrows.
  pose proof (used_task_rep_tcb64 sg owner (mutex_priority_task node priority) Hmulti Hprofiling) as Htcb.
  rewrite <- task_slot_addr_tcb64 in Htcb by assumption.
  assert (Hoff : forall slot, slot <> owner ->
    entry.(TskState).(inUsedTaskStates) slot = updated.(inUsedTaskStates) slot).
  { intros slot Hneq; unfold updated; cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates].
    apply Z.eqb_neq in Hneq; rewrite Hneq; reflexivity. }
  unfold mutex_del_priority_output.
  rewrite mutex_priority_image_task_eq, <- Htcb.
  rewrite mutex_del_priority_values_rewrite_alias by assumption.
  rewrite mutex_del_priority_current_eq by exact Hnonnull.
  rewrite <- Hgroup, <- Hrows.
  unfold mutex_del_priority_frame.
  rewrite (mutex_del_relocated_other_modules_eq sg entry ceiling owner node priority Habsent).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (used_task_rep sg)
    entry.(TskState).(inUsedTaskStates) updated.(inUsedTaskStates) owner Hoff)).
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) owner (mutex_priority_task node priority)
    updated.(inUsedTaskStates) (mutex_del_relocated_tasks_lookup entry ceiling owner node priority)).
  match goal with |- ?Pre |-- _ =>
    assert (Hpack : Pre |--
      task_public_storage sg updated **
      sched_raw_rep sg updated (mutex_del_relocated_sched sg entry owner node priority) **
      UCOS2_raw_rep_missing_task_storage_sched sg
        (mutex_del_relocated_state sg entry ceiling owner node priority))
  end.
  { unfold task_public_storage, store_used_task_map, store_prio_tbl, mutex_del_priority_values,
      sched_raw_rep, sched_physical_rep.
    rewrite sched_rows_array_equiv.
    unfold updated, ready, mutex_del_relocated_tasks, mutex_del_relocated_sched.
    cbn [glob_task_set_usedtask inUsedTaskStates unUsedTaskStates tcbListHead prioTbl
      taskCount taskLifecycle taskRegNextID parkedTaskStacks readyList curTaskID curSchedPrio
      highRdyTid highRdyPrio ctxSwCtr isRunning].
    entailer!. }
  match goal with |- _ |-- ?Post =>
    match type of Hpack with _ |-- ?Packed => assert (Hclose : Packed |-- Post) end
  end.
  { unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched; entailer!. }
  intros heap Howned; apply (Hclose heap); exact (Hpack heap Howned).
Qed.

Lemma mutex_del_relocated_sched_in_range : forall sg entry ceiling owner node priority,
  valid_stable_glob_vars sg -> task_in_range sg entry.(TskState) ->
  sched_in_range sg entry.(TskState) entry.(SchedState) ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_priority_in_range sg priority -> entry.(TskState).(prioTbl) priority = PTTask owner ->
  sched_in_range sg (mutex_del_relocated_tasks entry ceiling owner node priority)
    (mutex_del_relocated_sched sg entry owner node priority).
Proof.
  intros sg entry ceiling owner node priority Hsg Htasks Hsched Hnode Hpriority Halias.
  pose proof Hsched as [[Hmembers [Hsorted [Hcomplete Hnd]]] [Hhigh [Hcounter [Hcurrent Hcurprio]]]].
  assert (Hregistered : task_current_prio_registered entry.(TskState))
    by (unfold task_in_range in Htasks; tauto).
  assert (Hunique : task_priority_unique entry.(TskState))
    by (unfold task_in_range in Htasks; tauto).
  assert (Hold : task_priority_in_range sg node.(curPrio)).
  { unfold task_in_range in Htasks; intuition eauto. }
  pose proof (sched_ready_in_range_implies_structure sg entry.(TskState)
    entry.(SchedState) (proj1 Hsched)) as Hstructure.
  set (updated := mutex_del_relocated_tasks entry ceiling owner node priority).
  set (ready := mutex_del_relocated_ready sg entry.(TskState) entry.(SchedState) owner node priority).
  assert (Hmembership : forall slot, In slot ready <-> In slot entry.(SchedState).(readyList)).
  { intro slot; apply mutex_del_relocated_ready_membership; assumption. }
  assert (Hnewunique : task_priority_unique updated).
  { apply mutex_del_relocated_tasks_priority_unique; assumption. }
  assert (Hnewowner : updated.(inUsedTaskStates) owner = Some (mutex_priority_task node priority))
    by apply mutex_del_relocated_tasks_lookup.
  assert (Hkeyframe : forall slot, slot <> owner ->
    sched_task_key sg entry.(TskState) slot = sched_task_key sg updated slot).
  { intros slot Hneq; unfold sched_task_key, updated.
    cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates].
    apply Z.eqb_neq in Hneq; rewrite Hneq; reflexivity. }
  assert (Hpostmembers : forall slot, In slot ready -> exists found,
    updated.(inUsedTaskStates) slot = Some found /\ task_priority_in_range sg found.(curPrio) /\
    is_effectively_ready found.(stat) found.(dly) = true).
  { intros slot Hin; apply Hmembership in Hin.
    destruct (Hmembers slot Hin) as [old [Hlookup [Hrange Hready]]].
    unfold updated; cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb slot owner) eqn:E.
    - apply Z.eqb_eq in E; subst slot; assert (old = node) by congruence; subst old.
      exists (mutex_priority_task node priority); split; [reflexivity|]; split; assumption.
    - exists old; auto. }
  unfold sched_in_range; split.
  - change (sched_ready_in_range sg updated (mutex_del_relocated_sched sg entry owner node priority)).
    unfold sched_ready_in_range; cbn [mutex_del_relocated_sched readyList]; fold ready.
    split; [exact Hpostmembers|]; split.
    + change (strictly_sorted_by (sched_task_key sg updated) ready).
      unfold ready, mutex_del_relocated_ready.
      change (strictly_sorted_by (sched_task_key sg updated)
        (if mutex_priority_was_ready (sched_row_values entry.(TskState) entry.(SchedState).(readyList))
          (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio))
        then insert_sorted_by (sched_task_key sg updated) owner
          (remove_Z_eqb owner entry.(SchedState).(readyList))
        else entry.(SchedState).(readyList))).
      destruct (mutex_priority_was_ready _ _ _) eqn:Hwas.
      * apply insert_sorted_by_preserves.
        -- eapply strictly_sorted_by_key_eq_on; [|apply remove_Z_eqb_strictly_sorted_by; exact Hsorted].
           intros slot Hin; apply Hkeyframe; intro E; subst slot.
           exact (remove_Z_eqb_notin owner entry.(SchedState).(readyList) Hin).
        -- intros slot Hin Heq.
           assert (HinReady : In slot ready).
           { apply Hmembership; eapply remove_Z_eqb_in; exact Hin. }
           destruct (Hpostmembers slot HinReady) as [found [Hfound Hrest]].
           unfold sched_task_key in Heq; rewrite Hfound, Hnewowner in Heq.
           assert (slot = owner) by (eapply Hnewunique; eauto); subst slot.
           exact (remove_Z_eqb_notin owner entry.(SchedState).(readyList) Hin).
      * assert (Habsent : ~ In owner entry.(SchedState).(readyList)).
        { intro Hin; apply (proj2 (mutex_del_ready_observation_iff sg entry.(TskState)
            entry.(SchedState) owner node Hsg Hunique Hnode Hold Hstructure)) in Hin; congruence. }
        eapply strictly_sorted_by_key_eq_on; [|exact Hsorted].
        intros slot Hin; apply Hkeyframe; intro E; subst; contradiction.
    + split.
      * intros slot found Hfound Hready; apply Hmembership.
        unfold updated in Hfound; cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates] in Hfound.
        destruct (Z.eqb slot owner) eqn:E.
        -- apply Z.eqb_eq in E; subst slot; injection Hfound as E; subst found.
           eapply Hcomplete; [exact Hnode|exact Hready].
        -- eapply Hcomplete; eassumption.
      * unfold ready, mutex_del_relocated_ready.
        destruct (mutex_priority_was_ready _ _ _); [|exact Hnd].
        apply insert_sorted_by_preserves_NoDup; [apply remove_Z_eqb_NoDup; exact Hnd|apply remove_Z_eqb_notin].
  - split; [exact Hhigh|]; split; [exact Hcounter|]; split; [exact Hcurrent|].
    cbn [mutex_del_relocated_sched curSchedPrio]; unfold mutex_del_current_priority.
    destruct entry.(SchedState).(curTaskID) as [current|]; [|exact Hcurprio].
    destruct (Z.eq_dec owner current); [exact Hpriority|exact Hcurprio].
Qed.

Definition mutex_del_event_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  store_map_missing_i (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) eid **
  event_free_storage_rep sg state.(EventState) **
  task_public_storage sg state.(TskState) ** sched_raw_rep sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state.

Lemma mutex_del_raw_split_event : forall sg state eid node,
  state.(EventState).(inUsedEventStates) eid = Some node ->
  UCOS2_raw_rep sg state |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_image sg state.(TskState) node) **
  sg.(g_OSEventFreeList) # Ptr |->
    event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
  mutex_del_event_frame sg state eid.
Proof.
  intros sg state eid node Hnode.
  unfold UCOS2_raw_rep, task_shared_rep.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid node Hnode).
  unfold used_event_rep, event_raw_rep_no_eid, event_free_root_rep,
    mutex_del_event_frame, UCOS2_raw_rep_missing_task_storage_sched_event.
  entailer!.
Qed.

Lemma mutex_del_event_recycle_image_fields : forall sg free image,
  event_recycle_image sg free image EventTypeField = Some 0 /\
  event_recycle_image sg free image EventPtrField =
    Some (event_encode_pool_link sg (hd_error free)) /\
  event_recycle_image sg free image EventCntField = Some 0 /\
  (forall field, field <> EventTypeField -> field <> EventPtrField -> field <> EventCntField ->
    event_recycle_image sg free image field = image field).
Proof.
  intros; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  intros field Htype Hptr Hcnt; destruct field; try contradiction; reflexivity.
Qed.

(** This is the actual names-disabled Delete tail, after its Type/Ptr/Cnt
    stores and free-root publication.  It consumes the rewritten object;
    the same bytes become free-pool storage and disappear from the live map.
    The raw composition also works at the PCP-release intermediate stage:
    it does not require the non-Mutex premise of the shared Sem/Mbox
    full-invariant theorem or claim that Mutex validity follows from it. *)
Lemma mutex_del_recycle_event_merge_raw : forall sg state eid node image,
  event_pool_partition sg state.(EventState) ->
  event_free_storage_valid sg state.(EventState) ->
  state.(EventState).(inUsedEventStates) eid = Some node -> node.(queueFields) = None ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg state.(EventState).(unUsedEventStates) image) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
  mutex_del_event_frame sg state eid |--
  UCOS2_raw_rep sg (replace_EventS (event_recycle sg state.(EventState) eid image) state).
Proof.
  intros sg state eid node image Hpool Hfree Hnode Hqueue.
  unfold mutex_del_event_frame.
  sepcon_right_assoc.
  sep_apply_l_atomic (event_recycle_reconstructs_raw_rep sg state.(TskState)
    state.(EventState) eid node image Hpool Hfree Hnode).
  sep_apply_l_atomic (UCOS2_event_recycle_preserves_residual sg state eid node image Hnode Hqueue).
  unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched_event.
  cbn [replace_EventS TskState SchedState IntrState EventState TickState FlagState MemoryState
    TimerState StatsState ControlState NameState].
  entailer!.
Qed.

(** If the owner is NULL or the scan returns its unchanged priority, C
    skips RdyAtPrio.  This stage changes only the real ceiling cell; even a
    stale current-priority cache is preserved on that branch. *)
Definition mutex_del_released_tasks (entry : UCOS2_Verify_State) (ceiling : Priority)
  : Glob_TaskAbstractState :=
  let tasks := entry.(TskState) in
  {| inUsedTaskStates := tasks.(inUsedTaskStates);
     unUsedTaskStates := tasks.(unUsedTaskStates);
     tcbListHead := tasks.(tcbListHead);
     prioTbl := mutex_del_released_table entry ceiling;
     taskRegNextID := tasks.(taskRegNextID);
     parkedTaskStacks := tasks.(parkedTaskStacks);
     taskLifecycle := tasks.(taskLifecycle);
     taskCount := tasks.(taskCount) |}.

Definition mutex_del_released_state (entry : UCOS2_Verify_State) (ceiling : Priority)
  : UCOS2_Verify_State := replace_TskS (mutex_del_released_tasks entry ceiling) entry.

Lemma mutex_del_released_priority_frame_eq : forall sg entry ceiling,
  UCOS2_raw_rep_missing_priority_table sg entry =
  UCOS2_raw_rep_missing_priority_table sg (mutex_del_released_state entry ceiling).
Proof.
  intros; unfold UCOS2_raw_rep_missing_priority_table.
  rewrite (sched_raw_rep_change_task_index sg entry.(TskState)
    (mutex_del_released_tasks entry ceiling) entry.(SchedState) eq_refl),
    (UCOS2_raw_rep_missing_task_storage_sched_task_map_frame sg entry
      (mutex_del_released_tasks entry ceiling) eq_refl eq_refl).
  reflexivity.
Qed.

Lemma mutex_del_released_resources_raw_equiv : forall sg entry ceiling,
  mutex_del_released_resources sg entry ceiling --||--
  UCOS2_raw_rep sg (mutex_del_released_state entry ceiling).
Proof.
  intros; rewrite UCOS2_raw_rep_priority_table_equiv.
  unfold mutex_del_released_resources; rewrite (mutex_del_released_priority_frame_eq sg entry ceiling).
  split; reflexivity.
Qed.

Definition mutex_del_owner_priority_state (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (ceiling : Priority) (owner : TaskID)
  (node : TaskAbstractState) (priority : Priority) : UCOS2_Verify_State :=
  if Z.eq_dec node.(curPrio) priority then mutex_del_released_state entry ceiling
  else mutex_del_relocated_state sg entry ceiling owner node priority.

Lemma mutex_del_owner_priority_state_noncurrent : forall sg entry ceiling owner node priority,
  entry.(SchedState).(curTaskID) <> Some owner ->
  (mutex_del_owner_priority_state sg entry ceiling owner node priority).(SchedState).(curTaskID) =
    entry.(SchedState).(curTaskID) /\
  (mutex_del_owner_priority_state sg entry ceiling owner node priority).(SchedState).(curSchedPrio) =
    entry.(SchedState).(curSchedPrio) /\
  (mutex_del_owner_priority_state sg entry ceiling owner node priority).(SchedState).(highRdyTid) =
    entry.(SchedState).(highRdyTid) /\
  (mutex_del_owner_priority_state sg entry ceiling owner node priority).(SchedState).(highRdyPrio) =
    entry.(SchedState).(highRdyPrio).
Proof.
  intros; unfold mutex_del_owner_priority_state; destruct Z.eq_dec.
  - repeat split; reflexivity.
  - split; [reflexivity|]; split; [apply mutex_del_noncurrent_priority_frame; assumption|].
    split; reflexivity.
Qed.

(** The pure closing state is indexed by the ECB that the source actually
    recycles.  Clearing its ceiling alone is not an invariant-preserving
    operation while that same Mutex remains published. *)
Definition mutex_del_recycled_state (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (image : EventStorage) (ceiling : Priority)
  (owner : TaskID) (node : TaskAbstractState) (priority : Priority) : UCOS2_Verify_State :=
  replace_EventS (event_recycle sg entry.(EventState) eid image)
    (mutex_del_relocated_state sg entry ceiling owner node priority).

Lemma mutex_del_recycled_event_lookup : forall sg events eid image slot node,
  (event_recycle sg events eid image).(inUsedEventStates) slot = Some node <->
  slot <> eid /\ events.(inUsedEventStates) slot = Some node.
Proof.
  intros; cbn [event_recycle inUsedEventStates]; unfold kernel_map_set.
  destruct (Z.eq_dec slot eid); split; intros; intuition discriminate.
Qed.

Lemma mutex_del_owned_ceiling_slot : forall sg entry eid event mutex owner,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved \/
  entry.(TskState).(prioTbl) mutex.(mfPCP) = PTTask owner.
Proof.
  intros sg entry eid event mutex owner [_ [_ [_ [Hprotocol _]]]] He Htype Hm Ho Henabled.
  destruct (Hprotocol eid event mutex He Htype Hm) as [_ [_ [Hdisabled|[_ Hslot]]]].
  - contradiction.
  - destruct Hslot as [Hreserved|[tid [Htid Htask]]]; [left; exact Hreserved|].
    right; rewrite Ho in Htid; injection Htid as Htid; subst tid; exact Htask.
Qed.

Lemma mutex_del_released_base_priority : forall sg entry eid event mutex owner tid base,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  task_base_priority sg entry.(TskState).(prioTbl) tid base ->
  task_base_priority sg (mutex_del_released_table entry mutex.(mfPCP)) tid base.
Proof.
  intros sg entry eid event mutex owner tid base Hcross He Htype Hm Ho Henabled Hbase.
  destruct (Z.eq_dec tid owner) as [->|Hne].
  - unfold mutex_del_released_table; eapply mutex_owner_release_preserves_base_priority;
      try eassumption; [exact (proj1 (proj2 Hcross))|right; reflexivity].
  - pose proof (mutex_del_owned_ceiling_slot sg entry eid event mutex owner
      Hcross He Htype Hm Ho Henabled) as Hslot.
    eapply task_base_priority_alias_ext; [|exact Hbase].
    intro p; symmetry; apply task_priority_alias_foreign_write_iff.
    + destruct Hslot as [Hslot|Hslot]; rewrite Hslot; congruence.
    + discriminate.
Qed.

Lemma mutex_del_recycled_alias_consistency : forall sg entry eid event mutex owner node priority image,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  mutex_priority_alias_consistency sg
    (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority)
    (event_recycle sg entry.(EventState) eid image).
Proof.
  intros sg entry eid event mutex owner node priority image Hcross He Htype Hm Ho Henabled
    Hnode Heffective tid after Hafter.
  pose proof (proj2 (proj2 (proj1 Hcross))) as Halias.
  pose proof (mutex_del_owned_ceiling_slot sg entry eid event mutex owner
    Hcross He Htype Hm Ho Henabled) as Hslot.
  assert (Horigin : exists before, entry.(TskState).(inUsedTaskStates) tid = Some before /\
    (tid = owner /\ after = mutex_priority_task node priority \/
      tid <> owner /\ after = before)).
  { cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates] in Hafter.
    destruct (Z.eqb tid owner) eqn:E.
    - apply Z.eqb_eq in E; subst tid; injection Hafter as Hafter; subst after.
      exists node; auto.
    - apply Z.eqb_neq in E; exists after; auto. }
  destruct Horigin as [before [Hbefore Hcase]].
  destruct (Halias tid before Hbefore) as [base [Hbase [Hcurrent Hclaims]]].
  exists base; split.
  - eapply mutex_del_released_base_priority; eassumption.
  - split.
    + destruct Hcase as [[-> ->]|[Hne ->]]; [exact Heffective|].
      eapply task_effective_priority_alias_ext; [|exact Hcurrent].
      intro p; symmetry; apply task_priority_alias_foreign_write_iff.
      * destruct Hslot as [Hslot|Hslot]; rewrite Hslot; congruence.
      * discriminate.
    + intros p Hp; change (task_priority_alias sg
        (update_prio_tbl entry.(TskState).(prioTbl) mutex.(mfPCP) PTFree) tid p) in Hp.
      apply task_priority_alias_remove_iff in Hp; [|discriminate].
      destruct Hp as [Hne Hp]; destruct (Hclaims p Hp) as [HbaseEq|[Hlt Hclaim]];
        [left; exact HbaseEq|right; split; [exact Hlt|]].
      destruct Hclaim as [mid [e [m [Hget [Hty [Hfields [Howner [HmEnabled Hpcp]]]]]]]].
      exists mid, e, m; split.
      * apply mutex_del_recycled_event_lookup; split; [|exact Hget].
        intro E; subst mid; rewrite He in Hget; injection Hget as E; subst e.
        rewrite Hm in Hfields; injection Hfields as E; subst m; congruence.
      * repeat split; assumption.
Qed.

Lemma mutex_del_recycled_snapshot_in_range : forall sg entry eid event mutex owner node priority image,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_owner_snapshot_in_range sg
    (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority)
    (event_recycle sg entry.(EventState) eid image).
Proof.
  intros sg entry eid event mutex owner node priority image Hcross He Htype Hm Ho Henabled Hnode
    mid e m tid Hget Hty Hfields Howner.
  apply mutex_del_recycled_event_lookup in Hget; destruct Hget as [_ Hget].
  destruct (proj1 (proj2 Hcross) mid e m tid Hget Hty Hfields Howner)
    as [t [base [snapshot [Ht [Hbase Hrest]]]]].
  destruct (proj2 (glob_task_set_usedtask_live_iff entry.(TskState) owner node
    (mutex_priority_task node priority) tid Hnode) (ex_intro _ t Ht)) as [after Hafter].
  exists after, base, snapshot; split; [exact Hafter|].
  split; [exact (mutex_del_released_base_priority sg entry eid event mutex owner tid base
    Hcross He Htype Hm Ho Henabled Hbase)|exact Hrest].
Qed.

Lemma mutex_del_surviving_ceiling_ne : forall sg entry eid event mutex image mid e m,
  mutex_enabled_pcp_unique sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex_pcp_enabled sg mutex ->
  (event_recycle sg entry.(EventState) eid image).(inUsedEventStates) mid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m ->
  m.(mfPCP) <> mutex.(mfPCP).
Proof.
  intros sg entry eid event mutex image mid e m Hunique He Htype Hm Henabled Hget Hty Hfields E.
  apply mutex_del_recycled_event_lookup in Hget; destruct Hget as [Hne Hget].
  apply Hne; eapply Hunique; eauto; congruence.
Qed.

Lemma mutex_del_recycled_table_consistency : forall sg entry eid event mutex owner node priority image,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  task_mutex_priotbl_consistency sg
    (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority)
    (event_recycle sg entry.(EventState) eid image).
Proof.
  intros sg entry eid event mutex owner node priority image Hcross He Htype Hm Ho Henabled
    Hnode Heffective.
  pose proof Hcross as [[Hcreator [Hslots Halias]] [_ [_ [_ [Hunique _]]]]].
  split.
  - intros p reservation Hr [mid [e [m [Hget [Hty [Hfields Hclaim]]]]]].
    apply mutex_del_recycled_event_lookup in Hget; destruct Hget as [_ Hget].
    apply (Hcreator p reservation Hr); exists mid, e, m; auto.
  - split.
    + intros p Hp; cbn [mutex_del_relocated_tasks prioTbl]; unfold mutex_del_released_table,
        update_prio_tbl; destruct (Z.eq_dec p mutex.(mfPCP)) as [->|Hne].
      * intros [mid [e [m [Hget [Hty [Hfields [_ Hpcp]]]]]]].
        exact (mutex_del_surviving_ceiling_ne sg entry eid event mutex image mid e m
          Hunique He Htype Hm Henabled Hget Hty Hfields Hpcp).
      * specialize (Hslots p Hp); destruct (entry.(TskState).(prioTbl) p) as [| |slot].
        -- intros [mid [e [m [Hget Hrest]]]]; apply Hslots; exists mid, e, m.
           split; [apply mutex_del_recycled_event_lookup in Hget; tauto|exact Hrest].
        -- destruct Hslots as [Hreservation|[Hclaim|Hpending]].
           ++ left; exact Hreservation.
           ++ right; left; destruct Hclaim as [mid [e [m [Hget [Hty [Hfields Hclaim]]]]]].
              exists mid, e, m; split; [|auto].
              apply mutex_del_recycled_event_lookup; split; [|exact Hget].
              intro E; subst mid; rewrite He in Hget; injection Hget as E; subst e.
              rewrite Hm in Hfields; injection Hfields as E; subst m.
              destruct Hclaim as [_ Hpcp]; congruence.
           ++ right; right; exact Hpending.
        -- destruct Hslots as [t Ht].
           apply (proj2 (glob_task_set_usedtask_live_iff entry.(TskState) owner node
             (mutex_priority_task node priority) slot Hnode)); exists t; exact Ht.
    + eapply mutex_del_recycled_alias_consistency; eassumption.
Qed.

Lemma mutex_del_relocated_tasks_in_range : forall sg entry eid event mutex owner node priority,
  task_in_range sg entry.(TskState) -> cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  task_in_range sg (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority
    [Hpool [Hactive [Hfree [Hreservations [Hgenerations [Hregistered [Hunique [Hpriority Hrest]]]]]]]]
    Hcross He Htype Hm Ho Henabled Hnode Heffective.
  pose proof (mutex_del_recycled_alias_consistency sg entry eid event mutex owner node priority (fun _ => None)
    Hcross He Htype Hm Ho Henabled Hnode Heffective) as Halias.
  assert (Hlive : forall slot,
    (exists t, (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority).(inUsedTaskStates) slot = Some t) <->
    (exists t, entry.(TskState).(inUsedTaskStates) slot = Some t)).
  { intro slot; apply glob_task_set_usedtask_live_iff with (old := node); exact Hnode. }
  assert (Horigin : forall slot t,
    (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority).(inUsedTaskStates) slot = Some t ->
    exists before, entry.(TskState).(inUsedTaskStates) slot = Some before /\
      t.(taskGeneration) = before.(taskGeneration)).
  { intros slot t Ht; cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates] in Ht.
    destruct (Z.eqb slot owner) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Ht as E; subst t; exists node; auto.
    - exists t; auto. }
  split.
  - destruct Hpool as [Hdomain [Hused [Hprivate [Hnd [Hstorage HreservationUnique]]]]].
    split.
    + intro slot; rewrite Hlive; exact (Hdomain slot).
    + split.
      * intros slot t Ht; destruct (Horigin slot t Ht) as [before [Hb _]]; exact (Hused slot before Hb).
      * split; [exact Hprivate|]. split; [exact Hnd|]. split; [exact Hstorage|exact HreservationUnique].
  - split.
    + destruct Hactive as [Hnd [Hhead [Hcount [Hcover Hlinks]]]].
      split; [exact Hnd|]. split; [exact Hhead|]. split; [exact Hcount|]. split.
      * intro slot; rewrite Hlive; exact (Hcover slot).
      * eapply task_active_links_update; try eassumption; reflexivity.
    + split; [exact Hfree|]. split.
      * destruct Hreservations as [Hentries HuniqueInvocation]; split; [|exact HuniqueInvocation].
        intros p reservation Hr; destruct (Hentries p reservation Hr) as [Hp [Hslot Hinv]].
        split; [exact Hp|]. split; [|exact Hinv].
        cbn [mutex_del_relocated_tasks prioTbl]; unfold mutex_del_released_table.
        rewrite update_prio_tbl_other; [exact Hslot|].
        intro E; subst p; apply (proj1 (proj1 Hcross) mutex.(mfPCP) reservation Hr).
        exists eid, event, mutex; repeat split; assumption || reflexivity.
      * split.
        -- destruct Hgenerations as [Hgenerations Hother]; split; [|exact Hother].
           intros slot t Ht; destruct (Horigin slot t Ht) as [before [Hb Hg]].
           cbn [mutex_del_relocated_tasks glob_task_set_usedtask taskLifecycle]; rewrite Hg.
           exact (Hgenerations slot before Hb).
        -- split; [eapply mutex_priority_alias_consistency_current_registered; exact Halias|].
           split; [eapply mutex_priority_alias_consistency_priority_unique; exact Halias|].
           split; [|exact Hrest]. intros slot t Ht.
           destruct (Halias slot t Ht) as [base [_ [[[Hp _] _] _]]]; exact Hp.
Qed.

Lemma mutex_del_empty_event_remove_wait_consistency : forall sg s eid event image,
  s.(EventState).(inUsedEventStates) eid = Some event -> event.(waitList) = [] ->
  event_wait_object_consistency sg s ->
  event_wait_object_consistency sg (replace_EventS (event_recycle sg s.(EventState) eid image) s).
Proof.
  intros sg s eid event image He Hempty [Hentries [Hback Hclosed]].
  assert (Hsafe : forall tid t, s.(TskState).(inUsedTaskStates) tid = Some t ->
    t.(eventPtr) <> Some eid /\ ~ In eid t.(eventMultiWaitEvents)).
  { intros tid t Ht; split; intro Href;
      pose proof (Hback tid t eid event Ht He ltac:(auto)) as Hin;
      rewrite Hempty in Hin; contradiction. }
  split.
  - intros slot e Hget; apply mutex_del_recycled_event_lookup in Hget.
    exact (Hentries slot e (proj2 Hget)).
  - split.
    + intros tid t slot e Ht Hget Href; apply mutex_del_recycled_event_lookup in Hget.
      exact (Hback tid t slot e Ht (proj2 Hget) Href).
    + intros tid t Ht; destruct (Hclosed tid t Ht) as [Hsingle Hmulti].
      destruct (Hsafe tid t Ht) as [HnoSingle HnoMulti]; split.
      * intros slot Hptr; destruct (Hsingle slot Hptr) as [e Hget]; exists e.
        apply mutex_del_recycled_event_lookup; split; [congruence|exact Hget].
      * intros slot Hin; destruct (Hmulti slot Hin) as [e Hget]; exists e.
        apply mutex_del_recycled_event_lookup; split; [intro E; subst slot; contradiction|exact Hget].
Qed.

Lemma mutex_del_recycled_cross_module_consistency : forall sg entry eid event mutex owner node priority image,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex -> event.(waitList) = [] ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  cross_module_consistency sg
    (mutex_del_recycled_state sg entry eid image mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority image Hcross He Htype Hm Ho Henabled Hempty
    Hnode Heffective Habsent.
  pose proof Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  split.
  - exact (mutex_del_recycled_table_consistency sg entry eid event mutex owner node priority image
      Hcross He Htype Hm Ho Henabled Hnode Heffective).
  - split.
    + exact (mutex_del_recycled_snapshot_in_range sg entry eid event mutex owner node priority image
        Hcross He Htype Hm Ho Henabled Hnode).
    + split.
      * apply (mutex_del_empty_event_remove_wait_consistency sg
          (mutex_del_relocated_state sg entry mutex.(mfPCP) owner node priority)
          eid event image He Hempty).
        change (event_wait_object_consistency sg
          (replace_TskS (glob_task_set_usedtask entry.(TskState) owner (mutex_priority_task node priority)) entry)).
        eapply event_wait_object_update_unlisted_task; try eassumption; reflexivity.
      * split.
        -- intros mid e m Hget Hty Hfields.
           assert (Hne : m.(mfPCP) <> mutex.(mfPCP)).
           { exact (mutex_del_surviving_ceiling_ne sg entry eid event mutex image mid e m
               Hunique He Htype Hm Henabled Hget Hty Hfields). }
           apply mutex_del_recycled_event_lookup in Hget; destruct Hget as [_ Hget].
           destruct (Hprotocol mid e m Hget Hty Hfields) as [Hrange [Howner Hslot]].
           split; [exact Hrange|]. split; [exact Howner|].
           cbn [mutex_del_recycled_state mutex_del_relocated_state replace_EventS replace_SchedS
             replace_TskS TskState mutex_del_relocated_tasks prioTbl].
           unfold mutex_del_released_table; rewrite update_prio_tbl_other by exact Hne; exact Hslot.
        -- split.
           ++ eapply mutex_enabled_pcp_unique_transport with (lvs1 := entry); [|exact Hunique].
              intros mid e m Hget Hty Hfields; apply mutex_del_recycled_event_lookup in Hget.
              exists e, m; intuition.
           ++ split; [|exact Htimer].
              change (task_flag_waiter_consistency sg
                (glob_task_set_usedtask entry.(TskState) owner (mutex_priority_task node priority)) entry.(FlagState)).
              eapply task_flag_waiter_consistency_update_task;
                [exact Hnode|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflags];
                intros H; exact H.
Qed.

Lemma mutex_del_recycled_pending_mutex_consistency : forall sg entry eid event mutex owner node priority image,
  pending_mutex_consistency sg entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex_pcp_enabled sg mutex ->
  pending_mutex_consistency sg
    (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority)
    (event_recycle sg entry.(EventState) eid image).
Proof.
  intros sg entry eid event mutex owner node priority image Hpending He Htype Hm Henabled.
  eapply pending_mutex_consistency_event_transport with (events := entry.(EventState)); [reflexivity| |].
  - intros slot e Hget Hty; apply mutex_del_recycled_event_lookup in Hget.
    exists e; split; [exact (proj2 Hget)|]. split; [exact Hty|reflexivity].
  - eapply pending_mutex_consistency_table_transport with (tasks := entry.(TskState));
      [|intros; reflexivity|exact Hpending].
    intros p [slot [queue Hlease]]; cbn [mutex_del_relocated_tasks prioTbl].
    unfold mutex_del_released_table; apply update_prio_tbl_other.
    intro E; subst p; destruct (Hpending slot mutex.(mfPCP) queue Hlease)
      as [_ [_ [_ [_ [_ [Hnoclaim _]]]]]].
    apply Hnoclaim; exists eid, event, mutex; repeat split; assumption || reflexivity.
Qed.

Lemma mutex_del_relocated_idle_tail : forall sg entry ceiling owner node priority,
  task_current_prio_registered entry.(TskState) ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_priority_in_range sg priority -> node.(curPrio) <= priority ->
  entry.(TskState).(prioTbl) priority = PTTask owner ->
  task_idle_tail sg entry.(TskState) ->
  task_idle_tail sg (mutex_del_relocated_tasks entry ceiling owner node priority).
Proof.
  intros sg entry ceiling owner node priority Hregistered Hnode Hrange Hmono Halias
    [prefix [idle [t [Horder [Ht [Hprio Hprefix]]]]]].
  assert (HidleSlot : entry.(TskState).(prioTbl) sg.(osLowestPrio) = PTTask idle).
  { rewrite <- Hprio; exact (Hregistered idle t Ht). }
  exists prefix, idle; destruct (Z.eq_dec idle owner) as [E|Hne].
  - subst idle; rewrite Hnode in Ht; injection Ht as E; subst t.
    exists (mutex_priority_task node priority); split; [exact Horder|].
    split; [apply mutex_del_relocated_tasks_lookup|]. split.
    + cbn [mutex_priority_task curPrio]; unfold task_priority_in_range in Hrange; lia.
    + intros slot other Hin Hother; cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates] in Hother.
      destruct (Z.eqb slot owner) eqn:Eslot.
      * apply Z.eqb_eq in Eslot; subst slot; exfalso; exact (Hprefix owner node Hin Hnode Hprio).
      * exact (Hprefix slot other Hin Hother).
  - exists t; split; [exact Horder|]. split.
    + cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates].
      destruct (Z.eqb idle owner) eqn:E; [apply Z.eqb_eq in E; contradiction|exact Ht].
    + split; [exact Hprio|].
      intros slot other Hin Hother; cbn [mutex_del_relocated_tasks glob_task_set_usedtask inUsedTaskStates] in Hother.
      destruct (Z.eqb slot owner) eqn:Eslot.
      * injection Hother as E; subst other; cbn [mutex_priority_task curPrio].
        intro E; rewrite E, HidleSlot in Halias; injection Halias as Eowner; contradiction.
      * exact (Hprefix slot other Hin Hother).
Qed.

(** This is the protected pure closing theorem.  The new effective
    priority and its monotonicity are produced by the actual native scan,
    not post-validity or a ready/current/last-lock assumption. *)
Lemma mutex_del_recycled_state_preserves_validity : forall sg entry eid event mutex owner node priority image,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex -> event.(waitList) = [] ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  node.(curPrio) <= priority ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  UCOS2_state_inv sg
    (mutex_del_recycled_state sg entry eid image mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority image
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]]
    He Htype Hm Ho Henabled Hempty Hnode Heffective Hmono Habsent.
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof (proj1 Heffective) as Hhit.
  change (task_priority_alias sg
    (update_prio_tbl entry.(TskState).(prioTbl) mutex.(mfPCP) PTFree) owner priority) in Hhit.
  apply task_priority_alias_remove_iff in Hhit; [|discriminate].
  destruct Hhit as [Hne [Hpriority Halias]].
  assert (HreferencesAfter : kernel_names_valid sg
    (mutex_del_recycled_state sg entry eid image mutex.(mfPCP) owner node priority)).
  { eapply kernel_names_valid_frame with (before := entry);
      [exact Hreferences|reflexivity| | |intros; assumption|intros; assumption|intros; assumption].
    - apply task_update_name_references with (old := node); [exact Hnode|reflexivity].
    - apply event_recycle_name_references. }
  assert (HstacksAfter : parked_stacks_consistent
    (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) entry.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hnode|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  split; [exact Hprofile|]. split.
  - exact (mutex_del_relocated_tasks_in_range sg entry eid event mutex owner node priority
      Htasks Hcross He Htype Hm Ho Henabled Hnode Heffective).
  - split.
    + apply mutex_del_relocated_sched_in_range; assumption.
    + split.
      * apply event_recycle_preserves_in_range with (node := event); [|exact He].
        apply event_update_unlisted_task_preserves_in_range; assumption.
      * split.
        -- exact (mutex_del_recycled_cross_module_consistency sg entry eid event mutex owner node priority image
             Hcross He Htype Hm Ho Henabled Hempty Hnode Heffective Habsent).
        -- split.
           ++ intro Hrunning; eapply mutex_del_relocated_idle_tail;
                [unfold task_in_range in Htasks; tauto|exact Hnode|exact Hpriority|exact Hmono|
                 exact Halias|apply Hidle; exact Hrunning].
           ++ split.
              ** apply task_reserved_bits_clear_update_task; [exact Hstatus|exact (Hstatus owner node Hnode)].
              ** split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
                 split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
                 split; [exact HreferencesAfter|]. split; [exact HstacksAfter|].
                 exact (mutex_del_recycled_pending_mutex_consistency sg entry eid event mutex owner node priority image
                   Hpending He Htype Hm Henabled).
Qed.

Lemma mutex_del_relocated_tasks_same_priority : forall entry ceiling owner node,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_del_relocated_tasks entry ceiling owner node node.(curPrio) =
    mutex_del_released_tasks entry ceiling.
Proof.
  intros entry ceiling owner node Hnode.
  assert (Hsame : mutex_priority_task node node.(curPrio) = node) by (destruct node; reflexivity).
  assert (Hused : (glob_task_set_usedtask entry.(TskState) owner node).(inUsedTaskStates) =
    entry.(TskState).(inUsedTaskStates)).
  { apply functional_extensionality; intro slot; cbn [glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb slot owner) eqn:E; [apply Z.eqb_eq in E; subst slot; symmetry; exact Hnode|reflexivity]. }
  unfold mutex_del_relocated_tasks; rewrite Hsame.
  unfold mutex_del_released_tasks; rewrite Hused; reflexivity.
Qed.

(** Equal-priority is the C branch that does NOT call RdyAtPrio.  Its
    current-priority cache is left exactly as it was, including when that
    bounded cache was stale.  No fictitious write or current-cache equality
    is introduced in order to close the invariant. *)
Lemma mutex_del_owner_priority_recycle_preserves_validity :
  forall sg entry eid event mutex owner node priority image,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex -> event.(waitList) = [] ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  node.(curPrio) <= priority ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  UCOS2_state_inv sg
    (replace_EventS (event_recycle sg entry.(EventState) eid image)
      (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority)).
Proof.
  intros sg entry eid event mutex owner node priority image Hvalid He Htype Hm Ho Henabled Hempty
    Hnode Heffective Hmono Habsent.
  pose proof (mutex_del_recycled_state_preserves_validity sg entry eid event mutex owner node priority image
    Hvalid He Htype Hm Ho Henabled Hempty Hnode Heffective Hmono Habsent) as Hafter.
  unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority) as [E|Hne];
    [|exact Hafter].
  subst priority.
  assert (Hsched : sched_in_range sg
    (mutex_del_recycled_state sg entry eid image mutex.(mfPCP) owner node node.(curPrio)).(TskState)
    entry.(SchedState)).
  { change (sched_in_range sg (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node node.(curPrio))
      entry.(SchedState)).
    rewrite mutex_del_relocated_tasks_same_priority by exact Hnode.
    exact (proj1 (proj2 (proj2 Hvalid))). }
  pose proof (UCOS2_replace_sched_preserves_validity sg _ entry.(SchedState) Hafter Hsched eq_refl) as Hsame.
  assert (Epost : replace_SchedS entry.(SchedState)
      (mutex_del_recycled_state sg entry eid image mutex.(mfPCP) owner node node.(curPrio)) =
    replace_EventS (event_recycle sg entry.(EventState) eid image) (mutex_del_released_state entry mutex.(mfPCP))).
  { unfold mutex_del_recycled_state, mutex_del_relocated_state.
    rewrite mutex_del_relocated_tasks_same_priority by exact Hnode.
    destruct entry; reflexivity. }
  rewrite Epost in Hsame; exact Hsame.
Qed.

Lemma mutex_del_no_pend_owner_scan_closes_state : forall sg entry eid event mutex owner priority image,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex -> event.(waitList) = [] ->
  task_slot_addr sg owner <> 1 ->
  (forall node, entry.(TskState).(inUsedTaskStates) owner = Some node ->
    mutex_effective_priority_result
      (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
      (task_slot_addr sg owner) node.(curPrio) priority) ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  exists node, entry.(TskState).(inUsedTaskStates) owner = Some node /\
    UCOS2_state_inv sg
      (replace_EventS (event_recycle sg entry.(EventState) eid image)
        (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority)).
Proof.
  intros sg entry eid event mutex owner priority image Hvalid He Htype Hm Ho Henabled Hempty Hnotreserved Hscan Habsent.
  destruct (mutex_del_owner_scan_properties sg entry eid event mutex owner priority
    Hvalid He Htype Hm Ho Henabled Hnotreserved Hscan)
    as [node [base [Hnode [Hbase [Heffective [[Hmono Hbound] Hrest]]]]]].
  exists node; split; [exact Hnode|].
  eapply mutex_del_owner_priority_recycle_preserves_validity; eassumption.
Qed.

Lemma mutex_del_owner_priority_event_state_eq : forall sg entry ceiling owner node priority,
  (mutex_del_owner_priority_state sg entry ceiling owner node priority).(EventState) = entry.(EventState).
Proof.
  intros; unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority); reflexivity.
Qed.

Lemma mutex_del_event_group_zero_implies_empty : forall sg entry eid event,
  UCOS2_state_inv sg entry -> entry.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) entry.(TskState) = 0 -> event.(waitList) = [].
Proof.
  intros sg entry eid event [_ [_ [_ [_ [Hcross _]]]]] He Hzero.
  destruct Hcross as [_ [_ [[Hentries _] _]]].
  apply (proj1 (encode_event_wait_grp_zero_iff_empty sg entry.(TskState) event.(waitList)
    (proj1 (Hentries eid event He)))); exact Hzero.
Qed.

(** The closing resource rule consumes the actual source-written ECB and
    new free root together with the same priority phase's disjoint frame.
    Its zero-group premise is the literal NO_PEND branch observation.
    This does not supply the public caller's owner-use or Save producer. *)
Lemma mutex_del_no_pend_owner_recycle_merge_inv :
  forall sg entry eid event mutex owner node priority image,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  encode_event_wait_grp event.(waitList) entry.(TskState) = 0 ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg entry.(EventState).(unUsedEventStates) image) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
  mutex_del_event_frame sg (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority) eid |--
  UCOS2_inv sg (replace_EventS (event_recycle sg entry.(EventState) eid image)
    (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority)).
Proof.
  intros sg entry eid event mutex owner node priority image Hvalid He Htype Hm Ho Henabled
    Hzero Hnode Hnotreserved Hscan Habsent.
  pose proof (mutex_del_event_group_zero_implies_empty sg entry eid event Hvalid He Hzero) as Hempty.
  assert (HscanAll : forall other, entry.(TskState).(inUsedTaskStates) owner = Some other ->
    mutex_effective_priority_result
      (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
      (task_slot_addr sg owner) other.(curPrio) priority).
  { intros other Hother; rewrite Hnode in Hother; injection Hother as E; subst other; exact Hscan. }
  destruct (mutex_del_no_pend_owner_scan_closes_state sg entry eid event mutex owner priority image
    Hvalid He Htype Hm Ho Henabled Hempty Hnotreserved HscanAll Habsent)
    as [other [Hother Hafter]].
  rewrite Hnode in Hother; injection Hother as E; subst other.
  pose proof Hvalid as [_ [_ [_ [[Hpool [Hfree [_ [Hfields _]]]] _]]]].
  assert (Hqueue : event.(queueFields) = None).
  { apply non_queue_event_has_no_queue_fields; [exact (Hfields eid event He)|rewrite Htype; discriminate]. }
  pose proof (mutex_del_owner_priority_event_state_eq sg entry mutex.(mfPCP) owner node priority) as Eevents.
  pose proof (mutex_del_recycle_event_merge_raw sg
    (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority) eid event image
    ltac:(rewrite Eevents; exact Hpool) ltac:(rewrite Eevents; exact Hfree)
    ltac:(rewrite Eevents; exact He) Hqueue) as Hmerge.
  rewrite Eevents in Hmerge; sep_apply_l_atomic Hmerge.
  unfold UCOS2_inv; entailer!.
Qed.

(** The NULL-owner and disabled-PCP branches have no TCB/ready/cache
    operation.  The conditional here describes only the actual table store;
    every other Task field is definitionally framed. *)
Definition mutex_del_unrelocated_tasks (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (mutex : MutexFields) : Glob_TaskAbstractState :=
  {| inUsedTaskStates := entry.(TskState).(inUsedTaskStates);
     unUsedTaskStates := entry.(TskState).(unUsedTaskStates);
     tcbListHead := entry.(TskState).(tcbListHead);
     prioTbl := if Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)
       then entry.(TskState).(prioTbl) else mutex_del_released_table entry mutex.(mfPCP);
     taskRegNextID := entry.(TskState).(taskRegNextID);
     parkedTaskStacks := entry.(TskState).(parkedTaskStacks);
     taskLifecycle := entry.(TskState).(taskLifecycle);
     taskCount := entry.(TskState).(taskCount) |}.

Definition mutex_del_unrelocated_state (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (mutex : MutexFields) : UCOS2_Verify_State :=
  replace_TskS (mutex_del_unrelocated_tasks sg entry mutex) entry.

Lemma mutex_del_unrelocated_source_branch_eq : forall sg entry mutex,
  mutex_del_unrelocated_state sg entry mutex =
    if Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)
    then entry else mutex_del_released_state entry mutex.(mfPCP).
Proof.
  intros; unfold mutex_del_unrelocated_state, mutex_del_unrelocated_tasks.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [|reflexivity].
  destruct entry; simpl; f_equal.
  match goal with tasks : Glob_TaskAbstractState |- _ => destruct tasks; reflexivity end.
Qed.

Lemma mutex_del_unrelocated_table_other : forall sg entry mutex p,
  p <> mutex.(mfPCP) \/ mutex.(mfPCP) = sg.(osPrioMutexCeilDis) ->
  (mutex_del_unrelocated_tasks sg entry mutex).(prioTbl) p = entry.(TskState).(prioTbl) p.
Proof.
  intros sg entry mutex p Hframe; cbn [mutex_del_unrelocated_tasks prioTbl].
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [reflexivity|].
  apply update_prio_tbl_other; tauto.
Qed.

Lemma mutex_del_unrelocated_alias_iff : forall sg entry eid event mutex tid p,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ mutex.(mfOwner) = None) ->
  (task_priority_alias sg (mutex_del_unrelocated_tasks sg entry mutex).(prioTbl) tid p <->
   task_priority_alias sg entry.(TskState).(prioTbl) tid p).
Proof.
  intros sg entry eid event mutex tid p [_ [_ [_ [Hprotocol _]]]] He Htype Hm Hbranch.
  cbn [mutex_del_unrelocated_tasks prioTbl].
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled]; [reflexivity|].
  assert (Hnone : mutex.(mfOwner) = None) by tauto.
  destruct (Hprotocol eid event mutex He Htype Hm) as [_ [_ [Hdisabled|[_ Hslot]]]]; [contradiction|].
  assert (Hreserved : entry.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved).
  { destruct Hslot as [Hreserved|[owner [Howner _]]]; [exact Hreserved|congruence]. }
  apply task_priority_alias_foreign_write_iff; [rewrite Hreserved|]; discriminate.
Qed.

Lemma mutex_del_unrelocated_recycled_alias_consistency : forall sg entry eid event mutex image,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ mutex.(mfOwner) = None) ->
  mutex_priority_alias_consistency sg (mutex_del_unrelocated_tasks sg entry mutex)
    (event_recycle sg entry.(EventState) eid image).
Proof.
  intros sg entry eid event mutex image Hcross He Htype Hm Hbranch tid t Ht.
  pose proof (proj2 (proj2 (proj1 Hcross)) tid t Ht) as [base [Hbase [Heffective Hclaims]]].
  assert (Haliases : forall owner p,
    task_priority_alias sg entry.(TskState).(prioTbl) owner p <->
    task_priority_alias sg (mutex_del_unrelocated_tasks sg entry mutex).(prioTbl) owner p).
  { intros; symmetry; eapply mutex_del_unrelocated_alias_iff; eassumption. }
  exists base; split; [eapply task_base_priority_alias_ext; [apply Haliases|exact Hbase]|].
  split; [eapply task_effective_priority_alias_ext; [apply Haliases|exact Heffective]|].
  intros p Hp; apply Haliases in Hp; destruct (Hclaims p Hp) as [E|[Hlt Hclaim]]; [left; exact E|].
  right; split; [exact Hlt|].
  destruct Hclaim as [mid [e [m [Hget [Hty [Hfields [Howner [Henabled Hpcp]]]]]]]].
  exists mid, e, m; split; [|repeat split; assumption].
  apply mutex_del_recycled_event_lookup; split; [|exact Hget].
  intro E; subst mid; rewrite He in Hget; injection Hget as E; subst e.
  rewrite Hm in Hfields; injection Hfields as E; subst m.
  destruct Hbranch; [contradiction|congruence].
Qed.

Lemma mutex_del_recycled_slot_claim_forward : forall sg entry eid event mutex image p,
  entry.(EventState).(inUsedEventStates) eid = Some event -> event.(mutexFields) = Some mutex ->
  (p <> mutex.(mfPCP) \/ mutex.(mfPCP) = sg.(osPrioMutexCeilDis)) ->
  (exists mid e m, entry.(EventState).(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\ mutex_reserves_priority_slot sg m p) ->
  exists mid e m, (event_recycle sg entry.(EventState) eid image).(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\ mutex_reserves_priority_slot sg m p.
Proof.
  intros sg entry eid event mutex image p He Hm Hframe [mid [e [m [Hget [Hty [Hfields Hclaim]]]]]].
  exists mid, e, m; split; [|auto]. apply mutex_del_recycled_event_lookup; split; [|exact Hget].
  intro E; subst mid; rewrite He in Hget; injection Hget as E; subst e.
  rewrite Hm in Hfields; injection Hfields as E; subst m.
  destruct Hclaim as [Henabled Hpcp]; destruct Hframe; congruence.
Qed.

Lemma mutex_del_unrelocated_recycled_table_consistency : forall sg entry eid event mutex image,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ mutex.(mfOwner) = None) ->
  task_mutex_priotbl_consistency sg (mutex_del_unrelocated_tasks sg entry mutex)
    (event_recycle sg entry.(EventState) eid image).
Proof.
  intros sg entry eid event mutex image Hcross He Htype Hm Hbranch.
  pose proof Hcross as [[Hcreator [Hslots Halias]] [_ [_ [_ [Hunique _]]]]].
  split.
  - intros p reservation Hr [mid [e [m [Hget Hrest]]]].
    apply (Hcreator p reservation Hr); exists mid, e, m; split; [|exact Hrest].
    apply mutex_del_recycled_event_lookup in Hget; tauto.
  - split.
    + intros p Hp; destruct (Z.eq_dec p mutex.(mfPCP)) as [E|Hne];
        destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled].
      2: { subst p; cbn [mutex_del_unrelocated_tasks prioTbl].
           destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|].
           unfold mutex_del_released_table; rewrite update_prio_tbl_same.
           intros [mid [e [m [Hget [Hty [Hfields [_ Hpcp]]]]]]].
           exact (mutex_del_surviving_ceiling_ne sg entry eid event mutex image mid e m
             Hunique He Htype Hm Henabled Hget Hty Hfields Hpcp). }
      all: assert (Hframe : p <> mutex.(mfPCP) \/ mutex.(mfPCP) = sg.(osPrioMutexCeilDis)) by auto.
      all: rewrite mutex_del_unrelocated_table_other by exact Hframe.
      all: specialize (Hslots p Hp); destruct (entry.(TskState).(prioTbl) p) as [| |tid].
      all: try exact Hslots.
      all: try (intros [mid [e [m [Hget Hrest]]]]; apply Hslots; exists mid, e, m;
        split; [apply mutex_del_recycled_event_lookup in Hget; tauto|exact Hrest]).
      all: destruct Hslots as [Hreservation|[Hclaim|Hpending]];
        [left; exact Hreservation|right; left; eapply mutex_del_recycled_slot_claim_forward;
         [exact He|exact Hm|exact Hframe|exact Hclaim]|right; right; exact Hpending].
    + exact (mutex_del_unrelocated_recycled_alias_consistency sg entry eid event mutex image
        Hcross He Htype Hm Hbranch).
Qed.

Lemma mutex_del_unrelocated_tasks_in_range : forall sg entry eid event mutex,
  task_in_range sg entry.(TskState) -> cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ mutex.(mfOwner) = None) ->
  task_in_range sg (mutex_del_unrelocated_tasks sg entry mutex).
Proof.
  intros sg entry eid event mutex
    [Hpool [Hactive [Hfree [Hreservations [Hgenerations [Hregistered [Hunique [Hpriority Hrest]]]]]]]]
    Hcross He Htype Hm Hbranch.
  pose proof (mutex_del_unrelocated_recycled_alias_consistency sg entry eid event mutex (fun _ => None)
    Hcross He Htype Hm Hbranch) as Halias.
  split; [exact Hpool|]. split; [exact Hactive|]. split; [exact Hfree|]. split.
  - destruct Hreservations as [Hentries HuniqueInvocation]; split; [|exact HuniqueInvocation].
    intros p reservation Hr; destruct (Hentries p reservation Hr) as [Hp [Hslot Hinv]].
    split; [exact Hp|]. split; [|exact Hinv].
    rewrite mutex_del_unrelocated_table_other; [exact Hslot|].
    destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled]; [right; exact Hdisabled|].
    left; intro E; subst p; apply (proj1 (proj1 Hcross) mutex.(mfPCP) reservation Hr).
    exists eid, event, mutex; repeat split; assumption || reflexivity.
  - split; [exact Hgenerations|]. split.
    + eapply mutex_priority_alias_consistency_current_registered; exact Halias.
    + split; [exact Hunique|]. split; [exact Hpriority|exact Hrest].
Qed.

Lemma mutex_del_unrelocated_recycled_cross_module_consistency : forall sg entry eid event mutex image,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex -> event.(waitList) = [] ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ mutex.(mfOwner) = None) ->
  cross_module_consistency sg (replace_EventS (event_recycle sg entry.(EventState) eid image)
    (mutex_del_unrelocated_state sg entry mutex)).
Proof.
  intros sg entry eid event mutex image Hcross He Htype Hm Hempty Hbranch.
  pose proof Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  split.
  - exact (mutex_del_unrelocated_recycled_table_consistency sg entry eid event mutex image
      Hcross He Htype Hm Hbranch).
  - split.
    + intros mid e m owner Hget Hty Hfields Howner; apply mutex_del_recycled_event_lookup in Hget.
      destruct (Hsnapshot mid e m owner (proj2 Hget) Hty Hfields Howner)
        as [t [base [snapshot [Ht [Hbase Hrest]]]]].
      exists t, base, snapshot; split; [exact Ht|]. split; [|exact Hrest].
      eapply task_base_priority_alias_ext; [|exact Hbase].
      intro p; symmetry; exact (mutex_del_unrelocated_alias_iff sg entry eid event mutex owner p
        Hcross He Htype Hm Hbranch).
    + split.
      * apply (mutex_del_empty_event_remove_wait_consistency sg
          (mutex_del_unrelocated_state sg entry mutex) eid event image He Hempty); exact Hwait.
      * split.
        -- intros mid e m Hget Hty Hfields.
           assert (Hframe : m.(mfPCP) <> mutex.(mfPCP) \/ mutex.(mfPCP) = sg.(osPrioMutexCeilDis)).
           { destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled];
               [right; exact Hdisabled|left].
             exact (mutex_del_surviving_ceiling_ne sg entry eid event mutex image mid e m
               Hunique He Htype Hm Henabled Hget Hty Hfields). }
           apply mutex_del_recycled_event_lookup in Hget.
           destruct (Hprotocol mid e m (proj2 Hget) Hty Hfields) as [Hrange [Howner Hslot]].
           split; [exact Hrange|]. split; [exact Howner|].
           change (m.(mfPCP) = sg.(osPrioMutexCeilDis) \/
             (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
              ((mutex_del_unrelocated_tasks sg entry mutex).(prioTbl) m.(mfPCP) = PTReserved \/
               exists owner, m.(mfOwner) = Some owner /\
                 (mutex_del_unrelocated_tasks sg entry mutex).(prioTbl) m.(mfPCP) = PTTask owner))).
           rewrite mutex_del_unrelocated_table_other by exact Hframe; exact Hslot.
        -- split; [|split; [exact Hflags|exact Htimer]].
           eapply mutex_enabled_pcp_unique_transport with (lvs1 := entry); [|exact Hunique].
           intros mid e m Hget Hty Hfields; apply mutex_del_recycled_event_lookup in Hget.
           exists e, m; intuition.
Qed.

Lemma mutex_del_unrelocated_recycled_pending_consistency : forall sg entry eid event mutex image,
  pending_mutex_consistency sg entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  pending_mutex_consistency sg (mutex_del_unrelocated_tasks sg entry mutex)
    (event_recycle sg entry.(EventState) eid image).
Proof.
  intros sg entry eid event mutex image Hpending He Htype Hm.
  eapply pending_mutex_consistency_event_transport with (events := entry.(EventState)); [reflexivity| |].
  - intros slot e Hget Hty; apply mutex_del_recycled_event_lookup in Hget.
    exists e; split; [exact (proj2 Hget)|]. split; [exact Hty|reflexivity].
  - eapply pending_mutex_consistency_table_transport with (tasks := entry.(TskState));
      [|intros; reflexivity|exact Hpending].
    intros p [slot [queue Hlease]]; apply mutex_del_unrelocated_table_other.
    destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled]; [auto|left].
    intro E; subst p; destruct (Hpending slot mutex.(mfPCP) queue Hlease)
      as [_ [_ [_ [_ [_ [Hnoclaim _]]]]]].
    apply Hnoclaim; exists eid, event, mutex; repeat split; assumption || reflexivity.
Qed.

Lemma mutex_del_unrelocated_recycle_preserves_validity : forall sg entry eid event mutex image,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  event.(waitList) = [] ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ mutex.(mfOwner) = None) ->
  UCOS2_state_inv sg (replace_EventS (event_recycle sg entry.(EventState) eid image)
    (mutex_del_unrelocated_state sg entry mutex)).
Proof.
  intros sg entry eid event mutex image
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]]
    He Htype Hm Hempty Hbranch.
  assert (HreferencesAfter : kernel_names_valid sg
    (replace_EventS (event_recycle sg entry.(EventState) eid image)
      (mutex_del_unrelocated_state sg entry mutex))).
  { eapply kernel_names_valid_frame with (before := entry);
      [exact Hreferences|reflexivity|intros; assumption|apply event_recycle_name_references|
       intros; assumption|intros; assumption|intros; assumption]. }
  split; [exact Hprofile|]. split.
  - exact (mutex_del_unrelocated_tasks_in_range sg entry eid event mutex Htasks Hcross He Htype Hm Hbranch).
  - split; [exact Hsched|]. split.
    + apply event_recycle_preserves_in_range with (node := event); [exact Hevents|exact He].
    + split.
      * exact (mutex_del_unrelocated_recycled_cross_module_consistency sg entry eid event mutex image
          Hcross He Htype Hm Hempty Hbranch).
      * split; [exact Hidle|]. split; [exact Hstatus|]. split; [exact Hflags|].
        split; [exact Hmemory|]. split; [exact Htimer|]. split; [exact Hstats|].
        split; [exact Hcontrol|]. split; [exact Hnames|]. split; [exact HreferencesAfter|].
        split; [exact Hstacks|].
        exact (mutex_del_unrelocated_recycled_pending_consistency sg entry eid event mutex image Hpending He Htype Hm).
Qed.

Lemma mutex_del_no_pend_unrelocated_recycle_merge_inv : forall sg entry eid event mutex image,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  encode_event_wait_grp event.(waitList) entry.(TskState) = 0 ->
  (mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ mutex.(mfOwner) = None) ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg entry.(EventState).(unUsedEventStates) image) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
  mutex_del_event_frame sg (mutex_del_unrelocated_state sg entry mutex) eid |--
  UCOS2_inv sg (replace_EventS (event_recycle sg entry.(EventState) eid image)
    (mutex_del_unrelocated_state sg entry mutex)).
Proof.
  intros sg entry eid event mutex image Hvalid He Htype Hm Hzero Hbranch.
  pose proof (mutex_del_event_group_zero_implies_empty sg entry eid event Hvalid He Hzero) as Hempty.
  pose proof (mutex_del_unrelocated_recycle_preserves_validity sg entry eid event mutex image
    Hvalid He Htype Hm Hempty Hbranch) as Hafter.
  pose proof Hvalid as [_ [_ [_ [[Hpool [Hfree [_ [Hfields _]]]] _]]]].
  assert (Hqueue : event.(queueFields) = None).
  { apply non_queue_event_has_no_queue_fields; [exact (Hfields eid event He)|rewrite Htype; discriminate]. }
  pose proof (mutex_del_recycle_event_merge_raw sg
    (mutex_del_unrelocated_state sg entry mutex) eid event image Hpool Hfree He Hqueue) as Hmerge.
  assert (Eevents : (mutex_del_unrelocated_state sg entry mutex).(EventState) = entry.(EventState))
    by reflexivity.
  rewrite Eevents in Hmerge; sep_apply_l_atomic Hmerge.
  unfold UCOS2_inv; entailer!.
Qed.

(** Pure projection for the released-PCP wake phase.  The C heap still
    contains PTFree.  This function supplies no resource or extra kernel
    field: it is used only to prove the unchanged owner/lifetime protocol
    while the same target Mutex remains published.  Every actual table
    read must separately be proved disjoint from this one projected slot. *)
Definition mutex_del_ceiling_view_tasks (tasks : Glob_TaskAbstractState) (ceiling : Priority)
  : Glob_TaskAbstractState :=
  {| inUsedTaskStates := tasks.(inUsedTaskStates);
     unUsedTaskStates := tasks.(unUsedTaskStates);
     tcbListHead := tasks.(tcbListHead);
     prioTbl := update_prio_tbl tasks.(prioTbl) ceiling PTReserved;
     taskRegNextID := tasks.(taskRegNextID);
     parkedTaskStacks := tasks.(parkedTaskStacks);
     taskLifecycle := tasks.(taskLifecycle);
     taskCount := tasks.(taskCount) |}.

Definition mutex_del_ceiling_view (state : UCOS2_Verify_State) (ceiling : Priority)
  : UCOS2_Verify_State := replace_TskS (mutex_del_ceiling_view_tasks state.(TskState) ceiling) state.

Definition mutex_del_released_state_inv (sg : StableGlobVars) (eid : EventID)
  (mutex : MutexFields) (state : UCOS2_Verify_State) : Prop :=
  mutex_pcp_enabled sg mutex /\ state.(TskState).(prioTbl) mutex.(mfPCP) = PTFree /\
  UCOS2_state_inv sg (mutex_del_ceiling_view state mutex.(mfPCP)) /\
  exists event, state.(EventState).(inUsedEventStates) eid = Some event /\
    event.(eventType) = OS_EVENT_TYPE_MUTEX /\ event.(mutexFields) = Some mutex.

Definition mutex_del_released_rep (sg : StableGlobVars) (eid : EventID)
  (mutex : MutexFields) (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (mutex_del_released_state_inv sg eid mutex state) && UCOS2_raw_rep sg state.

Lemma mutex_del_ceiling_view_alias_iff : forall sg tasks ceiling tid p,
  tasks.(prioTbl) ceiling = PTFree ->
  (task_priority_alias sg (mutex_del_ceiling_view_tasks tasks ceiling).(prioTbl) tid p <->
    task_priority_alias sg tasks.(prioTbl) tid p).
Proof.
  intros; apply task_priority_alias_foreign_write_iff; [rewrite H|]; discriminate.
Qed.

Lemma mutex_del_ceiling_view_tasks_in_range : forall sg tasks ceiling,
  task_in_range sg tasks -> tasks.(prioTbl) ceiling = PTFree ->
  task_in_range sg (mutex_del_ceiling_view_tasks tasks ceiling).
Proof.
  intros sg tasks ceiling
    [Hpool [Hactive [Hfree [Hreservations [Hgenerations [Hregistered [Hunique [Hpriority Hrest]]]]]]]] Hclear.
  split; [exact Hpool|]. split; [exact Hactive|]. split; [exact Hfree|]. split.
  - destruct Hreservations as [Hentries Hdistinct]; split; [|exact Hdistinct].
    intros p reservation Hr; destruct (Hentries p reservation Hr) as [Hp [Hslot Hinv]].
    split; [exact Hp|]. split; [|exact Hinv].
    cbn [mutex_del_ceiling_view_tasks prioTbl].
    rewrite update_prio_tbl_other; [exact Hslot|congruence].
  - split; [exact Hgenerations|]. split.
    + intros tid t Ht; cbn [mutex_del_ceiling_view_tasks prioTbl].
      rewrite update_prio_tbl_other; [exact (Hregistered tid t Ht)|].
      pose proof (Hregistered tid t Ht); congruence.
    + split; [exact Hunique|]. split; [exact Hpriority|exact Hrest].
Qed.

Lemma mutex_del_ceiling_view_tasks_in_range_back : forall sg tasks ceiling,
  task_in_range sg (mutex_del_ceiling_view_tasks tasks ceiling) ->
  tasks.(prioTbl) ceiling = PTFree ->
  (forall reservation, tasks.(taskLifecycle).(taskReservations) ceiling <> Some reservation) ->
  task_in_range sg tasks.
Proof.
  intros sg tasks ceiling
    [Hpool [Hactive [Hfree [Hreservations [Hgenerations [Hregistered [Hunique [Hpriority Hrest]]]]]]]] Hclear HnoCreator.
  split; [exact Hpool|]. split; [exact Hactive|]. split; [exact Hfree|]. split.
  - destruct Hreservations as [Hentries Hdistinct]; split; [|exact Hdistinct].
    intros p reservation Hr; destruct (Hentries p reservation Hr) as [Hp [Hslot Hinv]].
    split; [exact Hp|]. split; [|exact Hinv].
    cbn [mutex_del_ceiling_view_tasks prioTbl] in Hslot.
    rewrite update_prio_tbl_other in Hslot; [exact Hslot|].
    intro E; subst p; exact (HnoCreator reservation Hr).
  - split; [exact Hgenerations|]. split.
    + intros tid t Ht; specialize (Hregistered tid t Ht).
      cbn [mutex_del_ceiling_view_tasks prioTbl] in Hregistered.
      destruct (Z.eq_dec t.(curPrio) ceiling) as [E|Hne].
      * rewrite E, update_prio_tbl_same in Hregistered; discriminate.
      * rewrite update_prio_tbl_other in Hregistered by exact Hne; exact Hregistered.
    + split; [exact Hunique|]. split; [exact Hpriority|exact Hrest].
Qed.

Lemma mutex_del_relocated_ceiling_view_alias_consistency :
  forall sg entry eid event mutex owner node priority,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  mutex_priority_alias_consistency sg
    (mutex_del_ceiling_view_tasks (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) mutex.(mfPCP))
    entry.(EventState).
Proof.
  intros sg entry eid event mutex owner node priority Hcross He Htype Hm Ho Henabled Hnode Heffective tid t Ht.
  pose proof (mutex_del_recycled_alias_consistency sg entry eid event mutex owner node priority (fun _ => None)
    Hcross He Htype Hm Ho Henabled Hnode Heffective tid t Ht) as [base [Hbase [Hcurrent Hclaims]]].
  assert (Hclear : (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority).(prioTbl) mutex.(mfPCP) = PTFree).
  { apply update_prio_tbl_same. }
  assert (Haliases : forall p, task_priority_alias sg
    (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority).(prioTbl) tid p <->
    task_priority_alias sg
      (mutex_del_ceiling_view_tasks (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)).(prioTbl) tid p).
  { intro p; symmetry; apply mutex_del_ceiling_view_alias_iff; exact Hclear. }
  exists base; split; [eapply task_base_priority_alias_ext; [apply Haliases|exact Hbase]|].
  split; [eapply task_effective_priority_alias_ext; [apply Haliases|exact Hcurrent]|].
  intros p Hp; apply Haliases in Hp; destruct (Hclaims p Hp) as [E|[Hlt Hclaim]]; [left; exact E|].
  right; split; [exact Hlt|].
  destruct Hclaim as [mid [e [m [Hget Hrest]]]].
  apply mutex_del_recycled_event_lookup in Hget; exists mid, e, m; split; [exact (proj2 Hget)|exact Hrest].
Qed.

Lemma mutex_del_relocated_ceiling_view_cross_module_consistency :
  forall sg entry eid event mutex owner node priority,
  cross_module_consistency sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  cross_module_consistency sg
    (mutex_del_ceiling_view (mutex_del_relocated_state sg entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)).
Proof.
  intros sg entry eid event mutex owner node priority Hcross He Htype Hm Ho Henabled Hnode Heffective Habsent.
  pose proof Hcross as [[Hcreator [Hslots Halias]] [Hsnapshot [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  assert (Htable : forall p,
    (mutex_del_ceiling_view_tasks (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)).(prioTbl) p =
      update_prio_tbl entry.(TskState).(prioTbl) mutex.(mfPCP) PTReserved p).
  { intro p; apply equal_f; apply update_prio_tbl_overwrite. }
  assert (Hclear : (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority).(prioTbl) mutex.(mfPCP) = PTFree)
    by apply update_prio_tbl_same.
  split.
  - split; [exact Hcreator|]. split.
    + intros p Hp; change (match (mutex_del_ceiling_view_tasks
        (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)).(prioTbl) p with
        | PTFree => ~ (exists mid e m, entry.(EventState).(inUsedEventStates) mid = Some e /\
            e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\ mutex_reserves_priority_slot sg m p)
        | PTReserved => (exists reservation, entry.(TskState).(taskLifecycle).(taskReservations) p = Some reservation) \/
            (exists mid e m, entry.(EventState).(inUsedEventStates) mid = Some e /\
              e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\ mutex_reserves_priority_slot sg m p) \/
            pending_mutex_priority_claim entry.(EventState) p
        | PTTask tid => exists t, (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority).(inUsedTaskStates) tid = Some t
        end).
      rewrite Htable; unfold update_prio_tbl; destruct (Z.eq_dec p mutex.(mfPCP)) as [->|Hne].
      * right; left; exists eid, event, mutex; repeat split; assumption || reflexivity.
      * specialize (Hslots p Hp); destruct (entry.(TskState).(prioTbl) p) as [| |tid]; [exact Hslots|exact Hslots|].
        apply (proj2 (glob_task_set_usedtask_live_iff entry.(TskState) owner node
          (mutex_priority_task node priority) tid Hnode)); exact Hslots.
    + exact (mutex_del_relocated_ceiling_view_alias_consistency sg entry eid event mutex owner node priority
        Hcross He Htype Hm Ho Henabled Hnode Heffective).
  - split.
    + intros mid e m tid Hget Hty Hfields Howner.
      destruct (Hsnapshot mid e m tid Hget Hty Hfields Howner)
        as [t [base [snapshot [Ht [Hbase Hrest]]]]].
      destruct (proj2 (glob_task_set_usedtask_live_iff entry.(TskState) owner node
        (mutex_priority_task node priority) tid Hnode) (ex_intro _ t Ht)) as [after Hafter].
      exists after, base, snapshot; split; [exact Hafter|]. split; [|exact Hrest].
      eapply task_base_priority_alias_ext.
      * intro p; symmetry; apply mutex_del_ceiling_view_alias_iff; exact Hclear.
      * exact (mutex_del_released_base_priority sg entry eid event mutex owner tid base
          Hcross He Htype Hm Ho Henabled Hbase).
    + split.
      * change (event_wait_object_consistency sg
          (replace_TskS (glob_task_set_usedtask entry.(TskState) owner (mutex_priority_task node priority)) entry)).
        eapply event_wait_object_update_unlisted_task; try eassumption; reflexivity.
      * split.
        -- intros mid e m Hget Hty Hfields.
           destruct (Hprotocol mid e m Hget Hty Hfields) as [Hrange [Howner Hslot]].
           split; [exact Hrange|]. split; [exact Howner|].
           destruct Hslot as [Hdisabled|[HmEnabled Hslot]]; [left; exact Hdisabled|right; split; [exact HmEnabled|]].
           change ((mutex_del_ceiling_view_tasks
             (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)).(prioTbl) m.(mfPCP) = PTReserved \/
             exists tid, m.(mfOwner) = Some tid /\ (mutex_del_ceiling_view_tasks
               (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)).(prioTbl) m.(mfPCP) = PTTask tid).
           rewrite Htable; unfold update_prio_tbl; destruct (Z.eq_dec m.(mfPCP) mutex.(mfPCP)); [left; reflexivity|exact Hslot].
        -- split; [exact Hunique|]. split; [|exact Htimer].
           change (task_flag_waiter_consistency sg
             (glob_task_set_usedtask entry.(TskState) owner (mutex_priority_task node priority)) entry.(FlagState)).
           eapply task_flag_waiter_consistency_update_task;
             [exact Hnode|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflags]; intros H; exact H.
Qed.

Lemma mutex_del_relocated_ceiling_view_preserves_validity :
  forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  node.(curPrio) <= priority ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  UCOS2_state_inv sg
    (mutex_del_ceiling_view (mutex_del_relocated_state sg entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)).
Proof.
  intros sg entry eid event mutex owner node priority
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]]
    He Htype Hm Ho Henabled Hnode Heffective Hmono Habsent.
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof (proj1 Heffective) as Hhit.
  change (task_priority_alias sg (update_prio_tbl entry.(TskState).(prioTbl) mutex.(mfPCP) PTFree) owner priority) in Hhit.
  apply task_priority_alias_remove_iff in Hhit; [|discriminate].
  destruct Hhit as [Hne [Hpriority Halias]].
  assert (Hclear : (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority).(prioTbl) mutex.(mfPCP) = PTFree)
    by apply update_prio_tbl_same.
  assert (HreferencesAfter : kernel_names_valid sg
    (mutex_del_ceiling_view (mutex_del_relocated_state sg entry mutex.(mfPCP) owner node priority) mutex.(mfPCP))).
  { eapply kernel_names_valid_frame with (before := entry);
      [exact Hreferences|reflexivity| |intros; assumption|intros; assumption|intros; assumption|intros; assumption].
    apply task_update_name_references with (old := node); [exact Hnode|reflexivity]. }
  assert (HstacksAfter : parked_stacks_consistent
    (mutex_del_ceiling_view_tasks (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) mutex.(mfPCP))
    entry.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hnode|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HpendingAfter : pending_mutex_consistency sg
    (mutex_del_ceiling_view_tasks (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)) entry.(EventState)).
  { eapply pending_mutex_consistency_table_transport with (tasks := entry.(TskState));
      [|intros; reflexivity|exact Hpending].
    intros p [slot [queue Hlease]].
    assert (Hpcp : p <> mutex.(mfPCP)).
    { intro E; subst p; destruct (Hpending slot mutex.(mfPCP) queue Hlease) as [_ [_ [_ [_ [_ [Hnomutex _]]]]]].
      apply Hnomutex; exists eid, event, mutex; repeat split; assumption || reflexivity. }
    change (update_prio_tbl (update_prio_tbl entry.(TskState).(prioTbl) mutex.(mfPCP) PTFree)
      mutex.(mfPCP) PTReserved p = entry.(TskState).(prioTbl) p).
    repeat rewrite update_prio_tbl_other by exact Hpcp; reflexivity. }
  split; [exact Hprofile|]. split.
  - apply mutex_del_ceiling_view_tasks_in_range; [|exact Hclear].
    exact (mutex_del_relocated_tasks_in_range sg entry eid event mutex owner node priority
      Htasks Hcross He Htype Hm Ho Henabled Hnode Heffective).
  - split.
    + apply mutex_del_relocated_sched_in_range; assumption.
    + split.
      * apply event_update_unlisted_task_preserves_in_range; assumption.
      * split.
        -- exact (mutex_del_relocated_ceiling_view_cross_module_consistency sg entry eid event mutex owner node priority
             Hcross He Htype Hm Ho Henabled Hnode Heffective Habsent).
        -- split.
           ++ intro Hrunning; eapply mutex_del_relocated_idle_tail;
                [unfold task_in_range in Htasks; tauto|exact Hnode|exact Hpriority|exact Hmono|
                 exact Halias|apply Hidle; exact Hrunning].
           ++ split.
              ** apply task_reserved_bits_clear_update_task; [exact Hstatus|exact (Hstatus owner node Hnode)].
              ** split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
                 split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
                 split; [exact HreferencesAfter|]. split; [exact HstacksAfter|exact HpendingAfter].
Qed.

Lemma mutex_del_owner_priority_ceiling_view_preserves_validity :
  forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  task_effective_priority sg (mutex_del_released_table entry mutex.(mfPCP)) owner priority ->
  node.(curPrio) <= priority ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  UCOS2_state_inv sg
    (mutex_del_ceiling_view (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority) mutex.(mfPCP)).
Proof.
  intros sg entry eid event mutex owner node priority Hvalid He Htype Hm Ho Henabled Hnode Heffective Hmono Habsent.
  pose proof (mutex_del_relocated_ceiling_view_preserves_validity sg entry eid event mutex owner node priority
    Hvalid He Htype Hm Ho Henabled Hnode Heffective Hmono Habsent) as Hafter.
  unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority) as [E|Hne]; [|exact Hafter].
  subst priority.
  assert (Hsched : sched_in_range sg
    (mutex_del_ceiling_view (mutex_del_relocated_state sg entry mutex.(mfPCP) owner node node.(curPrio)) mutex.(mfPCP)).(TskState)
    entry.(SchedState)).
  { change (sched_in_range sg (mutex_del_relocated_tasks entry mutex.(mfPCP) owner node node.(curPrio)) entry.(SchedState)).
    rewrite mutex_del_relocated_tasks_same_priority by exact Hnode; exact (proj1 (proj2 (proj2 Hvalid))). }
  pose proof (UCOS2_replace_sched_preserves_validity sg _ entry.(SchedState) Hafter Hsched eq_refl) as Hsame.
  assert (Epost : replace_SchedS entry.(SchedState)
      (mutex_del_ceiling_view (mutex_del_relocated_state sg entry mutex.(mfPCP) owner node node.(curPrio)) mutex.(mfPCP)) =
    mutex_del_ceiling_view (mutex_del_released_state entry mutex.(mfPCP)) mutex.(mfPCP)).
  { unfold mutex_del_ceiling_view, mutex_del_relocated_state.
    cbn [replace_SchedS replace_TskS TskState].
    rewrite mutex_del_relocated_tasks_same_priority by exact Hnode; destruct entry; reflexivity. }
  rewrite Epost in Hsame; exact Hsame.
Qed.

Lemma mutex_del_owner_scan_establishes_released_state :
  forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority ->
  (forall mid e, entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  mutex_del_released_state_inv sg eid mutex
    (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority Hvalid He Htype Hm Ho Henabled Hnode Hnotreserved Hscan Habsent.
  destruct (mutex_del_owner_scan_properties sg entry eid event mutex owner priority
    Hvalid He Htype Hm Ho Henabled Hnotreserved ltac:(intros other Hother;
      rewrite Hnode in Hother; injection Hother as E; subst other; exact Hscan))
    as [other [base [Hother [Hbase [Heffective [[Hmono Hbound] Hrest]]]]]].
  rewrite Hnode in Hother; injection Hother as E; subst other.
  split; [exact Henabled|]. split.
  - unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority); apply update_prio_tbl_same.
  - split.
    + exact (mutex_del_owner_priority_ceiling_view_preserves_validity sg entry eid event mutex owner node priority
        Hvalid He Htype Hm Ho Henabled Hnode Heffective Hmono Habsent).
    + exists event; rewrite mutex_del_owner_priority_event_state_eq; auto.
Qed.

Lemma mutex_del_released_state_ranges : forall sg eid mutex state,
  mutex_del_released_state_inv sg eid mutex state ->
  selected_kernel_profile sg /\ task_in_range sg state.(TskState) /\
  sched_in_range sg state.(TskState) state.(SchedState) /\
  event_in_range sg state.(TskState) state.(EventState).
Proof.
  intros sg eid mutex state [Henabled [Hclear [Hview [event [He [Htype Hm]]]]]].
  pose proof Hview as [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]].
  split; [exact Hprofile|]. split; [|split; [exact Hsched|exact Hevents]].
  eapply mutex_del_ceiling_view_tasks_in_range_back; [exact Htasks|exact Hclear|].
  intros reservation Hr; apply (proj1 (proj1 Hcross) mutex.(mfPCP) reservation Hr).
  exists eid, event, mutex; repeat split; assumption || reflexivity.
Qed.

Lemma mutex_del_ceiling_view_event_wake_commute :
  forall sg state ceiling eid event tid old kind message result,
  mutex_del_ceiling_view (event_wake_state sg state eid event tid old kind message result) ceiling =
  event_wake_state sg (mutex_del_ceiling_view state ceiling) eid event tid old kind message result.
Proof. intros; reflexivity. Qed.

Lemma mutex_del_released_waiter_selection : forall sg eid mutex state event,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  exists tid tail old,
    event.(waitList) = tid :: tail /\ state.(TskState).(inUsedTaskStates) tid = Some old /\
    old.(curPrio) <> mutex.(mfPCP) /\
    state.(TskState).(prioTbl) old.(curPrio) = PTTask tid /\
    event_task_rdy sg state eid PendMutex 0 PendAbort =
      Some (old.(curPrio), event_wake_state sg state eid event tid old PendMutex 0 PendAbort).
Proof.
  intros sg eid mutex state event Hphase He Hnonempty.
  pose proof (mutex_del_released_state_ranges sg eid mutex state Hphase) as [Hprofile [Htasks [Hsched Hevents]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  pose proof (Hentries eid event He) as Hentry.
  destruct event.(waitList) as [|tid tail] eqn:Hlist;
    [exfalso; apply Hnonempty; reflexivity|].
  destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail Hsg Htasks Hentry Hlist)
    as [old [Hold [Hpriority Htable]]].
  rewrite Hpriority in Htable.
  exists tid, tail, old; split; [reflexivity|]. split; [exact Hold|]. split.
  - pose proof (proj1 (proj2 Hphase)) as Hclear; congruence.
  - split; [exact Htable|].
    exact (event_task_rdy_selects_waiter sg state eid event tid tail old PendMutex 0 PendAbort
      Hsg Htasks Hentry He Hlist Hold).
Qed.

(** This is the actual C priority-table load address.  Its inequality is
    derived from registration and the real Free cell, not from a new loop
    precondition.  The projection cannot affect the lookup or selected TCB. *)
Lemma mutex_del_released_waiter_table_read_eq : forall sg eid mutex state event tid tail old,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> event.(waitList) = tid :: tail ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  event_wait_priority state.(TskState) event = old.(curPrio) /\ old.(curPrio) <> mutex.(mfPCP) /\
  (mutex_del_ceiling_view state mutex.(mfPCP)).(TskState).(prioTbl)
    (event_wait_priority state.(TskState) event) =
    state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event).
Proof.
  intros sg eid mutex state event tid tail old Hphase He Hlist Hold.
  pose proof (mutex_del_released_state_ranges sg eid mutex state Hphase) as [Hprofile [Htasks [_ Hevents]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail Hsg Htasks
    (Hentries eid event He) Hlist) as [found [Hfound [Hpriority Htable]]].
  rewrite Hold in Hfound; injection Hfound as E; subst found.
  assert (Hne : old.(curPrio) <> mutex.(mfPCP)).
  { pose proof (proj1 (proj2 Hphase)) as Hclear; rewrite Hpriority in Htable; congruence. }
  split; [exact Hpriority|]. split; [exact Hne|].
  change (update_prio_tbl state.(TskState).(prioTbl) mutex.(mfPCP) PTReserved
    (event_wait_priority state.(TskState) event) = state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event)).
  apply update_prio_tbl_other; congruence.
Qed.

Lemma mutex_del_released_wake_preserves_state : forall sg eid mutex state event tid old,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> In tid event.(waitList) ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  mutex_del_released_state_inv sg eid mutex
    (event_wake_state sg state eid event tid old PendMutex 0 PendAbort).
Proof.
  intros sg eid mutex state event tid old [Henabled [Hclear [Hview [actual [Hactual [Htype Hm]]]]]] He Hin Hold.
  rewrite He in Hactual; injection Hactual as E; subst actual.
  split; [exact Henabled|]. split; [exact Hclear|]. split.
  - rewrite mutex_del_ceiling_view_event_wake_commute.
    eapply UCOS2_event_wake_preserves_validity; [exact Hview|exact He|exact Hin|exact Hold|].
    rewrite Htype; reflexivity.
  - exists (event_set_wait_list event (remove_Z_eqb tid event.(waitList))).
    split.
    + cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState
        update_event_field_raw inUsedEventStates]; rewrite Z.eqb_refl; reflexivity.
    + split; [exact Htype|exact Hm].
Qed.

Lemma mutex_del_released_owner_not_waiter : forall sg eid mutex state event owner tid,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> mutex.(mfOwner) = Some owner ->
  In tid event.(waitList) -> tid <> owner.
Proof.
  intros sg eid mutex state event owner tid [_ [_ [Hview [actual [Hactual [Htype Hm]]]]]] He Ho Hin E.
  rewrite He in Hactual; injection Hactual as Hactual; subst actual; subst tid.
  pose proof Hview as [_ [_ [_ [_ [Hcross _]]]]].
  pose proof Hcross as [_ [Hsnapshot _]].
  destruct (Hsnapshot eid event mutex owner He Htype Hm Ho) as [t [base [snapshot [_ [_ [_ [_ [_ [Habsent _]]]]]]]]].
  contradiction.
Qed.

Lemma mutex_del_released_wake_decompose : forall sg eid mutex state event priority after,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendAbort = Some (priority, after) ->
  exists tid tail old,
    event.(waitList) = tid :: tail /\ state.(TskState).(inUsedTaskStates) tid = Some old /\
    priority = old.(curPrio) /\ priority <> mutex.(mfPCP) /\
    after = event_wake_state sg state eid event tid old PendMutex 0 PendAbort /\
    mutex_del_released_state_inv sg eid mutex after /\
    after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list event tail).
Proof.
  intros sg eid mutex state event priority after Hphase He Hnonzero Hstep.
  destruct (mutex_del_released_waiter_selection sg eid mutex state event Hphase He Hnonzero)
    as [tid [tail [old [Hlist [Hold [Hne [Htable Hcall]]]]]]].
  rewrite Hcall in Hstep; injection Hstep as Hp Hafter; subst priority after.
  exists tid, tail, old; split; [exact Hlist|]. split; [exact Hold|].
  split; [reflexivity|]. split; [exact Hne|]. split; [reflexivity|]. split.
  - eapply mutex_del_released_wake_preserves_state; [exact Hphase|exact He| |exact Hold].
    rewrite Hlist; left; reflexivity.
  - pose proof (mutex_del_released_state_ranges sg eid mutex state Hphase) as [_ [_ [_ Hevents]]].
    pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
    pose proof (proj1 (proj1 (Hentries eid event He))) as Hnd.
    rewrite Hlist in Hnd; inversion Hnd as [|? ? Habsent Htail]; subst.
    cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState
      update_event_field_raw inUsedEventStates].
    rewrite Z.eqb_refl, Hlist, remove_Z_eqb_x_cons_x, remove_Z_eqb_notin_eq by exact Habsent; reflexivity.
Qed.

Lemma mutex_del_ceiling_view_wait_group_eq : forall tasks ceiling waiters,
  encode_event_wait_grp waiters (mutex_del_ceiling_view_tasks tasks ceiling) =
    encode_event_wait_grp waiters tasks.
Proof.
  intros tasks ceiling waiters; induction waiters as [|tid rest IH]; [reflexivity|].
  cbn [encode_event_wait_grp mutex_del_ceiling_view_tasks inUsedTaskStates].
  rewrite IH; reflexivity.
Qed.

Lemma mutex_del_ceiling_view_wait_priority_eq : forall tasks ceiling event,
  event_wait_priority (mutex_del_ceiling_view_tasks tasks ceiling) event = event_wait_priority tasks event.
Proof.
  intros; unfold event_wait_priority; rewrite mutex_del_ceiling_view_wait_group_eq; reflexivity.
Qed.

Lemma mutex_del_released_event_step_view : forall sg eid mutex state event priority after,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendAbort = Some (priority, after) ->
  event_task_rdy sg (mutex_del_ceiling_view state mutex.(mfPCP)) eid PendMutex 0 PendAbort =
    Some (priority, mutex_del_ceiling_view after mutex.(mfPCP)).
Proof.
  intros sg eid mutex state event priority after Hphase He Hnonzero Hstep.
  destruct (mutex_del_released_waiter_selection sg eid mutex state event Hphase He Hnonzero)
    as [tid [tail [old [Hlist [Hold [Hne [Htable Hcall]]]]]]].
  rewrite Hcall in Hstep; injection Hstep as Hp Hafter; subst priority after.
  destruct (mutex_del_released_waiter_table_read_eq sg eid mutex state event tid tail old Hphase He Hlist Hold)
    as [Hpriority [_ Hread]].
  rewrite mutex_del_ceiling_view_event_wake_commute.
  unfold event_task_rdy; change (EventState (mutex_del_ceiling_view state mutex.(mfPCP))) with state.(EventState).
  rewrite He.
  change (TskState (mutex_del_ceiling_view state mutex.(mfPCP))) with (mutex_del_ceiling_view_tasks state.(TskState) mutex.(mfPCP)).
  rewrite mutex_del_ceiling_view_wait_priority_eq, Hpriority.
  cbn [mutex_del_ceiling_view_tasks prioTbl inUsedTaskStates].
  rewrite update_prio_tbl_other by exact Hne.
  rewrite Htable, Hold; reflexivity.
Qed.

Lemma mutex_del_released_broadcast_view : forall sg eid mutex state priorities after,
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  mutex_del_released_state_inv sg eid mutex state ->
  mutex_del_released_state_inv sg eid mutex after /\
  event_broadcast sg eid PendMutex 0 PendAbort
    (mutex_del_ceiling_view state mutex.(mfPCP)) priorities (mutex_del_ceiling_view after mutex.(mfPCP)).
Proof.
  intros sg eid mutex state priorities after Hloop.
  induction Hloop as [state event He Hzero|state event p mid ps after He Hnonzero Hstep Hloop IH]; intro Hphase.
  - split; [exact Hphase|]. eapply event_broadcast_done; [exact He|].
    change (encode_event_wait_grp event.(waitList) (mutex_del_ceiling_view_tasks state.(TskState) mutex.(mfPCP)) = 0).
    rewrite mutex_del_ceiling_view_wait_group_eq; exact Hzero.
  - destruct (mutex_del_released_wake_decompose sg eid mutex state event p mid Hphase He Hnonzero Hstep)
      as [tid [tail [old [Hlist [Hold [Hp [Hne [Hmid [HphaseMid Hlookup]]]]]]]]].
    destruct (IH HphaseMid) as [HphaseAfter HviewLoop]; split; [exact HphaseAfter|].
    eapply event_broadcast_next; [exact He| | |exact HviewLoop].
    + change (encode_event_wait_grp event.(waitList) (mutex_del_ceiling_view_tasks state.(TskState) mutex.(mfPCP)) <> 0).
      rewrite mutex_del_ceiling_view_wait_group_eq; exact Hnonzero.
    + exact (mutex_del_released_event_step_view sg eid mutex state event p mid Hphase He Hnonzero Hstep).
Qed.

Lemma mutex_del_released_broadcast_exists : forall waiters sg eid mutex state event,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> event.(waitList) = waiters ->
  exists priorities after, event_broadcast sg eid PendMutex 0 PendAbort state priorities after /\
    mutex_del_released_state_inv sg eid mutex after /\
    after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list event []) /\
    length priorities = length waiters.
Proof.
  induction waiters as [|tid tail IH]; intros sg eid mutex state event Hphase He Hlist.
  - exists [], state; split.
    + eapply event_broadcast_done; [exact He|rewrite Hlist; reflexivity].
    + split; [exact Hphase|]. split; [|reflexivity].
      rewrite <- Hlist, event_set_wait_list_put_back; exact He.
  - pose proof (mutex_del_released_state_ranges sg eid mutex state Hphase) as [_ [_ [_ Hevents]]].
    pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
    assert (Hnonzero : encode_event_wait_grp event.(waitList) state.(TskState) <> 0).
    { intro Hzero; apply (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState) event.(waitList)
        (proj1 (Hentries eid event He)))) in Hzero; congruence. }
    destruct (mutex_del_released_waiter_selection sg eid mutex state event Hphase He Hnonzero)
      as [head [rest [old [Hlist' [Hold [Hne [Htable Hcall]]]]]]].
    rewrite Hlist in Hlist'; injection Hlist' as Ehead Erest; subst head rest.
    set (mid := event_wake_state sg state eid event tid old PendMutex 0 PendAbort).
    destruct (mutex_del_released_wake_decompose sg eid mutex state event old.(curPrio) mid Hphase He Hnonzero Hcall)
      as [head [rest [selected [Hlist' [Hselected [Hp [Hne' [Hmid [HphaseMid Hlookup]]]]]]]]].
    rewrite Hlist in Hlist'; injection Hlist' as Ehead Erest; subst head rest.
    destruct (IH sg eid mutex mid (event_set_wait_list event tail) HphaseMid Hlookup eq_refl)
      as [priorities [after [Hloop [HphaseAfter [Hfinal Hlength]]]]].
    exists (old.(curPrio) :: priorities), after; split.
    + eapply event_broadcast_next; [exact He|exact Hnonzero|exact Hcall|exact Hloop].
    + split; [exact HphaseAfter|]. split.
      * rewrite event_set_wait_list_last_write in Hfinal; exact Hfinal.
      * simpl; rewrite Hlength; reflexivity.
Qed.

Lemma mutex_del_released_broadcast_result : forall sg eid mutex state event priorities after,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  mutex_del_released_state_inv sg eid mutex after /\
  after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list event []) /\
  length priorities = length event.(waitList).
Proof.
  intros sg eid mutex state event priorities after Hphase He Hloop.
  destruct (mutex_del_released_broadcast_exists event.(waitList) sg eid mutex state event Hphase He eq_refl)
    as [ps [post [Hrun Hresult]]].
  destruct (event_broadcast_deterministic sg eid PendMutex 0 PendAbort state ps post priorities after Hrun Hloop)
    as [-> ->]; exact Hresult.
Qed.

Lemma mutex_del_released_broadcast_owner_frame : forall sg eid mutex state event priorities after owner,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> mutex.(mfOwner) = Some owner ->
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  after.(TskState).(inUsedTaskStates) owner = state.(TskState).(inUsedTaskStates) owner.
Proof.
  intros sg eid mutex state event priorities after owner Hphase He Ho Hloop.
  pose proof Hphase as [_ [_ [Hview [actual [Hactual [Htype Hm]]]]]].
  rewrite He in Hactual; injection Hactual as E; subst actual.
  pose proof (proj2 (mutex_del_released_broadcast_view sg eid mutex state priorities after Hloop Hphase)) as HviewLoop.
  exact (event_broadcast_task_frame sg eid PendMutex 0 PendAbort _ priorities _ HviewLoop event owner Hview He
    ltac:(rewrite Htype; reflexivity)
    ltac:(intro Hin; exact (mutex_del_released_owner_not_waiter sg eid mutex state event owner owner Hphase He Ho Hin eq_refl))).
Qed.

(** Actual EventTaskRdy residual.  Its table is lent to the callee as one
    complete actual table (including PTFree at the released PCP), and is
    absent from this frame.  The selected TCB and ready cells are absent too. *)
Definition mutex_del_wake_task_frame (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (tid : TaskID) : Assertion :=
  store_map_missing_i (used_task_rep sg) tasks.(inUsedTaskStates) tid **
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error tasks.(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg tasks.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> tasks.(taskCount) ** task_reg_allocator_rep sg tasks.

Lemma mutex_del_wake_task_storage_split : forall sg tasks tid old,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false -> sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tasks.(inUsedTaskStates) tid = Some old ->
  task_public_storage sg tasks |--
  tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg old) **
  store_prio_tbl sg tasks.(prioTbl) ** mutex_del_wake_task_frame sg tasks tid.
Proof.
  intros sg tasks tid old Hmulti Hprofiling Hold.
  sep_apply_l_atomic (task_public_storage_split_task sg tasks tid old Hold).
  rewrite used_task_rep_tcb64, task_slot_addr_tcb64 by assumption.
  unfold task_public_storage_without_task, task_public_storage_without_used_map,
    mutex_del_wake_task_frame; entailer!.
Qed.

Lemma mutex_del_wake_task_storage_merge : forall sg tasks tid new,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false -> sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg new) **
  store_prio_tbl sg tasks.(prioTbl) ** mutex_del_wake_task_frame sg tasks tid |--
  task_public_storage sg (glob_task_set_usedtask tasks tid new).
Proof.
  intros sg tasks tid new Hmulti Hprofiling.
  rewrite task_slot_addr_tcb64 by assumption; rewrite <- used_task_rep_tcb64 by assumption.
  match goal with |- ?Pre |-- _ =>
    assert (Hopen : Pre |-- used_task_rep sg tid new ** task_public_storage_without_task sg tasks tid)
  end.
  { unfold mutex_del_wake_task_frame, task_public_storage_without_task,
      task_public_storage_without_used_map; entailer!. }
  intros heap Howned; apply (task_public_storage_merge_updated_task sg tasks tid new heap).
  exact (Hopen heap Howned).
Qed.

Definition mutex_del_wake_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (tid : TaskID) : Assertion :=
  mutex_del_wake_task_frame sg state.(TskState) tid **
  sched_physical_rep sg state.(SchedState) **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state.

Lemma mutex_del_raw_task_sched_event_equiv : forall sg state,
  UCOS2_raw_rep sg state --||--
    task_public_storage sg state.(TskState) **
    sched_raw_rep sg state.(TskState) state.(SchedState) **
    event_raw_rep sg state.(TskState) state.(EventState) **
    UCOS2_raw_rep_missing_task_storage_sched_event sg state.
Proof.
  intros; split; unfold UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched_event; entailer!.
Qed.

Lemma mutex_del_released_wake_split : forall sg eid mutex state event,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_object_layout_prop sg eid ->
  mutex_del_released_rep sg eid mutex state ** unmap_table_rep sg |-- EX tid, EX old,
    coq_prop (event_task_rdy_entry sg state.(TskState) eid event tid old) &&
    (event_task_rdy_pre sg state.(TskState) eid event tid old 16 2
       (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
       (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
     mutex_del_wake_frame sg state eid tid).
Proof.
  intros sg eid mutex state event Hphase He Hnonzero Hlayout.
  pose proof (mutex_del_released_state_ranges sg eid mutex state Hphase) as [Hprofile [Htasks [_ Hevents]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  destruct (mutex_del_released_waiter_selection sg eid mutex state event Hphase He Hnonzero)
    as [tid [tail [old [Hlist [Hold Hrest]]]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  assert (Hentry : event_task_rdy_entry sg state.(TskState) eid event tid old).
  { split; [exact Hsg|]. split; [exact Hlayout|]. split; [exact Hmulti|].
    split; [exact Htasks|]. split; [exact (Hentries eid event He)|].
    split; [rewrite Hlist; reflexivity|exact Hold]. }
  unfold mutex_del_released_rep; Intros.
  rewrite mutex_del_raw_task_sched_event_equiv.
  sep_apply_l_atomic (mutex_del_wake_task_storage_split sg state.(TskState) tid old Hmulti Hprofiling Hold).
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid event He).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  Exists tid old; unfold event_task_rdy_pre, mutex_del_wake_frame, used_event_rep.
  entailer!; unfold sched_row_values; reflexivity.
Qed.

Lemma mutex_del_raw_event_wake_merge : forall sg state eid event tid old kind message result,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  let post := event_wake_state sg state eid event tid old kind message result in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  event_raw_rep sg state.(TskState) post.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state |-- UCOS2_raw_rep sg post.
Proof.
  intros sg state eid event tid old kind message result He Hold post.
  assert (Hindex : event_raw_rep sg state.(TskState) post.(EventState) =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (UCOS2_event_wake_preserves_residual sg state eid event tid old kind message result He); fold post.
  unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched_event; entailer!.
Qed.

Lemma mutex_del_event_task_rdy_merge_raw : forall sg eid state event tid old priority,
  selected_kernel_profile sg ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_task_rdy_entry sg state.(TskState) eid event tid old ->
  event_task_rdy_post sg state.(TskState) eid event tid old 0 16 2
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
  mutex_del_wake_frame sg state eid tid |--
  coq_prop (event_task_rdy sg state eid PendMutex 0 PendAbort =
    Some (priority, event_wake_state sg state eid event tid old PendMutex 0 PendAbort)) &&
  (UCOS2_raw_rep sg (event_wake_state sg state eid event tid old PendMutex 0 PendAbort) **
   unmap_table_rep sg).
Proof.
  intros sg eid state event tid old priority Hprofile He Hentry.
  pose proof Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (event_task_rdy_selection sg state.(TskState) eid event tid old Hentry) as [_ [_ [_ [Hprio _]]]].
  destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  pose proof (event_task_rdy_selects_waiter sg state eid event tid tail old PendMutex 0 PendAbort
    Hsg Htasks Hwait He Hlist Hold) as Hstep.
  unfold event_task_rdy_post, mutex_del_wake_frame; Intros.
  assert (Hreturned : priority = old.(curPrio)) by tauto; subst priority.
  rewrite (event_task_rdy_typed_image_eq sg old 0 16 2 PendMutex PendAbort eq_refl eq_refl).
  rewrite (event_task_rdy_scheduler_group_eq sg state.(TskState) state.(SchedState) tid old _ Hold).
  rewrite (event_task_rdy_scheduler_rows_eq sg state.(TskState) state.(SchedState) tid old _ Hold Hprio).
  sep_apply_l_atomic (mutex_del_wake_task_storage_merge sg state.(TskState) tid
    (task_event_wake_single old PendMutex 0 PendAbort) Hmulti Hprofiling).
  fold (used_event_rep sg state.(TskState) eid (event_set_wait_list event (remove_Z_eqb tid event.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg state.(TskState) state.(EventState) eid
    (event_set_wait_list event (remove_Z_eqb tid event.(waitList)))).
  rewrite <- sched_rows_array_equiv.
  rewrite <- (sched_wake_by_status_physical_rep_eq sg state.(TskState) state.(SchedState) tid
    (task_status_clear_wait (encode_task_status old.(stat)) 16)).
  assert (Hstatus : task_status_clear_wait (encode_task_status old.(stat)) 16 =
    encode_task_status (task_event_wake_single old PendMutex 0 PendAbort).(stat)).
  { change (task_status_clear_wait (encode_task_status old.(stat)) 16 =
      encode_task_status (task_clear_pending_status old.(stat) PendMutex)).
    rewrite task_clear_pending_status_encoding; reflexivity. }
  rewrite Hstatus.
  assert (Hindex : forall s, sched_raw_rep sg state.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid (task_event_wake_single old PendMutex 0 PendAbort)) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    simpl; destruct (Z.eqb slot tid) eqn:E; [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  set (woken_sched := sched_wake_by_status sg state.(TskState) state.(SchedState) tid
    (encode_task_status (task_event_wake_single old PendMutex 0 PendAbort).(stat))).
  assert (Hsched :
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp woken_sched.(readyList) state.(TskState) **
    sched_rows_rep sg state.(TskState) woken_sched.(readyList) [0;1;2;3;4;5;6;7] **
    sched_physical_rep sg woken_sched |--
    sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid
      (task_event_wake_single old PendMutex 0 PendAbort)) woken_sched).
  { rewrite <- Hindex; unfold sched_raw_rep; reflexivity. }
  sep_apply_l_atomic Hsched.
  pose proof (mutex_del_raw_event_wake_merge sg state eid event tid old PendMutex 0 PendAbort He Hold) as Hmerge.
  cbn zeta in Hmerge; cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState SchedState EventState] in Hmerge.
  fold woken_sched in Hmerge; sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Lemma mutex_del_released_wake_merge : forall sg eid mutex state event tid old priority,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_task_rdy_entry sg state.(TskState) eid event tid old ->
  event_task_rdy_post sg state.(TskState) eid event tid old 0 16 2
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
  mutex_del_wake_frame sg state eid tid |--
  coq_prop (event_task_rdy sg state eid PendMutex 0 PendAbort =
    Some (priority, event_wake_state sg state eid event tid old PendMutex 0 PendAbort)) &&
  (mutex_del_released_rep sg eid mutex (event_wake_state sg state eid event tid old PendMutex 0 PendAbort) **
   unmap_table_rep sg).
Proof.
  intros sg eid mutex state event tid old priority Hphase He Hentry.
  pose proof (proj1 (mutex_del_released_state_ranges sg eid mutex state Hphase)) as Hprofile.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hin : In tid event.(waitList)).
  { destruct event.(waitList); [discriminate|]. inversion Hhead; left; reflexivity. }
  pose proof (mutex_del_released_wake_preserves_state sg eid mutex state event tid old Hphase He Hin Hold) as Hafter.
  sep_apply_l_atomic (mutex_del_event_task_rdy_merge_raw sg eid state event tid old priority Hprofile He Hentry).
  unfold mutex_del_released_rep; entailer!.
Qed.

Lemma mutex_del_released_ceiling_view_eq : forall state ceiling,
  state.(TskState).(prioTbl) ceiling = PTFree ->
  mutex_del_released_state (mutex_del_ceiling_view state ceiling) ceiling = state.
Proof.
  intros state ceiling Hclear.
  assert (Htable : update_prio_tbl state.(TskState).(prioTbl) ceiling PTFree = state.(TskState).(prioTbl)).
  { rewrite <- Hclear; apply update_prio_tbl_put_back. }
  assert (Htasks : mutex_del_released_tasks (mutex_del_ceiling_view state ceiling) ceiling = state.(TskState)).
  { unfold mutex_del_released_tasks, mutex_del_ceiling_view, mutex_del_ceiling_view_tasks, mutex_del_released_table.
    cbn [replace_TskS TskState inUsedTaskStates unUsedTaskStates tcbListHead prioTbl
      taskRegNextID parkedTaskStacks taskLifecycle taskCount].
    rewrite update_prio_tbl_overwrite, Htable; destruct state.(TskState); reflexivity. }
  unfold mutex_del_released_state; rewrite Htasks; unfold mutex_del_ceiling_view; destruct state; reflexivity.
Qed.

Lemma mutex_del_released_recycle_owned_consistency : forall sg eid mutex state event owner image,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> event.(waitList) = [] ->
  mutex.(mfOwner) = Some owner ->
  cross_module_consistency sg (replace_EventS (event_recycle sg state.(EventState) eid image) state) /\
  pending_mutex_consistency sg state.(TskState) (event_recycle sg state.(EventState) eid image).
Proof.
  intros sg eid mutex state event owner image Hphase He Hempty Ho.
  pose proof Hphase as [Henabled [Hclear [Hview [actual [Hactual [Htype Hm]]]]]].
  rewrite He in Hactual; injection Hactual as E; subst actual.
  pose proof Hview as [_ [_ [_ [_ [Hcross Hrest]]]]].
  pose proof Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  destruct (Hsnapshot eid event mutex owner He Htype Hm Ho)
    as [node [base [snapshot [Hnode [Hbase HsnapshotRest]]]]].
  destruct (proj2 (proj2 Htable) owner node Hnode) as [permanent [_ [Hcurrent Hclaims]]].
  assert (HreleasedTasks : mutex_del_released_tasks (mutex_del_ceiling_view state mutex.(mfPCP)) mutex.(mfPCP) = state.(TskState)).
  { exact (f_equal TskState (mutex_del_released_ceiling_view_eq state mutex.(mfPCP) Hclear)). }
  assert (HrelocatedTasks : mutex_del_relocated_tasks (mutex_del_ceiling_view state mutex.(mfPCP))
    mutex.(mfPCP) owner node node.(curPrio) = state.(TskState)).
  { rewrite mutex_del_relocated_tasks_same_priority by exact Hnode; exact HreleasedTasks. }
  assert (Heffective : task_effective_priority sg
    (mutex_del_released_table (mutex_del_ceiling_view state mutex.(mfPCP)) mutex.(mfPCP)) owner node.(curPrio)).
  { change (task_effective_priority sg
      (mutex_del_released_tasks (mutex_del_ceiling_view state mutex.(mfPCP)) mutex.(mfPCP)).(prioTbl) owner node.(curPrio)).
    rewrite HreleasedTasks; eapply task_effective_priority_alias_ext; [|exact Hcurrent].
    intro p; apply mutex_del_ceiling_view_alias_iff; exact Hclear. }
  pose proof (mutex_del_recycled_table_consistency sg (mutex_del_ceiling_view state mutex.(mfPCP))
    eid event mutex owner node node.(curPrio) image Hcross He Htype Hm Ho Henabled Hnode Heffective) as HtableAfter.
  rewrite HrelocatedTasks in HtableAfter.
  pose proof (mutex_del_recycled_snapshot_in_range sg (mutex_del_ceiling_view state mutex.(mfPCP))
    eid event mutex owner node node.(curPrio) image Hcross He Htype Hm Ho Henabled Hnode) as HsnapshotAfter.
  rewrite HrelocatedTasks in HsnapshotAfter.
  assert (Hpending : pending_mutex_consistency sg (mutex_del_ceiling_view state mutex.(mfPCP)).(TskState) state.(EventState)).
  { exact (UCOS2_state_inv_pending_mutex sg _ Hview). }
  pose proof (mutex_del_recycled_pending_mutex_consistency sg (mutex_del_ceiling_view state mutex.(mfPCP))
    eid event mutex owner node node.(curPrio) image Hpending He Htype Hm Henabled) as HpendingAfter.
  rewrite HrelocatedTasks in HpendingAfter.
  split; [|exact HpendingAfter]. split; [exact HtableAfter|]. split; [exact HsnapshotAfter|]. split.
  - apply (mutex_del_empty_event_remove_wait_consistency sg state eid event image He Hempty); exact Hwait.
  - split.
    + intros mid e m Hget Hty Hfields.
      assert (Hne : m.(mfPCP) <> mutex.(mfPCP)).
      { exact (mutex_del_surviving_ceiling_ne sg state eid event mutex image mid e m
          Hunique He Htype Hm Henabled Hget Hty Hfields). }
      apply mutex_del_recycled_event_lookup in Hget.
      destruct (Hprotocol mid e m (proj2 Hget) Hty Hfields) as [Hrange [Howner Hslot]].
      split; [exact Hrange|]. split; [exact Howner|].
      change (m.(mfPCP) = sg.(osPrioMutexCeilDis) \/
        (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
         (update_prio_tbl state.(TskState).(prioTbl) mutex.(mfPCP) PTReserved m.(mfPCP) = PTReserved \/
          exists tid, m.(mfOwner) = Some tid /\
            update_prio_tbl state.(TskState).(prioTbl) mutex.(mfPCP) PTReserved m.(mfPCP) = PTTask tid))) in Hslot.
      rewrite update_prio_tbl_other in Hslot by exact Hne; exact Hslot.
    + split; [|split; [exact Hflags|exact Htimer]].
      eapply mutex_enabled_pcp_unique_transport with (lvs1 := state); [|exact Hunique].
      intros mid e m Hget Hty Hfields; apply mutex_del_recycled_event_lookup in Hget.
      exists e, m; intuition.
Qed.

(** The projection is discarded here.  The conclusion is the full
    invariant of the actual Free-table state after actual ECB recycling.
    Equal-priority owner TCBs/caches are not changed merely to use a lemma. *)
Lemma mutex_del_released_recycle_preserves_validity : forall sg eid mutex state event image,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> event.(waitList) = [] ->
  UCOS2_state_inv sg (replace_EventS (event_recycle sg state.(EventState) eid image) state).
Proof.
  intros sg eid mutex state event image Hphase He Hempty.
  pose proof Hphase as [Henabled [Hclear [Hview [actual [Hactual [Htype Hm]]]]]].
  rewrite He in Hactual; injection Hactual as E; subst actual.
  destruct mutex.(mfOwner) as [owner|] eqn:Ho.
  - destruct (mutex_del_released_recycle_owned_consistency sg eid mutex state event owner image
      Hphase He Hempty Ho) as [HcrossAfter HpendingAfter].
    pose proof (mutex_del_released_state_ranges sg eid mutex state Hphase) as [Hprofile [Htasks [Hsched Hevents]]].
    pose proof Hview as [_ [_ [_ [_ [_ [Hidle [Hstatus [Hflags [Hmemory [Htimer [Hstats [Hcontrol
      [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]].
    assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (event_recycle sg state.(EventState) eid image) state)).
    { apply kernel_names_valid_replace_event; [exact Hreferences|apply event_recycle_name_references]. }
    split; [exact Hprofile|]. split; [exact Htasks|]. split; [exact Hsched|]. split.
    + apply event_recycle_preserves_in_range with (node := event); [exact Hevents|exact He].
    + split; [exact HcrossAfter|]. split; [exact Hidle|]. split; [exact Hstatus|].
      split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
      split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
      split; [exact HreferencesAfter|]. split; [exact Hstacks|exact HpendingAfter].
  - pose proof (mutex_del_unrelocated_recycle_preserves_validity sg (mutex_del_ceiling_view state mutex.(mfPCP))
      eid event mutex image Hview He Htype Hm Hempty (or_intror Ho)) as Hafter.
    rewrite mutex_del_unrelocated_source_branch_eq in Hafter.
    destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|].
    rewrite mutex_del_released_ceiling_view_eq in Hafter by exact Hclear; exact Hafter.
Qed.

Lemma mutex_del_released_ceiling_in_range : forall sg eid mutex state,
  mutex_del_released_state_inv sg eid mutex state -> 0 <= mutex.(mfPCP) < 64.
Proof.
  intros sg eid mutex state [Henabled [Hclear [Hview [event [He [Htype Hm]]]]]].
  pose proof Hview as [Hprofile [_ [_ [_ [Hcross _]]]]].
  pose proof Hcross as [_ [_ [_ [Hprotocol _]]]].
  pose proof (proj1 (Hprotocol eid event mutex He Htype Hm)) as Hrange.
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  destruct Hrange as [Hdisabled|Hrange]; [contradiction|lia].
Qed.

Lemma mutex_del_released_ceiling_merge_repeated_store : forall sg eid mutex state,
  mutex_del_released_state_inv sg eid mutex state ->
  (sg.(g_OSTCBPrioTbl) + mutex.(mfPCP) * sizeof(PTR)) # Ptr |-> 0 **
  store_prio_tbl_missing_i sg state.(TskState).(prioTbl) mutex.(mfPCP) **
  UCOS2_raw_rep_missing_priority_table sg state |-- mutex_del_released_rep sg eid mutex state.
Proof.
  intros sg eid mutex state Hphase.
  pose proof (mutex_del_released_ceiling_in_range sg eid mutex state Hphase) as Hrange.
  pose proof (proj1 (proj2 Hphase)) as Hclear.
  assert (Htable : update_prio_tbl state.(TskState).(prioTbl) mutex.(mfPCP) PTFree = state.(TskState).(prioTbl)).
  { rewrite <- Hclear; apply update_prio_tbl_put_back. }
  pose proof (store_prio_tbl_merge_updated_cell sg state.(TskState).(prioTbl) mutex.(mfPCP) PTFree Hrange) as Hmerge.
  cbn [prio_tbl_entry_to_addr] in Hmerge; rewrite Htable in Hmerge.
  sep_apply_l_atomic Hmerge; unfold mutex_del_released_rep; rewrite UCOS2_raw_rep_priority_table_equiv; entailer!.
Qed.

Lemma mutex_del_released_recycle_merge_inv : forall sg eid mutex state event image,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg state.(EventState).(unUsedEventStates) image) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid ** mutex_del_event_frame sg state eid |--
  UCOS2_inv sg (replace_EventS (event_recycle sg state.(EventState) eid image) state).
Proof.
  intros sg eid mutex state event image Hphase He Hzero.
  pose proof (mutex_del_released_state_ranges sg eid mutex state Hphase) as [_ [_ [_ Hevents]]].
  pose proof Hevents as [Hpool [Hfree [_ [Hfields [_ [_ Hentries]]]]]].
  pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState) event.(waitList)
    (proj1 (Hentries eid event He))) Hzero) as Hempty.
  pose proof (mutex_del_released_recycle_preserves_validity sg eid mutex state event image Hphase He Hempty) as Hafter.
  pose proof Hphase as [_ [_ [_ [actual [Hactual [Htype Hm]]]]]].
  rewrite He in Hactual; injection Hactual as E; subst actual.
  assert (Hqueue : event.(queueFields) = None).
  { apply non_queue_event_has_no_queue_fields; [exact (Hfields eid event He)|rewrite Htype; discriminate]. }
  sep_apply_l_atomic (mutex_del_recycle_event_merge_raw sg state eid event image Hpool Hfree He Hqueue).
  unfold UCOS2_inv; entailer!.
Qed.

Lemma mutex_del_released_broadcast_priority_table_eq : forall sg eid mutex state priorities after,
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  mutex_del_released_state_inv sg eid mutex state ->
  after.(TskState).(prioTbl) = state.(TskState).(prioTbl).
Proof.
  intros sg eid mutex state priorities after Hloop.
  induction Hloop as [state event He Hzero|state event p mid ps after He Hnonzero Hstep Hloop IH]; intro Hphase;
    [reflexivity|].
  destruct (mutex_del_released_wake_decompose sg eid mutex state event p mid Hphase He Hnonzero Hstep)
    as [tid [tail [old [Hlist [Hold [Hp [Hne [Hmid [HphaseMid Hlookup]]]]]]]]].
  rewrite (IH HphaseMid), Hmid; reflexivity.
Qed.

Lemma mutex_del_released_broadcast_updates_waiter : forall sg eid mutex state event priorities after tid old,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  In tid event.(waitList) -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  after.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old PendMutex 0 PendAbort).
Proof.
  intros sg eid mutex state event priorities after tid old Hphase He Hloop Hin Hold.
  pose proof Hphase as [_ [_ [Hview [actual [Hactual [Htype Hm]]]]]].
  rewrite He in Hactual; injection Hactual as E; subst actual.
  pose proof (proj2 (mutex_del_released_broadcast_view sg eid mutex state priorities after Hloop Hphase)) as HviewLoop.
  exact (event_broadcast_updates_waiter sg eid PendMutex 0 PendAbort _ priorities _ HviewLoop event tid old
    Hview He ltac:(rewrite Htype; reflexivity) Hin Hold).
Qed.

(** The source retains this INITIAL EventGrp observation for its later
    OS_Sched guard.  It does not mean that a waiter was actually made ready:
    suspended waiters are still woken/aborted without ready insertion. *)
Lemma mutex_del_released_broadcast_empty_iff_initial_group_zero :
  forall sg eid mutex state event priorities after,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  (encode_event_wait_grp event.(waitList) state.(TskState) = 0 <-> priorities = []).
Proof.
  intros sg eid mutex state event priorities after Hphase He Hloop.
  pose proof (mutex_del_released_broadcast_result sg eid mutex state event priorities after Hphase He Hloop)
    as [_ [_ Hlength]].
  pose proof (mutex_del_released_state_ranges sg eid mutex state Hphase) as [_ [_ [_ Hevents]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  rewrite (encode_event_wait_grp_zero_iff_empty sg state.(TskState) event.(waitList) (proj1 (Hentries eid event He))).
  split; intro Hempty.
  - apply length_zero_iff_nil; rewrite Hlength, Hempty; reflexivity.
  - apply length_zero_iff_nil; rewrite <- Hlength, Hempty; reflexivity.
Qed.

Lemma mutex_del_released_broadcast_recycle_merge_inv :
  forall sg eid mutex state event priorities after image,
  mutex_del_released_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg after.(EventState).(unUsedEventStates) image) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid ** mutex_del_event_frame sg after eid |--
  UCOS2_inv sg (replace_EventS (event_recycle sg after.(EventState) eid image) after).
Proof.
  intros sg eid mutex state event priorities after image Hphase He Hloop.
  destruct (mutex_del_released_broadcast_result sg eid mutex state event priorities after Hphase He Hloop)
    as [HphaseAfter [Hlookup Hlength]].
  apply (mutex_del_released_recycle_merge_inv sg eid mutex after (event_set_wait_list event []) image
    HphaseAfter Hlookup eq_refl).
Qed.

(** The parent C loop joins two real states: a disabled PCP has not
    changed the invariant, while an enabled PCP has been released.  The
    latter alternative retains its actual Free table and only the pure
    projection proved above.  This is not an extra public call premise. *)
Definition mutex_del_wake_state_inv (sg : StableGlobVars) (eid : EventID)
  (mutex : MutexFields) (state : UCOS2_Verify_State) : Prop :=
  exists event, state.(EventState).(inUsedEventStates) eid = Some event /\
    event.(eventType) = OS_EVENT_TYPE_MUTEX /\ event.(mutexFields) = Some mutex /\
    ((mutex.(mfPCP) = sg.(osPrioMutexCeilDis) /\ UCOS2_state_inv sg state) \/
     mutex_del_released_state_inv sg eid mutex state).

Definition mutex_del_wake_rep (sg : StableGlobVars) (eid : EventID)
  (mutex : MutexFields) (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (mutex_del_wake_state_inv sg eid mutex state) && UCOS2_raw_rep sg state.

Lemma mutex_del_released_state_implies_wake_state : forall sg eid mutex state,
  mutex_del_released_state_inv sg eid mutex state -> mutex_del_wake_state_inv sg eid mutex state.
Proof.
  intros sg eid mutex state Hreleased.
  destruct Hreleased as [Henabled [Hclear [Hview [event [He [Htype Hfields]]]]]].
  exists event; repeat split; try assumption.
  right; split; [exact Henabled|]. split; [exact Hclear|]. split; [exact Hview|].
  exists event; auto.
Qed.

Lemma mutex_del_disabled_state_implies_wake_state : forall sg eid mutex state event,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfPCP) = sg.(osPrioMutexCeilDis) -> mutex_del_wake_state_inv sg eid mutex state.
Proof. intros; exists event; repeat split; auto. Qed.

Lemma mutex_del_ceiling_view_release_eq : forall state ceiling,
  state.(TskState).(prioTbl) ceiling = PTReserved ->
  mutex_del_ceiling_view (mutex_del_released_state state ceiling) ceiling = state.
Proof.
  intros state ceiling Hreserved.
  assert (Htable : update_prio_tbl state.(TskState).(prioTbl) ceiling PTReserved = state.(TskState).(prioTbl)).
  { rewrite <- Hreserved; apply update_prio_tbl_put_back. }
  unfold mutex_del_ceiling_view, mutex_del_released_state, mutex_del_ceiling_view_tasks,
    mutex_del_released_tasks, mutex_del_released_table.
  cbn [replace_TskS TskState inUsedTaskStates unUsedTaskStates tcbListHead prioTbl
    taskRegNextID parkedTaskStacks taskLifecycle taskCount].
  rewrite update_prio_tbl_overwrite, Htable.
  destruct state as [interrupt tasks scheduler events tick flags memory timer statistics control names].
  simpl; destruct tasks; reflexivity.
Qed.

Lemma mutex_del_unowned_enabled_establishes_released_state : forall sg entry eid event mutex,
  UCOS2_state_inv sg entry -> entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = None -> mutex_pcp_enabled sg mutex ->
  mutex_del_released_state_inv sg eid mutex (mutex_del_released_state entry mutex.(mfPCP)).
Proof.
  intros sg entry eid event mutex Hvalid He Htype Hfields Hnone Henabled.
  pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  pose proof Hcross as [_ [_ [_ [Hprotocol _]]]].
  destruct (Hprotocol eid event mutex He Htype Hfields) as [_ [_ Hslot]].
  assert (Hreserved : entry.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved).
  { destruct Hslot as [Hdisabled|[_ [Hreserved|[owner [Howner Hcell]]]]];
      [contradiction|exact Hreserved|congruence]. }
  split; [exact Henabled|]. split; [apply update_prio_tbl_same|]. split.
  - rewrite mutex_del_ceiling_view_release_eq by exact Hreserved; exact Hvalid.
  - exists event; repeat split; assumption.
Qed.

Lemma mutex_del_wake_state_ranges : forall sg eid mutex state,
  mutex_del_wake_state_inv sg eid mutex state ->
  selected_kernel_profile sg /\ task_in_range sg state.(TskState) /\
  sched_in_range sg state.(TskState) state.(SchedState) /\
  event_in_range sg state.(TskState) state.(EventState).
Proof.
  intros sg eid mutex state [event [He [Htype [Hfields [[Hdisabled Hvalid]|Hreleased]]]]].
  - destruct Hvalid as [Hprofile [Htasks [Hsched [Hevents Hrest]]]]; auto.
  - exact (mutex_del_released_state_ranges sg eid mutex state Hreleased).
Qed.

Lemma mutex_del_wake_preserves_state : forall sg eid mutex state event tid old,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> In tid event.(waitList) ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  mutex_del_wake_state_inv sg eid mutex
    (event_wake_state sg state eid event tid old PendMutex 0 PendAbort).
Proof.
  intros sg eid mutex state event tid old [actual [Hactual [Htype [Hfields Hphase]]]] He Hin Hold.
  rewrite He in Hactual; injection Hactual as E; subst actual.
  destruct Hphase as [[Hdisabled Hvalid]|Hreleased].
  - exists (event_set_wait_list event (remove_Z_eqb tid event.(waitList))).
    split.
    + cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState
        update_event_field_raw inUsedEventStates]; rewrite Z.eqb_refl; reflexivity.
    + split; [exact Htype|]. split; [exact Hfields|]. left; split; [exact Hdisabled|].
      eapply UCOS2_event_wake_preserves_validity; [exact Hvalid|exact He|exact Hin|exact Hold|].
      rewrite Htype; reflexivity.
  - apply mutex_del_released_state_implies_wake_state.
    exact (mutex_del_released_wake_preserves_state sg eid mutex state event tid old Hreleased He Hin Hold).
Qed.

Lemma mutex_del_wake_recycle_preserves_validity : forall sg eid mutex state event image,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event -> event.(waitList) = [] ->
  UCOS2_state_inv sg (replace_EventS (event_recycle sg state.(EventState) eid image) state).
Proof.
  intros sg eid mutex state event image [actual [Hactual [Htype [Hfields Hphase]]]] He Hempty.
  rewrite He in Hactual; injection Hactual as E; subst actual.
  destruct Hphase as [[Hdisabled Hvalid]|Hreleased].
  - pose proof (mutex_del_unrelocated_recycle_preserves_validity sg state eid event mutex image
      Hvalid He Htype Hfields Hempty (or_introl Hdisabled)) as Hafter.
    rewrite mutex_del_unrelocated_source_branch_eq in Hafter.
    destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [exact Hafter|contradiction].
  - exact (mutex_del_released_recycle_preserves_validity sg eid mutex state event image Hreleased He Hempty).
Qed.

Lemma mutex_del_wake_split : forall sg eid mutex state event,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_object_layout_prop sg eid ->
  mutex_del_wake_rep sg eid mutex state ** unmap_table_rep sg |-- EX tid, EX old,
    coq_prop (event_task_rdy_entry sg state.(TskState) eid event tid old) &&
    (event_task_rdy_pre sg state.(TskState) eid event tid old 16 2
       (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
       (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
     mutex_del_wake_frame sg state eid tid).
Proof.
  intros sg eid mutex state event Hphase He Hnonzero Hlayout.
  pose proof (mutex_del_wake_state_ranges sg eid mutex state Hphase) as [Hprofile [Htasks [_ Hevents]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  destruct event.(waitList) as [|tid tail] eqn:Hlist; [contradiction Hnonzero; reflexivity|].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail
    Hsg Htasks (Hentries eid event He) Hlist) as [old [Hold Hselection]].
  assert (Hentry : event_task_rdy_entry sg state.(TskState) eid event tid old).
  { split; [exact Hsg|]. split; [exact Hlayout|]. split; [exact Hmulti|].
    split; [exact Htasks|]. split; [exact (Hentries eid event He)|].
    split; [rewrite Hlist; reflexivity|exact Hold]. }
  unfold mutex_del_wake_rep; Intros.
  rewrite mutex_del_raw_task_sched_event_equiv.
  sep_apply_l_atomic (mutex_del_wake_task_storage_split sg state.(TskState) tid old Hmulti Hprofiling Hold).
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid event He).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  Exists tid old; unfold event_task_rdy_pre, mutex_del_wake_frame, used_event_rep.
  entailer!; unfold sched_row_values; reflexivity.
Qed.

Lemma mutex_del_wake_merge : forall sg eid mutex state event tid old priority,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_task_rdy_entry sg state.(TskState) eid event tid old ->
  event_task_rdy_post sg state.(TskState) eid event tid old 0 16 2
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
  mutex_del_wake_frame sg state eid tid |--
  coq_prop (event_task_rdy sg state eid PendMutex 0 PendAbort =
    Some (priority, event_wake_state sg state eid event tid old PendMutex 0 PendAbort)) &&
  (mutex_del_wake_rep sg eid mutex (event_wake_state sg state eid event tid old PendMutex 0 PendAbort) **
   unmap_table_rep sg).
Proof.
  intros sg eid mutex state event tid old priority Hphase He Hentry.
  pose proof (proj1 (mutex_del_wake_state_ranges sg eid mutex state Hphase)) as Hprofile.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hin : In tid event.(waitList)).
  { destruct event.(waitList); [discriminate|]. inversion Hhead; left; reflexivity. }
  pose proof (mutex_del_wake_preserves_state sg eid mutex state event tid old Hphase He Hin Hold) as Hafter.
  sep_apply_l_atomic (mutex_del_event_task_rdy_merge_raw sg eid state event tid old priority Hprofile He Hentry).
  unfold mutex_del_wake_rep; entailer!.
Qed.

Lemma mutex_del_wake_recycle_merge_inv : forall sg eid mutex state event image,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg state.(EventState).(unUsedEventStates) image) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid ** mutex_del_event_frame sg state eid |--
  UCOS2_inv sg (replace_EventS (event_recycle sg state.(EventState) eid image) state).
Proof.
  intros sg eid mutex state event image Hphase He Hzero.
  pose proof (mutex_del_wake_state_ranges sg eid mutex state Hphase) as [_ [_ [_ Hevents]]].
  pose proof Hevents as [Hpool [Hfree [_ [Hfields [_ [_ Hentries]]]]]].
  pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState) event.(waitList)
    (proj1 (Hentries eid event He))) Hzero) as Hempty.
  pose proof (mutex_del_wake_recycle_preserves_validity sg eid mutex state event image Hphase He Hempty) as Hafter.
  pose proof Hphase as [actual [Hactual [Htype Hrest]]].
  rewrite He in Hactual; injection Hactual as E; subst actual.
  assert (Hqueue : event.(queueFields) = None).
  { apply non_queue_event_has_no_queue_fields; [exact (Hfields eid event He)|rewrite Htype; discriminate]. }
  sep_apply_l_atomic (mutex_del_recycle_event_merge_raw sg state eid event image Hpool Hfree He Hqueue).
  unfold UCOS2_inv; entailer!.
Qed.

(** This records the source's clear/scan/conditional-helper order.  It is
    an observation relation, not a validity precondition: the client-use
    protocol and the concrete non-sentinel pointer fact are consumed only
    by its preservation theorem below.  The fallback is the TCB byte that
    EffectivePrio actually reads, not the Mutex count's old low byte. *)
Definition mutex_del_prepare (sg : StableGlobVars) (mutex : MutexFields)
  (entry after : UCOS2_Verify_State) : Prop :=
  if Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis) then after = entry
  else match mutex.(mfOwner) with
       | None => after = mutex_del_released_state entry mutex.(mfPCP)
       | Some owner => exists node priority,
           entry.(TskState).(inUsedTaskStates) owner = Some node /\
           mutex_effective_priority_result
             (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
             (task_slot_addr sg owner) node.(curPrio) priority /\
           after = mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority
       end.

Lemma mutex_del_prepare_event_state_eq : forall sg mutex entry after,
  mutex_del_prepare sg mutex entry after -> after.(EventState) = entry.(EventState).
Proof.
  intros sg mutex entry after Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst; reflexivity|].
  destruct mutex.(mfOwner) as [owner|]; [destruct Hprepare as [node [priority [_ [_ ->]]]]|subst; reflexivity].
  apply mutex_del_owner_priority_event_state_eq.
Qed.

Lemma mutex_del_prepare_establishes_wake_state : forall sg entry eid event mutex after,
  UCOS2_state_inv sg entry -> entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (forall owner, mutex.(mfOwner) = Some owner -> task_slot_addr sg owner <> 1) ->
  (forall owner mid e, mutex.(mfOwner) = Some owner ->
    entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  mutex_del_prepare sg mutex entry after -> mutex_del_wake_state_inv sg eid mutex after.
Proof.
  intros sg entry eid event mutex after Hvalid He Htype Hfields Hpointer Habsent Hprepare.
  unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled].
  - subst after; exact (mutex_del_disabled_state_implies_wake_state sg eid mutex entry event
      Hvalid He Htype Hfields Hdisabled).
  - apply mutex_del_released_state_implies_wake_state.
    destruct mutex.(mfOwner) as [owner|] eqn:Howner.
    + destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
      exact (mutex_del_owner_scan_establishes_released_state sg entry eid event mutex owner node priority
        Hvalid He Htype Hfields Howner Henabled Hnode (Hpointer owner eq_refl) Hscan
        ltac:(intros mid e Hget; exact (Habsent owner mid e eq_refl Hget))).
    + subst after; exact (mutex_del_unowned_enabled_establishes_released_state sg entry eid event mutex
        Hvalid He Htype Hfields Howner Henabled).
Qed.

Lemma mutex_del_wake_broadcast_result : forall sg eid mutex state event priorities after,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  mutex_del_wake_state_inv sg eid mutex after /\
  after.(EventState).(inUsedEventStates) eid = Some (event_set_wait_list event []) /\
  length priorities = length event.(waitList).
Proof.
  intros sg eid mutex state event priorities after Hphase He Hloop.
  destruct Hphase as [actual [Hactual [Htype [Hfields [[Hdisabled Hvalid]|Hreleased]]]]];
    rewrite He in Hactual; injection Hactual as E; subst actual.
  - destruct (event_broadcast_result sg state eid event PendMutex 0 PendAbort priorities after
      Hvalid He ltac:(rewrite Htype; reflexivity) Hloop) as [Hafter [Hlookup [Hlength Hframe]]].
    split.
    + exact (mutex_del_disabled_state_implies_wake_state sg eid mutex after (event_set_wait_list event [])
        Hafter Hlookup Htype Hfields Hdisabled).
    + auto.
  - destruct (mutex_del_released_broadcast_result sg eid mutex state event priorities after
      Hreleased He Hloop) as [Hafter [Hlookup Hlength]].
    split; [exact (mutex_del_released_state_implies_wake_state sg eid mutex after Hafter)|auto].
Qed.

(** Prefix of the actual EventGrp-tested calls, used by the C loop
    invariant.  Its priority list is proof data; it neither changes the
    concrete kernel state nor grants any callee resources. *)
Inductive mutex_del_wake_prefix (sg : StableGlobVars) (eid : EventID)
  : UCOS2_Verify_State -> list Priority -> UCOS2_Verify_State -> Prop :=
| mutex_del_wake_prefix_nil : forall state,
    mutex_del_wake_prefix sg eid state [] state
| mutex_del_wake_prefix_cons : forall state event priority mid priorities after,
    state.(EventState).(inUsedEventStates) eid = Some event ->
    encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
    event_task_rdy sg state eid PendMutex 0 PendAbort = Some (priority, mid) ->
    mutex_del_wake_prefix sg eid mid priorities after ->
    mutex_del_wake_prefix sg eid state (priority :: priorities) after.

Lemma mutex_del_wake_prefix_snoc : forall sg eid initial priorities state event priority after,
  mutex_del_wake_prefix sg eid initial priorities state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendAbort = Some (priority, after) ->
  mutex_del_wake_prefix sg eid initial (priorities ++ [priority]) after.
Proof.
  intros sg eid initial priorities state event priority after Hprefix.
  induction Hprefix; intros Hlookup Hnonzero Hstep; simpl.
  - eapply mutex_del_wake_prefix_cons; [exact Hlookup|exact Hnonzero|exact Hstep|constructor].
  - eapply mutex_del_wake_prefix_cons; eauto.
Qed.

Lemma mutex_del_wake_prefix_done : forall sg eid initial priorities state event,
  mutex_del_wake_prefix sg eid initial priorities state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) = 0 ->
  event_broadcast sg eid PendMutex 0 PendAbort initial priorities state.
Proof.
  intros sg eid initial priorities state event Hprefix.
  induction Hprefix; intros Hlookup Hzero.
  - eapply event_broadcast_done; eauto.
  - eapply event_broadcast_next; eauto.
Qed.

Definition mutex_del_recycle_state (sg : StableGlobVars) (eid : EventID)
  (event : OSEventAbstractState) (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_EventS (event_recycle sg state.(EventState) eid (event_image sg state.(TskState) event)) state.

(** Protected source endpoint only.  The result is
    (returned pointer, (error code, request OS_Sched after Restore)).
    This deliberately does not assert that Restore or OS_Sched has
    returned to the caller.  The perr store is after those source calls.
    All three INT8U option classes are represented, including unchanged
    TASK_WAITING and INVALID_OPT outcomes. *)
Definition mutex_del_critical (sg : StableGlobVars) (eid : EventID) (opt : Z)
  (entry : UCOS2_Verify_State) (result : Z * (OSErrCode * bool))
  (after : UCOS2_Verify_State) : Prop :=
  exists event mutex,
    entry.(EventState).(inUsedEventStates) eid = Some event /\
    event.(eventType) = OS_EVENT_TYPE_MUTEX /\ event.(mutexFields) = Some mutex /\
    if Z.eq_dec opt 0 then
      if Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0 then
        exists prepared, mutex_del_prepare sg mutex entry prepared /\
          after = mutex_del_recycle_state sg eid event prepared /\
          result = (0, (OS_ERR_NONE, false))
      else after = entry /\ result = (event_addr sg eid, (OS_ERR_TASK_WAITING, false))
    else if Z.eq_dec opt 1 then
      exists prepared priorities drained,
        mutex_del_prepare sg mutex entry prepared /\
        event_broadcast sg eid PendMutex 0 PendAbort prepared priorities drained /\
        after = mutex_del_recycle_state sg eid (event_set_wait_list event []) drained /\
        result = (0, (OS_ERR_NONE,
          negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0)))
    else after = entry /\ result = (event_addr sg eid, (OS_ERR_INVALID_OPT, false)).

Lemma mutex_del_critical_preserves_validity : forall sg eid opt entry result after,
  UCOS2_state_inv sg entry ->
  (forall event mutex owner, entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some owner -> task_slot_addr sg owner <> 1) ->
  (forall event mutex owner mid e, entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex -> mutex.(mfOwner) = Some owner ->
    entry.(EventState).(inUsedEventStates) mid = Some e -> ~ In owner e.(waitList)) ->
  mutex_del_critical sg eid opt entry result after -> UCOS2_state_inv sg after.
Proof.
  intros sg eid opt entry result after Hvalid Hpointer Habsent
    [event [mutex [He [Htype [Hfields Hsource]]]]].
  assert (Hprepare : forall prepared, mutex_del_prepare sg mutex entry prepared ->
    mutex_del_wake_state_inv sg eid mutex prepared).
  { intros prepared Hstep; eapply mutex_del_prepare_establishes_wake_state; try eassumption.
    - intros owner Howner; exact (Hpointer event mutex owner He Htype Hfields Howner).
    - intros owner mid e Howner Hlookup; exact (Habsent event mutex owner mid e He Htype Hfields Howner Hlookup). }
  destruct (Z.eq_dec opt 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0) as [Hzero|Hnonzero].
    + destruct Hsource as [prepared [Hstep [-> Hresult]]].
      assert (Hlookup : prepared.(EventState).(inUsedEventStates) eid = Some event).
      { rewrite (mutex_del_prepare_event_state_eq sg mutex entry prepared Hstep); exact He. }
      pose proof Hvalid as [_ [_ [_ [Hevents Hrest]]]].
      pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
      pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg entry.(TskState) event.(waitList)
        (proj1 (Hentries eid event He))) Hzero) as Hempty.
      exact (mutex_del_wake_recycle_preserves_validity sg eid mutex prepared event _
        (Hprepare prepared Hstep) Hlookup Hempty).
    + destruct Hsource as [-> Hresult]; exact Hvalid.
  - destruct (Z.eq_dec opt 1).
    + destruct Hsource as [prepared [priorities [drained [Hstep [Hloop [-> Hresult]]]]]].
      assert (Hlookup : prepared.(EventState).(inUsedEventStates) eid = Some event).
      { rewrite (mutex_del_prepare_event_state_eq sg mutex entry prepared Hstep); exact He. }
      destruct (mutex_del_wake_broadcast_result sg eid mutex prepared event priorities drained
        (Hprepare prepared Hstep) Hlookup Hloop) as [Hphase [Hfinal Hlength]].
      exact (mutex_del_wake_recycle_preserves_validity sg eid mutex drained (event_set_wait_list event []) _
        Hphase Hfinal eq_refl).
    + destruct Hsource as [-> Hresult]; exact Hvalid.
Qed.

Lemma mutex_del_owner_use_implies_not_waiter : forall sg entry eid event mutex owner,
  UCOS2_state_inv sg entry ->
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner ->
  forall mid other, entry.(EventState).(inUsedEventStates) mid = Some other -> ~ In owner other.(waitList).
Proof.
  intros sg entry eid event mutex owner Hvalid Huse He Htype Hfields Howner.
  pose proof Hvalid as [_ [_ [_ [Hevents [[_ [Howners Hcross]] Hrest]]]]].
  destruct (Howners eid event mutex owner He Htype Hfields Howner)
    as [node [base [snapshot [Hnode Hsnapshot]]]].
  exact (mutex_owner_event_unlinked_not_waiter sg entry.(TskState) entry.(EventState)
    eid event mutex owner node Hevents Huse He Htype Hfields Howner Hnode).
Qed.

Lemma mutex_del_prepare_under_owner_use : forall sg entry eid event mutex after,
  UCOS2_state_inv sg entry ->
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  (forall owner, mutex.(mfOwner) = Some owner -> task_slot_addr sg owner <> 1) ->
  mutex_del_prepare sg mutex entry after -> mutex_del_wake_state_inv sg eid mutex after.
Proof.
  intros sg entry eid event mutex after Hvalid Huse He Htype Hfields Hpointer Hprepare.
  eapply mutex_del_prepare_establishes_wake_state; try eassumption.
  intros owner mid other Howner Hother.
  exact (mutex_del_owner_use_implies_not_waiter sg entry eid event mutex owner
    Hvalid Huse He Htype Hfields Howner mid other Hother).
Qed.

Lemma mutex_del_critical_under_owner_use_preserves_validity : forall sg eid opt entry result after,
  UCOS2_state_inv sg entry ->
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  (forall event mutex owner, entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some owner -> task_slot_addr sg owner <> 1) ->
  mutex_del_critical sg eid opt entry result after -> UCOS2_state_inv sg after.
Proof.
  intros sg eid opt entry result after Hvalid Huse Hpointer Hsource.
  eapply mutex_del_critical_preserves_validity; [exact Hvalid|exact Hpointer| |exact Hsource].
  intros event mutex owner mid other He Htype Hfields Howner Hother.
  exact (mutex_del_owner_use_implies_not_waiter sg entry eid event mutex owner
    Hvalid Huse He Htype Hfields Howner mid other Hother).
Qed.

(** Same interval as acquisition.  The registered clients must carry
    their source-specific proofs for the selected use protocol; neither
    a generic validity certificate nor Save alone supplies this premise.
    Physical heap acquisition remains the region owner's obligation. *)
Lemma mutex_del_critical_interval_preserves_validity :
  forall critical sg invocation before entry eid opt result after,
  (forall action initial final,
    critical_region_clients critical action -> UCOS2_state_inv sg initial ->
    mutex_owner_event_unlinked initial.(TskState) initial.(EventState) ->
    kernel_client_step action sg initial final ->
    mutex_owner_event_unlinked final.(TskState) final.(EventState)) ->
  critical_region_interval critical sg invocation before entry ->
  UCOS2_state_inv sg before ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  (forall event mutex owner, entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some owner -> task_slot_addr sg owner <> 1) ->
  mutex_del_critical sg eid opt entry result after -> UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation before entry eid opt result after Hclients Hinterval Hvalid Huse Hpointer Hsource.
  pose proof (proj1 (critical_region_interval_transports_resources critical sg invocation before entry Hinterval Hvalid))
    as Hentry.
  pose proof (critical_region_interval_preserves_mutex_owner_event_unlinked critical sg invocation before entry
    Hclients Hinterval Hvalid Huse) as Hentryuse.
  exact (mutex_del_critical_under_owner_use_preserves_validity sg eid opt entry result after
    Hentry Hentryuse Hpointer Hsource).
Qed.

Lemma mutex_del_priority_input_merge_released : forall sg entry ceiling owner node,
  selected_kernel_profile sg -> entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_del_priority_input sg entry ceiling owner node ** mutex_del_priority_frame sg entry owner |--
  mutex_del_released_resources sg entry ceiling.
Proof.
  intros sg entry ceiling owner node Hprofile Hnode.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold mutex_del_priority_input, mutex_del_priority_frame.
  rewrite task_slot_addr_tcb64 by assumption; rewrite <- used_task_rep_tcb64 by assumption.
  rewrite <- sched_rows_array_equiv.
  unfold mutex_del_released_resources, UCOS2_raw_rep_missing_priority_table,
    task_public_storage_without_prio_tbl, store_used_task_map, sched_raw_rep, sched_physical_rep,
    store_prio_tbl, mutex_del_priority_values.
  entailer!.
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) owner node entry.(TskState).(inUsedTaskStates) Hnode).
  entailer!.
Qed.

Lemma mutex_del_owner_priority_skip_merge : forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority -> node.(curPrio) = priority ->
  mutex_del_priority_input sg entry mutex.(mfPCP) owner node ** mutex_del_priority_frame sg entry owner |--
  mutex_del_wake_rep sg eid mutex (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority Hvalid Huse He Htype Hfields Howner
    Henabled Hnode Hpointer Hscan Hequal.
  pose proof (mutex_del_owner_use_implies_not_waiter sg entry eid event mutex owner
    Hvalid Huse He Htype Hfields Howner) as Habsent.
  pose proof (mutex_del_owner_scan_establishes_released_state sg entry eid event mutex owner node priority
    Hvalid He Htype Hfields Howner Henabled Hnode Hpointer Hscan Habsent) as Hreleased.
  pose proof (mutex_del_released_state_implies_wake_state sg eid mutex _ Hreleased) as Hphase.
  sep_apply_l_atomic (mutex_del_priority_input_merge_released sg entry mutex.(mfPCP) owner node (proj1 Hvalid) Hnode).
  rewrite mutex_del_released_resources_raw_equiv.
  unfold mutex_del_wake_rep, mutex_del_owner_priority_state in *.
  destruct (Z.eq_dec node.(curPrio) priority); [entailer!|contradiction].
Qed.

Lemma mutex_del_owner_priority_update_merge : forall sg entry eid event mutex owner node priority,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> mutex_pcp_enabled sg mutex ->
  entry.(TskState).(inUsedTaskStates) owner = Some node -> task_slot_addr sg owner <> 1 ->
  mutex_effective_priority_result
    (mutex_del_priority_values sg (mutex_del_released_table entry mutex.(mfPCP)))
    (task_slot_addr sg owner) node.(curPrio) priority -> node.(curPrio) <> priority ->
  mutex_del_priority_output sg entry mutex.(mfPCP) owner node priority ** mutex_del_priority_frame sg entry owner |--
  mutex_del_wake_rep sg eid mutex (mutex_del_owner_priority_state sg entry mutex.(mfPCP) owner node priority).
Proof.
  intros sg entry eid event mutex owner node priority Hvalid Huse He Htype Hfields Howner
    Henabled Hnode Hpointer Hscan Hdifferent.
  pose proof (mutex_del_owner_use_implies_not_waiter sg entry eid event mutex owner
    Hvalid Huse He Htype Hfields Howner) as Habsent.
  pose proof (mutex_del_owner_scan_establishes_released_state sg entry eid event mutex owner node priority
    Hvalid He Htype Hfields Howner Henabled Hnode Hpointer Hscan Habsent) as Hreleased.
  pose proof (mutex_del_released_state_implies_wake_state sg eid mutex _ Hreleased) as Hphase.
  destruct (mutex_del_owner_scan_properties sg entry eid event mutex owner priority
    Hvalid He Htype Hfields Howner Henabled Hpointer ltac:(intros other Hother;
      rewrite Hnode in Hother; injection Hother as E; subst other; exact Hscan))
    as [other [base [Hother [Hbase [Heffective Hproperties]]]]].
  pose proof (proj1 Heffective) as [Hrange Halias].
  assert (Hprio : 0 <= priority < 64).
  { assert (Hlowest : sg.(osLowestPrio) = 63)
      by (pose proof (proj1 Hvalid) as Hprofile;
        unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
    unfold task_priority_in_range in Hrange; lia. }
  sep_apply_l_atomic (mutex_del_priority_output_merge_raw sg entry mutex.(mfPCP) owner node priority
    Hvalid Hnode Hprio Halias Habsent).
  unfold mutex_del_wake_rep, mutex_del_owner_priority_state in *.
  destruct (Z.eq_dec node.(curPrio) priority); [contradiction|entailer!].
Qed.

Lemma mutex_del_prepare_preserves_owner_use : forall sg mutex entry after,
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  mutex_del_prepare sg mutex entry after ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg mutex entry after Huse Hprepare; unfold mutex_del_prepare in Hprepare.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst; exact Huse|].
  destruct mutex.(mfOwner) as [owner|].
  - destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
    unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority); [exact Huse|].
    change (mutex_owner_event_unlinked
      (glob_task_set_usedtask (mutex_del_released_tasks entry mutex.(mfPCP)) owner
        (mutex_priority_task node priority)) entry.(EventState)).
    eapply mutex_owner_event_unlinked_task_fields_frame;
      [exact Hnode|reflexivity|reflexivity|exact Huse].
  - subst; exact Huse.
Qed.

Lemma mutex_del_wake_decompose : forall sg eid mutex state event priority after,
  mutex_del_wake_state_inv sg eid mutex state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendAbort = Some (priority, after) ->
  exists tid old,
    In tid event.(waitList) /\ state.(TskState).(inUsedTaskStates) tid = Some old /\
    priority = old.(curPrio) /\ after = event_wake_state sg state eid event tid old PendMutex 0 PendAbort /\
    mutex_del_wake_state_inv sg eid mutex after.
Proof.
  intros sg eid mutex state event priority after Hphase He Hnonzero Hstep.
  pose proof (mutex_del_wake_state_ranges sg eid mutex state Hphase) as [Hprofile [Htasks [_ Hevents]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct event.(waitList) as [|tid tail] eqn:Hlist; [contradiction Hnonzero; reflexivity|].
  destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail
    (proj1 Hprofile) Htasks (Hentries eid event He) Hlist) as [old [Hold Hselection]].
  pose proof (event_task_rdy_selects_waiter sg state eid event tid tail old PendMutex 0 PendAbort
    (proj1 Hprofile) Htasks (Hentries eid event He) He Hlist Hold) as Hactual.
  rewrite Hstep in Hactual; injection Hactual as Hpriority Hafter; subst priority after.
  exists tid, old; split; [try rewrite Hlist; left; reflexivity|].
  split; [exact Hold|]. split; [reflexivity|]. split; [reflexivity|].
  eapply mutex_del_wake_preserves_state; [exact Hphase|exact He|try rewrite Hlist; left; reflexivity|exact Hold].
Qed.

Lemma mutex_del_broadcast_preserves_owner_use : forall sg eid mutex state priorities after,
  event_broadcast sg eid PendMutex 0 PendAbort state priorities after ->
  mutex_del_wake_state_inv sg eid mutex state ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg eid mutex state priorities after Hloop.
  induction Hloop as [state event He Hzero|state event priority mid priorities after He Hnonzero Hstep Hloop IH];
    intros Hphase Huse; [exact Huse|].
  destruct (mutex_del_wake_decompose sg eid mutex state event priority mid Hphase He Hnonzero Hstep)
    as [tid [old [Hin [Hold [Hpriority [Hmid HphaseMid]]]]]].
  apply IH; [exact HphaseMid|]; rewrite Hmid.
  exact (event_wake_preserves_mutex_owner_event_unlinked sg state eid event tid old PendMutex 0 PendAbort
    He Hold Huse).
Qed.

Lemma mutex_del_recycle_preserves_owner_use : forall sg eid event state,
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  let after := mutex_del_recycle_state sg eid event state in
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg eid event state Huse; cbn zeta.
  intros mid other mutex owner node Hother Htype Hfields Howner Hnode.
  apply mutex_del_recycled_event_lookup in Hother; destruct Hother as [Hne Hother].
  exact (Huse mid other mutex owner node Hother Htype Hfields Howner Hnode).
Qed.

Lemma mutex_del_critical_preserves_owner_use : forall sg eid opt entry result after,
  UCOS2_state_inv sg entry ->
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  (forall event mutex owner, entry.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
    mutex.(mfOwner) = Some owner -> task_slot_addr sg owner <> 1) ->
  mutex_del_critical sg eid opt entry result after ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg eid opt entry result after Hvalid Huse Hpointer
    [event [mutex [He [Htype [Hfields Hsource]]]]].
  destruct (Z.eq_dec opt 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hsource as [prepared [Hstep [-> Hresult]]].
      apply mutex_del_recycle_preserves_owner_use.
      exact (mutex_del_prepare_preserves_owner_use sg mutex entry prepared Huse Hstep).
    + destruct Hsource as [-> Hresult]; exact Huse.
  - destruct (Z.eq_dec opt 1).
    + destruct Hsource as [prepared [priorities [drained [Hstep [Hloop [-> Hresult]]]]]].
      apply mutex_del_recycle_preserves_owner_use.
      eapply mutex_del_broadcast_preserves_owner_use; [exact Hloop| |].
      * eapply mutex_del_prepare_under_owner_use; try eassumption.
        intros owner Howner; exact (Hpointer event mutex owner He Htype Hfields Howner).
      * exact (mutex_del_prepare_preserves_owner_use sg mutex entry prepared Huse Hstep).
    + destruct Hsource as [-> Hresult]; exact Huse.
Qed.

(** Selected ARG_CHK=1 / safety-disabled source prefix.  The two byte
    arguments are the actual ordered reads, not a common unmasked kernel
    snapshot.  NULL needs neither read; a type rejection needs no nesting
    read.  No task, stack, ready-list or caller-current premise appears. *)
Definition mutex_del_before_save_error (pevent observed_type observed_nesting : Z)
  : option (Z * OSErrCode) :=
  if Z.eqb pevent 0 then Some (0, OS_ERR_PEVENT_NULL)
  else if Z.eqb observed_type 4 then
    if Z.ltb 0 observed_nesting then Some (pevent, OS_ERR_DEL_ISR) else None
  else Some (pevent, OS_ERR_EVENT_TYPE).

Lemma mutex_del_before_save_null : forall observed_type observed_nesting,
  mutex_del_before_save_error 0 observed_type observed_nesting = Some (0, OS_ERR_PEVENT_NULL).
Proof. intros; reflexivity. Qed.

Lemma mutex_del_before_save_wrong_type : forall pevent observed_type observed_nesting,
  pevent <> 0 -> observed_type <> 4 ->
  mutex_del_before_save_error pevent observed_type observed_nesting = Some (pevent, OS_ERR_EVENT_TYPE).
Proof.
  intros pevent observed_type observed_nesting Hnonnull Htype.
  unfold mutex_del_before_save_error; apply Z.eqb_neq in Hnonnull, Htype; rewrite Hnonnull, Htype; reflexivity.
Qed.

Lemma mutex_del_before_save_isr : forall pevent observed_nesting,
  pevent <> 0 -> 0 < observed_nesting ->
  mutex_del_before_save_error pevent 4 observed_nesting = Some (pevent, OS_ERR_DEL_ISR).
Proof.
  intros pevent observed_nesting Hnonnull Hnesting.
  unfold mutex_del_before_save_error; apply Z.eqb_neq in Hnonnull; apply Z.ltb_lt in Hnesting.
  rewrite Hnonnull, Hnesting; reflexivity.
Qed.

Lemma mutex_del_before_save_continues_iff : forall pevent observed_type observed_nesting,
  0 <= observed_nesting ->
  (mutex_del_before_save_error pevent observed_type observed_nesting = None <->
   pevent <> 0 /\ observed_type = 4 /\ observed_nesting = 0).
Proof.
  intros pevent observed_type observed_nesting Hrange; unfold mutex_del_before_save_error.
  destruct (Z.eqb pevent 0) eqn:Ep; [apply Z.eqb_eq in Ep|apply Z.eqb_neq in Ep].
  - split; [discriminate|tauto].
  - destruct (Z.eqb observed_type 4) eqn:Et; [apply Z.eqb_eq in Et|apply Z.eqb_neq in Et].
    + destruct (Z.ltb 0 observed_nesting) eqn:En; [apply Z.ltb_lt in En|apply Z.ltb_ge in En];
        split; intros; try discriminate; try reflexivity; intuition lia.
    + split; [discriminate|tauto].
Qed.

Definition mutex_del_critical_result (sg : StableGlobVars) (eid : EventID)
  (opt initial_group : Z) : Z * (OSErrCode * bool) :=
  if Z.eq_dec opt 0 then
    if Z.eq_dec initial_group 0 then (0, (OS_ERR_NONE, false))
    else (event_addr sg eid, (OS_ERR_TASK_WAITING, false))
  else if Z.eq_dec opt 1 then (0, (OS_ERR_NONE, negb (Z.eqb initial_group 0)))
  else (event_addr sg eid, (OS_ERR_INVALID_OPT, false)).

Lemma mutex_del_critical_result_observation : forall sg eid opt entry event result after,
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  mutex_del_critical sg eid opt entry result after ->
  result = mutex_del_critical_result sg eid opt
    (encode_event_wait_grp event.(waitList) entry.(TskState)).
Proof.
  intros sg eid opt entry event result after He [actual [mutex [Hactual [Htype [Hfields Hsource]]]]].
  rewrite He in Hactual; injection Hactual as E; subst actual.
  unfold mutex_del_critical_result; destruct (Z.eq_dec opt 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0).
    + destruct Hsource as [prepared [Hstep [Hafter Hresult]]]; exact Hresult.
    + exact (proj2 Hsource).
  - destruct (Z.eq_dec opt 1).
    + destruct Hsource as [prepared [priorities [drained [Hstep [Hloop [Hafter Hresult]]]]]]; exact Hresult.
    + exact (proj2 Hsource).
Qed.

Lemma mutex_del_raw_merge_event : forall sg state eid event,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_image sg state.(TskState) event) **
  sg.(g_OSEventFreeList) # Ptr |->
    event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
  mutex_del_event_frame sg state eid |-- UCOS2_raw_rep sg state.
Proof.
  intros sg state eid event He.
  unfold mutex_del_event_frame.
  fold (used_event_rep sg state.(TskState) eid event).
  unfold UCOS2_raw_rep, task_shared_rep, event_raw_rep, event_free_root_rep,
    UCOS2_raw_rep_missing_task_storage_sched_event.
  entailer!.
  sep_apply_l_atomic (store_map_merge (used_event_rep sg state.(TskState)) eid event
    state.(EventState).(inUsedEventStates) He); entailer!.
Qed.

(** The loop guard owns exactly the numeric-profile EventGrp byte.  The
    remaining ECB bytes, free-list root and other modules stay in a real
    disjoint residual, not another whole-state representation. *)
Definition mutex_del_event_group_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (event : OSEventAbstractState) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_image sg state.(TskState) event) EventGrpField **
  sg.(g_OSEventFreeList) # Ptr |->
    event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)) **
  mutex_del_event_frame sg state eid.

Definition mutex_del_wake_guard_rep (sg : StableGlobVars) (eid : EventID)
  (mutex : MutexFields) (state : UCOS2_Verify_State) (event : OSEventAbstractState) : Assertion :=
  coq_prop (mutex_del_wake_state_inv sg eid mutex state /\
    state.(EventState).(inUsedEventStates) eid = Some event) &&
  ((event_pool_addr sg eid + 10) # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState) **
   mutex_del_event_group_frame sg state eid event).

Lemma mutex_del_wake_guard_split : forall sg eid mutex state,
  mutex_del_wake_rep sg eid mutex state |-- EX event, mutex_del_wake_guard_rep sg eid mutex state event.
Proof.
  intros sg eid mutex state; unfold mutex_del_wake_rep; Intros.
  pose proof H as [event [He Hfields]].
  sep_apply_l_atomic (mutex_del_raw_split_event sg state eid event He).
  pose proof (event_storage_split_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_image sg state.(TskState) event) EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hsplit.
  cbn [event_cell event_image event_field_offset] in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists event; unfold mutex_del_wake_guard_rep, mutex_del_event_group_frame; entailer!.
Qed.

Lemma mutex_del_wake_guard_merge : forall sg eid mutex state event,
  mutex_del_wake_guard_rep sg eid mutex state event |-- mutex_del_wake_rep sg eid mutex state.
Proof.
  intros sg eid mutex state event; unfold mutex_del_wake_guard_rep, mutex_del_event_group_frame; Intros.
  destruct H as [Hphase He].
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_image sg state.(TskState) event) EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hmerge.
  cbn [event_cell event_image event_field_offset] in Hmerge.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (mutex_del_raw_merge_event sg state eid event He).
  unfold mutex_del_wake_rep; entailer!.
Qed.

Lemma mutex_del_wake_guard_c_field : forall sg eid mutex state event group_addr,
  event_wait_fields_layout_prop sg eid group_addr
    (event_addr sg eid + OSEventTbl_off) ->
  mutex_del_wake_guard_rep sg eid mutex state event --||--
  coq_prop (mutex_del_wake_state_inv sg eid mutex state /\
    state.(EventState).(inUsedEventStates) eid = Some event) &&
  (group_addr # UChar |-> encode_event_wait_grp event.(waitList) state.(TskState) **
   mutex_del_event_group_frame sg state eid event).
Proof.
  intros sg eid mutex state event group_addr [Hgroup Htable].
  unfold mutex_del_wake_guard_rep.
  change (group_addr = event_pool_addr sg eid + 10) in Hgroup.
  rewrite Hgroup; split; reflexivity.
Qed.
