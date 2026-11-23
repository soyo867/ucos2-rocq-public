Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The prepared publication cut owns the actual initialized node, existing
    head links, ready tables, and residual module resources. Flag nodes use
    their six typed fields; supplemental padding remains in the caller frame.
    The same five C stores, commit protocol, initial stack buffer and explicit
    initial local are consumed. No earlier allocation or StackInit is implied. *)


Definition task_tcb_init_publication_fields_other (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage)
    s.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_root sg s **
  sched_physical_rep sg s.(SchedState) **
  task_reg_allocator_rep sg s.(TskState) **
  flag_fields_configured_rep sg s.(FlagState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg s.

Definition task_tcb_init_publication_fields_tail_storage sg args current slot image : Assertion :=
  task_slot_storage_rep sg slot
    (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image)) **
  task_tcb_init_used_with_head_prev sg current slot **
  sg.(g_OSTCBList) # Ptr |-> task_tcb_init_active_head sg current **
  sg.(g_OSTaskCtr) # UChar |-> task_tcb_init_count current **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group current **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows current) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg current) **
  task_tcb_init_publication_fields_other sg current.

Definition task_create_publication_fields_storage sg actual invocation acquired current slot image : Assertion :=
  let committed := task_tcb_init_published_state sg actual invocation acquired current slot image in
  task_slot_storage_rep sg slot
    (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) actual image)) **
  task_tcb_init_used_with_head_prev sg current slot **
  sg.(g_OSTCBList) # Ptr |-> task_slot_addr sg slot **
  sg.(g_OSTaskCtr) # UChar |-> (task_tcb_init_count current + 1) **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group committed **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows committed) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg committed) **
  task_tcb_init_publication_fields_other sg current.

(** Actual five-store production with the fields residual framed throughout. *)

Lemma task_tcb_init_publication_tail_fields_store_execution :
  forall sg args invocation origin acquired current slot image (frame : Assertion) before,
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  0 <= args.(initPrio) < 64 ->
  0 <= task_slot_addr sg slot < 4294967296 ->
  (task_tcb_init_publication_fields_tail_storage sg args current slot image ** frame) before ->
  exists after,
    task_tcb_init_publication_tail_fragment sg args.(initPrio) (task_slot_addr sg slot) before after /\
    (task_create_publication_fields_storage sg args invocation acquired current slot image ** frame) after.
Proof.
  intros sg args invocation origin acquired current slot image frame before
    Hvalid Hbinding Hpriority Hpointer Hbefore.
  assert (Hy : 0 <= args.(initPrio) / 8 < 8)
    by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (Hx : 0 <= args.(initPrio) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  set (initialized := task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
    (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile) args image)).
  pose proof (task_tcb_init_storage_split_ready_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg slot) initialized args.(initPrio)) as Hfields.
  assert (Hfield_values : initialized (TCBCommonField TCBY) = Some (args.(initPrio) / 8) /\
    initialized (TCBCommonField TCBBitY) = Some (Z.shiftl 1 (args.(initPrio) / 8)) /\
    initialized (TCBCommonField TCBBitX) = Some (Z.shiftl 1 (args.(initPrio) mod 8))).
  { unfold initialized; destruct sg.(osKernelConfig).(cfgEventMultiEnabled),
      sg.(osKernelConfig).(cfgTaskProfile); repeat split; reflexivity. }
  specialize (Hfields (proj1 Hfield_values) (proj1 (proj2 Hfield_values)) (proj2 (proj2 Hfield_values))).
  set (rest := task_tcb_init_without_ready_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg slot) initialized **
    task_tcb_init_used_with_head_prev sg current slot **
    UCharArray.missing_i sg.(g_OSRdyTbl) (args.(initPrio) / 8) 0 8 (task_tcb_init_ready_rows current) **
    PtrArray.missing_i sg.(g_OSTCBPrioTbl) args.(initPrio) 0 64 (task_tcb_init_priority_table sg current) **
    task_tcb_init_publication_fields_other sg current ** frame).
  assert (Hsplit : task_tcb_init_publication_fields_tail_storage sg args current slot image ** frame |--
    task_tcb_init_publication_cells sg args.(initPrio) (task_slot_addr sg slot)
      (task_tcb_init_active_head sg current) (task_tcb_init_ready_group current)
      (Znth (args.(initPrio) / 8) (task_tcb_init_ready_rows current) 0)
      (task_tcb_init_count current)
      (Znth args.(initPrio) (task_tcb_init_priority_table sg current) 0) ** rest).
  { unfold task_tcb_init_publication_fields_tail_storage, task_slot_storage_rep; fold initialized.
    rewrite Hfields.
    sep_apply_l_atomic (UCharArray.full_split_to_missing_i sg.(g_OSRdyTbl)
      (args.(initPrio) / 8) 8 (task_tcb_init_ready_rows current) 0 Hy).
    sep_apply_l_atomic (PtrArray.full_split_to_missing_i sg.(g_OSTCBPrioTbl)
      args.(initPrio) 64 (task_tcb_init_priority_table sg current) 0 Hpriority).
    unfold task_tcb_init_publication_cells, rest; entailer!. }
  pose proof (Hsplit before Hbefore) as Hcells.
  destruct (task_tcb_init_publication_cells_reads _ _ _ _ _ _ _ _ _ _ Hcells)
    as [Hgroup_load [Hrow_load _]].
  assert (Hgroup : 0 <= Z.lor (task_tcb_init_ready_group current)
    (Z.shiftl 1 (args.(initPrio) / 8)) < 256).
  { apply (bitmap_lor_in_range 8); [lia|exact (proj1 Hgroup_load)|].
    apply (bitmap_single_bit_in_range 8); exact Hy. }
  assert (Hrow : 0 <= Z.lor (Znth (args.(initPrio) / 8) (task_tcb_init_ready_rows current) 0)
    (Z.shiftl 1 (args.(initPrio) mod 8)) < 256).
  { apply (bitmap_lor_in_range 8); [lia|exact (proj1 Hrow_load)|].
    apply (bitmap_single_bit_in_range 8); exact Hx. }
  assert (Hcount : 0 <= task_tcb_init_count current + 1 < 256).
  { pose proof (task_count_in_pool_range sg current.(TskState)
      (proj1 Hvalid) (proj1 (proj2 Hvalid))); unfold task_tcb_init_count; lia. }
  destruct (task_tcb_init_publication_cells_store_execution _ _ _ _ _ _ _ _ _ before
    Hpointer Hgroup Hrow Hcount Hcells) as [after [Hrun Hafter]].
  pose proof (task_tcb_init_commit_binding_identity args invocation origin acquired current slot image Hbinding)
    as Hidentity.
  assert (Hnot : ~ In slot current.(SchedState).(readyList)).
  { pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
    destruct (task_private_excludes_public sg current.(TskState) slot
      (proj1 (proj1 (proj2 Hvalid))) Hprivate) as [Hnone _].
    intro Hin.
    destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) slot Hin) as [t [Hget _]].
    congruence. }
  set (published := task_tcb_init_published_state sg args invocation acquired current slot image).
  assert (Hgroup_eq : task_tcb_init_ready_group published =
    Z.lor (task_tcb_init_ready_group current) (Z.shiftl 1 (args.(initPrio) / 8))).
  { exact (proj1 (sched_commit_ready_encodings__publication_and_returns sg current.(TskState)
      current.(SchedState) args.(initPrio) invocation
      (task_tcb_init_commit_node args acquired slot image) Hnot)). }
  assert (Hrows_eq : task_tcb_init_ready_rows published =
    replace_Znth (args.(initPrio) / 8)
      (Z.lor (Znth (args.(initPrio) / 8) (task_tcb_init_ready_rows current) 0)
        (Z.shiftl 1 (args.(initPrio) mod 8))) (task_tcb_init_ready_rows current)).
  { exact (sched_commit_rows_replace_eq__publication_and_returns sg current.(TskState)
      current.(SchedState) args.(initPrio) invocation
      (task_tcb_init_commit_node args acquired slot image) Hnot Hy). }
  assert (Htable_eq : task_tcb_init_priority_table sg published =
    replace_Znth args.(initPrio) (task_slot_addr sg slot) (task_tcb_init_priority_table sg current)).
  { exact (task_commit_priority_table_replace_eq__publication_and_returns sg current.(TskState)
      args.(initPrio) invocation (task_tcb_init_commit_node args acquired slot image) Hpriority). }
  exists after; split; [exact Hrun|].
  match type of Hafter with ?P after =>
    assert (Hmerge : P |-- task_create_publication_fields_storage sg args invocation acquired current slot image ** frame)
  end.
  { unfold task_tcb_init_publication_cells, rest; sepcon_assoc_change.
    pose proof (UCharArray.missing_i_merge_to_full sg.(g_OSRdyTbl) (args.(initPrio) / 8) 8
      (Z.lor (Znth (args.(initPrio) / 8) (task_tcb_init_ready_rows current) 0)
        (Z.shiftl 1 (args.(initPrio) mod 8))) (task_tcb_init_ready_rows current) Hy) as Hrows_merge.
    cbv beta in Hrows_merge.
    sep_apply_l_atomic Hrows_merge.
    pose proof (PtrArray.missing_i_merge_to_full sg.(g_OSTCBPrioTbl) args.(initPrio) 64
      (task_slot_addr sg slot) (task_tcb_init_priority_table sg current) Hpriority) as Htable_merge.
    cbv beta in Htable_merge; rewrite sizeof_ptr.
    unfold ptr_size_Z in Htable_merge; sep_apply_l_atomic Htable_merge.
    unfold task_create_publication_fields_storage; fold published; fold initialized.
    rewrite Hgroup_eq, Hrows_eq, Htable_eq.
    unfold task_slot_storage_rep; rewrite Hfields; entailer!. }
  exact (Hmerge after Hafter).
Qed.

(** Task commit changes Event encodings through the same actual task index. *)

Local Lemma UCOS2_task_commit_residual_without_flag_frame : forall sg s p invocation node sched',
  event_in_range sg s.(TskState) s.(EventState) ->
  s.(TskState).(inUsedTaskStates) node.(taskID) = None ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg s =
  UCOS2_raw_rep_missing_task_storage_sched_flag sg
    (replace_SchedS sched' (replace_TskS (task_commit s.(TskState) p invocation node) s)).
Proof.
  intros sg s p invocation node sched' Hevent Hnone.
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag; simpl.
  rewrite (event_raw_rep_change_task_index sg s.(TskState)
    (task_commit s.(TskState) p invocation node) s.(EventState)).
  - reflexivity.
  - eapply event_task_commit_encoding_frame; eauto.
Qed.

Local Lemma UCOS2_fields_task_commit_merge_task_sched : forall sg s p invocation node,
  UCOS2_state_inv sg s ->
  task_commit_identity s.(TskState) p invocation node ->
  is_effectively_ready node.(stat) node.(dly) = true ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = nil ->
  node.(tcbFlagNode) = 0 ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name s.(NameState) node.(tcbTaskName) chars) ->
  let post := task_sched_commit_state sg s p invocation node in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  flag_fields_configured_rep sg post.(FlagState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg s |-- UCOS2_fields_inv sg post.
Proof.
  intros sg s p invocation node Hvalid Hidentity Hready Hptr Hmulti Hflag Hnewname; cbv zeta.
  apply UCOS2_fields_inv_merge_updated_task_storage_sched_flag.
  - apply UCOS2_task_commit_preserves_validity; assumption.
  - apply UCOS2_task_commit_residual_without_flag_frame.
    + exact (proj1 (proj2 (proj2 (proj2 Hvalid)))).
    + exact (proj1 (task_private_excludes_public sg s.(TskState) node.(taskID)
        (proj1 (proj1 (proj2 Hvalid)))
        (task_commit_identity_private s.(TskState) p invocation node Hidentity))).
Qed.

(** Reassemble the published node and scheduler cells into the fields world. *)

Lemma task_tcb_init_publication_fields_storage_merge :
  forall sg args invocation origin acquired current slot image flags,
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name current.(NameState)
      (task_tcb_init_commit_node args acquired slot image).(tcbTaskName) chars) ->
  let post := task_tcb_init_published_state sg args invocation acquired current slot image in
  task_create_publication_fields_storage sg args invocation acquired current slot image |-- UCOS2_fields_inv sg post.
Proof.
  intros sg args invocation origin acquired current slot image flags Hvalid Hbinding Hflags Hnewname; cbv zeta.
  unfold task_create_publication_fields_storage; cbv zeta.
  sep_apply_l_atomic (task_tcb_init_linked_storage_rep sg args acquired current slot image flags Hflags).
  sep_apply_l_atomic (task_tcb_init_used_merge_published_node__publication_and_returns
    sg args invocation origin acquired current slot image Hvalid Hbinding).
  pose proof (task_tcb_init_commit_binding_identity args invocation origin acquired current slot image Hbinding)
    as Hidentity.
  match goal with
  | |- ?resources |-- _ =>
    assert (Hassembled : resources |--
      task_public_storage sg
        (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState) **
      sched_raw_rep sg
        (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState)
        (task_tcb_init_published_state sg args invocation acquired current slot image).(SchedState) **
      flag_fields_configured_rep sg current.(FlagState) **
       UCOS2_raw_rep_missing_task_storage_sched_flag sg current)
  end.
  {
  unfold task_public_storage, sched_raw_rep, store_prio_tbl,
    task_tcb_init_publication_fields_other, task_tcb_init_priority_table, task_tcb_init_ready_group,
    task_tcb_init_ready_rows, task_tcb_init_free_root, task_tcb_init_count.
  rewrite sched_rows_array_equiv.
  unfold sched_row_values.
  unfold task_tcb_init_published_state, task_tcb_init_commit_state.
  cbn [task_sched_commit_state replace_TskS replace_SchedS TskState SchedState].
  entailer!.
  cbn [task_commit taskFreeStorage taskLifecycle unUsedTaskStates tcbListHead taskCount
    encode_task_link task_tcb_init_commit_node task_tcb_init_node_from_free_image taskID].
  unfold sched_physical_rep.
  cbn [sched_commit_ready sched_set_ready curSchedPrio highRdyPrio
    curTaskID highRdyTid ctxSwCtr isRunning].
  entailer!.
  }
  intros heap Hresources.
  apply (UCOS2_fields_task_commit_merge_task_sched sg current args.(initPrio)
    invocation (task_tcb_init_commit_node args acquired slot image)
    Hvalid Hidentity eq_refl eq_refl eq_refl eq_refl Hnewname heap).
  exact (Hassembled heap Hresources).
Qed.

(** Consume the physical initial stack and its explicitly owned local cut. *)

Lemma kernel_task_publication_continuation_fields_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication current local active,
  UCOS2_state_inv sg current -> task_create_stack_publication_input sg publication current ->
  task_stack_live_coverage current.(TskState) active ->
  let after := task_create_stack_publication_state sg publication current in
  task_create_publication_fields_storage sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_acquired)
    current publication.(stack_publication_slot) publication.(stack_publication_image) **
  task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
  local (task_create_stack_publication_continuation publication) **
  store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
    current.(TskState).(parkedTaskStacks) |--
  coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current after /\
    task_stack_live_coverage after.(TskState) active) &&
  (UCOS2_fields_inv sg after **
   store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
     after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg publication current local active Hvalid Hinput Hcoverage after.
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg current after)
    by (split; [exact Hinput|reflexivity]).
  destruct Hinput as [Hlayout [Hregion [Hcommit [Hcreation [[flags Hflags] Hname]]]]].
  set (actual := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node actual publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  set (lease := publication.(stack_publication_lease)).
  set (saved := task_create_stack_publication_continuation publication).
  assert (Hidentity : task_commit_identity current.(TskState) actual.(initPrio)
    publication.(stack_publication_invocation) node)
    by (eapply task_tcb_init_commit_binding_identity; exact Hcommit).
  destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _ Hcreation Hidentity) as [Hslot Hgen].
  assert (Hconsistent : parked_stacks_consistent current.(TskState) current.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hfresh : current.(TskState).(parkedTaskStacks) (task_stack_key lease) = None).
  { unfold task_stack_key, lease; rewrite <- Hslot, <- Hgen.
    eapply task_commit_stack_key_absent; [exact (proj1 (proj2 Hvalid))|exact Hidentity|exact Hconsistent]. }
  assert (Hcovered : task_stack_live_coverage after.(TskState) active)
    by (apply task_commit_stack_coverage; assumption).
  assert (Hinitial : armv7a_initial_frame_binding saved).
  { apply task_create_initial_frame_binding with (region := publication.(stack_publication_region)); assumption. }
  assert (Hsp : task_stack_live_sp after.(TskState) (task_stack_key lease) saved.(armv7a_continuation_sp)).
  { destruct (task_create_stack_published_initial_pointer sg publication.(stack_publication_args)
      publication.(stack_publication_return) publication.(stack_publication_lower) publication.(stack_publication_upper)
      publication.(stack_publication_name) publication.(stack_publication_invocation)
      publication.(stack_publication_origin) publication.(stack_publication_acquired) current
      publication.(stack_publication_slot) publication.(stack_publication_image) lease Hcommit Hcreation)
      as [published [Hnode [Hid [Hg Hpointer]]]].
    change (after.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some published) in Hnode.
    intros updated Hupdated Hgeneration; cbn [task_stack_key fst] in Hupdated.
    assert (updated = published) by congruence; subst updated; exact Hpointer. }
  assert (Hattachment : local saved **
      store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
        current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
      after.(TskState).(parkedTaskStacks)).
  { assert (Hnewkey : current.(TskState).(parkedTaskStacks) (node.(taskID), node.(taskGeneration)) = None).
    { rewrite Hslot, Hgen; exact Hfresh. }
    sep_apply_l_atomic (kernel_saved_continuation_map_commit external platform port abi current.(TskState)
      actual.(initPrio) publication.(stack_publication_invocation) node local
      current.(TskState).(parkedTaskStacks) Hnewkey).
    sep_apply_l_atomic (kernel_saved_continuation_map_used_map_eq external platform port abi
      (task_commit current.(TskState) actual.(initPrio) publication.(stack_publication_invocation) node)
      after.(TskState) local current.(TskState).(parkedTaskStacks) eq_refl).
    sepcon_assoc_change.
    sep_apply_l_atomic (kernel_saved_continuation_map_park_initial external platform port abi
      after.(TskState) local current.(TskState).(parkedTaskStacks)
      saved Hinitial eq_refl Hfresh Hsp).
    entailer!. }
  sepcon_assoc_change; sep_apply_l_atomic Hattachment.
  set (committed := task_create_stack_publication_raw_state sg publication current).
  assert (Hmerge : task_create_publication_fields_storage sg actual publication.(stack_publication_invocation)
      publication.(stack_publication_acquired) current publication.(stack_publication_slot)
      publication.(stack_publication_image) |-- UCOS2_fields_inv sg committed).
  { exact (task_tcb_init_publication_fields_storage_merge sg actual
      publication.(stack_publication_invocation) publication.(stack_publication_origin)
      publication.(stack_publication_acquired) current publication.(stack_publication_slot)
      publication.(stack_publication_image) flags Hvalid Hcommit Hflags Hname). }
  sep_apply_l_atomic Hmerge; rewrite UCOS2_fields_inv_split_parked_stacks; Intros.
  assert (Hcommitted : UCOS2_state_inv sg committed) by assumption.
  assert (Hmap : committed.(TskState).(parkedTaskStacks) = current.(TskState).(parkedTaskStacks)) by reflexivity.
  rewrite Hmap.
  pose proof (task_create_stack_protected_commit_resources sg TaskStackNoVFP publication.(stack_publication_region)
    publication.(stack_publication_args) publication.(stack_publication_return) publication.(stack_publication_lower)
    publication.(stack_publication_upper) publication.(stack_publication_name) publication.(stack_publication_invocation)
    publication.(stack_publication_origin) publication.(stack_publication_acquired) current
    publication.(stack_publication_slot) publication.(stack_publication_image) lease
    Hlayout Hregion Hcommit Hcreation Hconsistent Hfresh) as Hpark.
  change (task_stack_storage publication.(stack_publication_region)
      (task_create_stack_publication_words publication) **
    store_parked_stacks current.(TskState).(parkedTaskStacks) |--
    coq_prop (parked_stacks_consistent after.(TskState) after.(TskState).(parkedTaskStacks)) &&
    store_parked_stacks after.(TskState).(parkedTaskStacks)) in Hpark.
  sepcon_assoc_change; sep_apply_l_atomic Hpark; Intros.
  assert (Hconsistent_after : parked_stacks_consistent committed.(TskState) after.(TskState).(parkedTaskStacks))
    by assumption.
  sepcon_assoc_change.
  sep_apply_l_atomic (UCOS2_fields_inv_merge_updated_parked_stacks sg committed
    after.(TskState).(parkedTaskStacks) Hcommitted Hconsistent_after).
  unfold after, task_create_stack_publication_state, task_create_stack_published_state; entailer!.
Qed.

(** Bind production and reassembly to the supplied actual source endpoint. *)

Lemma kernel_task_publication_continuation_fields_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication state local active
  (frame : Assertion) before after,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  task_stack_live_coverage state.(TskState) active ->
  0 <= (task_create_stack_publication_args publication).(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_fields_tail_storage sg (task_create_stack_publication_args publication)
     state publication.(stack_publication_slot) publication.(stack_publication_image) **
   (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
    local (task_create_stack_publication_continuation publication) **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame)) before ->
  task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  let published := task_create_stack_publication_state sg publication state in
  kernel_client_step (task_create_stack_publication_client publication) sg state published /\
  task_stack_live_coverage published.(TskState) active /\
  (kernel_program_fields_inv sg published **
   store_parked_continuations (kernel_saved_continuation_entry abi published.(TskState) local)
     published.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg publication state local active frame before after
    Hvalid Hinput Hcoverage Hpriority Hpointer Hpre Hsource published.
  pose proof (proj1 (proj2 (proj2 Hinput))) as Hbinding.
  destruct (task_tcb_init_publication_tail_fields_store_execution sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) state publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid Hbinding Hpriority Hpointer Hpre)
    as [produced [Hrun Hpost]].
  assert (produced = after) by (eapply kernel_client_publication_final_eq; eassumption); subst produced.
  pose proof (kernel_task_publication_continuation_fields_merge external platform port abi sg publication state
    local active Hvalid Hinput Hcoverage) as Hclose; cbv zeta in Hclose.
  match type of Hpost with ?P after =>
    assert (Hmerge : P |--
      coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg state published /\
        task_stack_live_coverage published.(TskState) active) &&
      (kernel_program_fields_inv sg published **
       store_parked_continuations (kernel_saved_continuation_entry abi published.(TskState) local)
         published.(TskState).(parkedTaskStacks) ** frame))
  end.
  { rewrite kernel_program_fields_inv_split_unmap; sepcon_assoc_change.
    sep_apply_l_atomic Hclose; Intros; entailer!. }
  destruct (Hmerge after Hpost) as [[Hstep Hcovered] Howned].
  split; [exact Hstep|]. split; assumption.
Qed.
