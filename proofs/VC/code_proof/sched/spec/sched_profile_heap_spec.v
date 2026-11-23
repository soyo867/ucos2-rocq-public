Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Source/os_core.c:1716-1718 and 713-715 with profiling enabled.
    A UInt and a pointer share the checked Arch32 four-byte encoding;
    reusing its load/store relation grants no pointer provenance or right
    to call/dereference the integer. The typed bridges below are proved
    from existing QCP representations. Each four-byte list models ONE
    masked typed C store, not four interruptible C statements. *)
Lemma sched_profile_uint_load : forall address value heap,
  (address # UInt |-> value) heap -> pointer_load address value heap.
Proof.
  intros address value heap Hrep; apply pointer_store_load.
  exact (kernel_store_uint_store_ptr address value heap Hrep).
Qed.

Lemma sched_profile_uint_store_frame_post : forall address value (frame : Assertion) heap,
  0 <= value < 4294967296 -> (address # UInt |->_ ** frame) heap ->
  exists final, kernel_heap_execution (pointer_store_writes address value) heap final /\
    (address # UInt |-> value ** frame) final.
Proof.
  intros address value frame heap Hvalue Hbefore.
  assert (Hsplit : address # UInt |->_ ** frame |-- address # Ptr |->_ ** frame).
  { apply derivable1_sepcon_mono; [exact (proj1 (kernel_undef_store_uint_ptr_equiv address))|reflexivity]. }
  destruct (framed_pointer_store_execution address value frame heap Hvalue (Hsplit heap Hbefore))
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|].
  assert (Hmerge : address # Ptr |-> value ** frame |-- address # UInt |-> value ** frame).
  { apply derivable1_sepcon_mono; [exact (store_ptr_store_uint address value eq_refl eq_refl)|reflexivity]. }
  exact (Hmerge final Hpost).
Qed.

Definition os_sched_profile_task_state (state : UCOS2_Verify_State)
  (slot : TaskID) (node : TaskAbstractState) : UCOS2_Verify_State :=
  replace_TskS (glob_task_set_usedtask state.(TskState) slot
    (task_record_context_switch node)) state.

Definition os_sched_profile_global_state (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_SchedS (sched_increment_switch_counter state.(SchedState)) state.

Definition os_sched_profile_counts_state (state : UCOS2_Verify_State)
  (slot : TaskID) (node : TaskAbstractState) : UCOS2_Verify_State :=
  os_sched_profile_global_state (os_sched_profile_task_state state slot node).

Definition sched_profile_counter_address (pointer : addr) : addr :=
  &(pointer # "os_tcb" ->ₛ "OSTCBCtxSwCtr").

(** The selected pointer is read from the actual new high-ready cache.
    The source still dereferences NULL/reserved encodings if reached;
    liveness is a caller proof obligation, not a new guard in this relation. *)
Definition os_sched_profile_task_fragment (sg : StableGlobVars) (before after : model) : Prop :=
  exists pointer count,
    pointer_load sg.(g_OSTCBHighRdy) pointer before /\
    pointer_load (sched_profile_counter_address pointer) count before /\
    kernel_heap_execution
      (pointer_store_writes (sched_profile_counter_address pointer)
        (kernel_u32 (count + 1))) before after.

Definition os_sched_profile_global_fragment (sg : StableGlobVars) (before after : model) : Prop :=
  exists count, pointer_load sg.(g_OSCtxSwCtr) count before /\
    kernel_heap_execution (pointer_store_writes sg.(g_OSCtxSwCtr)
      (kernel_u32 (count + 1))) before after.

Definition os_sched_profile_counts_fragment (sg : StableGlobVars) (before after : model) : Prop :=
  exists middle, os_sched_profile_task_fragment sg before middle /\
    os_sched_profile_global_fragment sg middle after.

Lemma os_sched_profile_task_raw_post : forall sg state slot node heap,
  sg.(osKernelConfig).(cfgTaskProfile) = true ->
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  UCOS2_raw_rep sg state heap ->
  exists final, os_sched_profile_task_fragment sg heap final /\
    UCOS2_raw_rep sg (os_sched_profile_task_state state slot node) final.
Proof.
  intros sg state slot node heap Hprofile Hhigh Hnode Hraw.
  assert (Hin : In TCBCtxSwCtr (tcb_configured_fields
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile))).
  { rewrite Hprofile; apply tcb_configured_profile_field_in; simpl; tauto. }
  assert (Hsplit : UCOS2_raw_rep sg state |--
    (sched_profile_counter_address (task_slot_addr sg slot)) # UInt |-> node.(tcbCtxSwCtr) **
    (task_public_storage_without_field sg state.(TskState) slot node TCBCtxSwCtr **
     (sched_raw_rep sg state.(TskState) state.(SchedState) **
      UCOS2_raw_rep_missing_task_storage_sched sg state))).
  { unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
    sep_apply_l_atomic (task_public_storage_split_field sg state.(TskState) slot node TCBCtxSwCtr Hnode Hin).
    cbn [tcb_layout_cell task_layout_image tcb_layout_image]; entailer!. }
  assert (Hpointer : pointer_load sg.(g_OSTCBHighRdy) (task_slot_addr sg slot) heap).
  { assert (Hfocus : UCOS2_raw_rep sg state |--
      sg.(g_OSTCBHighRdy) # Ptr |-> task_slot_addr sg slot ** TT).
    { unfold UCOS2_raw_rep, sched_raw_rep, sched_physical_rep; rewrite Hhigh.
      cbn [encode_task_link]; entailer!; intros ? ?; exact I. }
    eapply framed_pointer_store_load; exact (Hfocus heap Hraw). }
  assert (Hcount : pointer_load (sched_profile_counter_address (task_slot_addr sg slot))
    node.(tcbCtxSwCtr) heap).
  { destruct (Hsplit heap Hraw) as [cell [rest [Hjoin [Hcell Hrest]]]].
    eapply pointer_load_frame; [apply sched_profile_uint_load; exact Hcell|exact Hjoin]. }
  assert (Hforget : UCOS2_raw_rep sg state |--
    (sched_profile_counter_address (task_slot_addr sg slot)) # UInt |->_ **
    (task_public_storage_without_field sg state.(TskState) slot node TCBCtxSwCtr **
     (sched_raw_rep sg state.(TskState) state.(SchedState) **
      UCOS2_raw_rep_missing_task_storage_sched sg state))).
  { eapply derivable1_trans; [exact Hsplit|].
    apply derivable1_sepcon_mono; [apply store_uint_undef_store_uint|reflexivity]. }
  destruct (sched_profile_uint_store_frame_post _ (kernel_u32 (node.(tcbCtxSwCtr) + 1)) _ heap
    (kernel_u32_in_range _) (Hforget heap Hraw)) as [final [Hrun Hpost]].
  exists final; split.
  - exists (task_slot_addr sg slot), node.(tcbCtxSwCtr); split; [exact Hpointer|]; split; assumption.
  - assert (Hsched : sched_raw_rep sg state.(TskState) state.(SchedState) =
      sched_raw_rep sg (glob_task_set_usedtask state.(TskState) slot (task_record_context_switch node)) state.(SchedState)).
    { apply sched_raw_rep_priority_ext; intros tid Htid; symmetry.
      eapply glob_task_set_usedtask_observation; [exact Hnode|reflexivity]. }
    assert (Hevent : event_raw_rep sg state.(TskState) state.(EventState) =
      event_raw_rep sg (glob_task_set_usedtask state.(TskState) slot (task_record_context_switch node)) state.(EventState)).
    { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
      eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hnode|reflexivity]. }
    assert (Hmerge :
      (sched_profile_counter_address (task_slot_addr sg slot)) # UInt |-> kernel_u32 (node.(tcbCtxSwCtr) + 1) **
      (task_public_storage_without_field sg state.(TskState) slot node TCBCtxSwCtr **
       (sched_raw_rep sg state.(TskState) state.(SchedState) ** UCOS2_raw_rep_missing_task_storage_sched sg state)) |--
      UCOS2_raw_rep sg (os_sched_profile_task_state state slot node)).
    { unfold os_sched_profile_task_state, UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
      cbn [replace_TskS TskState SchedState IntrState EventState TickState FlagState MemoryState
        TimerState StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
      rewrite <- Hsched, <- Hevent.
      unfold sched_profile_counter_address.
      pose proof (task_public_storage_merge_context_switch sg state.(TskState) slot node Hprofile) as Hfield.
      cbn [tcb_layout_cell] in Hfield.
      sep_apply_l_atomic Hfield.
      entailer!. }
    exact (Hmerge final Hpost).
Qed.

Lemma os_sched_profile_global_raw_post : forall sg state heap,
  UCOS2_raw_rep sg state heap ->
  exists final, os_sched_profile_global_fragment sg heap final /\
    UCOS2_raw_rep sg (os_sched_profile_global_state state) final.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_raw_rep sg state |--
    sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
    (sched_physical_without_counter sg state.(SchedState) **
     sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_raw_rep_missing_sched sg state)).
  { rewrite (UCOS2_raw_rep_split_module sg state SchedModule); cbn [UCOS2_module_rep].
    unfold sched_raw_rep; sep_apply_l_atomic (sched_physical_split_counter sg state.(SchedState)); entailer!. }
  assert (Hload : pointer_load sg.(g_OSCtxSwCtr) state.(SchedState).(ctxSwCtr) heap).
  { destruct (Hsplit heap Hraw) as [cell [rest [Hjoin [Hcell Hrest]]]].
    eapply pointer_load_frame; [apply sched_profile_uint_load; exact Hcell|exact Hjoin]. }
  assert (Hforget : sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
    (sched_physical_without_counter sg state.(SchedState) **
     sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_raw_rep_missing_sched sg state) |--
    sg.(g_OSCtxSwCtr) # UInt |->_ **
    (sched_physical_without_counter sg state.(SchedState) **
     sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_raw_rep_missing_sched sg state)).
  { apply derivable1_sepcon_mono; [apply store_uint_undef_store_uint|reflexivity]. }
  destruct (sched_profile_uint_store_frame_post _ (kernel_u32 (state.(SchedState).(ctxSwCtr) + 1)) _ heap
    (kernel_u32_in_range _) (Hforget heap (Hsplit heap Hraw))) as [final [Hrun Hpost]].
  exists final; split; [exists state.(SchedState).(ctxSwCtr); split; assumption|].
  assert (Hmerge : sg.(g_OSCtxSwCtr) # UInt |-> kernel_u32 (state.(SchedState).(ctxSwCtr) + 1) **
    (sched_physical_without_counter sg state.(SchedState) **
     sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_raw_rep_missing_sched sg state) |-- UCOS2_raw_rep sg (os_sched_profile_global_state state)).
  { rewrite (UCOS2_raw_rep_split_module sg (os_sched_profile_global_state state) SchedModule).
    cbn [UCOS2_module_rep]. unfold os_sched_profile_global_state.
    change (sg.(g_OSCtxSwCtr) # UInt |-> kernel_u32 (state.(SchedState).(ctxSwCtr) + 1) **
      (sched_physical_without_counter sg state.(SchedState) **
       sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
       sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
       UCOS2_raw_rep_missing_sched sg state) |--
      sched_raw_rep sg state.(TskState) (sched_increment_switch_counter state.(SchedState)) **
      UCOS2_raw_rep_missing_sched sg state).
    unfold sched_raw_rep; cbn [sched_increment_switch_counter readyList].
    sep_apply_l_atomic (sched_physical_merge_incremented_counter sg state.(SchedState)); entailer!. }
  exact (Hmerge final Hpost).
Qed.

Lemma os_sched_profile_counts_raw_post : forall sg state slot node heap,
  sg.(osKernelConfig).(cfgTaskProfile) = true ->
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  UCOS2_raw_rep sg state heap ->
  exists final, os_sched_profile_counts_fragment sg heap final /\
    UCOS2_raw_rep sg (os_sched_profile_counts_state state slot node) final.
Proof.
  intros sg state slot node heap Hprofile Hhigh Hnode Hraw.
  destruct (os_sched_profile_task_raw_post _ _ _ _ _ Hprofile Hhigh Hnode Hraw)
    as [middle [Htask Hmiddle]].
  destruct (os_sched_profile_global_raw_post sg _ middle Hmiddle) as [final [Hglobal Hfinal]].
  exists final; split; [exists middle; split; assumption|exact Hfinal].
Qed.

Lemma os_sched_profile_task_fragment_frame : forall sg before after frame whole,
  os_sched_profile_task_fragment sg before after -> join before frame whole ->
  exists final, os_sched_profile_task_fragment sg whole final /\ join after frame final.
Proof.
  intros sg before after frame whole [pointer [count [Hp [Hc Hrun]]]] Hjoin.
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  exists final; split; [|exact Hfinal].
  exists pointer, count; split; [eapply pointer_load_frame; eassumption|].
  split; [eapply pointer_load_frame; eassumption|exact Hwhole].
Qed.

Lemma os_sched_profile_global_fragment_frame : forall sg before after frame whole,
  os_sched_profile_global_fragment sg before after -> join before frame whole ->
  exists final, os_sched_profile_global_fragment sg whole final /\ join after frame final.
Proof.
  intros sg before after frame whole [count [Hc Hrun]] Hjoin.
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  exists final; split; [|exact Hfinal].
  exists count; split; [eapply pointer_load_frame; eassumption|exact Hwhole].
Qed.

Lemma os_sched_profile_counts_fragment_frame : forall sg before after frame whole,
  os_sched_profile_counts_fragment sg before after -> join before frame whole ->
  exists final, os_sched_profile_counts_fragment sg whole final /\ join after frame final.
Proof.
  intros sg before after frame whole [middle [Htask Hglobal]] Hjoin.
  destruct (os_sched_profile_task_fragment_frame sg before middle frame whole Htask Hjoin)
    as [mid [Hmid Hjoinmid]].
  destruct (os_sched_profile_global_fragment_frame sg middle after frame mid Hglobal Hjoinmid)
    as [final [Hfinal Hjoinfinal]].
  exists final; split; [exists mid; split; assumption|exact Hjoinfinal].
Qed.

Lemma os_sched_profile_task_fragment_deterministic : forall sg before first second,
  os_sched_profile_task_fragment sg before first ->
  os_sched_profile_task_fragment sg before second -> first = second.
Proof.
  intros sg before first second [pointer [count [Hp [Hc Hrun]]]]
    [pointer' [count' [Hp' [Hc' Hrun']]]].
  assert (pointer = pointer') by (eapply pointer_load_deterministic; eassumption); subst pointer'.
  assert (count = count') by (eapply pointer_load_deterministic; eassumption); subst count'.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma os_sched_profile_global_fragment_deterministic : forall sg before first second,
  os_sched_profile_global_fragment sg before first ->
  os_sched_profile_global_fragment sg before second -> first = second.
Proof.
  intros sg before first second [count [Hc Hrun]] [count' [Hc' Hrun']].
  assert (count = count') by (eapply pointer_load_deterministic; eassumption); subst count'.
  eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma os_sched_profile_counts_fragment_deterministic : forall sg before first second,
  os_sched_profile_counts_fragment sg before first ->
  os_sched_profile_counts_fragment sg before second -> first = second.
Proof.
  intros sg before first second [middle [Htask Hglobal]] [middle' [Htask' Hglobal']].
  assert (middle = middle') by (eapply os_sched_profile_task_fragment_deterministic; eassumption).
  subst middle'; eapply os_sched_profile_global_fragment_deterministic; eassumption.
Qed.

Lemma os_sched_profile_counts_preserves_full_validity : forall sg state slot node,
  UCOS2_full_state_inv sg state -> state.(TskState).(inUsedTaskStates) slot = Some node ->
  UCOS2_full_state_inv sg (os_sched_profile_counts_state state slot node).
Proof.
  intros sg state slot node Hvalid Hnode.
  assert (Htask : UCOS2_full_state_inv sg (os_sched_profile_task_state state slot node)).
  { unfold os_sched_profile_task_state, task_record_context_switch.
    eapply UCOS2_full_state_inv_task_set_profile_preserved; eassumption. }
  unfold os_sched_profile_counts_state, os_sched_profile_global_state.
  destruct Htask as [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hrest]]]]]].
  split; [exact Hprofile|]. split; [exact Htasks|]. split.
  - apply sched_increment_switch_counter_preserves_registered_in_range; exact Hsched.
  - split; [exact Hevents|]. split.
    + apply cross_module_registration_sched_frame; [reflexivity|exact Hcross].
    + split; [exact Hidle|exact Hrest].
Qed.

(** Consume the two actual typed stores and recover the SAME full-profile
    global owner plus the same disjoint caller frame. The live high-ready
    lookup is an internal source-cut requirement; the caller must establish
    it from the actual selection. No guard is added to the C relation. *)
Lemma os_sched_profile_counts_full_frame_post : forall sg state slot node (frame : Assertion) heap,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  (UCOS2_full_inv sg state ** frame) heap ->
  exists final, os_sched_profile_counts_fragment sg heap final /\
    (UCOS2_full_inv sg (os_sched_profile_counts_state state slot node) ** frame) final.
Proof.
  intros sg state slot node frame heap Hhigh Hnode
    [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  assert (Hprofile : sg.(osKernelConfig).(cfgTaskProfile) = true).
  { pose proof (proj1 Hvalid) as Hprofile.
    unfold full_features_kernel_profile in Hprofile; tauto. }
  destruct (os_sched_profile_counts_raw_post sg state slot node owned Hprofile Hhigh Hnode Hraw)
    as [after [Hsource Hpost]].
  destruct (os_sched_profile_counts_fragment_frame sg owned after rest heap Hsource Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]. split; [|exact Hframe].
  split; [eapply os_sched_profile_counts_preserves_full_validity; eassumption|exact Hpost].
Qed.

Lemma os_sched_profile_counts_full_frame_preservation : forall sg state slot node
  (frame : Assertion) before after,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  (UCOS2_full_inv sg state ** frame) before ->
  os_sched_profile_counts_fragment sg before after ->
  (UCOS2_full_inv sg (os_sched_profile_counts_state state slot node) ** frame) after.
Proof.
  intros sg state slot node frame before after Hhigh Hnode Hbefore Hrun.
  destruct (os_sched_profile_counts_full_frame_post sg state slot node frame before Hhigh Hnode Hbefore)
    as [final [Hsource Hpost]].
  replace after with final by (eapply os_sched_profile_counts_fragment_deterministic; eassumption).
  exact Hpost.
Qed.

(** The shared actual selection/counting block of OS_Sched and OSIntExit.
    The two enclosing nesting/lock guards and masked-entry resources are
    supplied by their callers. This relation itself tests the NEW priority
    bytes, before entering the profiling stores. It does not call the
    platform switch or claim that this invocation has returned. *)
Definition os_sched_profile_selection_fragment (sg : StableGlobVars)
  (before after : model) : Prop :=
  exists selected high current,
    os_int_exit_selection_heap_fragment sg before selected /\
    uchar_load sg.(g_OSPrioHighRdy) high selected /\
    uchar_load sg.(g_OSPrioCur) current selected /\ high <> current /\
    os_sched_profile_counts_fragment sg selected after.

Lemma os_sched_profile_selection_full_frame_post : forall sg state head tail node
  (frame : Assertion) heap,
  state.(SchedState).(readyList) = head :: tail ->
  state.(TskState).(inUsedTaskStates) head = Some node ->
  sched_selected_priority state.(TskState) state.(SchedState) <>
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  (UCOS2_full_inv sg state ** unmap_table_rep sg ** frame) heap ->
  exists final, os_sched_profile_selection_fragment sg heap final /\
    (UCOS2_full_inv sg
      (os_sched_profile_counts_state (os_int_exit_selection_state state) head node) **
      unmap_table_rep sg ** frame) final.
Proof.
  intros sg state head tail node frame heap Hready Hnode Hdiff Hbefore.
  assert (Hvalid : UCOS2_full_state_inv sg state).
  { destruct Hbefore as [owned [rest [Hj [[kernel [table [Hj2 [[Hvalid Hraw] Htable]]]] Hframe]]]].
    exact Hvalid. }
  assert (Hsg : valid_stable_glob_vars sg) by exact (proj1 (proj1 Hvalid)).
  assert (Hregistered : task_current_prio_registered state.(TskState)).
  { destruct Hvalid as [_ [Ht _]]; unfold task_in_range in Ht; tauto. }
  assert (Hnonempty : state.(SchedState).(readyList) <> []) by (rewrite Hready; discriminate).
  assert (Herase : UCOS2_full_inv sg state ** unmap_table_rep sg ** frame |--
    UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame) by (unfold UCOS2_full_inv; entailer!).
  destruct (os_int_exit_selection_raw_frame_post_with_ready_structure sg state frame heap Hsg
    (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) Hregistered Hnonempty (Herase heap Hbefore))
    as [selected [Hselect [Hhighread [Hcurrentread Hselected]]]].
  assert (HvalidSelected : UCOS2_full_state_inv sg (os_int_exit_selection_state state)).
  { apply os_int_exit_selection_state_preserves_full_validity; exact Hvalid. }
  assert (Hmerge : UCOS2_raw_rep sg (os_int_exit_selection_state state) ** unmap_table_rep sg ** frame |--
    UCOS2_full_inv sg (os_int_exit_selection_state state) ** (unmap_table_rep sg ** frame)).
  { unfold UCOS2_full_inv; entailer!. }
  assert (Hhigh : (os_int_exit_selection_state state).(SchedState).(highRdyTid) = Some head).
  { unfold os_int_exit_selection_state; cbn [replace_SchedS SchedState sched_refresh_high highRdyTid].
    rewrite Hready; reflexivity. }
  destruct (os_sched_profile_counts_full_frame_post sg (os_int_exit_selection_state state)
    head node (unmap_table_rep sg ** frame) selected Hhigh Hnode (Hmerge selected Hselected))
    as [final [Hcounts Hfinal]].
  exists final; split.
  - exists selected, (sched_selected_priority state.(TskState) state.(SchedState)),
      (sched_priority_byte state.(SchedState).(curSchedPrio)).
    split; [exact Hselect|]. split; [exact Hhighread|]. split; [exact Hcurrentread|].
    split; assumption.
  - assert (Hreassoc : UCOS2_full_inv sg
      (os_sched_profile_counts_state (os_int_exit_selection_state state) head node) **
      (unmap_table_rep sg ** frame) |--
      UCOS2_full_inv sg (os_sched_profile_counts_state (os_int_exit_selection_state state) head node) **
      unmap_table_rep sg ** frame) by entailer!.
    exact (Hreassoc final Hfinal).
Qed.
