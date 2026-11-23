Require Export Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
Require Export AUXLib.ListLib AUXLib.int_auto AUXLib.Axioms.
From SimpleC.SL Require Export Mem SeparationLogic.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.array_abstraction.
Require Export Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.mutex.
Require Export Ucos2Verify.lib.event_wait Ucos2Verify.lib.cross_module_invariants.
Require Export Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The sole source store changes the configured native register word.
    It does not allocate an ID, change a task generation or modify an IPC,
    scheduling, stack or lifecycle field. *)
Definition task_set_reg0 (t : TaskAbstractState) (value : Z) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr); tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom); tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt); tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode); tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName); tcbReg0 := value;
     tcbCtxSwCtr := t.(tcbCtxSwCtr); tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart); tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed); tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43); tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := t.(stat); statPend := t.(statPend);
     dly := t.(dly); eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy); msg := t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_set_reg0_put_back : forall t, task_set_reg0 t t.(tcbReg0) = t.
Proof. intros []; reflexivity. Qed.

Lemma task_set_reg0_last_write : forall t first last,
  task_set_reg0 (task_set_reg0 t first) last = task_set_reg0 t last.
Proof. reflexivity. Qed.

Lemma task_set_reg0_layout_image_eq : forall sg t value,
  task_layout_image sg (task_set_reg0 t value) =
    tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBReg0) (Some value).
Proof. intros; apply functional_extensionality; intros [f| | | | | | |];
  try reflexivity; destruct f; reflexivity. Qed.

Definition task_reg_set_state (entry : UCOS2_Verify_State) tid old value :=
  replace_TskS (glob_task_set_usedtask entry.(TskState) tid (task_set_reg0 old value)) entry.

Lemma task_set_reg0_preserves_in_range : forall sg tasks tid old value,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_set_reg0 old value)).
Proof. intros; eapply task_update_preserves_in_range; eauto; reflexivity. Qed.

Lemma task_set_reg0_priority_observation_eq : forall tasks tid old value slot,
  tasks.(inUsedTaskStates) tid = Some old ->
  option_map curPrio (tasks.(inUsedTaskStates) slot) =
  option_map curPrio
    ((glob_task_set_usedtask tasks tid (task_set_reg0 old value)).(inUsedTaskStates) slot).
Proof.
  intros tasks tid old value slot Hold; simpl.
  destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E; subst slot; rewrite Hold; reflexivity.
Qed.

Lemma task_reg_set_preserves_cross_module_consistency : forall sg s tid old value,
  s.(TskState).(inUsedTaskStates) tid = Some old -> cross_module_consistency sg s ->
  cross_module_consistency sg (task_reg_set_state s tid old value).
Proof.
  intros sg s tid old value Hold
    [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  unfold task_reg_set_state.
  split; [eapply task_mutex_priotbl_consistency_update_task; [exact Hold|reflexivity|exact Htable]|].
  split; [eapply mutex_owner_snapshot_update_task; eauto|].
  split.
  - eapply event_wait_object_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hwait].
    intros kind Hphase; exact Hphase.
  - split; [exact Hprotocol|]; split; [exact Hunique|]; split; [|exact Htimer].
    eapply task_flag_waiter_consistency_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag]; auto.
Qed.

Lemma task_reg_set_preserves_validity : forall sg s tid old value,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_state_inv sg (task_reg_set_state s tid old value).
Proof.
  intros sg s tid old value
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]] Hold.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HreferencesAfter : kernel_names_valid sg (task_reg_set_state s tid old value)).
  { apply kernel_names_valid_replace_task; [exact Hreferences|].
    eapply task_update_name_references; [exact Hold|reflexivity]. }
  assert (HstacksAfter : parked_stacks_consistent
    (task_reg_set_state s tid old value).(TskState) s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  split; [exact Hprofile|]; split.
  - apply task_set_reg0_preserves_in_range with (old := old); assumption.
  - split.
    + eapply sched_update_task_preserves_in_range; [exact Hsched|exact Hold|reflexivity|reflexivity].
    + split.
      * eapply event_update_task_preserves_in_range;
          [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hevents].
        intros kind Hphase; exact Hphase.
      * split; [apply task_reg_set_preserves_cross_module_consistency; assumption|].
        split.
        -- intro Hrunning; eapply task_update_preserves_idle_tail;
             [exact Hold|reflexivity|apply Hidle; exact Hrunning].
        -- split.
           ++ apply task_reserved_bits_clear_update_task; [exact Hstatus|exact (Hstatus tid old Hold)].
           ++ repeat (split; [assumption|]); exact Hpending.
Qed.

Lemma task_reg_set_sched_rep_eq : forall sg s tid old value,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  sched_raw_rep sg s.(TskState) s.(SchedState) =
    sched_raw_rep sg (task_reg_set_state s tid old value).(TskState)
      (task_reg_set_state s tid old value).(SchedState).
Proof.
  intros; apply sched_raw_rep_priority_ext; intros.
  apply task_set_reg0_priority_observation_eq; assumption.
Qed.

Lemma task_reg_set_residual_eq : forall sg s tid old value,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_raw_rep_missing_task_storage_sched sg s =
    UCOS2_raw_rep_missing_task_storage_sched sg (task_reg_set_state s tid old value).
Proof.
  intros; unfold UCOS2_raw_rep_missing_task_storage_sched, task_reg_set_state; simpl.
  assert (Hevent : event_raw_rep sg s.(TskState) s.(EventState) =
    event_raw_rep sg (glob_task_set_usedtask s.(TskState) tid (task_set_reg0 old value)) s.(EventState)).
  { apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes.
    intros eid e slot He Hin; apply task_set_reg0_priority_observation_eq; assumption. }
  rewrite Hevent; reflexivity.
Qed.

(** A structural complement: the selected TCB's Reg0 is removed, not
    duplicated; all non-target task and module bytes remain owned. *)
Definition task_reg_set_without_reg0 (sg : StableGlobVars) (s : UCOS2_Verify_State)
  tid old : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid old (TCBCommonField TCBReg0) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Lemma task_reg_set_split_live_reg0 : forall sg s tid old,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_inv sg s |--
    coq_prop (UCOS2_state_inv sg s) &&
    (UIntArray.full (tcb_field_address (task_slot_addr sg tid) TCBReg0) 1 [old.(tcbReg0)] **
      task_reg_set_without_reg0 sg s tid old).
Proof.
  intros; sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg s).
  Intros.
  sep_apply_l_atomic (task_public_storage_split_field sg s.(TskState) tid old
    (TCBCommonField TCBReg0) H (tcb_configured_common_field_in _ _ TCBReg0)).
  unfold task_reg_set_without_reg0.
  cbn [task_layout_image tcb_layout_image tcb_layout_cell tcb_cell task_tcb64_image].
  entailer!.
Qed.

Lemma task_reg_set_merge_live_reg0 : forall sg s tid old value,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  UIntArray.full (tcb_field_address (task_slot_addr sg tid) TCBReg0) 1 [value] **
    task_reg_set_without_reg0 sg s tid old |--
      UCOS2_inv sg (task_reg_set_state s tid old value).
Proof.
  intros sg s tid old value Hvalid Hold.
  unfold task_reg_set_without_reg0.
  assert (Hcell : UIntArray.full (tcb_field_address (task_slot_addr sg tid) TCBReg0) 1 [value] =
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
      (TCBCommonField TCBReg0) (Some value)) by reflexivity.
  rewrite Hcell.
  sep_apply_l_atomic (task_public_storage_merge_updated_field sg s.(TskState) tid old
    (task_set_reg0 old value) (TCBCommonField TCBReg0) (Some value)
    (tcb_configured_common_field_in _ _ TCBReg0) (task_set_reg0_layout_image_eq sg old value)).
  rewrite (task_reg_set_sched_rep_eq sg s tid old value Hold).
  pose proof (task_reg_set_preserves_validity sg s tid old value Hvalid Hold) as Hpost.
  rewrite (task_reg_set_residual_eq sg s tid old value Hold).
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched; entailer!.
Qed.

Definition task_reg_set_current_pointer (sg : StableGlobVars) (s : UCOS2_Verify_State) :=
  encode_task_link sg s.(SchedState).(curTaskID).

Definition task_reg_set_pointer (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (priority : Z) :=
  if Z.eqb priority 255 then task_reg_set_current_pointer sg s
  else prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) priority).

Definition task_reg_set_addresses (sg : StableGlobVars) (current table : Z) : Prop :=
  current = sg.(g_OSTCBCur) /\ table = sg.(g_OSTCBPrioTbl).

Definition task_reg_set_free_state (s : UCOS2_Verify_State) tid image value :=
  let life := s.(TskState).(taskLifecycle) in
  replace_TskS (glob_task_set_lifecycle s.(TskState)
    {| taskFreeStorage := fun slot => if Z.eq_dec slot tid then
         Some (tcb_layout_write image (TCBCommonField TCBReg0) (Some value))
         else life.(taskFreeStorage) slot;
       taskReservations := life.(taskReservations);
       taskActiveOrder := life.(taskActiveOrder);
       taskNextGeneration := life.(taskNextGeneration);
       taskInvocations := life.(taskInvocations);
       taskRetiredInvocations := life.(taskRetiredInvocations);
       taskNextInvocation := life.(taskNextInvocation);
       taskPublications := life.(taskPublications) |}) s.

(** A commit records the exact storage owner.  In particular, an external
    caller-owned word cannot be obtained from a public/private slot merely
    by choosing an address: the actual separated caller cut is required. *)
Inductive task_reg_set_commit (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (caller : Assertion) (pointer value : Z)
  : UCOS2_Verify_State -> Assertion -> Prop :=
| TaskRegSetLive : forall tid old,
    pointer = task_slot_addr sg tid ->
    entry.(TskState).(inUsedTaskStates) tid = Some old ->
    task_reg_set_commit sg entry caller pointer value
      (task_reg_set_state entry tid old value) caller
| TaskRegSetFree : forall tid image,
    pointer = task_slot_addr sg tid -> In tid entry.(TskState).(unUsedTaskStates) ->
    entry.(TskState).(taskLifecycle).(taskFreeStorage) tid = Some image ->
    task_reg_set_commit sg entry caller pointer value
      (task_reg_set_free_state entry tid image value) caller
| TaskRegSetPrivate : forall priority reservation allocation invocation frame,
    pointer = task_slot_addr sg allocation.(privateSlot) ->
    entry.(TskState).(taskLifecycle).(taskReservations) priority = Some reservation ->
    reservation.(creationAllocation) = Some allocation ->
    reservation.(creationInvocation) = invocation ->
    caller = task_private_storage sg entry.(TskState) invocation ** frame ->
    task_reg_set_commit sg entry caller pointer value
      (replace_TskS (task_update_private_image entry.(TskState) priority reservation allocation
        (tcb_layout_write allocation.(privateStorage) (TCBCommonField TCBReg0) (Some value))) entry)
      (task_private_storage sg
        (task_update_private_image entry.(TskState) priority reservation allocation
          (tcb_layout_write allocation.(privateStorage) (TCBCommonField TCBReg0) (Some value)))
        invocation ** frame)
| TaskRegSetCaller : forall residual,
    (caller |-- UIntArray.undef_full (tcb_field_address pointer TCBReg0) 1 ** residual) ->
    task_reg_set_commit sg entry caller pointer value entry
      (UIntArray.full (tcb_field_address pointer TCBReg0) 1 [value] ** residual).

(** This is an actual writable cut, with the SAME untouched residual on
    both sides of the sole store.  It is neither a Boolean validity test nor
    a platform assumption, and accepts uninitialized writable Reg0 storage. *)
Definition task_reg_set_writable (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (caller : Assertion) (pointer value : Z) : Prop :=
  exists released after_caller residual,
    UCOS2_state_inv sg released /\
    task_reg_set_commit sg entry caller pointer value released after_caller /\
    (UCOS2_inv sg entry ** caller |--
      UIntArray.undef_full (tcb_field_address pointer TCBReg0) 1 ** residual) /\
    (UIntArray.full (tcb_field_address pointer TCBReg0) 1 [value] ** residual |--
      UCOS2_inv sg released ** after_caller).

Lemma task_reg_set_live_writable : forall sg entry caller tid old value,
  UCOS2_state_inv sg entry -> entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_reg_set_writable sg entry caller (task_slot_addr sg tid) value.
Proof.
  intros sg entry caller tid old value Hvalid Hold.
  exists (task_reg_set_state entry tid old value), caller,
    (coq_prop (UCOS2_state_inv sg entry) &&
      (task_reg_set_without_reg0 sg entry tid old ** caller)).
  split; [eapply task_reg_set_preserves_validity; eauto|].
  split; [econstructor; eauto|]; split.
  - sep_apply_l_atomic (task_reg_set_split_live_reg0 sg entry tid old Hold).
    Intros; sep_apply_l_atomic
      (UIntArray.full_to_undef_full (tcb_field_address (task_slot_addr sg tid) TCBReg0) 1 [old.(tcbReg0)]).
    entailer!.
  - Intros; sep_apply_l_atomic
      (task_reg_set_merge_live_reg0 sg entry tid old value Hvalid Hold); entailer!.
Qed.

Lemma task_reg_set_caller_writable : forall sg entry caller pointer value residual,
  UCOS2_state_inv sg entry ->
  (caller |-- UIntArray.undef_full (tcb_field_address pointer TCBReg0) 1 ** residual) ->
  task_reg_set_writable sg entry caller pointer value.
Proof.
  intros sg entry caller pointer value residual Hvalid Hcut.
  exists entry, (UIntArray.full (tcb_field_address pointer TCBReg0) 1 [value] ** residual),
    (UCOS2_inv sg entry ** residual).
  split; [exact Hvalid|]; split; [constructor; exact Hcut|]; split.
  - sep_apply_l_atomic Hcut; entailer!.
  - entailer!.
Qed.

(** No prerequisite is imposed on early errors, explicit-table branches or
    concrete NULL/reserved selections.  A client supplies this admission
    only for an actual SELF dereference at an acquired endpoint. *)
Definition task_reg_set_self_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (priority id value : Z) (caller : Assertion) : Prop :=
  priority = 255 -> id = 0 -> forall entry,
    critical_region_interval critical sg invocation before entry ->
    UCOS2_state_inv sg entry ->
    task_reg_set_current_pointer sg entry <> 0 ->
    task_reg_set_current_pointer sg entry <> 1 ->
    task_reg_set_writable sg entry caller (task_reg_set_current_pointer sg entry) value.

Definition task_reg_set_live_current (s : UCOS2_Verify_State) : Prop :=
  forall tid, s.(SchedState).(curTaskID) = Some tid ->
    exists t, s.(TskState).(inUsedTaskStates) tid = Some t.

Lemma task_reg_set_boot_live_current : forall s,
  s.(SchedState).(curTaskID) = None -> task_reg_set_live_current s.
Proof. intros s Hboot tid Hcurrent; rewrite Hboot in Hcurrent; discriminate. Qed.

Lemma task_reg_set_installed_live_current : forall tasks sched s,
  sched_high_ready_consistency tasks sched -> s.(TskState) = tasks ->
  s.(SchedState) = sched_install_selected sched -> task_reg_set_live_current s.
Proof.
  intros tasks sched s Hselected Htasks Hsched tid Hcurrent.
  pose proof (sched_install_selected_synchronizes_current tasks sched Hselected) as Hsync.
  unfold sched_current_consistency in Hsync.
  rewrite Hsched in Hcurrent; rewrite Hcurrent in Hsync.
  destruct Hsync as [t [Hlookup _]]; exists t; rewrite Htasks; exact Hlookup.
Qed.

Lemma task_reg_set_interval_live_current : forall critical sg invocation before after,
  (forall client, critical.(critical_region_clients) client -> forall first next,
    UCOS2_state_inv sg first -> kernel_client_step client sg first next ->
    task_reg_set_live_current first -> task_reg_set_live_current next) ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before -> task_reg_set_live_current before ->
  task_reg_set_live_current after.
Proof.
  intros critical sg invocation before after Hclients Hinterval.
  pose proof (critical_region_interval_raw_trace critical sg invocation before after Hinterval) as Htrace.
  clear Hinterval; induction Htrace; intros Hvalid Hcurrent; [exact Hcurrent|].
  apply IHHtrace.
  - eapply kernel_client_preserves_validity;
      [eapply (critical_region_client_certificates critical); eassumption|exact Hvalid|eassumption].
  - eapply Hclients; eassumption.
Qed.

(** Only the observed pointer cell is removed.  The remaining Scheduler,
    Task and other module storage is the original structural complement. *)
Definition task_reg_set_current_frame (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  task_public_storage sg s.(TskState) **
  (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(SchedState).(readyList) s.(TskState) **
   sched_rows_rep sg s.(TskState) s.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
   sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(SchedState).(curSchedPrio) **
   sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(SchedState).(highRdyPrio) **
   sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(SchedState).(highRdyTid) **
   sg.(g_OSCtxSwCtr) # UInt |-> s.(SchedState).(ctxSwCtr) **
   sg.(g_OSRunning) # UChar |-> (if s.(SchedState).(isRunning) then 1 else 0)) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Lemma task_reg_set_split_current : forall sg s,
  UCOS2_inv sg s |--
    coq_prop (UCOS2_state_inv sg s) &&
    (sg.(g_OSTCBCur) # Ptr |-> task_reg_set_current_pointer sg s **
     task_reg_set_current_frame sg s).
Proof.
  intros; unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    task_reg_set_current_frame, sched_raw_rep, sched_physical_rep,
    task_reg_set_current_pointer, UCOS2_raw_rep_missing_task_storage_sched; entailer!.
Qed.

Lemma task_reg_set_merge_current : forall sg s,
  UCOS2_state_inv sg s ->
  sg.(g_OSTCBCur) # Ptr |-> task_reg_set_current_pointer sg s **
    task_reg_set_current_frame sg s |-- UCOS2_inv sg s.
Proof.
  intros; unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    task_reg_set_current_frame, sched_raw_rep, sched_physical_rep,
    task_reg_set_current_pointer, UCOS2_raw_rep_missing_task_storage_sched; entailer!.
Qed.

Definition task_reg_set_table_pointer (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (priority : Z) : Z :=
  prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) priority).

Definition task_reg_set_table_frame (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (priority : Z) : Assertion :=
  store_prio_tbl_missing_i sg s.(TskState).(prioTbl) priority **
  UCOS2_raw_rep_missing_priority_table sg s.

Lemma task_reg_set_split_table : forall sg s priority,
  0 <= priority < 64 -> UCOS2_inv sg s |--
  coq_prop (UCOS2_state_inv sg s) &&
    ((sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
       task_reg_set_table_pointer sg s priority **
     task_reg_set_table_frame sg s priority).
Proof.
  intros; unfold task_reg_set_table_pointer, task_reg_set_table_frame.
  sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg s priority H); entailer!.
Qed.

Lemma task_reg_set_merge_table : forall sg s priority,
  UCOS2_state_inv sg s -> 0 <= priority < 64 ->
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    task_reg_set_table_pointer sg s priority **
    task_reg_set_table_frame sg s priority |-- UCOS2_inv sg s.
Proof.
  intros sg s priority Hvalid Hpriority.
  unfold task_reg_set_table_pointer, task_reg_set_table_frame.
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg s.(TskState).(prioTbl) priority Hpriority).
  unfold UCOS2_inv; rewrite UCOS2_raw_rep_priority_table_equiv; entailer!.
Qed.

Lemma task_reg_set_table_selection_live : forall sg s priority,
  UCOS2_state_inv sg s -> 0 <= priority < 63 ->
  task_reg_set_table_pointer sg s priority <> 0 ->
  task_reg_set_table_pointer sg s priority <> 1 ->
  exists tid old, task_reg_set_table_pointer sg s priority = task_slot_addr sg tid /\
    s.(TskState).(inUsedTaskStates) tid = Some old.
Proof.
  intros sg s priority Hvalid Hpriority Hnull Hreserved.
  destruct Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]].
  destruct Hprofile as [Hsg _].
  assert (Hlowest : sg.(osLowestPrio) = 63) by (unfold valid_stable_glob_vars in Hsg; tauto).
  destruct Hcross as [[_ [Htable _]] _].
  assert (Hrange : task_priority_in_range sg priority) by
    (unfold task_priority_in_range; lia).
  specialize (Htable priority Hrange).
  unfold task_reg_set_table_pointer, prio_tbl_entry_to_addr in *.
  destruct (s.(TskState).(prioTbl) priority) as [| |tid];
    [contradiction|contradiction|].
  destruct Htable as [old Hold]; exists tid, old; auto.
Qed.

(** The program's ordered errors are independent of selected-task liveness. *)
Definition task_reg_set_priority_valid (priority : Z) : Prop :=
  priority < 63 \/ priority = 255.

Definition task_reg_set_effect (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (caller : Assertion) (priority id value pointer error : Z)
  (released : UCOS2_Verify_State) (after_caller : Assertion) : Prop :=
  task_reg_set_priority_valid priority /\ id = 0 /\
  pointer = task_reg_set_pointer sg entry priority /\
  (((pointer = 0 \/ pointer = 1) /\ error = 67 /\
      released = entry /\ after_caller = caller) \/
   (pointer <> 0 /\ pointer <> 1 /\ error = 0 /\
      task_reg_set_commit sg entry caller pointer value released after_caller)).

(** This post-store resource consequence is carried across the concrete
    assignment.  Its witness is obtained from the writable ownership cut;
    no callee supplies a task-liveness fact. *)
Definition task_reg_set_store_closure (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (caller : Assertion) (pointer value : Z)
  (released : UCOS2_Verify_State) (after_caller residual : Assertion) : Prop :=
  UCOS2_state_inv sg released /\
  task_reg_set_commit sg entry caller pointer value released after_caller /\
  (UIntArray.full (tcb_field_address pointer TCBReg0) 1 [value] ** residual |--
    UCOS2_inv sg released ** after_caller).

Lemma task_reg_set_selection_writable :
  forall critical sg invocation before entry priority id value caller,
  UCOS2_state_inv sg entry -> 0 <= priority ->
  task_reg_set_priority_valid priority -> id = 0 ->
  task_reg_set_self_admission critical sg invocation before priority id value caller ->
  critical_region_interval critical sg invocation before entry ->
  task_reg_set_pointer sg entry priority <> 0 ->
  task_reg_set_pointer sg entry priority <> 1 ->
  task_reg_set_writable sg entry caller (task_reg_set_pointer sg entry priority) value.
Proof.
  intros critical sg invocation before entry priority id value caller
    Hvalid Hnonnegative Hpriority Hid Hadmission Hinterval Hnull Hreserved.
  unfold task_reg_set_pointer in *.
  destruct (Z.eqb priority 255) eqn:Hself.
  - apply Z.eqb_eq in Hself.
    exact (Hadmission Hself Hid entry Hinterval Hvalid Hnull Hreserved).
  - apply Z.eqb_neq in Hself.
    destruct (task_reg_set_table_selection_live sg entry priority Hvalid
      ltac:(unfold task_reg_set_priority_valid in Hpriority; lia) Hnull Hreserved)
      as [tid [old [Hpointer Hold]]].
    change (task_reg_set_writable sg entry caller
      (task_reg_set_table_pointer sg entry priority) value).
    rewrite Hpointer; eapply task_reg_set_live_writable; eassumption.
Qed.

Lemma task_reg_set_focus_writable : forall sg entry caller pointer value,
  task_reg_set_writable sg entry caller pointer value ->
  UCOS2_inv sg entry ** caller |--
    EX released after_caller residual,
      coq_prop (task_reg_set_store_closure sg entry caller pointer value
        released after_caller residual) &&
      (UIntArray.undef_full (tcb_field_address pointer TCBReg0) 1 ** residual).
Proof.
  intros sg entry caller pointer value
    [released [after_caller [residual [Hvalid [Hcommit [Hbefore Hafter]]]]]].
  Exists released after_caller residual.
  sep_apply_l_atomic Hbefore.
  unfold task_reg_set_store_closure; entailer!.
Qed.

(** The observable result is the byte written through [perr], not a return
    value of this void C function.  The protected store reuses the exact
    existing ownership-indexed commit; its caller resource is retained by
    the concrete postcondition, while the program projects its kernel state. *)
Definition task_reg_set_protected_program (sg : StableGlobVars)
  (caller : Assertion) (priority value : Z) : program UCOS2_Verify_State Z :=
  StateRelMonad.bind (get' (fun entry => task_reg_set_pointer sg entry priority))
    (fun pointer =>
      if orb (Z.eqb pointer 0) (Z.eqb pointer 1) then StateRelMonad.ret 67
      else StateRelMonad.bind
        (update (fun entry released => exists after_caller,
          task_reg_set_commit sg entry caller pointer value released after_caller))
        (fun _ => StateRelMonad.ret 0)).

(** These are the two real enabled-interrupt intervals around the protected
    lookup/store.  The entire API is not a single atomic operation. *)
Definition task_reg_set_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (caller : Assertion)
  (priority id value : Z) : program UCOS2_Verify_State Z :=
  if andb (Z.leb 63 priority) (negb (Z.eqb priority 255)) then StateRelMonad.ret 42
  else if Z.leb 1 id then StateRelMonad.ret 8
  else StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (task_reg_set_protected_program sg caller priority value)
      (fun error => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret error))).

Definition task_reg_set_result critical sg invocation before caller priority id value
  error after after_caller : Prop :=
  (63 <= priority /\ priority <> 255 /\ error = 42 /\
    after = before /\ after_caller = caller) \/
  (task_reg_set_priority_valid priority /\ 1 <= id /\ error = 8 /\
    after = before /\ after_caller = caller) \/
  (exists entry released pointer,
    critical_region_interval critical sg invocation before entry /\
    task_reg_set_effect sg entry caller priority id value pointer error released after_caller /\
    critical_region_interval critical sg invocation released after).

Definition task_reg_set_safe critical sg invocation before caller priority id value
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (task_reg_set_program critical sg invocation caller priority id value) X.

Definition task_reg_set_safe_result error after
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = after) (StateRelMonad.ret error) X.

Lemma task_reg_set_priority_valid_guard : forall priority,
  task_reg_set_priority_valid priority ->
  andb (Z.leb 63 priority) (negb (Z.eqb priority 255)) = false.
Proof.
  intros priority [Hlt | ->]; [|reflexivity].
  assert (E : Z.leb 63 priority = false) by (apply Z.leb_gt; lia).
  rewrite E; reflexivity.
Qed.

Lemma task_reg_set_effect_program : forall sg entry caller priority id value pointer
  error released after_caller,
  task_reg_set_effect sg entry caller priority id value pointer error released after_caller ->
  task_reg_set_protected_program sg caller priority value entry error released.
Proof.
  intros sg entry caller priority id value pointer error released after_caller
    [_ [_ [Hpointer Hstep]]].
  unfold task_reg_set_protected_program.
  exists pointer, entry; split; [split; [exact Hpointer|reflexivity]|].
  destruct Hstep as [[Hmissing [-> [-> _]]]|[Hnull [Hreserved [-> Hcommit]]]].
  - assert (E : orb (Z.eqb pointer 0) (Z.eqb pointer 1) = true).
    { apply orb_true_iff; destruct Hmissing as [-> | ->]; auto. }
    rewrite E; split; reflexivity.
  - assert (E0 : Z.eqb pointer 0 = false) by (apply Z.eqb_neq; assumption).
    assert (E1 : Z.eqb pointer 1 = false) by (apply Z.eqb_neq; assumption).
    rewrite E0, E1; exists tt, released; split.
    + exists after_caller; exact Hcommit.
    + split; reflexivity.
Qed.

Lemma task_reg_set_result_program : forall critical sg invocation before caller priority id value
  error after after_caller,
  task_reg_set_result critical sg invocation before caller priority id value error after after_caller ->
  task_reg_set_program critical sg invocation caller priority id value before error after.
Proof.
  intros critical sg invocation before caller priority id value error after after_caller Hresult.
  unfold task_reg_set_program.
  destruct Hresult as [[Hbound [Hself [-> [-> _]]]]|
    [[Hpriority [Hid [-> [-> _]]]]|[entry [released [pointer [Hacquire [Heffect Hrelease]]]]]]].
  - assert (Ebound : Z.leb 63 priority = true) by (apply Z.leb_le; assumption).
    assert (Eself : Z.eqb priority 255 = false) by (apply Z.eqb_neq; assumption).
    rewrite Ebound, Eself; split; reflexivity.
  - rewrite (task_reg_set_priority_valid_guard priority Hpriority).
    assert (Eid : Z.leb 1 id = true) by (apply Z.leb_le; assumption).
    rewrite Eid; split; reflexivity.
  - pose proof Heffect as Horiginal.
    destruct Heffect as [Hpriority [Hid Hrest]].
    rewrite (task_reg_set_priority_valid_guard priority Hpriority), Hid; cbn.
    exists tt, entry; split; [exact Hacquire|].
    exists error, released; split.
    + eapply task_reg_set_effect_program; exact Horiginal.
    + exists tt, after; split; [exact Hrelease|split; reflexivity].
Qed.

Lemma task_reg_set_safe_return : forall critical sg invocation before caller priority id value
  error after after_caller X,
  task_reg_set_result critical sg invocation before caller priority id value error after after_caller ->
  task_reg_set_safe critical sg invocation before caller priority id value X ->
  task_reg_set_safe_result error after X.
Proof.
  intros critical sg invocation before caller priority id value error after after_caller X Hresult Hsafe.
  unfold task_reg_set_safe_result.
  eapply (highstependret_derive
    (task_reg_set_program critical sg invocation caller priority id value)
    (fun state => state = before) error (fun _ state => state = after)).
  - intros state ->; exists after; split; [|reflexivity].
    eapply task_reg_set_result_program; exact Hresult.
  - exact Hsafe.
Qed.

Lemma task_reg_set_protected_program_effect : forall sg caller priority value entry error released,
  task_reg_set_priority_valid priority ->
  task_reg_set_protected_program sg caller priority value entry error released ->
  exists after_caller, task_reg_set_effect sg entry caller priority 0 value
    (task_reg_set_pointer sg entry priority) error released after_caller.
Proof.
  intros sg caller priority value entry error released Hpriority Hprogram.
  unfold task_reg_set_protected_program in Hprogram.
  destruct Hprogram as [pointer [mid [[Hpointer Hmid] Hprogram]]].
  subst pointer mid.
  destruct (orb (Z.eqb (task_reg_set_pointer sg entry priority) 0)
    (Z.eqb (task_reg_set_pointer sg entry priority) 1)) eqn:E.
  - destruct Hprogram as [-> Hreleased]; subst released.
    assert (Hmissing : task_reg_set_pointer sg entry priority = 0 \/
      task_reg_set_pointer sg entry priority = 1).
    { apply orb_true_iff in E; destruct E as [E|E]; [left|right]; apply Z.eqb_eq; exact E. }
    exists caller; unfold task_reg_set_effect.
    split; [exact Hpriority|]; split; [reflexivity|]; split; [reflexivity|].
    left; repeat split; auto.
  - apply orb_false_iff in E; destruct E as [E0 E1].
    apply Z.eqb_neq in E0; apply Z.eqb_neq in E1.
    destruct Hprogram as [u [written [Hcommit [-> Hreleased]]]].
    subst written; destruct Hcommit as [after_caller Hcommit].
    exists after_caller; unfold task_reg_set_effect.
    split; [exact Hpriority|]; split; [reflexivity|]; split; [reflexivity|].
    right; repeat split; assumption.
Qed.

(** Exact endpoint equivalence with the old relation, after hiding only the
    resource index which remains explicit in the separation-logic post. *)
Lemma task_reg_set_program_result_iff : forall critical sg invocation before caller priority id value
  error after,
  0 <= id ->
  (task_reg_set_program critical sg invocation caller priority id value before error after <->
   exists after_caller,
     task_reg_set_result critical sg invocation before caller priority id value error after after_caller).
Proof.
  intros critical sg invocation before caller priority id value error after Hid.
  split; [|intros [after_caller Hresult]; eapply task_reg_set_result_program; exact Hresult].
  unfold task_reg_set_program.
  destruct (andb (Z.leb 63 priority) (negb (Z.eqb priority 255))) eqn:Epriority.
  - intros [-> Hafter]; subst after.
    apply andb_true_iff in Epriority; destruct Epriority as [Hbound Hself].
    apply Z.leb_le in Hbound; apply negb_true_iff in Hself; apply Z.eqb_neq in Hself.
    exists caller; left; repeat split; auto.
  - assert (Hpriority : task_reg_set_priority_valid priority).
    { apply andb_false_iff in Epriority; destruct Epriority as [Hbound|Hself].
      - apply Z.leb_gt in Hbound; left; exact Hbound.
      - apply negb_false_iff in Hself; apply Z.eqb_eq in Hself; right; exact Hself. }
    destruct (Z.leb 1 id) eqn:Eid.
    + intros [-> Hafter]; subst after; apply Z.leb_le in Eid.
      exists caller; right; left; repeat split; auto.
    + apply Z.leb_gt in Eid; assert (Ezero : id = 0) by lia; subst id.
      intros [u [entry [Hacquire [code [released [Hprotected [v [current [Hrelease [Herror Hafter]]]]]]]]]].
      subst code current.
      destruct (task_reg_set_protected_program_effect sg caller priority value entry error released
        Hpriority Hprotected) as [after_caller Heffect].
      exists after_caller; right; right.
      exists entry, released, (task_reg_set_pointer sg entry priority); auto.
Qed.

(** Witness a normal endpoint from the original scalar/resource domain, with
    stuttering environment intervals.  This is not an eventual-return claim. *)
Lemma task_reg_set_program_has_result : forall critical sg invocation before caller priority id value,
  0 <= priority -> 0 <= id -> UCOS2_state_inv sg before ->
  task_reg_set_self_admission critical sg invocation before priority id value caller ->
  exists error after, task_reg_set_program critical sg invocation caller priority id value before error after.
Proof.
  intros critical sg invocation before caller priority id value Hpriority Hid Hvalid Hadmission.
  destruct (Z_le_gt_dec 63 priority) as [Hbound|Hbound].
  all: destruct (Z.eq_dec priority 255) as [Hself|Hself].
  all: try solve [exists 42, before; eapply task_reg_set_result_program with (after_caller := caller);
    left; repeat split; auto].
  all: assert (Hgood : task_reg_set_priority_valid priority) by
    (unfold task_reg_set_priority_valid; lia).
  all: destruct (Z_le_gt_dec 1 id) as [Hbadid|Hgoodid].
  all: try solve [exists 8, before; eapply task_reg_set_result_program with (after_caller := caller);
    right; left; repeat split; auto].
  all: assert (Eid : id = 0) by lia; subst id.
  all: assert (Hinterval : critical_region_interval critical sg invocation before before) by constructor.
  all: destruct (Z.eq_dec (task_reg_set_pointer sg before priority) 0) as [Hnull|Hnull].
  all: try solve [exists 67, before; eapply task_reg_set_result_program with (after_caller := caller);
    right; right; exists before, before, (task_reg_set_pointer sg before priority);
    split; [exact Hinterval|]; split; [|exact Hinterval]; unfold task_reg_set_effect;
    split; [exact Hgood|]; split; [reflexivity|]; split; [reflexivity|];
    left; repeat split; auto].
  all: destruct (Z.eq_dec (task_reg_set_pointer sg before priority) 1) as [Hreserved|Hreserved].
  all: try solve [exists 67, before; eapply task_reg_set_result_program with (after_caller := caller);
    right; right; exists before, before, (task_reg_set_pointer sg before priority);
    split; [exact Hinterval|]; split; [|exact Hinterval]; unfold task_reg_set_effect;
    split; [exact Hgood|]; split; [reflexivity|]; split; [reflexivity|];
    left; repeat split; auto].
  all: destruct (task_reg_set_selection_writable critical sg invocation before before priority 0 value caller
    Hvalid Hpriority Hgood eq_refl Hadmission Hinterval Hnull Hreserved)
    as [released [after_caller [residual [Hreleased [Hcommit Hcut]]]]].
  all: exists 0, released; eapply task_reg_set_result_program with (after_caller := after_caller);
    right; right; exists before, released, (task_reg_set_pointer sg before priority);
    split; [exact Hinterval|]; split; [|constructor]; unfold task_reg_set_effect;
    split; [exact Hgood|]; split; [reflexivity|]; split; [reflexivity|];
    right; repeat split; assumption.
Qed.

Definition task_reg_set_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation s).

Definition task_reg_set_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (priority id value error_pointer : Z) (caller : Assertion) : Assertion :=
  coq_prop (task_reg_set_self_admission critical sg invocation before priority id value caller) &&
    (task_reg_set_closed platform critical sg invocation origin mask before **
     caller ** error_pointer # UChar |->_).

Definition task_reg_set_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (released : UCOS2_Verify_State) : Assertion :=
  EX after, coq_prop (critical_region_interval critical sg invocation released after) &&
    task_reg_set_closed platform critical sg invocation origin
      (armv7a_irq_fiq_mask saved) after.

Definition task_reg_set_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (priority id value error_pointer : Z) (caller : Assertion)
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  (coq_prop (63 <= priority /\ priority <> 255 /\ task_reg_set_safe_result 42 before X) &&
    (task_reg_set_closed platform critical sg invocation origin mask before **
     caller ** error_pointer # UChar |-> 42)) ||
  (coq_prop (task_reg_set_priority_valid priority /\ 1 <= id /\
      task_reg_set_safe_result 8 before X) &&
    (task_reg_set_closed platform critical sg invocation origin mask before **
     caller ** error_pointer # UChar |-> 8)) ||
  (EX entry released after after_caller pointer error,
    coq_prop (critical_region_interval critical sg invocation before entry /\
      task_reg_set_effect sg entry caller priority id value pointer error released after_caller /\
      critical_region_interval critical sg invocation released after /\
      task_reg_set_safe_result error after X) &&
    (task_reg_set_closed platform critical sg invocation origin mask after **
     after_caller ** error_pointer # UChar |-> error)).

Lemma task_reg_set_self_admission_from_live_current :
  forall critical sg invocation before priority id value caller,
  UCOS2_state_inv sg before -> task_reg_set_live_current before ->
  (forall client, critical.(critical_region_clients) client -> forall first next,
    UCOS2_state_inv sg first -> kernel_client_step client sg first next ->
    task_reg_set_live_current first -> task_reg_set_live_current next) ->
  task_reg_set_self_admission critical sg invocation before priority id value caller.
Proof.
  intros critical sg invocation before priority id value caller Hvalid Hcurrent Hclients
    Hself Hid entry Hinterval Hentry Hnonnull Hreserved.
  pose proof (task_reg_set_interval_live_current critical sg invocation before entry
    Hclients Hinterval Hvalid Hcurrent) as Hlive.
  unfold task_reg_set_current_pointer, encode_task_link in *.
  destruct entry.(SchedState).(curTaskID) as [tid|] eqn:Htid; [|contradiction].
  destruct (Hlive tid Htid) as [old Hold].
  eapply task_reg_set_live_writable; eassumption.
Qed.
