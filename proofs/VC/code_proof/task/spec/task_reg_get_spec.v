Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.array_abstraction.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition task_reg_get_global_addresses (sg : StableGlobVars)
  (current table : addr) : Prop :=
  sg.(g_OSTCBCur) = current /\ sg.(g_OSTCBPrioTbl) = table.

Definition task_reg_get_current_pointer (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : addr :=
  encode_task_link sg s.(SchedState).(curTaskID).

Definition task_reg_get_table_pointer (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (prio : Z) : addr :=
  prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) prio).

Definition task_reg_get_pointer (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (prio : Z) : addr :=
  if Z.eqb prio 255 then task_reg_get_current_pointer sg s
  else task_reg_get_table_pointer sg s prio.

Definition task_reg_get_scalar_valid (prio id : Z) : Prop :=
  0 <= prio <= 255 /\ (prio < 63 \/ prio = 255) /\ id = 0.

Definition task_reg_get_selection (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (prio pointer : Z) : Prop :=
  pointer = task_reg_get_pointer sg s prio.

(** A reversible view of an ACTUAL readable word. The complement retains
    the complete old kernel and caller owner, including the allocator.
    This is not a live-task axiom: initialized free words and a separately
    caller-owned private word can also supply such a view. *)
Definition task_reg_get_word_view (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (caller : Assertion) (pointer value : Z)
  (residual : Assertion) : Prop :=
  (UCOS2_raw_rep sg s ** caller |--
    UIntArray.full (tcb_field_address pointer TCBReg0) 1 [value] ** residual) /\
  (UIntArray.full (tcb_field_address pointer TCBReg0) 1 [value] ** residual |--
    UCOS2_raw_rep sg s ** caller).

Definition task_reg_get_current_readable (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (caller : Assertion) : Prop :=
  task_reg_get_current_pointer sg s <> 0 ->
  task_reg_get_current_pointer sg s <> 1 ->
  exists value residual,
    task_reg_get_word_view sg s caller
      (task_reg_get_current_pointer sg s) value residual.

(** Only the actual successful SELF dereference needs admission. Scalar
    errors have no acquisition requirement; acquired NULL/1 needs no word.
    The quantified interval is the registered rely, not a new Save Ensure,
    a future-return promise, or a claim about all invariant states. *)
Definition task_reg_get_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (caller : Assertion) (prio id : Z) : Prop :=
  prio = 255 -> id = 0 ->
  forall entry, critical_region_interval critical sg invocation before entry ->
    UCOS2_state_inv sg entry ->
    task_reg_get_current_readable sg entry caller.

Definition task_reg_get_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Prop :=
  UCOS2_state_inv sg before /\ interrupt_saved_value mask saved /\
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry.

(** Exact ordered mathematical observation. A protected Get closes the
    unchanged acquired heap before release; the after heap may differ by
    the registered release interval. The word view records the read, not
    ownership of the old word after Restore. *)
Definition task_reg_get_call_post (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask : Z)
  (before : UCOS2_Verify_State) (caller : Assertion)
  (prio id error value : Z) (after : UCOS2_Verify_State) : Prop :=
  if andb (Z.leb 63 prio) (negb (Z.eqb prio 255)) then
    error = 42 /\ value = 0 /\ after = before
  else if Z.leb 1 id then
    error = 8 /\ value = 0 /\ after = before
  else exists entry saved,
    task_reg_get_acquire_facts critical sg invocation mask saved before entry /\
    critical_region_interval critical sg invocation entry after /\
    let pointer := task_reg_get_pointer sg entry prio in
    if orb (Z.eqb pointer 0) (Z.eqb pointer 1) then error = 67 /\ value = 0
    else error = 0 /\ exists residual,
      task_reg_get_word_view sg entry caller pointer value residual.

(** The protected computation selects the acquired pointer, rejects NULL and
    RESERVED, then observes the actual readable word without changing its owner.
    [caller] permits the existing initialized-free/private SELF cases; it is not
    replaced by a live-task-only lookup or an unconstrained returned integer. *)
Definition task_reg_get_protected_program (sg : StableGlobVars)
  (caller : Assertion) (prio : Z) : program UCOS2_Verify_State (Z * Z) :=
  StateRelMonad.bind (get' (fun s => task_reg_get_pointer sg s prio))
    (fun pointer =>
      if orb (Z.eqb pointer 0) (Z.eqb pointer 1)
      then StateRelMonad.ret (0, 67)
      else StateRelMonad.bind
        (get (fun s value => exists residual,
          task_reg_get_word_view sg s caller pointer value residual))
        (fun value => StateRelMonad.ret (value, 0))).

(** Ordered source checks and two distinct registered environment intervals.
    The result pairs the C return value with the privately written error byte. *)
Definition task_reg_get_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (caller : Assertion) (prio id : Z)
  : program UCOS2_Verify_State (Z * Z) :=
  if andb (Z.leb 63 prio) (negb (Z.eqb prio 255))
  then StateRelMonad.ret (0, 42)
  else if Z.leb 1 id then StateRelMonad.ret (0, 8)
  else StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (task_reg_get_protected_program sg caller prio)
      (fun result => StateRelMonad.bind
        (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret result))).

Definition task_reg_get_safe critical sg invocation before caller prio id
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (task_reg_get_program critical sg invocation caller prio id)
    (fun result state => X (fst result) (snd result) state).

Definition task_reg_get_post critical sg invocation mask before caller
  prio id error value after (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  task_reg_get_call_post critical sg invocation mask before caller
    prio id error value after /\
  safeExec (fun state => state = after) (StateRelMonad.ret (value, error))
    (fun result state => X (fst result) (snd result) state).

Lemma task_reg_get_protected_program_iff : forall sg caller prio before value error after,
  task_reg_get_protected_program sg caller prio before (value, error) after <->
  after = before /\
  (let pointer := task_reg_get_pointer sg before prio in
   if orb (Z.eqb pointer 0) (Z.eqb pointer 1) then error = 67 /\ value = 0
   else error = 0 /\ exists residual,
     task_reg_get_word_view sg before caller pointer value residual).
Proof.
  intros sg caller prio before value error after; cbn zeta; split.
  - intros [pointer [selected [[Hpointer Hselected] Hprogram]]].
    subst pointer selected.
    destruct (orb (Z.eqb (task_reg_get_pointer sg before prio) 0)
      (Z.eqb (task_reg_get_pointer sg before prio) 1)) eqn:Hguard.
    + destruct Hprogram as [Hresult Hafter].
      inversion Hresult; subst; auto.
    + destruct Hprogram as [observed [read [[Hview Hread] [Hresult Hafter]]]].
      inversion Hresult; subst; auto.
  - intros [-> Hresult].
    exists (task_reg_get_pointer sg before prio), before.
    split; [split; reflexivity|].
    destruct (orb (Z.eqb (task_reg_get_pointer sg before prio) 0)
      (Z.eqb (task_reg_get_pointer sg before prio) 1)) eqn:Hguard.
    + destruct Hresult as [-> ->]; split; reflexivity.
    + destruct Hresult as [-> Hview].
      exists value, before; split; [split; [exact Hview|reflexivity]|].
      split; reflexivity.
Qed.

Lemma task_reg_get_call_post_program :
  forall critical sg invocation mask before caller prio id error value after,
  task_reg_get_call_post critical sg invocation mask before caller
    prio id error value after ->
  task_reg_get_program critical sg invocation caller prio id before (value, error) after.
Proof.
  intros critical sg invocation mask before caller prio id error value after Hpost.
  unfold task_reg_get_call_post in Hpost; unfold task_reg_get_program.
  destruct (andb (Z.leb 63 prio) (negb (Z.eqb prio 255))).
  - destruct Hpost as [-> [-> ->]]; split; reflexivity.
  - destruct (Z.leb 1 id).
    + destruct Hpost as [-> [-> ->]]; split; reflexivity.
    + destruct Hpost as [entry [saved [[Hbefore [Hsaved [Hacquire Hentry]]]
        [Hrelease Hresult]]]].
      exists tt, entry; split; [exact Hacquire|].
      exists (value, error), entry; split.
      * apply task_reg_get_protected_program_iff; split; [reflexivity|exact Hresult].
      * exists tt, after; split; [exact Hrelease|split; reflexivity].
Qed.

Lemma task_reg_get_safe_return :
  forall critical sg invocation mask before caller prio id error value after X,
  task_reg_get_call_post critical sg invocation mask before caller
    prio id error value after ->
  task_reg_get_safe critical sg invocation before caller prio id X ->
  task_reg_get_post critical sg invocation mask before caller
    prio id error value after X.
Proof.
  intros critical sg invocation mask before caller prio id error value after X Hpost Hsafe.
  split; [exact Hpost|].
  eapply (highstependret_derive
    (task_reg_get_program critical sg invocation caller prio id)
    (fun state => state = before) (value, error) (fun _ state => state = after)).
  - intros state ->; exists after; split; [|reflexivity].
    eapply task_reg_get_call_post_program; exact Hpost.
  - exact Hsafe.
Qed.

Definition task_reg_get_read_frame (pointer value : Z) (residual : Assertion)
  : Assertion :=
  UIntArray.missing_i (tcb_field_address pointer TCBReg0) 0 0 1 [value] ** residual.

Definition task_reg_get_sched_without_current (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tasks **
  sched_rows_rep sg tasks s.(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Definition task_reg_get_current_frame (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  task_reg_get_sched_without_current sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_sched sg s.

Definition task_reg_get_table_frame (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (prio : Z) : Assertion :=
  store_prio_tbl_missing_i sg s.(TskState).(prioTbl) prio **
  UCOS2_raw_rep_missing_priority_table sg s.

Lemma task_reg_get_current_split_merge : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (sg.(g_OSTCBCur) # Ptr |-> task_reg_get_current_pointer sg s **
     task_reg_get_current_frame sg s).
Proof.
  intros sg s; rewrite (UCOS2_inv_split_sched sg s).
  unfold task_reg_get_current_pointer, task_reg_get_current_frame,
    task_reg_get_sched_without_current, sched_raw_rep, sched_physical_rep.
  split; entailer!.
Qed.

Lemma task_reg_get_table_split : forall sg s prio,
  0 <= prio < 64 -> UCOS2_inv sg s |--
  coq_prop (UCOS2_state_inv sg s) &&
  ((sg.(g_OSTCBPrioTbl) + prio * sizeof(PTR)) # Ptr |->
     task_reg_get_table_pointer sg s prio **
   task_reg_get_table_frame sg s prio).
Proof.
  intros sg s prio Hprio.
  pose proof (UCOS2_inv_split_priority_cell sg s prio Hprio) as Hsplit.
  unfold task_reg_get_table_pointer, task_reg_get_table_frame.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma task_reg_get_table_merge : forall sg s prio,
  0 <= prio < 64 ->
  coq_prop (UCOS2_state_inv sg s) &&
  ((sg.(g_OSTCBPrioTbl) + prio * sizeof(PTR)) # Ptr |->
     task_reg_get_table_pointer sg s prio **
   task_reg_get_table_frame sg s prio) |-- UCOS2_inv sg s.
Proof.
  intros sg s prio Hprio.
  unfold task_reg_get_table_frame, task_reg_get_table_pointer, UCOS2_inv.
  rewrite UCOS2_raw_rep_priority_table_equiv; Intros.
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg s.(TskState).(prioTbl) prio Hprio).
  entailer!.
Qed.

(** Retain aliases; do not equate the lookup key with effective priority. *)
Lemma task_reg_get_table_task_live : forall sg s prio tid,
  UCOS2_state_inv sg s -> task_priority_in_range sg prio ->
  s.(TskState).(prioTbl) prio = PTTask tid ->
  exists t, s.(TskState).(inUsedTaskStates) tid = Some t.
Proof.
  intros sg s prio tid
    [_ [_ [_ [_ [[[_ [Htable _]] _] _]]]]] Hprio Hentry.
  specialize (Htable prio Hprio); rewrite Hentry in Htable; exact Htable.
Qed.

Definition task_reg_get_reg0_residual (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (tid : TaskID) (t : TaskAbstractState)
  : Assertion :=
  task_public_storage_without_field sg tasks tid t (TCBCommonField TCBReg0).

Lemma task_reg_get_reg0_split : forall sg tasks tid t,
  tasks.(inUsedTaskStates) tid = Some t ->
  task_public_storage sg tasks |--
    UIntArray.full (tcb_field_address (task_slot_addr sg tid) TCBReg0) 1
      [t.(tcbReg0)] ** task_reg_get_reg0_residual sg tasks tid t.
Proof.
  intros sg tasks tid t Htask.
  exact (task_public_storage_split_field sg tasks tid t (TCBCommonField TCBReg0)
    Htask (tcb_configured_common_field_in _ _ TCBReg0)).
Qed.

Lemma task_reg_get_reg0_merge : forall sg tasks tid t,
  tasks.(inUsedTaskStates) tid = Some t ->
  UIntArray.full (tcb_field_address (task_slot_addr sg tid) TCBReg0) 1
    [t.(tcbReg0)] ** task_reg_get_reg0_residual sg tasks tid t |--
  task_public_storage sg tasks.
Proof.
  intros sg tasks tid t Htask.
  exact (task_public_storage_merge_field sg tasks tid t (TCBCommonField TCBReg0)
    Htask (tcb_configured_common_field_in _ _ TCBReg0)).
Qed.

Lemma task_reg_get_word_split : forall address value,
  UIntArray.full address 1 [value] |--
    address # UInt |-> value ** UIntArray.missing_i address 0 0 1 [value].
Proof.
  intros address value.
  pose proof (UIntArray.full_split_to_missing_i address 0 1 [value] 0
    ltac:(lia)) as Hsplit.
  change (UIntArray.full address 1 [value] |--
    (address + 0) # UInt |-> Znth 0 [value] 0 **
      UIntArray.missing_i address 0 0 1 [value]) in Hsplit.
  rewrite Z.add_0_r, Znth0_cons in Hsplit; exact Hsplit.
Qed.

Lemma task_reg_get_word_merge : forall address value,
  address # UInt |-> value ** UIntArray.missing_i address 0 0 1 [value] |--
    UIntArray.full address 1 [value].
Proof.
  intros address value.
  pose proof (UIntArray.missing_i_merge_to_full address 0 1 value [value]
    ltac:(lia)) as Hmerge.
  change ((address + 0) # UInt |-> value **
    UIntArray.missing_i address 0 0 1 [value] |--
    UIntArray.full address 1 (replace_Znth 0 value [value])) in Hmerge.
  rewrite Z.add_0_r in Hmerge.
  replace (replace_Znth 0 value [value]) with [value] in Hmerge by reflexivity.
  exact Hmerge.
Qed.

Definition task_reg_get_live_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (caller : Assertion) tid t : Assertion :=
  task_reg_get_reg0_residual sg s.(TskState) tid t **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s ** caller.

Lemma task_reg_get_live_word_view : forall sg s caller tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  task_reg_get_word_view sg s caller (task_slot_addr sg tid) t.(tcbReg0)
    (task_reg_get_live_residual sg s caller tid t).
Proof.
  intros sg s caller tid t Htask.
  unfold task_reg_get_word_view, task_reg_get_live_residual.
  split.
  - unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
    sep_apply_l_atomic (task_reg_get_reg0_split sg s.(TskState) tid t Htask); entailer!.
  - unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
    sep_apply_l_atomic (task_reg_get_reg0_merge sg s.(TskState) tid t Htask); entailer!.
Qed.

(** This constructor also covers invocation-private storage when the
    actual caller owns that word. It does not steal a private allocation
    from the public kernel representation. *)
Lemma task_reg_get_caller_word_view : forall sg s pointer value extra,
  task_reg_get_word_view sg s
    (UIntArray.full (tcb_field_address pointer TCBReg0) 1 [value] ** extra)
    pointer value (UCOS2_raw_rep sg s ** extra).
Proof. intros; split; entailer!. Qed.

Lemma task_reg_get_free_storage_app : forall sg storage prefix suffix,
  task_free_storage_rep sg storage (prefix ++ suffix) --||--
    task_free_storage_rep sg storage prefix ** task_free_storage_rep sg storage suffix.
Proof.
  intros sg storage prefix; induction prefix as [|tid rest IH]; intros suffix;
    cbn [app task_free_storage_rep]; [split; entailer!|].
  rewrite IH; split; Intros image; Exists image; entailer!.
Qed.

Lemma task_reg_get_free_storage_focus : forall sg storage prefix tid suffix image,
  storage tid = Some image ->
  task_free_storage_rep sg storage (prefix ++ tid :: suffix) --||--
    task_slot_storage_rep sg tid image **
    task_free_storage_rep sg storage prefix ** task_free_storage_rep sg storage suffix.
Proof.
  intros sg storage prefix tid suffix image Himage.
  rewrite task_reg_get_free_storage_app; cbn [task_free_storage_rep].
  split.
  - Intros actual; assert (actual = image) by congruence; subst actual; entailer!.
  - Exists image; entailer!.
Qed.

Definition task_reg_get_free_word_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (caller : Assertion)
  (prefix suffix : list TaskID) (tid : TaskID) (image : TCBLayoutImage) : Assertion :=
  tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg tid) image
    (TCBCommonField TCBReg0) **
  task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage) prefix **
  task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage) suffix **
  store_used_task_map sg s.(TskState).(inUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error s.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg s.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> s.(TskState).(taskCount) **
  store_prio_tbl sg s.(TskState).(prioTbl) ** task_reg_allocator_rep sg s.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s ** caller.

(** A free slot is not a live task, but Some value in its native public
    image is a real readable word. None is deliberately not promoted to
    an initialized value; the complete free-list/pool owner is restored. *)
Lemma task_reg_get_free_word_view : forall sg s caller prefix tid suffix image value,
  s.(TskState).(unUsedTaskStates) = prefix ++ tid :: suffix ->
  s.(TskState).(taskLifecycle).(taskFreeStorage) tid = Some image ->
  image (TCBCommonField TCBReg0) = Some value ->
  task_reg_get_word_view sg s caller (task_slot_addr sg tid) value
    (task_reg_get_free_word_residual sg s caller prefix suffix tid image).
Proof.
  intros sg s caller prefix tid suffix image value Hids Himage Hreg.
  pose proof (tcb_configured_storage_split_field
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image (TCBCommonField TCBReg0)
    (tcb_configured_common_field_in _ _ TCBReg0)) as Hsplit.
  pose proof (tcb_configured_storage_merge_field
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image (TCBCommonField TCBReg0)
    (tcb_configured_common_field_in _ _ TCBReg0)) as Hmerge.
  rewrite Hreg in Hsplit, Hmerge; cbn [tcb_layout_cell tcb_cell] in Hsplit, Hmerge.
  unfold task_reg_get_word_view, task_reg_get_free_word_residual.
  split.
  - unfold UCOS2_raw_rep, task_shared_rep, task_public_storage,
      UCOS2_raw_rep_missing_task_storage_sched.
    rewrite Hids, (task_reg_get_free_storage_focus sg
      s.(TskState).(taskLifecycle).(taskFreeStorage) prefix tid suffix image Himage).
    unfold task_slot_storage_rep; sep_apply_l_atomic Hsplit; entailer!.
  - unfold UCOS2_raw_rep, task_shared_rep, task_public_storage,
      UCOS2_raw_rep_missing_task_storage_sched.
    rewrite Hids, (task_reg_get_free_storage_focus sg
      s.(TskState).(taskLifecycle).(taskFreeStorage) prefix tid suffix image Himage).
    unfold task_slot_storage_rep; sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma task_reg_get_free_current_readable : forall sg s caller prefix tid suffix image value,
  s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(unUsedTaskStates) = prefix ++ tid :: suffix ->
  s.(TskState).(taskLifecycle).(taskFreeStorage) tid = Some image ->
  image (TCBCommonField TCBReg0) = Some value ->
  task_reg_get_current_readable sg s caller.
Proof.
  intros sg s caller prefix tid suffix image value Hcurrent Hids Himage Hreg _ _.
  unfold task_reg_get_current_pointer; rewrite Hcurrent; cbn [encode_task_link].
  exists value, (task_reg_get_free_word_residual sg s caller prefix suffix tid image).
  apply task_reg_get_free_word_view; assumption.
Qed.

Lemma task_reg_get_nonself_word_view : forall sg s caller prio,
  UCOS2_state_inv sg s -> 0 <= prio < 63 ->
  task_reg_get_table_pointer sg s prio <> 0 ->
  task_reg_get_table_pointer sg s prio <> 1 ->
  exists value residual,
    task_reg_get_word_view sg s caller
      (task_reg_get_table_pointer sg s prio) value residual.
Proof.
  intros sg s caller prio Hvalid Hprio Hnull Hreserved.
  assert (Hp : task_priority_in_range sg prio).
  { pose proof (proj1 (proj1 Hvalid)) as Hsg.
    unfold task_priority_in_range, valid_stable_glob_vars in *; intuition lia. }
  unfold task_reg_get_table_pointer in *.
  destruct (s.(TskState).(prioTbl) prio) as [| |tid] eqn:Hentry;
    [contradiction|contradiction|].
  destruct (task_reg_get_table_task_live sg s prio tid Hvalid Hp Hentry) as [t Htask].
  exists t.(tcbReg0), (task_reg_get_live_residual sg s caller tid t).
  apply task_reg_get_live_word_view; exact Htask.
Qed.

Lemma task_reg_get_success_word_view : forall critical sg invocation mask saved
  before entry caller prio id pointer,
  task_reg_get_acquire_facts critical sg invocation mask saved before entry ->
  task_reg_get_admission critical sg invocation before caller prio id ->
  0 <= prio -> (prio < 63 \/ prio = 255) -> id = 0 ->
  pointer = task_reg_get_pointer sg entry prio -> pointer <> 0 -> pointer <> 1 ->
  exists value residual, task_reg_get_word_view sg entry caller pointer value residual.
Proof.
  intros critical sg invocation mask saved before entry caller prio id pointer
    [_ [_ [Hinterval Hvalid]]] Hadmit Hnonnegative Hprio Hid -> Hnull Hreserved.
  unfold task_reg_get_pointer in *.
  destruct (Z.eqb prio 255) eqn:Hself.
  - apply Z.eqb_eq in Hself.
    apply (Hadmit Hself Hid entry Hinterval Hvalid); assumption.
  - apply Z.eqb_neq in Hself.
    apply task_reg_get_nonself_word_view; try assumption; destruct Hprio; lia.
Qed.

Lemma task_reg_get_read_open : forall sg s caller pointer value residual,
  task_reg_get_word_view sg s caller pointer value residual ->
  UCOS2_inv sg s ** caller |--
  coq_prop (UCOS2_state_inv sg s) &&
    ((tcb_field_address pointer TCBReg0) # UInt |-> value **
     task_reg_get_read_frame pointer value residual).
Proof.
  intros sg s caller pointer value residual [Hsplit Hmerge].
  unfold UCOS2_inv, task_reg_get_read_frame; Intros.
  sep_apply_l_atomic Hsplit.
  sep_apply_l_atomic (task_reg_get_word_split (tcb_field_address pointer TCBReg0) value).
  entailer!.
Qed.

Lemma task_reg_get_read_close : forall sg s caller pointer value residual,
  UCOS2_state_inv sg s ->
  task_reg_get_word_view sg s caller pointer value residual ->
  (tcb_field_address pointer TCBReg0) # UInt |-> value **
    task_reg_get_read_frame pointer value residual |-- UCOS2_inv sg s ** caller.
Proof.
  intros sg s caller pointer value residual Hvalid [Hsplit Hmerge].
  unfold task_reg_get_read_frame.
  sep_apply_l_atomic (task_reg_get_word_merge (tcb_field_address pointer TCBReg0) value).
  sep_apply_l_atomic Hmerge; unfold UCOS2_inv; entailer!.
Qed.

(** Source-stage producer, separate from generic CPU ownership. NULL is
    accepted; a non-NULL live task supplies its native readable word. *)
Definition task_reg_get_live_current (s : UCOS2_Verify_State) : Prop :=
  forall tid, s.(SchedState).(curTaskID) = Some tid ->
    exists t, s.(TskState).(inUsedTaskStates) tid = Some t.

Lemma task_reg_get_live_current_readable : forall sg s caller,
  task_reg_get_live_current s -> task_reg_get_current_readable sg s caller.
Proof.
  intros sg s caller Hcurrent Hnull Hreserved.
  unfold task_reg_get_current_pointer in *.
  destruct s.(SchedState).(curTaskID) as [tid|] eqn:Htid; [|contradiction].
  destruct (Hcurrent tid Htid) as [t Htask].
  exists t.(tcbReg0), (task_reg_get_live_residual sg s caller tid t).
  apply task_reg_get_live_word_view; exact Htask.
Qed.

Lemma task_reg_get_boot_current_source :
  forall sg task_name flag_name memory_name names,
  task_reg_get_live_current (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof. intros sg task_name flag_name memory_name names tid Htid; discriminate. Qed.

Lemma task_reg_get_installed_current_source : forall s,
  sched_high_ready_consistency s.(TskState) s.(SchedState) ->
  task_reg_get_live_current (replace_SchedS (sched_install_selected s.(SchedState)) s).
Proof.
  intros s Hhigh.
  pose proof (sched_install_selected_synchronizes_current
    s.(TskState) s.(SchedState) Hhigh) as Hcurrent.
  intros tid Htid; unfold sched_current_consistency in Hcurrent.
  change (curTaskID (sched_install_selected (SchedState s)) = Some tid) in Htid.
  rewrite Htid in Hcurrent; destruct Hcurrent as [t [Ht _]]; eauto.
Qed.

Lemma task_reg_get_creation_client_preserves_live_current : forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  task_reg_get_live_current before -> task_reg_get_live_current after.
Proof.
  intros action sg before after [_ [_ ->]] Hcurrent.
  destruct action; cbn [task_lifecycle_action_state].
  - exact Hcurrent.
  - exact Hcurrent.
  - intros tid Htid.
    change (before.(SchedState).(curTaskID) = Some tid) in Htid.
    change (exists t, (task_commit before.(TskState) priority invocation node).(inUsedTaskStates)
      tid = Some t).
    apply task_commit_live_iff; right; exact (Hcurrent tid Htid).
  - exact Hcurrent.
Qed.

(** A proved rely induction. Clients may change current: they need only
    preserve this source stage, not frame the current pointer universally. *)
Lemma task_reg_get_admission_from_source : forall critical sg invocation before caller prio id,
  UCOS2_state_inv sg before -> task_reg_get_live_current before ->
  (forall action, critical_region_clients critical action ->
    forall a b, UCOS2_state_inv sg a -> kernel_client_step action sg a b ->
      task_reg_get_live_current a -> task_reg_get_live_current b) ->
  task_reg_get_admission critical sg invocation before caller prio id.
Proof.
  intros critical sg invocation before caller prio id Hvalid Hinitial Hclients
    Hprio Hid entry Hinterval HvalidEntry.
  apply task_reg_get_live_current_readable.
  pose proof (critical_region_interval_raw_trace critical sg invocation before entry Hinterval)
    as Htrace.
  clear Hinterval HvalidEntry Hprio Hid.
  revert Hvalid Hinitial.
  induction Htrace as [s|action first middle last stopped Hin Hforeign Hevent Hstep Htail IH].
  all: intros Hvalid Hinitial.
  - exact Hinitial.
  - apply IH.
    + exact (kernel_client_preserves_validity action
        (critical_region_client_certificates critical action Hin)
        sg first middle Hvalid Hstep).
    + eapply Hclients; eassumption.
Qed.

Lemma task_reg_get_admission_creation_clients :
  forall critical sg invocation before caller prio id,
  UCOS2_state_inv sg before -> task_reg_get_live_current before ->
  (forall client, critical_region_clients critical client -> task_creation_client_family client) ->
  task_reg_get_admission critical sg invocation before caller prio id.
Proof.
  intros critical sg invocation before caller prio id Hvalid Hsource Hclients.
  apply task_reg_get_admission_from_source; try assumption.
  intros client Hin a b Ha Hstep Hcurrent.
  destruct (Hclients client Hin) as [action ->].
  eapply task_reg_get_creation_client_preserves_live_current; eassumption.
Qed.

Lemma task_reg_get_admission_early : forall critical sg invocation before caller prio id,
  (prio <> 255 \/ id <> 0) ->
  task_reg_get_admission critical sg invocation before caller prio id.
Proof. intros critical sg invocation before caller prio id H Hprio Hid; tauto. Qed.

Require Import Coq.Bool.Bool.
Lemma task_reg_get_priority_guard_false__read_and_observation : forall prio,
  (prio < 63 \/ prio = 255) ->
  andb (Z.leb 63 prio) (negb (Z.eqb prio 255)) = false.
Proof.
  intros prio [Hprio | ->]; apply andb_false_iff.
  - left; apply Z.leb_gt; lia.
  - right; reflexivity.
Qed.
Lemma task_reg_get_call_post_read__read_and_observation :
  forall critical sg invocation mask saved before entry after caller prio id pointer value residual,
  (prio < 63 \/ prio = 255) -> id = 0 ->
  task_reg_get_acquire_facts critical sg invocation mask saved before entry ->
  critical_region_interval critical sg invocation entry after ->
  task_reg_get_selection sg entry prio pointer -> pointer <> 0 -> pointer <> 1 ->
  task_reg_get_word_view sg entry caller pointer value residual ->
  task_reg_get_call_post critical sg invocation mask before caller prio id 0 value after.
Proof.
  intros critical sg invocation mask saved before entry after caller prio id pointer value residual
    Hprio -> Hacquire Hrelease Hselection Hnull Hreserved Hview.
  unfold task_reg_get_call_post.
  rewrite (task_reg_get_priority_guard_false__read_and_observation prio Hprio).
  cbn [Z.leb]; exists entry, saved; split; [exact Hacquire|].
  split; [exact Hrelease|].
  unfold task_reg_get_selection in Hselection; rewrite <- Hselection.
  assert (orb (Z.eqb pointer 0) (Z.eqb pointer 1) = false) as Hguard.
  { apply orb_false_iff; split; apply Z.eqb_neq; assumption. }
  rewrite Hguard; split; [reflexivity|]; exists residual; exact Hview.
Qed.
Lemma task_reg_get_call_post_missing__read_and_observation :
  forall critical sg invocation mask saved before entry after caller prio id pointer,
  (prio < 63 \/ prio = 255) -> id = 0 ->
  task_reg_get_acquire_facts critical sg invocation mask saved before entry ->
  critical_region_interval critical sg invocation entry after ->
  task_reg_get_selection sg entry prio pointer -> (pointer = 0 \/ pointer = 1) ->
  task_reg_get_call_post critical sg invocation mask before caller prio id 67 0 after.
Proof.
  intros critical sg invocation mask saved before entry after caller prio id pointer
    Hprio -> Hacquire Hrelease Hselection Hbad.
  unfold task_reg_get_call_post.
  rewrite (task_reg_get_priority_guard_false__read_and_observation prio Hprio).
  cbn [Z.leb]; exists entry, saved; split; [exact Hacquire|].
  split; [exact Hrelease|].
  unfold task_reg_get_selection in Hselection; rewrite <- Hselection.
  assert (orb (Z.eqb pointer 0) (Z.eqb pointer 1) = true) as Hguard.
  { apply orb_true_iff; destruct Hbad as [-> | ->]; [left|right]; reflexivity. }
  rewrite Hguard; auto.
Qed.
Lemma task_reg_get_call_post_invalid_id__read_and_observation :
  forall critical sg invocation mask before caller prio id,
  (prio < 63 \/ prio = 255) -> 1 <= id ->
  task_reg_get_call_post critical sg invocation mask before caller prio id 8 0 before.
Proof.
  intros critical sg invocation mask before caller prio id Hprio Hid.
  unfold task_reg_get_call_post.
  rewrite (task_reg_get_priority_guard_false__read_and_observation prio Hprio).
  assert (Z.leb 1 id = true) as Hguard by (apply Z.leb_le; exact Hid).
  rewrite Hguard; auto.
Qed.
Lemma task_reg_get_call_post_invalid_priority__read_and_observation :
  forall critical sg invocation mask before caller prio id,
  63 <= prio -> prio <> 255 ->
  task_reg_get_call_post critical sg invocation mask before caller prio id 42 0 before.
Proof.
  intros critical sg invocation mask before caller prio id Hprio Hself.
  unfold task_reg_get_call_post.
  assert (Z.leb 63 prio = true) as Hguard by (apply Z.leb_le; exact Hprio).
  assert (Z.eqb prio 255 = false) as Hother by (apply Z.eqb_neq; exact Hself).
  rewrite Hguard, Hother; simpl; auto.
Qed.

(** The saved CPU word is a separate platform certificate, not an abstract
    program guard or a new public Require. The C acquire facts provide it. *)
Lemma task_reg_get_program_call_post :
  forall critical sg invocation mask saved before caller prio id error value after,
  UCOS2_state_inv sg before -> interrupt_saved_value mask saved ->
  task_reg_get_program critical sg invocation caller prio id before (value, error) after ->
  task_reg_get_call_post critical sg invocation mask before caller
    prio id error value after.
Proof.
  intros critical sg invocation mask saved before caller prio id error value after
    Hbefore Hsaved Hprogram.
  unfold task_reg_get_program in Hprogram; unfold task_reg_get_call_post.
  destruct (andb (Z.leb 63 prio) (negb (Z.eqb prio 255))).
  - destruct Hprogram as [Hresult Hafter]; inversion Hresult; subst; auto.
  - destruct (Z.leb 1 id).
    + destruct Hprogram as [Hresult Hafter]; inversion Hresult; subst; auto.
    + destruct Hprogram as [u [entry [Hacquire [result [released [Hprotected
        [v [returned [Hrelease [Hresult Hafter]]]]]]]]]].
      subst result returned.
      apply task_reg_get_protected_program_iff in Hprotected.
      destruct Hprotected as [-> Hobserved].
      exists entry, saved; split.
      * unfold task_reg_get_acquire_facts.
        split; [exact Hbefore|]. split; [exact Hsaved|].
        split; [exact Hacquire|].
        exact (proj1 (critical_region_interval_transports_resources
          critical sg invocation before entry Hacquire Hbefore)).
      * split; assumption.
Qed.

Lemma task_reg_get_program_call_post_iff :
  forall critical sg invocation mask saved before caller prio id error value after,
  UCOS2_state_inv sg before -> interrupt_saved_value mask saved ->
  (task_reg_get_program critical sg invocation caller prio id before (value, error) after <->
   task_reg_get_call_post critical sg invocation mask before caller
     prio id error value after).
Proof.
  intros; split.
  - eapply task_reg_get_program_call_post; eassumption.
  - apply task_reg_get_call_post_program.
Qed.

(** There is a normal endpoint for every original admissible scalar input,
    choosing empty environment intervals. This is not an environment-liveness
    claim and imposes no allocated-ID or extra live-current requirement. *)
Lemma task_reg_get_program_has_result :
  forall critical sg invocation before caller prio id,
  UCOS2_state_inv sg before -> 0 <= prio <= 255 -> 0 <= id ->
  task_reg_get_admission critical sg invocation before caller prio id ->
  exists result after,
    task_reg_get_program critical sg invocation caller prio id before result after.
Proof.
  intros critical sg invocation before caller prio id Hbefore Hprio Hid Hadmit.
  unfold task_reg_get_program.
  destruct (andb (Z.leb 63 prio) (negb (Z.eqb prio 255))) eqn:Eprio.
  - exists (0, 42), before; split; reflexivity.
  - destruct (Z.leb 1 id) eqn:Eid.
    + exists (0, 8), before; split; reflexivity.
    + assert (Hdomain : prio < 63 \/ prio = 255).
      { apply Bool.andb_false_iff in Eprio.
        destruct Eprio as [Hlower|Hself].
        - apply Z.leb_gt in Hlower; auto.
        - apply Bool.negb_false_iff in Hself; apply Z.eqb_eq in Hself; auto. }
      assert (Hzero : id = 0) by (apply Z.leb_gt in Eid; lia).
      assert (Hacquire : task_reg_get_acquire_facts critical sg invocation 0 0 before before).
      { unfold task_reg_get_acquire_facts; split; [exact Hbefore|].
        split; [split; [unfold valid_os_cpu_sr; lia|reflexivity]|].
        split; [constructor|exact Hbefore]. }
      destruct (orb (Z.eqb (task_reg_get_pointer sg before prio) 0)
        (Z.eqb (task_reg_get_pointer sg before prio) 1)) eqn:Epointer.
      * exists (0, 67), before.
        exists tt, before; split; [constructor|].
        exists (0, 67), before; split.
        -- apply task_reg_get_protected_program_iff; split; [reflexivity|].
           cbn zeta; rewrite Epointer; auto.
        -- exists tt, before; split; [constructor|split; reflexivity].
      * apply Bool.orb_false_iff in Epointer; destruct Epointer as [Hnull Hreserved].
        apply Z.eqb_neq in Hnull; apply Z.eqb_neq in Hreserved.
        destruct (task_reg_get_success_word_view critical sg invocation 0 0 before before
          caller prio id (task_reg_get_pointer sg before prio) Hacquire Hadmit
          (proj1 Hprio) Hdomain Hzero eq_refl Hnull Hreserved) as [value [residual Hview]].
        exists (value, 0), before.
        exists tt, before; split; [constructor|].
        exists (value, 0), before; split.
        -- apply task_reg_get_protected_program_iff; split; [reflexivity|].
           assert (E : orb (Z.eqb (task_reg_get_pointer sg before prio) 0)
             (Z.eqb (task_reg_get_pointer sg before prio) 1) = false).
           { apply Bool.orb_false_iff; split; apply Z.eqb_neq; assumption. }
           cbn zeta; rewrite E; split; [reflexivity|exists residual; exact Hview].
        -- exists tt, before; split; [constructor|split; reflexivity].
Qed.
