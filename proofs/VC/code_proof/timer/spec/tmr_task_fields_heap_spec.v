Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion CNotation SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_resource_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_repaired_scan_spec.
Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_del_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_link_spec Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(** Only the six fields actually read by OSTmr_Task are selected. The
    selected C/ABI input must prove these alias-arrow equations. The old
    Task profile alone does not contain the Option/Callback/Arg equations. *)
Definition tmr_task_image_kind (field : TmrTaskImageField) : TmrTaskCellKind :=
  match field with
  | TaskMatchField => TaskUIntCell
  | TaskOptionField | TaskStateField => TaskByteCell
  | _ => TaskPointerCell
  end.
Definition tmr_task_image_name (field : TmrTaskImageField) : string :=
  match field with
  | TaskNextField => "OSTmrNext" | TaskMatchField => "OSTmrMatch"
  | TaskOptionField => "OSTmrOpt" | TaskCallbackField => "OSTmrCallback"
  | TaskArgumentField => "OSTmrCallbackArg" | TaskStateField => "OSTmrState"
  end.
Definition tmr_task_image_offset (c : KernelConfiguration) (field : TmrTaskImageField) : Z :=
  match field with
  | TaskNextField => 12 | TaskMatchField => 20
  | TaskOptionField => timer_option_offset c | TaskCallbackField => 4
  | TaskArgumentField => 8 | TaskStateField => timer_option_offset c + 1
  end.
Definition tmr_task_fields_layout (sg : StableGlobVars) : Prop :=
  forall pointer field,
    tmr_unlink_timer_field pointer (tmr_task_image_name field) =
      pointer + tmr_task_image_offset sg.(osKernelConfig) field.

Module TmrTaskFieldsHeap.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

Definition cell (kind : TmrTaskCellKind) (pointer value : Z) : Assertion :=
  match kind with
  | TaskByteCell => pointer # UChar |-> value
  | TaskUIntCell => pointer # UInt |-> value
  | TaskPointerCell => pointer # Ptr |-> value
  end.

Definition object_without_field (c : KernelConfiguration) pointer image field : Assertion :=
  pointer # UChar |-> image.(timerImageType) **
  store_optional_bytes (pointer + 1) (firstn 3 image.(timerImagePadding)) **
  (match field with TaskCallbackField => emp | _ =>
    (pointer + 4) # Ptr |-> image.(timerImageCallback) end) **
  (match field with TaskArgumentField => emp | _ =>
    (pointer + 8) # Ptr |-> image.(timerImageArg) end) **
  (match field with TaskNextField => emp | _ =>
    (pointer + 12) # Ptr |-> image.(timerImageNext) end) **
  (pointer + 16) # Ptr |-> image.(timerImagePrev) **
  (match field with TaskMatchField => emp | _ =>
    (pointer + 20) # UInt |-> image.(timerImageMatch) end) **
  (pointer + 24) # UInt |-> image.(timerImageDelay) **
  (pointer + 28) # UInt |-> image.(timerImagePeriod) **
  (if c.(cfgTimerNames) then (pointer + 32) # Ptr |-> image.(timerImageName) else emp) **
  (match field with TaskOptionField => emp | _ =>
    (pointer + timer_option_offset c) # UChar |-> image.(timerImageOption) end) **
  (match field with TaskStateField => emp | _ =>
    (pointer + timer_option_offset c + 1) # UChar |-> image.(timerImageState) end) **
  store_optional_bytes (pointer + timer_option_offset c + 2) (skipn 3 image.(timerImagePadding)).

Lemma object_split_merge_field : forall sg pointer image field,
  tmr_task_fields_layout sg ->
  timer_object_rep sg.(osKernelConfig) pointer image --||--
    cell (tmr_task_image_kind field)
      (tmr_unlink_timer_field pointer (tmr_task_image_name field))
      (tmr_task_image_value field image) **
    object_without_field sg.(osKernelConfig) pointer image field.
Proof.
  intros sg pointer image field Hlayout; rewrite Hlayout.
  destruct field; unfold timer_object_rep, object_without_field, cell,
    tmr_task_image_kind, tmr_task_image_offset, tmr_task_image_value;
    try replace (pointer + (timer_option_offset sg.(osKernelConfig) + 1))
      with (pointer + timer_option_offset sg.(osKernelConfig) + 1) by lia;
    split; entailer!.
Qed.

Definition timer_without_field sg timers index image field : Assertion :=
  object_without_field sg.(osKernelConfig) (timer_pool_addr sg index) image field **
  timer_images_without sg timers index **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) **
  timer_globals_rep sg timers.

Lemma timer_split_field : forall sg timers index image field,
  tmr_task_fields_layout sg -> timers.(timerImages) index = Some image ->
  timer_raw_rep sg timers |--
    cell (tmr_task_image_kind field)
      (tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field))
      (tmr_task_image_value field image) ** timer_without_field sg timers index image field.
Proof.
  intros sg timers index image field Hlayout Himage.
  unfold timer_raw_rep, timer_without_field.
  sep_apply_l_atomic (timer_images_split_object sg timers index image Himage).
  rewrite (object_split_merge_field sg (timer_pool_addr sg index) image field Hlayout).
  entailer!.
Qed.

Lemma timer_merge_field : forall sg timers index image field,
  tmr_task_fields_layout sg -> timers.(timerImages) index = Some image ->
  cell (tmr_task_image_kind field)
    (tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field))
    (tmr_task_image_value field image) ** timer_without_field sg timers index image field |--
  timer_raw_rep sg timers.
Proof.
  intros sg timers index image field Hlayout Himage.
  unfold timer_raw_rep, timer_without_field.
  assert (Hobjects : timer_images_rep sg timers --||--
    timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg index) image **
    timer_images_without sg timers index).
  { split; [apply timer_images_split_object|apply timer_images_merge_object]; exact Himage. }
  rewrite Hobjects.
  rewrite (object_split_merge_field sg (timer_pool_addr sg index) image field Hlayout).
  entailer!.
Qed.

Definition globals_without_time sg timers : Assertion :=
  sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg timers.(timerFree) **
  sg.(g_OSTmrFree) # UShort |-> timers.(timerFreeCount) **
  sg.(g_OSTmrUsed) # UShort |-> timers.(timerUsedCount) **
  sg.(g_OSTmrSem) # Ptr |-> timers.(timerSem) **
  sg.(g_OSTmrSemSignal) # Ptr |-> timers.(timerSignalSem).
Definition timer_without_time sg timers : Assertion :=
  timer_images_rep sg timers **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) **
  globals_without_time sg timers.

Lemma timer_split_merge_time : forall sg timers,
  timer_raw_rep sg timers --||--
    cell TaskUIntCell sg.(g_OSTmrTime) timers.(timerTime) ** timer_without_time sg timers.
Proof.
  intros; unfold timer_raw_rep, timer_globals_rep, timer_without_time,
    globals_without_time, cell; split; entailer!.
Qed.

Lemma timer_merge_incremented_time : forall sg timers,
  cell TaskUIntCell sg.(g_OSTmrTime) (timerTime (timer_service_advance timers)) **
    timer_without_time sg timers |-- timer_raw_rep sg (timer_service_advance timers).
Proof.
  intros; unfold timer_raw_rep, timer_globals_rep, timer_without_time,
    globals_without_time, timer_images_rep, timer_service_advance, cell; cbn; entailer!.
Qed.

Definition timer_without_time_field sg timers index image field : Assertion :=
  object_without_field sg.(osKernelConfig) (timer_pool_addr sg index) image field **
  timer_images_without sg timers index **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) **
  globals_without_time sg timers.

Lemma timer_split_merge_time_field : forall sg timers index image field,
  tmr_task_fields_layout sg -> timers.(timerImages) index = Some image ->
  timer_raw_rep sg timers --||--
    (cell TaskUIntCell sg.(g_OSTmrTime) timers.(timerTime) **
     cell (tmr_task_image_kind field)
       (tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field))
       (tmr_task_image_value field image)) **
    timer_without_time_field sg timers index image field.
Proof.
  intros sg timers index image field Hlayout Himage; split.
  - sep_apply_l_atomic (timer_split_field sg timers index image field Hlayout Himage).
    unfold timer_without_field, timer_without_time_field, timer_globals_rep,
      globals_without_time, cell; entailer!.
  - sep_apply_r_atomic (timer_merge_field sg timers index image field Hlayout Himage).
    unfold timer_without_field, timer_without_time_field, timer_globals_rep,
      globals_without_time, cell; entailer!.
Qed.

Lemma wheel_update_original_row : forall wheel spoke row,
  nth_error wheel spoke = Some row -> timer_wheel_update wheel spoke row = wheel.
Proof.
  intros wheel; induction wheel as [|head rest IH]; intros [|spoke] row Hrow;
    cbn in Hrow; try discriminate; cbn [timer_wheel_update].
  - injection Hrow as Hrow; subst; reflexivity.
  - rewrite (IH spoke row Hrow); reflexivity.
Qed.

Definition timer_without_head sg timers spoke (row : list TimerID) : Assertion :=
  (sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke + 4) # UShort |-> Z.of_nat (List.length row) **
  tmr_link_wheel_without_spoke sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) spoke **
  timer_images_rep sg timers ** timer_globals_rep sg timers.

Lemma timer_split_merge_head : forall sg timers spoke row,
  nth_error timers.(timerWheel) spoke = Some row ->
  timer_raw_rep sg timers --||--
    cell TaskPointerCell (sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke)
      (timer_id_pointer sg row) ** timer_without_head sg timers spoke row.
Proof.
  intros sg timers spoke row Hrow; unfold timer_raw_rep, timer_without_head, cell; split.
  - sep_apply_l_atomic (tmr_link_wheel_split_spoke sg timers.(timerWheel) spoke row
      sg.(g_OSTmrWheelTbl) Hrow); entailer!.
  - pose proof (tmr_link_wheel_merge_updated_spoke sg timers.(timerWheel) spoke row row
      sg.(g_OSTmrWheelTbl) Hrow) as Hmerge.
    rewrite (wheel_update_original_row _ _ _ Hrow) in Hmerge.
    rewrite <- Hmerge; entailer!.
Qed.

(** This rest stores the old pure invariant, the actual unmodified Timer
    bytes, and the actual continuation family/map. It owns no second copy
    of Timer. Only a concrete Timer mutation may rebuild the changed owner. *)
Definition context_rest environment local sg call mask state (rest : Assertion) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    (rest ** TmrTaskFields.tmr_task_fields_timer_frame environment local sg call mask state).

Lemma context_split_part : forall environment local sg call mask state cells rest,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState) ->
  (timer_raw_rep sg state.(TimerState) |-- cells ** rest) ->
  TmrTaskFields.tmr_task_fields_context environment local sg call mask state |--
    cells ** context_rest environment local sg call mask state rest.
Proof.
  intros environment local sg call mask state cells rest Hen Hinit Hsplit.
  rewrite TmrTaskFields.tmr_task_fields_context_split_timer.
  rewrite (timer_initialized_configured_rep_eq sg state.(TimerState) Hen Hinit).
  unfold context_rest; Intros; sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma context_merge_part : forall environment local sg call mask state timers cells rest,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized timers ->
  (UCOS2_state_inv sg state -> UCOS2_state_inv sg (replace_TimerS timers state)) ->
  (cells ** rest |-- timer_raw_rep sg timers) ->
  cells ** context_rest environment local sg call mask state rest |--
    TmrTaskFields.tmr_task_fields_context environment local sg call mask (replace_TimerS timers state).
Proof.
  intros environment local sg call mask state timers cells rest Hen Hinit Hvalid Hmerge.
  unfold context_rest; Intros.
  assert (Hpost : UCOS2_state_inv sg (replace_TimerS timers state)) by (apply Hvalid; assumption).
  sep_apply_l_atomic Hmerge.
  rewrite <- (timer_initialized_configured_rep_eq sg timers Hen Hinit).
  sep_apply_r_atomic (TmrTaskFields.tmr_task_fields_context_merge_timer
    environment local sg call mask state timers Hpost); entailer!.
Qed.

Lemma context_merge_read_part : forall environment local sg call mask state cells rest,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState) ->
  (cells ** rest |-- timer_raw_rep sg state.(TimerState)) ->
  cells ** context_rest environment local sg call mask state rest |--
    TmrTaskFields.tmr_task_fields_context environment local sg call mask state.
Proof.
  intros environment local sg call mask state cells rest Hen Hinit Hmerge.
  rewrite TmrTaskFields.tmr_task_fields_context_split_timer.
  rewrite (timer_initialized_configured_rep_eq sg state.(TimerState) Hen Hinit).
  unfold context_rest; Intros; sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma complete_preserves_kernel_validity : forall sg state index node timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> UCOS2_state_inv sg state ->
  timer_api_initialized state.(TimerState) -> state.(TimerState).(timerUsed) index = Some node ->
  node.(timerState) <> TimerRunning -> timer_complete state.(TimerState) index = Some timers ->
  UCOS2_state_inv sg (replace_TimerS timers state).
Proof.
  intros sg state index node timers Hen Hvalid Hinit Hnode Hinactive Hstep.
  assert (Htimer : valid_timer_configuration sg state.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hafterinit : timer_api_initialized timers).
  { unfold timer_api_initialized in *.
    rewrite (timer_complete_preserves_initialization_phase _ _ _ Hstep); exact Hinit. }
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid| |intros; exact Hafterinit|].
  - apply (proj2 (timer_initialized_configuration_iff sg timers Hen Hafterinit)).
    eapply timer_complete_preserves_state_validity; [|exact Hnode|exact Hinactive|exact Hstep].
    apply (proj1 (timer_initialized_configuration_iff sg state.(TimerState) Hen Hinit)); exact Htimer.
  - unfold timer_complete in Hstep; rewrite Hnode in Hstep.
    destruct (timerImages (TimerState state) index) as [image|]; [|discriminate].
    injection Hstep as Hstep; subst timers.
    intros name [other [value [Hvalue Hname]]].
    cbn [timer_replace_wheel_objects timerUsed] in Hvalue.
    destruct (Z.eq_dec other index) as [->|Hother].
    + rewrite kernel_map_set_same in Hvalue; injection Hvalue as Hvalue; subst value.
      exists index, node; split; [exact Hnode|exact Hname].
    + rewrite kernel_map_set_other in Hvalue by exact Hother.
      exists other, value; split; assumption.
Qed.

End TmrTaskFieldsHeap.

Lemma tmr_task_fields_cell_lift : forall kind pointer value,
  TmrTaskFieldsRules.logic_equiv (tmr_task_cell kind pointer value)
    (TmrTaskFieldsRules.lift (TmrTaskFieldsHeap.cell kind pointer value)).
Proof.
  intros kind pointer value; destruct kind; cbn [tmr_task_cell TmrTaskFieldsHeap.cell];
    apply TmrTaskFieldsRules.store_uchar_lift || apply TmrTaskFieldsRules.store_uint_lift ||
    apply TmrTaskFieldsRules.store_ptr_lift.
Qed.

Section TaskFieldsHeapOwner.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars) (mask perr : Z).

(** The existential is the CURRENT actual family. A callback consumer can
    apply these lemmas directly to its returned owner; no equality with
    the pre-callback family or task map is needed. *)
Definition tmr_task_fields_heap_view call (before : tmr_task_scan_world Application)
  (cells rest : Assertion) : TmrTaskFieldsRules.expr :=
  fun heap => exists local,
    TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.lift cells)
        (TmrTaskFieldsRules.lift (TmrTaskFieldsHeap.context_rest environment local sg
          call mask (fst before) rest)))
      (TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.lift (sem_pend_error_cell perr))
        (AppRep (snd before))) heap.

Definition tmr_task_fields_cell_rest call (before : tmr_task_scan_world Application)
  (rest : Assertion) : TmrTaskFieldsRules.expr :=
  fun heap => exists local,
    TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.lift (TmrTaskFieldsHeap.context_rest environment local sg
        call mask (fst before) rest))
      (TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.lift (sem_pend_error_cell perr))
        (AppRep (snd before))) heap.

(** This is the typed cell shape consumed by the C dereference/store. The
    rest is the same physical frame, with its actual local family hidden;
    it is not an assumed entailment to an arbitrary future world. *)
Lemma tmr_task_fields_heap_view_cell : forall call before kind pointer value rest,
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_fields_heap_view call before (TmrTaskFieldsHeap.cell kind pointer value) rest)
    (TmrTaskFieldsRules.sepcon (tmr_task_cell kind pointer value)
      (tmr_task_fields_cell_rest call before rest)).
Proof.
  intros call before kind pointer value rest; split.
  - intros heap [local [kernel [client [Hwhole
      [[part [remaining [Hpart [Hcell Hremaining]]]] Hclient]]]]].
    destruct (TmrTaskFieldsRules.join_assoc part remaining client kernel heap Hpart Hwhole)
      as [tail [Htail Hjoin]].
    exists part, tail; split; [exact Hjoin|]. split.
    + exact (proj2 (tmr_task_fields_cell_lift kind pointer value) part Hcell).
    + exists local, remaining, client; split; [exact Htail|]. split; assumption.
  - intros heap [part [tail [Hwhole [Hcell
      [local [remaining [client [Htail [Hremaining Hclient]]]]]]]]].
    destruct (TmrTaskFieldsRules.join_assoc client remaining part tail heap
      (TmrTaskFieldsRules.join_comm _ _ _ Htail)
      (TmrTaskFieldsRules.join_comm _ _ _ Hwhole)) as [kernel [Hpart Hjoin]].
    exists local, kernel, client; split.
    + apply TmrTaskFieldsRules.join_comm; exact Hjoin.
    + split; [|exact Hclient]. exists part, remaining; split.
      * apply TmrTaskFieldsRules.join_comm; exact Hpart.
      * split; [|exact Hremaining].
        exact (proj1 (tmr_task_fields_cell_lift kind pointer value) part Hcell).
Qed.

Lemma tmr_task_current_fields_timer_valid : forall call before,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (TmrTaskFieldsRules.andp (TmrTaskFieldsRules.coq_prop
      (valid_timer_state sg (tmr_task_timers before)))
      (tmr_task_current_fields_owned AppRep environment sg mask perr call before)).
Proof.
  intros call before Hen Hinit heap Howned; split; [|exact Howned].
  pose proof (proj1 (tmr_task_current_fields_owned_valid AppRep environment sg mask perr
    call before heap Howned)) as Hvalid.
  change (UCOS2_state_inv sg (fst before)) in Hvalid.
  apply (proj1 (timer_initialized_configuration_iff sg (tmr_task_timers before) Hen Hinit)).
  change (valid_timer_configuration sg (fst before).(TimerState)).
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
Qed.

Lemma tmr_task_current_fields_split_part : forall call before cells rest,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  UCOS2_C_Rules.derivable1 (timer_raw_rep sg (tmr_task_timers before))
    (UCOS2_C_Rules.sepcon cells rest) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_heap_view call before cells rest).
Proof.
  intros call before cells rest Hen Hinit Hsplit heap
    [local [kernel [client [Hjoin [Hkernel Hclient]]]]].
  exists local, kernel, client; split; [exact Hjoin|]. split; [|exact Hclient].
  apply (proj1 (TmrTaskFieldsRules.lift_sepcon _ _ kernel)).
  exact (TmrTaskFieldsHeap.context_split_part environment local sg call mask (fst before)
    cells rest Hen Hinit Hsplit (fst kernel) Hkernel).
Qed.

Lemma tmr_task_current_fields_merge_read_part : forall call before cells rest,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  UCOS2_C_Rules.derivable1 (UCOS2_C_Rules.sepcon cells rest)
    (timer_raw_rep sg (tmr_task_timers before)) ->
  TmrTaskFieldsRules.derivable1 (tmr_task_fields_heap_view call before cells rest)
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before).
Proof.
  intros call before cells rest Hen Hinit Hmerge heap
    [local [kernel [client [Hjoin [Hfields Hclient]]]]].
  exists local, kernel, client; split; [exact Hjoin|]. split; [|exact Hclient].
  apply (TmrTaskFieldsHeap.context_merge_read_part environment local sg call mask
    (fst before) cells rest Hen Hinit Hmerge (fst kernel)).
  exact (proj2 (TmrTaskFieldsRules.lift_sepcon _ _ kernel) Hfields).
Qed.

Lemma tmr_task_current_fields_merge_updated_part : forall call before timers cells rest,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized timers ->
  (UCOS2_state_inv sg (fst before) -> UCOS2_state_inv sg (replace_TimerS timers (fst before))) ->
  UCOS2_C_Rules.derivable1 (UCOS2_C_Rules.sepcon cells rest) (timer_raw_rep sg timers) ->
  TmrTaskFieldsRules.derivable1 (tmr_task_fields_heap_view call before cells rest)
    (tmr_task_current_fields_owned AppRep environment sg mask perr call (tmr_task_set_timers timers before)).
Proof.
  intros call before timers cells rest Hen Hinit Hvalid Hmerge heap
    [local [kernel [client [Hjoin [Hfields Hclient]]]]].
  exists local, kernel, client; split; [exact Hjoin|]. split; [|exact Hclient].
  apply (TmrTaskFieldsHeap.context_merge_part environment local sg call mask (fst before)
    timers cells rest Hen Hinit Hvalid Hmerge (fst kernel)).
  exact (proj2 (TmrTaskFieldsRules.lift_sepcon _ _ kernel) Hfields).
Qed.

Lemma tmr_task_current_fields_split_time : forall call before,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_heap_view call before
      (TmrTaskFieldsHeap.cell TaskUIntCell sg.(g_OSTmrTime) (timerTime (tmr_task_timers before)))
      (TmrTaskFieldsHeap.timer_without_time sg (tmr_task_timers before))).
Proof.
  intros; apply tmr_task_current_fields_split_part; try assumption.
  apply (proj1 (TmrTaskFieldsHeap.timer_split_merge_time _ _)).
Qed.

Lemma tmr_task_current_fields_merge_incremented_time : forall call before,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_heap_view call before
      (TmrTaskFieldsHeap.cell TaskUIntCell sg.(g_OSTmrTime)
        (timerTime (timer_service_advance (tmr_task_timers before))))
      (TmrTaskFieldsHeap.timer_without_time sg (tmr_task_timers before)))
    (tmr_task_current_fields_owned AppRep environment sg mask perr call
      (tmr_task_set_timers (timer_service_advance (tmr_task_timers before)) before)).
Proof.
  intros call before Hen Hinit; apply tmr_task_current_fields_merge_updated_part.
  - exact Hen.
  - exact Hinit.
  - intros Hvalid; apply UCOS2_timer_service_advance_preserves_validity; assumption.
  - apply TmrTaskFieldsHeap.timer_merge_incremented_time.
Qed.

Lemma tmr_task_current_fields_merge_time : forall call before,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_heap_view call before
      (TmrTaskFieldsHeap.cell TaskUIntCell sg.(g_OSTmrTime) (timerTime (tmr_task_timers before)))
      (TmrTaskFieldsHeap.timer_without_time sg (tmr_task_timers before)))
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before).
Proof.
  intros; apply tmr_task_current_fields_merge_read_part; try assumption.
  apply (proj2 (TmrTaskFieldsHeap.timer_split_merge_time _ _)).
Qed.

Lemma tmr_task_current_fields_split_merge_image : forall call before index image field,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  tmr_task_fields_layout sg -> (tmr_task_timers before).(timerImages) index = Some image ->
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_heap_view call before
      (TmrTaskFieldsHeap.cell (tmr_task_image_kind field)
        (tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field))
        (tmr_task_image_value field image))
      (TmrTaskFieldsHeap.timer_without_field sg (tmr_task_timers before) index image field)).
Proof.
  intros call before index image field Hen Hinit Hlayout Himage; split.
  - apply tmr_task_current_fields_split_part; try assumption.
    apply TmrTaskFieldsHeap.timer_split_field; assumption.
  - apply tmr_task_current_fields_merge_read_part; try assumption.
    apply TmrTaskFieldsHeap.timer_merge_field; assumption.
Qed.

Lemma tmr_task_current_fields_split_merge_time_match : forall call before index image,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  tmr_task_fields_layout sg -> (tmr_task_timers before).(timerImages) index = Some image ->
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_heap_view call before
      (UCOS2_C_Rules.sepcon
        (TmrTaskFieldsHeap.cell TaskUIntCell sg.(g_OSTmrTime) (timerTime (tmr_task_timers before)))
        (TmrTaskFieldsHeap.cell TaskUIntCell
          (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrMatch") image.(timerImageMatch)))
      (TmrTaskFieldsHeap.timer_without_time_field sg (tmr_task_timers before) index image TaskMatchField)).
Proof.
  intros call before index image Hen Hinit Hlayout Himage; split.
  - apply tmr_task_current_fields_split_part; try assumption.
    apply (proj1 (TmrTaskFieldsHeap.timer_split_merge_time_field _ _ _ _ TaskMatchField Hlayout Himage)).
  - apply tmr_task_current_fields_merge_read_part; try assumption.
    apply (proj2 (TmrTaskFieldsHeap.timer_split_merge_time_field _ _ _ _ TaskMatchField Hlayout Himage)).
Qed.

Lemma tmr_task_current_fields_split_merge_head : forall call before spoke row,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  nth_error (timerWheel (tmr_task_timers before)) spoke = Some row ->
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_heap_view call before
      (TmrTaskFieldsHeap.cell TaskPointerCell (sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke)
        (timer_id_pointer sg row))
      (TmrTaskFieldsHeap.timer_without_head sg (tmr_task_timers before) spoke row)).
Proof.
  intros call before spoke row Hen Hinit Hrow; split.
  - apply tmr_task_current_fields_split_part; try assumption.
    apply (proj1 (TmrTaskFieldsHeap.timer_split_merge_head _ _ _ _ Hrow)).
  - apply tmr_task_current_fields_merge_read_part; try assumption.
    apply (proj2 (TmrTaskFieldsHeap.timer_split_merge_head _ _ _ _ Hrow)).
Qed.

(** In particular, instantiate this with the callback's returned descriptor
    and returned world. The row is read from that world; the saved Next and
    pre-callback wheel are not inputs to this operation. *)
Lemma tmr_task_current_fields_reload_head : forall call before spoke,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  tmr_task_spoke_in_range sg spoke ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_heap_view call before
      (TmrTaskFieldsHeap.cell TaskPointerCell (sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke)
        (tmr_task_head sg spoke (tmr_task_timers before)))
      (TmrTaskFieldsHeap.timer_without_head sg (tmr_task_timers before) spoke
        (nth spoke (timerWheel (tmr_task_timers before)) []))).
Proof.
  intros call before spoke Hen Hinit Hspoke heap Howned.
  pose proof (proj1 (tmr_task_current_fields_timer_valid call before Hen Hinit heap Howned)) as Hvalid.
  pose proof Hvalid as [_ [[Hlength _] _]].
  assert (Hrow : nth_error (timerWheel (tmr_task_timers before)) spoke =
    Some (nth spoke (timerWheel (tmr_task_timers before)) [])).
  { apply nth_error_nth'; unfold tmr_task_spoke_in_range in Hspoke; lia. }
  exact (proj1 (tmr_task_current_fields_split_merge_head call before spoke _ Hen Hinit Hrow)
    heap Howned).
Qed.

Lemma tmr_task_current_fields_scan_image : forall call before scan index tail,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  timer_scan_continuation_valid sg (tmr_task_timers before) scan ->
  timerScanRemaining scan = index :: tail ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (fun heap => exists node image,
      (tmr_task_timers before).(timerUsed) index = Some node /\ node.(timerState) = TimerRunning /\
      (tmr_task_timers before).(timerImages) index = Some image /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call before heap).
Proof.
  intros call before scan index tail Hen Hinit Hscan Hremaining heap Howned.
  pose proof (proj1 (tmr_task_current_fields_timer_valid call before Hen Hinit heap Howned)) as Hvalid.
  destruct (timer_scan_continuation_remaining_running sg (tmr_task_timers before) scan index
    Hscan ltac:(rewrite Hremaining; left; reflexivity)) as [node [Hnode Hrunning]].
  pose proof Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused index node Hnode) as [_ [_ [_ [image [Himage _]]]]].
  exists node, image; split; [exact Hnode|]. split; [exact Hrunning|].
  split; [exact Himage|exact Howned].
Qed.

Lemma tmr_task_current_fields_split_completed_state : forall call before index image,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  (tmr_task_timers before).(timerImages) index = Some image ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_heap_view call before
      (TmrTaskFieldsHeap.cell TaskByteCell
        (timer_pool_addr sg index + timer_option_offset sg.(osKernelConfig) + 1) image.(timerImageState))
      (timer_complete_rep_without_state sg (tmr_task_timers before) index image)).
Proof.
  intros; apply tmr_task_current_fields_split_part; try assumption.
  apply timer_complete_split_state; assumption.
Qed.

Lemma tmr_task_current_fields_merge_completed_state : forall call before index node image timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  (tmr_task_timers before).(timerUsed) index = Some node -> node.(timerState) <> TimerRunning ->
  (tmr_task_timers before).(timerImages) index = Some image ->
  timer_complete (tmr_task_timers before) index = Some timers ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_heap_view call before
      (TmrTaskFieldsHeap.cell TaskByteCell
        (timer_pool_addr sg index + timer_option_offset sg.(osKernelConfig) + 1) 2)
      (timer_complete_rep_without_state sg (tmr_task_timers before) index image))
    (tmr_task_current_fields_owned AppRep environment sg mask perr call (tmr_task_set_timers timers before)).
Proof.
  intros call before index node image timers Hen Hinit Hnode Hinactive Himage Hstep.
  apply tmr_task_current_fields_merge_updated_part; [exact Hen| | |].
  - unfold timer_api_initialized in *.
    rewrite (timer_complete_preserves_initialization_phase _ _ _ Hstep); exact Hinit.
  - intros Hvalid; eapply TmrTaskFieldsHeap.complete_preserves_kernel_validity; eassumption.
  - apply timer_complete_merge_state; assumption.
Qed.

End TaskFieldsHeapOwner.

Module TmrTaskFieldsRawHeap.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

Definition unlink_frame environment local sg call mask state : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    (timer_images_type_rep sg state.(TimerState) **
     timer_service_globals_rep sg state.(TimerState) **
     TmrTaskFields.tmr_task_fields_timer_frame environment local sg call mask state).

Definition unlink_return environment local sg call mask state index : Assertion :=
  EX timers, coq_prop (timer_unlink sg state.(TimerState) index = Some timers) &&
    TmrTaskFields.tmr_task_fields_context environment local sg call mask (replace_TimerS timers state).

Lemma unlink_pool_post_merge_context : forall environment local sg call mask state index,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState) ->
  tmr_unlink_running state.(TimerState) index ->
  tmr_del_unlink_pool_body_post sg state.(TimerState) index **
    unlink_frame environment local sg call mask state |--
  unlink_return environment local sg call mask state index.
Proof.
  intros environment local sg call mask state index Hen Hinit [node [Hnode Hrunning]].
  unfold tmr_del_unlink_pool_body_post, unlink_frame, unlink_return; Intros timers.
  assert (Hstep : timer_unlink sg state.(TimerState) index = Some timers) by tauto.
  assert (Hafterinit : timer_api_initialized timers) by tauto.
  assert (Hvalid : UCOS2_state_inv sg state) by tauto.
  pose proof (UCOS2_timer_unlink_preserves_validity sg state index node timers
    Hvalid Hen Hinit Hnode Hrunning Hstep) as Hafter.
  Exists timers; entailer!.
  sep_apply_r_atomic (TmrTaskFields.tmr_task_fields_context_merge_timer
    environment local sg call mask state timers Hafter).
  rewrite (timer_initialized_configured_rep_eq sg timers Hen Hafterinit).
  rewrite timer_raw_rep_split_pool, timer_pool_rep_split_types.
  unfold timer_images_type_rep.
  rewrite (timer_unlink_image_types_eq sg state.(TimerState) index timers Hstep),
    (timer_unlink_service_globals_eq sg state.(TimerState) index timers Hstep).
  entailer!.
Qed.

Definition unlink_call_view environment local sg call mask state index (returned : bool) : Assertion :=
  EX match_time next previous first entries frame,
    (if returned then tmr_unlink_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
      match_time next previous first entries frame
     else tmr_unlink_raw_pre (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
      match_time next previous first entries frame) **
    (tmr_unlink_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
      match_time next previous first entries frame -*
      unlink_return environment local sg call mask state index).

Lemma context_split_unlink_call : forall environment local sg call mask state index,
  tmr_unlink_layout -> tmr_unlink_profile sg -> timer_api_initialized state.(TimerState) ->
  tmr_unlink_running state.(TimerState) index ->
  TmrTaskFields.tmr_task_fields_context environment local sg call mask state |--
    unlink_call_view environment local sg call mask state index false.
Proof.
  intros environment local sg call mask state index Hlayout Hprofile Hinit Hrunning.
  pose proof (proj1 Hprofile) as Hen.
  assert (Hsplit : TmrTaskFields.tmr_task_fields_context environment local sg call mask state |--
    EX match_time next previous first entries frame,
      tmr_unlink_raw_pre (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
        match_time next previous first entries frame **
      (tmr_unlink_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
        match_time next previous first entries frame -*
        (tmr_del_unlink_pool_body_post sg state.(TimerState) index **
          unlink_frame environment local sg call mask state))).
  { rewrite TmrTaskFields.tmr_task_fields_context_split_timer; Intros.
    assert (Hconfig : valid_timer_configuration sg state.(TimerState))
      by (match goal with H : UCOS2_state_inv sg state |- _ =>
        unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in H; tauto end).
    rewrite (timer_initialized_configured_rep_eq sg state.(TimerState) Hen Hinit).
    rewrite timer_raw_rep_split_pool, timer_pool_rep_split_types.
    sep_apply_r_atomic (tmr_del_unlink_pool_body_spec_consequence sg state.(TimerState)
      index (unlink_frame environment local sg call mask state)
      Hlayout Hprofile Hconfig Hinit Hrunning).
    unfold unlink_frame; entailer!. }
  intros heap Hcontext.
  destruct (Hsplit heap Hcontext) as
    [match_time [next [previous [first [entries [frame
      [raw [rest [Hjoin [Hraw Hrestore]]]]]]]]]].
  exists match_time, next, previous, first, entries, frame, raw, rest.
  split; [exact Hjoin|]. split; [exact Hraw|].
  intros supplied combined Hcombined Hpost.
  exact (unlink_pool_post_merge_context environment local sg call mask state index
    Hen Hinit Hrunning combined (Hrestore supplied combined Hcombined Hpost)).
Qed.

Lemma unlink_call_return_context : forall environment local sg call mask state index,
  unlink_call_view environment local sg call mask state index true |--
    unlink_return environment local sg call mask state index.
Proof.
  intros environment local sg call mask state index heap
    [match_time [next [previous [first [entries [frame
      [raw [rest [Hjoin [Hraw Hrestore]]]]]]]]]].
  apply (Hrestore raw heap); [apply join_comm; exact Hjoin|exact Hraw].
Qed.

(** This is a caller footprint construction for the literal periodic Link
    call. The callee remains its original raw contract. The image and
    wheel byte proofs are reused from tmr_link_spec, with both empty and
    nonempty target spokes preserved by those lemmas. *)
Lemma periodic_link_split_raw : forall sg timers index (R : Assertion),
  tmr_link_layout -> tmr_link_profile sg -> valid_timer_configuration sg timers ->
  timer_api_initialized timers -> tmr_link_eligible timers index ->
  timer_raw_rep sg timers ** R |--
  EX delay period first entries frame,
    tmr_link_raw_pre (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl) sg.(g_OSTmrTime)
      1 timers.(timerTime) delay period first entries frame **
    (tmr_link_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl) sg.(g_OSTmrTime)
      1 timers.(timerTime) delay period first entries frame -*
      (tmr_link_configured_post sg timers index 1 ** R)).
Proof.
  intros sg timers index R Hlayout Hprofile Hconfig Hinit [node [Hnode Hinactive]].
  pose proof Hprofile as [Hen [Hnames [Hcapacity [Hsize [Hpool Hwheelregion]]]]].
  pose proof (proj1 (timer_initialized_configuration_iff sg timers Hen Hinit) Hconfig) as Hvalid.
  pose proof Hvalid as [_ [Hwheel [Htime [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused index node Hnode) as [Hnodevalid [_ [_ [image [Himage Himageeq]]]]].
  set (target := timerMatch (timer_link_object (timerTime timers) true node)).
  assert (Hmatch : tmr_link_match 1 (timerImageDelay image) (timerImagePeriod image)
    (timerTime timers) = target).
  { unfold target, tmr_link_match; rewrite Himageeq; reflexivity. }
  assert (Hspoke : timer_spoke sg.(osKernelConfig) target = target mod 7).
  { unfold timer_spoke, kernel_u16; rewrite Hsize.
    apply Z.mod_small; pose proof (Z.mod_pos_bound target 7 ltac:(lia)); lia. }
  set (spoke := Z.to_nat (target mod 7)).
  set (row := nth spoke timers.(timerWheel) []).
  assert (Hspoke_range : (spoke < List.length timers.(timerWheel))%nat).
  { unfold spoke; rewrite <- Hspoke; apply timer_wheel_spoke_index_in_range; [lia|exact Hwheel]. }
  assert (Hrow : nth_error timers.(timerWheel) spoke = Some row).
  { unfold row; apply nth_error_nth'; exact Hspoke_range. }
  assert (Houtside : ~ In index row).
  { intros Hin; apply (tmr_link_eligible_not_in_wheel sg timers index Hvalid).
    - exists node; split; assumption.
    - unfold timer_wheel_member; eapply timer_wheel_row_member; eauto. }
  pose proof (tmr_link_profile_pool_region sg Hprofile) as Hpoolregion.
  pose proof (timer_wheel_row_pointer_null_iff sg timers spoke row Hpoolregion Hvalid Hrow) as Hnull.
  assert (Himages : forall other, In other row -> exists value, timerImages timers other = Some value).
  { intros other Hin.
    destruct (timer_wheel_member_spoke sg timers spoke row other Hwheel Hrow Hin) as [value [Hvalue _]].
    destruct (Hused other value Hvalue) as [_ [_ [_ [stored [Hstored _]]]]]; eauto. }
  destruct (tmr_link_images_fields_split_merge sg (timerImages timers) index image target row
    Hlayout Hnames Himage Houtside Hnull Himages) as [Fimages [Hsplitimages Hmergeimages]].
  assert (Htargetbounds : 0 < timer_pool_addr sg index /\
    timer_pool_addr sg index + 40 <= 4294967296).
  { pose proof (timer_pool_addr_in_range sg index Hpoolregion
      (timer_used_id_in_range sg timers index node Hvalid Hnode)) as Hbounds.
    rewrite (tmr_link_profile_object_size sg Hprofile) in Hbounds; exact Hbounds. }
  assert (Hneighbor : tmr_link_neighbor_bounds (timer_id_pointer sg row)).
  { unfold tmr_link_neighbor_bounds; intros Hnonnull.
    destruct row as [|other rest]; [contradiction|].
    pose proof (timer_pool_addr_in_range sg other Hpoolregion
      (timer_wheel_row_ids_in_range sg timers spoke (other :: rest) other Hvalid Hrow
        (or_introl eq_refl))) as Hbounds.
    rewrite (tmr_link_profile_object_size sg Hprofile) in Hbounds; exact Hbounds. }
  pose proof (timer_wheel_row_entries_in_range sg timers spoke row ltac:(lia) Hvalid Hrow) as Hentries.
  pose proof (tmr_link_row_entries_increase sg timers spoke row index Hprofile Hvalid Hrow) as Hcount.
  assert (Haddress : tmr_link_spoke_addr sg.(g_OSTmrWheelTbl) target =
    sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke).
  { unfold tmr_link_spoke_addr, spoke; rewrite Z2Nat.id; [reflexivity|apply Z.mod_pos_bound; lia]. }
  pose proof Hlayout as [_ [_ [_ [_ [_ [_ [Hfirst [Hentriesaddr Hsizeof]]]]]]]].
  set (Fwheel := tmr_link_wheel_without_spoke sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) spoke).
  set (frame := Fimages ** Fwheel ** TmrTaskFieldsHeap.globals_without_time sg timers ** R).
  set (after := timer_replace_wheel_objects timers
    (kernel_map_set timers.(timerUsed) index (Some (timer_link_object timers.(timerTime) true node)))
    (timer_wheel_prepend_images sg timers.(timerImages) index
      (timer_link_image image target (timer_id_pointer sg row)) row)
    (timer_wheel_update timers.(timerWheel) spoke (index :: row))).
  assert (Hstep : timer_link sg timers index true = Some after).
  { unfold timer_link, after; rewrite Hnode, Himage; cbn zeta.
    fold target; rewrite Hspoke; reflexivity. }
  destruct (timer_link_preserves_configuration sg timers index node true after
    Hen ltac:(lia) Hconfig Hinit Hnode Hinactive Hstep) as [Hafter Hafterinit].
  assert (Hpost : tmr_link_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
    sg.(g_OSTmrTime) 1 timers.(timerTime) image.(timerImageDelay) image.(timerImagePeriod)
    (timer_id_pointer sg row) (Z.of_nat (List.length row)) frame |--
      tmr_link_configured_post sg timers index 1 ** R).
  { unfold tmr_link_configured_post; Exists after; unfold timer_inv.
    rewrite (timer_initialized_configured_rep_eq sg after Hen Hafterinit); entailer!.
    unfold tmr_link_raw_post; rewrite Hmatch, Haddress, Hfirst, Hentriesaddr, Hcount.
    unfold frame, Fwheel, after, timer_raw_rep, timer_images_rep, timer_globals_rep,
      TmrTaskFieldsHeap.globals_without_time.
    cbn [timer_replace_wheel_objects timerImages timerWheel timerFree timerFreeCount
      timerUsedCount timerTime timerSem timerSignalSem].
    sepcon_right_assoc; sep_apply_l_atomic Hmergeimages.
    pose proof (tmr_link_wheel_merge_updated_spoke sg timers.(timerWheel) spoke row (index :: row)
      sg.(g_OSTmrWheelTbl) Hrow) as Hmergewheel.
    cbn [timer_id_pointer] in Hmergewheel.
    rewrite <- Hmergewheel; entailer!. }
  assert (Hrestore : emp |--
    tmr_link_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl) sg.(g_OSTmrTime)
      1 timers.(timerTime) image.(timerImageDelay) image.(timerImagePeriod)
      (timer_id_pointer sg row) (Z.of_nat (List.length row)) frame -*
      (tmr_link_configured_post sg timers index 1 ** R)).
  { apply_sepcon_adjoint; rewrite <- Hpost; entailer!. }
  Exists image.(timerImageDelay) image.(timerImagePeriod) (timer_id_pointer sg row)
    (Z.of_nat (List.length row)) frame.
  rewrite <- Hrestore.
  unfold tmr_link_raw_pre; rewrite Hmatch, Haddress, Hfirst, Hentriesaddr.
  unfold timer_raw_rep, timer_images_rep, timer_globals_rep, frame, Fwheel,
    TmrTaskFieldsHeap.globals_without_time.
  sep_apply_l_atomic Hsplitimages.
  sep_apply_l_atomic (tmr_link_wheel_split_spoke sg timers.(timerWheel) spoke row
    sg.(g_OSTmrWheelTbl) Hrow).
  assert (Hdelay : 0 <= image.(timerImageDelay) < 4294967296).
  { rewrite Himageeq; cbn [timer_object_image]; exact (proj1 Hnodevalid). }
  assert (Hperiod : 0 <= image.(timerImagePeriod) < 4294967296).
  { rewrite Himageeq; cbn [timer_object_image]; exact (proj1 (proj2 Hnodevalid)). }
  unfold kernel_region_valid in Hwheelregion; cbn in Hwheelregion; entailer!.
Qed.

Definition link_frame environment local sg call mask state : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    TmrTaskFields.tmr_task_fields_timer_frame environment local sg call mask state.
Definition link_return environment local sg call mask state index : Assertion :=
  EX timers, coq_prop (timer_link sg state.(TimerState) index true = Some timers) &&
    TmrTaskFields.tmr_task_fields_context environment local sg call mask (replace_TimerS timers state).

Lemma link_post_merge_context : forall environment local sg call mask state index,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState) ->
  tmr_link_eligible state.(TimerState) index ->
  tmr_link_configured_post sg state.(TimerState) index 1 **
    link_frame environment local sg call mask state |--
  link_return environment local sg call mask state index.
Proof.
  intros environment local sg call mask state index Hen Hinit [node [Hnode Hinactive]].
  unfold tmr_link_configured_post, link_frame, link_return, timer_inv; Intros timers.
  assert (Hstep : timer_link sg state.(TimerState) index true = Some timers) by tauto.
  assert (Hvalid : UCOS2_state_inv sg state) by tauto.
  pose proof (UCOS2_timer_link_preserves_validity sg state index node true timers
    Hvalid Hen Hinit Hnode Hinactive Hstep) as Hafter.
  Exists timers; entailer!.
  sep_apply_r_atomic (TmrTaskFields.tmr_task_fields_context_merge_timer
    environment local sg call mask state timers Hafter); entailer!.
Qed.

Definition link_call_view environment local sg call mask state index (returned : bool) : Assertion :=
  EX delay period first entries frame,
    (if returned then tmr_link_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
      sg.(g_OSTmrTime) 1 state.(TimerState).(timerTime) delay period first entries frame
     else tmr_link_raw_pre (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
      sg.(g_OSTmrTime) 1 state.(TimerState).(timerTime) delay period first entries frame) **
    (tmr_link_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
      sg.(g_OSTmrTime) 1 state.(TimerState).(timerTime) delay period first entries frame -*
      link_return environment local sg call mask state index).

Lemma context_split_link_call : forall environment local sg call mask state index,
  tmr_link_layout -> tmr_link_profile sg -> timer_api_initialized state.(TimerState) ->
  tmr_link_eligible state.(TimerState) index ->
  TmrTaskFields.tmr_task_fields_context environment local sg call mask state |--
    link_call_view environment local sg call mask state index false.
Proof.
  intros environment local sg call mask state index Hlayout Hprofile Hinit Heligible.
  pose proof (proj1 Hprofile) as Hen.
  assert (Hsplit : TmrTaskFields.tmr_task_fields_context environment local sg call mask state |--
    EX delay period first entries frame,
      tmr_link_raw_pre (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl) sg.(g_OSTmrTime)
        1 state.(TimerState).(timerTime) delay period first entries frame **
      (tmr_link_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl) sg.(g_OSTmrTime)
        1 state.(TimerState).(timerTime) delay period first entries frame -*
        (tmr_link_configured_post sg state.(TimerState) index 1 **
          link_frame environment local sg call mask state))).
  { rewrite TmrTaskFields.tmr_task_fields_context_split_timer; Intros.
    assert (Hconfig : valid_timer_configuration sg state.(TimerState))
      by (match goal with H : UCOS2_state_inv sg state |- _ =>
        unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in H; tauto end).
    rewrite (timer_initialized_configured_rep_eq sg state.(TimerState) Hen Hinit).
    sep_apply_r_atomic (periodic_link_split_raw sg state.(TimerState) index
      (link_frame environment local sg call mask state) Hlayout Hprofile Hconfig Hinit Heligible).
    unfold link_frame; entailer!. }
  intros heap Hcontext.
  destruct (Hsplit heap Hcontext) as [delay [period [first [entries [frame
    [raw [rest [Hjoin [Hraw Hrestore]]]]]]]]].
  exists delay, period, first, entries, frame, raw, rest.
  split; [exact Hjoin|]. split; [exact Hraw|].
  intros supplied combined Hcombined Hpost.
  exact (link_post_merge_context environment local sg call mask state index
    Hen Hinit Heligible combined (Hrestore supplied combined Hcombined Hpost)).
Qed.

Lemma link_call_return_context : forall environment local sg call mask state index,
  link_call_view environment local sg call mask state index true |--
    link_return environment local sg call mask state index.
Proof.
  intros environment local sg call mask state index heap [delay [period [first [entries [frame
    [raw [rest [Hjoin [Hraw Hrestore]]]]]]]]].
  apply (Hrestore raw heap); [apply join_comm; exact Hjoin|exact Hraw].
Qed.

End TmrTaskFieldsRawHeap.

Section TaskFieldsRawOwner.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars) (mask perr : Z).

Definition tmr_task_fields_unlink_call_view call (before : tmr_task_scan_world Application)
  index returned : TmrTaskFieldsRules.expr :=
  fun heap => exists local,
    TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.lift (TmrTaskFieldsRawHeap.unlink_call_view
        environment local sg call mask (fst before) index returned))
      (TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.lift (sem_pend_error_cell perr))
        (AppRep (snd before))) heap.
Definition tmr_task_fields_link_call_view call (before : tmr_task_scan_world Application)
  index returned : TmrTaskFieldsRules.expr :=
  fun heap => exists local,
    TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.lift (TmrTaskFieldsRawHeap.link_call_view
        environment local sg call mask (fst before) index returned))
      (TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.lift (sem_pend_error_cell perr))
        (AppRep (snd before))) heap.

Lemma tmr_task_current_fields_split_unlink_call : forall call before index,
  tmr_unlink_layout -> tmr_unlink_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  tmr_unlink_running (tmr_task_timers before) index ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_unlink_call_view call before index false).
Proof.
  intros call before index Hlayout Hprofile Hinit Hrunning heap
    [local [kernel [client [Hjoin [Hkernel Hclient]]]]].
  exists local, kernel, client; split; [exact Hjoin|]. split; [|exact Hclient].
  exact (TmrTaskFieldsRawHeap.context_split_unlink_call environment local sg call mask
    (fst before) index Hlayout Hprofile Hinit Hrunning (fst kernel) Hkernel).
Qed.

Lemma tmr_task_current_fields_unlink_return : forall call before index,
  TmrTaskFieldsRules.derivable1 (tmr_task_fields_unlink_call_view call before index true)
    (fun heap => exists after, tmr_task_unlink_world sg before index after /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call after heap).
Proof.
  intros call before index heap [local [kernel [client [Hjoin [Hpost Hclient]]]]].
  destruct (TmrTaskFieldsRawHeap.unlink_call_return_context environment local sg call mask
    (fst before) index (fst kernel) Hpost) as [timers [Hstep Hcontext]].
  exists (tmr_task_set_timers timers before); split.
  - exists timers; split; [exact Hstep|reflexivity].
  - exists local, kernel, client; split; [exact Hjoin|]. split; assumption.
Qed.

Lemma tmr_task_current_fields_split_link_call : forall call before index,
  tmr_link_layout -> tmr_link_profile sg -> timer_api_initialized (tmr_task_timers before) ->
  tmr_link_eligible (tmr_task_timers before) index ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call before)
    (tmr_task_fields_link_call_view call before index false).
Proof.
  intros call before index Hlayout Hprofile Hinit Heligible heap
    [local [kernel [client [Hjoin [Hkernel Hclient]]]]].
  exists local, kernel, client; split; [exact Hjoin|]. split; [|exact Hclient].
  exact (TmrTaskFieldsRawHeap.context_split_link_call environment local sg call mask
    (fst before) index Hlayout Hprofile Hinit Heligible (fst kernel) Hkernel).
Qed.

Lemma tmr_task_current_fields_link_return : forall call before index,
  TmrTaskFieldsRules.derivable1 (tmr_task_fields_link_call_view call before index true)
    (fun heap => exists after, tmr_task_link_world sg before index after /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call after heap).
Proof.
  intros call before index heap [local [kernel [client [Hjoin [Hpost Hclient]]]]].
  destruct (TmrTaskFieldsRawHeap.link_call_return_context environment local sg call mask
    (fst before) index (fst kernel) Hpost) as [timers [Hstep Hcontext]].
  exists (tmr_task_set_timers timers before); split.
  - exists timers; split; [exact Hstep|reflexivity].
  - exists local, kernel, client; split; [exact Hjoin|]. split; assumption.
Qed.

End TaskFieldsRawOwner.

Section TaskFieldsSourceConsumers.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars) (mask perr : Z).

Lemma tmr_task_fields_incremented_time_continue : forall Result callback call before
  (next : (list tmr_task_scan_event * OsSchedCallContext) ->
    StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop),
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers before) ->
  safeExec (eq before) (StateRelMonad.bind (tmr_task_tick_program sg callback call) next) X ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_heap_view AppRep environment sg mask perr call before
      (TmrTaskFieldsHeap.cell TaskUIntCell sg.(g_OSTmrTime)
        (timerTime (timer_service_advance (tmr_task_timers before))))
      (TmrTaskFieldsHeap.timer_without_time sg (tmr_task_timers before)))
    (fun heap =>
      let advanced := tmr_task_set_timers (timer_service_advance (tmr_task_timers before)) before in
      safeExec (eq advanced)
        (StateRelMonad.bind (tmr_task_scan_program sg callback
          (Z.to_nat (timer_spoke sg.(osKernelConfig) (timerTime (tmr_task_timers advanced))))
          call (timer_scan_begin sg (tmr_task_timers advanced))) next) X /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call advanced heap).
Proof.
  intros Result callback call before next X Hen Hinit Hsafe heap Hview; split.
  - exact (tmr_task_tick_advance_continue Application sg callback call Result before next X Hsafe).
  - exact (tmr_task_current_fields_merge_incremented_time AppRep environment sg mask perr
      call before Hen Hinit heap Hview).
Qed.

(** Actual callback return consumption reaches the C head cell, while
    retaining the same arbitrary continuation X, body-proved facts and
    function capability. The current owner supplies its returned local. *)
Lemma tmr_task_fields_callback_resume_head_cell : forall Result callback fn self argument call before
  (next : OsSchedCallContext -> StateRelMonad.M (tmr_task_scan_world Application) Result)
  (X : Result -> tmr_task_scan_world Application -> Prop) frame spoke,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> tmr_task_spoke_in_range sg spoke ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_callback_resume AppRep environment sg callback mask perr
      fn self argument call before next X frame)
    (fun heap => exists returned after,
      tmr_task_fields_callback_return_facts sg callback fn self argument call before returned after /\
      safeExec (eq after) (next returned) X /\
      TmrTaskFieldsRules.sepcon
        (TmrTaskFieldsRules.sepcon
          (tmr_task_cell TaskPointerCell (sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke)
            (tmr_task_head sg spoke (tmr_task_timers after)))
          (tmr_task_fields_cell_rest AppRep environment sg mask perr returned after
            (TmrTaskFieldsHeap.timer_without_head sg (tmr_task_timers after) spoke
              (nth spoke (timerWheel (tmr_task_timers after)) [])))) frame heap /\
      tmr_task_fields_callback_capability AppRep environment sg callback mask perr fn self argument heap).
Proof.
  intros Result callback fn self argument call before next X frame spoke Hen Hspoke heap
    [returned [after [Hfacts [Hsafe [[owned [rest [Hjoin [Howned Hframe]]]] Hcap]]]]].
  exists returned, after; split; [exact Hfacts|]. split; [exact Hsafe|].
  split; [|exact Hcap]. exists owned, rest; split; [exact Hjoin|]. split; [|exact Hframe].
  apply (proj1 (tmr_task_fields_heap_view_cell AppRep environment sg mask perr returned after
    TaskPointerCell (sg.(g_OSTmrWheelTbl) + 8 * Z.of_nat spoke)
    (tmr_task_head sg spoke (tmr_task_timers after))
    (TmrTaskFieldsHeap.timer_without_head sg (tmr_task_timers after) spoke
      (nth spoke (timerWheel (tmr_task_timers after)) []))) owned).
  exact (tmr_task_current_fields_reload_head AppRep environment sg mask perr returned after spoke
    Hen (proj2 (proj1 (proj2 Hfacts))) Hspoke owned Howned).
Qed.

End TaskFieldsSourceConsumers.
