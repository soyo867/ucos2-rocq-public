Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.error_codes.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module TimerFieldStorage := FieldStorage Arch32 LittleEndian
  UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules.

(** Timer time advances once per OSTmr_Task loop after OSSemPend returns;
    it is not OSTime.  The source ignores the semaphore error, so successful
    signal consumption is a separate service protocol.  OSTmrSem and
    OSTmrSemSignal below are handle cells only.  Their semaphore objects
    are Event-owned, and the timer service task is Task-owned. *)
Definition encode_timer_mode (m : TimerMode) : Z :=
  match m with TimerOneShot => 1 | TimerPeriodic => 2 end.
Definition encode_timer_status (st : TimerStatus) : Z :=
  match st with TimerUnused => 0 | TimerStopped => 1 | TimerCompleted => 2 | TimerRunning => 3 end.
Definition timer_spoke (c : KernelConfiguration) (time : Z) :=
  kernel_u16 (time mod c.(cfgTimerWheelSize)).
Lemma timer_spoke_in_range : forall c time,
  0 < c.(cfgTimerWheelSize) <= 65536 -> 0 <= timer_spoke c time < c.(cfgTimerWheelSize).
Proof.
  intros c time H; unfold timer_spoke, kernel_u16.
  pose proof (Z.mod_pos_bound time c.(cfgTimerWheelSize) ltac:(lia)) as Hr.
  rewrite Z.mod_small; lia.
Qed.
Definition timer_link_delay (t : TimerObjectState) (periodic : bool) : Z :=
  if periodic then t.(timerPeriod) else
  if Z.eqb t.(timerDelay) 0 then t.(timerPeriod) else t.(timerDelay).
Definition timer_set_status (t : TimerObjectState) (st : TimerStatus) : TimerObjectState :=
  {| timerGeneration := t.(timerGeneration); timerDelay := t.(timerDelay);
     timerPeriod := t.(timerPeriod); timerMatch := t.(timerMatch);
     timerMode := t.(timerMode); timerState := st; timerCallback := t.(timerCallback);
     timerCallbackArg := t.(timerCallbackArg); timerName := t.(timerName) |}.
Definition timer_link_object (time : Z) (periodic : bool) (t : TimerObjectState) : TimerObjectState :=
  {| timerGeneration := t.(timerGeneration); timerDelay := t.(timerDelay);
     timerPeriod := t.(timerPeriod); timerMatch := kernel_u32 (timer_link_delay t periodic + time);
     timerMode := t.(timerMode); timerState := TimerRunning; timerCallback := t.(timerCallback);
     timerCallbackArg := t.(timerCallbackArg); timerName := t.(timerName) |}.
Definition timer_expire_object (time : Z) (t : TimerObjectState) : TimerObjectState :=
  match t.(timerMode) with
  | TimerPeriodic => timer_link_object time true t
  | TimerOneShot => timer_set_status t TimerCompleted
  end.
Definition valid_timer_object (t : TimerObjectState) : Prop :=
  0 <= t.(timerDelay) < 4294967296 /\ 0 <= t.(timerPeriod) < 4294967296 /\
  0 <= t.(timerMatch) < 4294967296 /\ t.(timerState) <> TimerUnused /\
  match t.(timerMode) with TimerOneShot => 0 < t.(timerDelay) | TimerPeriodic => 0 < t.(timerPeriod) end.
Lemma timer_link_preserves_object_validity : forall time periodic t,
  valid_timer_object t -> valid_timer_object (timer_link_object time periodic t).
Proof.
  intros time periodic t [Hd [Hp [Hm [Hs Ho]]]]; unfold valid_timer_object, timer_link_object; simpl.
  split; [exact Hd|]. split; [exact Hp|]. split; [apply kernel_u32_in_range|].
  split; [discriminate|exact Ho].
Qed.
Lemma timer_set_status_preserves_object_validity : forall t st,
  valid_timer_object t -> st <> TimerUnused -> valid_timer_object (timer_set_status t st).
Proof.
  intros t st [Hd [Hp [Hm [Hs Ho]]]] Hst; unfold valid_timer_object, timer_set_status; simpl; tauto.
Qed.
Lemma timer_expire_preserves_object_validity : forall time t,
  valid_timer_object t -> valid_timer_object (timer_expire_object time t).
Proof.
  intros time t H; unfold timer_expire_object; destruct (timerMode t).
  - apply timer_set_status_preserves_object_validity; [exact H|discriminate].
  - apply timer_link_preserves_object_validity; exact H.
Qed.
Lemma timer_link_match_wraps : forall time periodic t,
  (timer_link_object time periodic t).(timerMatch) =
  (timer_link_delay t periodic + time) mod 4294967296.
Proof. reflexivity. Qed.

Definition timer_remaining (time : Z) (t : TimerObjectState) : Z * OSErrCode :=
  match t.(timerState) with
  | TimerRunning => (kernel_u32 (t.(timerMatch) - time), OS_ERR_NONE)
  | TimerStopped =>
    (match t.(timerMode) with
     | TimerPeriodic => if Z.eqb t.(timerDelay) 0 then t.(timerPeriod) else t.(timerDelay)
     | TimerOneShot => t.(timerDelay) end, OS_ERR_NONE)
  | TimerCompleted => (0, OS_ERR_NONE)
  | TimerUnused => (0, OS_ERR_TMR_INACTIVE)
  end.
Lemma timer_remaining_in_range : forall time t,
  valid_timer_object t -> 0 <= fst (timer_remaining time t) < 4294967296.
Proof.
  intros time t [Hd [Hp H]]; unfold timer_remaining.
  destruct (timerState t); simpl; try lia.
  - destruct (timerMode t); simpl; [exact Hd|].
    destruct (Z.eqb (timerDelay t) 0); assumption.
  - apply kernel_u32_in_range.
Qed.
Definition timer_image_set_links (v : TimerImage) (next prev : addr) : TimerImage :=
  {| timerImageType := v.(timerImageType); timerImageCallback := v.(timerImageCallback);
     timerImageArg := v.(timerImageArg); timerImageNext := next; timerImagePrev := prev;
     timerImageMatch := v.(timerImageMatch); timerImageDelay := v.(timerImageDelay);
     timerImagePeriod := v.(timerImagePeriod); timerImageName := v.(timerImageName);
     timerImageOption := v.(timerImageOption); timerImageState := v.(timerImageState);
     timerImagePadding := v.(timerImagePadding) |}.
Definition timer_free_image (v : TimerImage) (next name : addr) : TimerImage :=
  {| timerImageType := v.(timerImageType); timerImageCallback := 0; timerImageArg := 0;
     timerImageNext := next; timerImagePrev := 0; timerImageMatch := 0;
     timerImageDelay := v.(timerImageDelay); timerImagePeriod := 0; timerImageName := name;
     timerImageOption := 0; timerImageState := 0; timerImagePadding := v.(timerImagePadding) |}.
Lemma timer_free_retains_type_and_delay : forall v next name,
  (timer_free_image v next name).(timerImageType) = v.(timerImageType) /\
  (timer_free_image v next name).(timerImageDelay) = v.(timerImageDelay).
Proof. intros; split; reflexivity. Qed.
Definition timer_object_image (t : TimerObjectState) (next prev : addr)
  (padding : list (option Z)) : TimerImage :=
  {| timerImageType := 100; timerImageCallback := t.(timerCallback);
     timerImageArg := t.(timerCallbackArg); timerImageNext := next; timerImagePrev := prev;
     timerImageMatch := t.(timerMatch); timerImageDelay := t.(timerDelay);
     timerImagePeriod := t.(timerPeriod); timerImageName := t.(timerName);
     timerImageOption := encode_timer_mode t.(timerMode);
     timerImageState := encode_timer_status t.(timerState); timerImagePadding := padding |}.

Definition timer_object_rep (c : KernelConfiguration) (p : addr) (v : TimerImage) : Assertion :=
  p # UChar |-> v.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) ** (p + 8) # Ptr |-> v.(timerImageArg) **
  (p + 12) # Ptr |-> v.(timerImageNext) ** (p + 16) # Ptr |-> v.(timerImagePrev) **
  (p + 20) # UInt |-> v.(timerImageMatch) ** (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (if c.(cfgTimerNames) then (p + 32) # Ptr |-> v.(timerImageName) else emp) **
  (p + timer_option_offset c) # UChar |-> v.(timerImageOption) **
  (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
  store_optional_bytes (p + timer_option_offset c + 2) (skipn 3 v.(timerImagePadding)).

(** Remove the observed type byte while retaining every other field and
    padding byte.  This split needs ownership of the object; it does not
    open a shared region or establish interference freedom. *)
Definition timer_object_rep_without_type (c : KernelConfiguration)
  (p : addr) (v : TimerImage) : Assertion :=
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) ** (p + 8) # Ptr |-> v.(timerImageArg) **
  (p + 12) # Ptr |-> v.(timerImageNext) ** (p + 16) # Ptr |-> v.(timerImagePrev) **
  (p + 20) # UInt |-> v.(timerImageMatch) ** (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (if c.(cfgTimerNames) then (p + 32) # Ptr |-> v.(timerImageName) else emp) **
  (p + timer_option_offset c) # UChar |-> v.(timerImageOption) **
  (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
  store_optional_bytes (p + timer_option_offset c + 2) (skipn 3 v.(timerImagePadding)).

Lemma timer_object_rep_split_type : forall c p v,
  timer_object_rep c p v |--
    p # UChar |-> v.(timerImageType) ** timer_object_rep_without_type c p v.
Proof. intros; unfold timer_object_rep, timer_object_rep_without_type; entailer!. Qed.

Lemma timer_object_rep_merge_type : forall c p v,
  p # UChar |-> v.(timerImageType) ** timer_object_rep_without_type c p v |--
    timer_object_rep c p v.
Proof. intros; unfold timer_object_rep, timer_object_rep_without_type; entailer!. Qed.

Definition timer_id_pointer (sg : StableGlobVars) (ids : list TimerID) : addr :=
  match ids with [] => 0 | i :: _ => timer_pool_addr sg i end.
Fixpoint timer_wheel_rep_from (sg : StableGlobVars) (p : addr) (wheel : list (list TimerID)) : Assertion :=
  match wheel with
  | [] => emp
  | ids :: rest => p # Ptr |-> timer_id_pointer sg ids **
    (p + 4) # UShort |-> Z.of_nat (List.length ids) **
    UCharArray.undef_full (p + 6) 2 ** timer_wheel_rep_from sg (p + 8) rest
  end.
Definition timer_images_rep (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  store_map (fun i v => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v) s.(timerImages).
Definition timer_images_without (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID) : Assertion :=
  store_map_missing_i (fun i v => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v) s.(timerImages) i.
Definition timer_globals_rep (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg s.(timerFree) **
  sg.(g_OSTmrFree) # UShort |-> s.(timerFreeCount) **
  sg.(g_OSTmrUsed) # UShort |-> s.(timerUsedCount) **
  sg.(g_OSTmrTime) # UInt |-> s.(timerTime) **
  sg.(g_OSTmrSem) # Ptr |-> s.(timerSem) **
  sg.(g_OSTmrSemSignal) # Ptr |-> s.(timerSignalSem).
Definition timer_raw_rep (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  timer_images_rep sg s **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) **
  timer_globals_rep sg s.

(** The scheduler-protected pool part, separate from globals needed by
    the timer service and its ISR signal path. *)
Definition timer_pool_rep (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  timer_images_rep sg s **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) **
  sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg s.(timerFree) **
  sg.(g_OSTmrFree) # UShort |-> s.(timerFreeCount) **
  sg.(g_OSTmrUsed) # UShort |-> s.(timerUsedCount).

Definition timer_service_globals_rep (sg : StableGlobVars)
  (s : GlobTimerState) : Assertion :=
  sg.(g_OSTmrTime) # UInt |-> s.(timerTime) **
  sg.(g_OSTmrSem) # Ptr |-> s.(timerSem) **
  sg.(g_OSTmrSemSignal) # Ptr |-> s.(timerSignalSem).

Lemma timer_raw_rep_split_pool : forall sg s,
  timer_raw_rep sg s --||-- timer_pool_rep sg s ** timer_service_globals_rep sg s.
Proof.
  intros; unfold timer_raw_rep, timer_globals_rep, timer_pool_rep,
    timer_service_globals_rep; split; entailer!.
Qed.

(** Timer APIs read the type byte before their ISR rejection.  The pool
    body below therefore excludes ALL type cells, not just the current
    target's. Private allocations remain absent from both map projections,
    exactly as they are absent from timerImages. These are spatial splits,
    not rules for obtaining a loan from a shared-region handle. *)
Definition timer_image_types (images : TimerID -> option TimerImage)
  : TimerID -> option Z := fun i => option_map timerImageType (images i).

Definition timer_images_type_rep (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  store_map (fun i ty => timer_pool_addr sg i # UChar |-> ty)
    (timer_image_types s.(timerImages)).

Definition timer_images_rep_without_types (sg : StableGlobVars)
  (s : GlobTimerState) : Assertion :=
  store_map (fun i v => timer_object_rep_without_type sg.(osKernelConfig)
    (timer_pool_addr sg i) v) s.(timerImages).

Definition timer_images_without_types_missing_object (sg : StableGlobVars)
  (s : GlobTimerState) (i : TimerID) : Assertion :=
  store_map_missing_i (fun j v => timer_object_rep_without_type sg.(osKernelConfig)
    (timer_pool_addr sg j) v) s.(timerImages) i.

Definition timer_pool_rep_without_types (sg : StableGlobVars)
  (s : GlobTimerState) : Assertion :=
  timer_images_rep_without_types sg s **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) **
  sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg s.(timerFree) **
  sg.(g_OSTmrFree) # UShort |-> s.(timerFreeCount) **
  sg.(g_OSTmrUsed) # UShort |-> s.(timerUsedCount).

Lemma timer_images_rep_split_types : forall sg s,
  timer_images_rep sg s --||--
  timer_images_type_rep sg s ** timer_images_rep_without_types sg s.
Proof.
  intros; unfold timer_images_rep, timer_images_type_rep,
    timer_images_rep_without_types, timer_image_types.
  pose proof (TimerFieldStorage.store_map_value_map TimerID TimerImage Z
    (fun i ty => timer_pool_addr sg i # UChar |-> ty) timerImageType
    (timerImages s)) as Htypes.
  pose proof (TimerFieldStorage.store_map_sepcon TimerID TimerImage
    (fun i v => timer_pool_addr sg i # UChar |-> timerImageType v)
    (fun i v => timer_object_rep_without_type (osKernelConfig sg) (timer_pool_addr sg i) v)
    (timerImages s)) as Hsplit.
  split.
  - eapply derivable1_trans with (y := store_map
      (fun i v => timer_pool_addr sg i # UChar |-> timerImageType v **
        timer_object_rep_without_type (osKernelConfig sg) (timer_pool_addr sg i) v)
      (timerImages s)).
    + apply TimerFieldStorage.store_map_mono; intros; apply timer_object_rep_split_type.
    + rewrite Hsplit, Htypes; reflexivity.
  - rewrite <- Htypes, <- Hsplit.
    apply TimerFieldStorage.store_map_mono; intros; apply timer_object_rep_merge_type.
Qed.

Lemma timer_pool_rep_split_types : forall sg s,
  timer_pool_rep sg s --||--
  timer_images_type_rep sg s ** timer_pool_rep_without_types sg s.
Proof.
  intros; unfold timer_pool_rep, timer_pool_rep_without_types.
  rewrite timer_images_rep_split_types; split; entailer!.
Qed.

Lemma timer_images_without_types_split_object : forall sg s i v,
  s.(timerImages) i = Some v -> timer_images_rep_without_types sg s |--
  timer_object_rep_without_type sg.(osKernelConfig) (timer_pool_addr sg i) v **
  timer_images_without_types_missing_object sg s i.
Proof.
  intros; unfold timer_images_rep_without_types, timer_images_without_types_missing_object.
  sep_apply_l_atomic (store_map_split
    (fun j w => timer_object_rep_without_type (osKernelConfig sg) (timer_pool_addr sg j) w)
    i v _ H); entailer!.
Qed.

Lemma timer_images_without_types_merge_updated_object : forall sg s post i v,
  post.(timerImages) i = Some v ->
  (forall j, j <> i -> s.(timerImages) j = post.(timerImages) j) ->
  timer_object_rep_without_type sg.(osKernelConfig) (timer_pool_addr sg i) v **
  timer_images_without_types_missing_object sg s i |-- timer_images_rep_without_types sg post.
Proof.
  intros sg s post i v Hlookup Hframe.
  unfold timer_images_rep_without_types, timer_images_without_types_missing_object.
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun j w => timer_object_rep_without_type (osKernelConfig sg) (timer_pool_addr sg j) w)
    _ _ i Hframe)).
  sep_apply_l_atomic (store_map_merge
    (fun j w => timer_object_rep_without_type (osKernelConfig sg) (timer_pool_addr sg j) w)
    i v _ Hlookup); entailer!.
Qed.

Definition timer_allocated_slots (s : GlobTimerState) : TimerID -> option unit :=
  fun i => match s.(timerUsed) i, s.(timerPrivate) i with
    | None, None => None | _, _ => Some tt end.
Definition timer_wheel_member (s : GlobTimerState) (i : TimerID) : Prop :=
  In i (concat s.(timerWheel)).
Definition timer_wheel_valid (sg : StableGlobVars) (s : GlobTimerState) : Prop :=
  Z.of_nat (List.length s.(timerWheel)) = sg.(osKernelConfig).(cfgTimerWheelSize) /\
  NoDup (concat s.(timerWheel)) /\
  (forall i, timer_wheel_member s i <->
    exists t, s.(timerUsed) i = Some t /\ t.(timerState) = TimerRunning) /\
  (forall n row pre i rest, nth_error s.(timerWheel) n = Some row -> row = pre ++ i :: rest ->
    exists t v, s.(timerUsed) i = Some t /\ s.(timerImages) i = Some v /\
      timer_spoke sg.(osKernelConfig) t.(timerMatch) = Z.of_nat n /\
      v.(timerImageNext) = timer_id_pointer sg rest /\
      v.(timerImagePrev) = match rev pre with [] => 0 | j :: _ => timer_pool_addr sg j end).
Definition valid_timer_state (sg : StableGlobVars) (s : GlobTimerState) : Prop :=
  kernel_pool_partition sg.(osKernelConfig).(cfgMaxTimers) s.(timerFree) (timer_allocated_slots s) /\
  timer_wheel_valid sg s /\ 0 <= s.(timerTime) < 4294967296 /\
  s.(timerFreeCount) = Z.of_nat (List.length s.(timerFree)) /\
  s.(timerUsedCount) + s.(timerFreeCount) = sg.(osKernelConfig).(cfgMaxTimers) /\
  0 <= s.(timerFreeCount) < 65536 /\ 0 <= s.(timerUsedCount) < 65536 /\
  (forall i t, s.(timerUsed) i = Some t ->
    valid_timer_object t /\ (t.(timerGeneration) < s.(timerNextGeneration))%nat /\
    s.(timerPrivate) i = None /\
    exists v, s.(timerImages) i = Some v /\
      v = timer_object_image t v.(timerImageNext) v.(timerImagePrev) v.(timerImagePadding)) /\
  (forall i p, s.(timerPrivate) i = Some p -> s.(timerUsed) i = None /\ s.(timerImages) i = None) /\
  (forall i, s.(timerPrivate) i = None ->
    ((exists v, s.(timerImages) i = Some v) <-> 0 <= i < sg.(osKernelConfig).(cfgMaxTimers))) /\
  (forall i v, s.(timerImages) i = Some v -> List.length v.(timerImagePadding) = 5%nat) /\
  (forall pre i rest, s.(timerFree) = pre ++ i :: rest ->
    exists v, s.(timerImages) i = Some v /\ v.(timerImageType) = 100 /\
      v.(timerImageState) = 0 /\ v.(timerImageNext) = timer_id_pointer sg rest /\ v.(timerImagePrev) = 0).
(** The first OSInit call starts with no published Timer objects and BSS
    scalar globals.  This is not a contract for repeated/reentrant OSInit.
    Disabled configurations use the same empty ghost value but own no
    Timer bytes; enabled, not-yet-initialized configurations own both
    real arrays and every scalar/handle cell through the raw boot rep. *)
Definition timer_uninitialized : GlobTimerState :=
  {| timerUsed := fun _ => None; timerFree := []; timerImages := fun _ => None;
     timerPrivate := fun _ => None; timerWheel := []; timerTime := 0;
     timerFreeCount := 0; timerUsedCount := 0; timerSem := 0; timerSignalSem := 0;
     timerTask := None; timerNextGeneration := 0; timerInitPhase := TimerUninitialized |}.
Definition timer_uninitialized_rep (sg : StableGlobVars) : Assertion :=
  UCharArray.undef_full sg.(g_OSTmrTbl)
    (timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) **
  UCharArray.undef_full sg.(g_OSTmrWheelTbl)
    (8 * sg.(osKernelConfig).(cfgTimerWheelSize)) **
  timer_globals_rep sg timer_uninitialized.
Definition valid_timer_initialization_phase (s : GlobTimerState) : Prop :=
  match s.(timerInitPhase) with
  | TimerUninitialized => s = timer_uninitialized
  | TimerPoolInitialized => s.(timerSem) = 0 /\ s.(timerSignalSem) = 0 /\ s.(timerTask) = None
  | TimerLockAttempted => s.(timerSignalSem) = 0 /\ s.(timerTask) = None
  | TimerSignalAttempted => s.(timerTask) = None
  | TimerInitializationFinished => True
  end.
Definition valid_timer_configuration (sg : StableGlobVars) (s : GlobTimerState) : Prop :=
  if sg.(osKernelConfig).(cfgTimerEnabled) then
    match s.(timerInitPhase) with
    | TimerUninitialized => s = timer_uninitialized
    | _ => valid_timer_state sg s /\ valid_timer_initialization_phase s
    end
  else s = timer_uninitialized.
Definition timer_configured_rep (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  if sg.(osKernelConfig).(cfgTimerEnabled) then
    match s.(timerInitPhase) with
    | TimerUninitialized => timer_uninitialized_rep sg
    | _ => timer_raw_rep sg s
    end
  else emp.
Definition timer_api_initialized (s : GlobTimerState) : Prop :=
  s.(timerInitPhase) = TimerInitializationFinished.
Definition timer_inv (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  coq_prop (valid_timer_configuration sg s) && timer_configured_rep sg s.
Lemma timer_disabled_configuration_valid : forall sg,
  sg.(osKernelConfig).(cfgTimerEnabled) = false -> valid_timer_configuration sg timer_uninitialized.
Proof. intros; unfold valid_timer_configuration; rewrite H; reflexivity. Qed.
Lemma timer_uninitialized_configuration_valid : forall sg,
  valid_timer_configuration sg timer_uninitialized.
Proof. intros; unfold valid_timer_configuration; destruct (cfgTimerEnabled (osKernelConfig sg)); reflexivity. Qed.
Lemma timer_uninitialized_enabled_owns_arrays : forall sg,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_configured_rep sg timer_uninitialized = timer_uninitialized_rep sg.
Proof. intros; unfold timer_configured_rep; rewrite H; reflexivity. Qed.
Lemma timer_initialized_configuration_iff : forall sg s,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s ->
  (valid_timer_configuration sg s <-> valid_timer_state sg s).
Proof.
  intros sg s He Hp; unfold timer_api_initialized in Hp.
  unfold valid_timer_configuration; rewrite He, Hp; unfold valid_timer_initialization_phase; rewrite Hp; tauto.
Qed.
Lemma timer_initialized_configured_rep_eq : forall sg s,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s ->
  timer_configured_rep sg s = timer_raw_rep sg s.
Proof. intros sg s He Hp; unfold timer_api_initialized in Hp; unfold timer_configured_rep; rewrite He, Hp; reflexivity. Qed.

Lemma timer_images_split_object : forall sg s i v,
  s.(timerImages) i = Some v -> timer_images_rep sg s |--
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v ** timer_images_without sg s i.
Proof.
  intros; unfold timer_images_rep, timer_images_without.
  sep_apply_l_atomic (store_map_split
    (fun i v => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v) i v _ H); entailer!.
Qed.
Lemma timer_images_merge_object : forall sg s i v,
  s.(timerImages) i = Some v ->
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v ** timer_images_without sg s i |-- timer_images_rep sg s.
Proof.
  intros; unfold timer_images_rep, timer_images_without.
  sep_apply_l_atomic (store_map_merge
    (fun i v => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v) i v _ H); entailer!.
Qed.
Lemma timer_images_merge_updated_object : forall sg s post i v,
  post.(timerImages) i = Some v ->
  (forall j, j <> i -> s.(timerImages) j = post.(timerImages) j) ->
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v ** timer_images_without sg s i |-- timer_images_rep sg post.
Proof.
  intros sg s post i v H Hframe; unfold timer_images_rep, timer_images_without.
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun i v => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v) _ _ i Hframe)).
  sep_apply_l_atomic (store_map_merge
    (fun i v => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v) i v _ H); entailer!.
Qed.

Definition timer_raw_rep_without_type (sg : StableGlobVars)
  (s : GlobTimerState) (i : TimerID) (v : TimerImage) : Assertion :=
  timer_object_rep_without_type sg.(osKernelConfig) (timer_pool_addr sg i) v **
  timer_images_without sg s i **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) **
  timer_globals_rep sg s.

(** Structural view exposing both discriminator bytes.  It grants no
    concurrent access: OSTmrDel reads the type before OSSchedLock and the
    state afterwards, so its pre-lock observation uses the type-only view. *)
Definition timer_object_rep_without_type_state
  (c : KernelConfiguration) (p : addr) (v : TimerImage) : Assertion :=
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) **
  (p + 8) # Ptr |-> v.(timerImageArg) **
  (p + 12) # Ptr |-> v.(timerImageNext) **
  (p + 16) # Ptr |-> v.(timerImagePrev) **
  (p + 20) # UInt |-> v.(timerImageMatch) **
  (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (if c.(cfgTimerNames) then (p + 32) # Ptr |-> v.(timerImageName) else emp) **
  (p + timer_option_offset c) # UChar |-> v.(timerImageOption) **
  store_optional_bytes (p + timer_option_offset c + 2)
    (skipn 3 v.(timerImagePadding)).

Lemma timer_object_rep_split_type_state : forall c p v,
  timer_object_rep c p v |--
    p # UChar |-> v.(timerImageType) **
    (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
    timer_object_rep_without_type_state c p v.
Proof.
  intros; unfold timer_object_rep, timer_object_rep_without_type_state; entailer!.
Qed.

Lemma timer_object_rep_merge_type_state : forall c p v,
  p # UChar |-> v.(timerImageType) **
    (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
    timer_object_rep_without_type_state c p v |-- timer_object_rep c p v.
Proof.
  intros; unfold timer_object_rep, timer_object_rep_without_type_state; entailer!.
Qed.

Definition timer_raw_rep_without_type_state (sg : StableGlobVars)
  (s : GlobTimerState) (i : TimerID) (v : TimerImage) : Assertion :=
  timer_object_rep_without_type_state sg.(osKernelConfig)
    (timer_pool_addr sg i) v **
  timer_images_without sg s i **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) **
  timer_globals_rep sg s.

Lemma timer_raw_rep_split_type : forall sg s i v,
  s.(timerImages) i = Some v ->
  timer_raw_rep sg s |--
    timer_pool_addr sg i # UChar |-> v.(timerImageType) **
    timer_raw_rep_without_type sg s i v.
Proof.
  intros sg s i v Himage; unfold timer_raw_rep, timer_raw_rep_without_type.
  sep_apply_l_atomic (timer_images_split_object sg s i v Himage).
  sep_apply_l_atomic (timer_object_rep_split_type sg.(osKernelConfig) (timer_pool_addr sg i) v).
  entailer!.
Qed.

(** Expose both bytes when the caller already owns the timer representation.
    The split preserves every other field and must be applied at the state
    whose ownership the surrounding synchronization protocol supplies. *)
Lemma timer_raw_rep_split_type_state : forall sg s i v,
  s.(timerImages) i = Some v ->
  timer_raw_rep sg s |--
    timer_pool_addr sg i # UChar |-> v.(timerImageType) **
    (timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1) # UChar |->
      v.(timerImageState) **
    timer_raw_rep_without_type_state sg s i v.
Proof.
  intros sg s i v Himage; unfold timer_raw_rep, timer_raw_rep_without_type_state.
  sep_apply_l_atomic (timer_images_split_object sg s i v Himage).
  sep_apply_l_atomic
    (timer_object_rep_split_type_state sg.(osKernelConfig)
      (timer_pool_addr sg i) v).
  entailer!.
Qed.

Lemma timer_raw_rep_merge_type_state : forall sg s i v,
  s.(timerImages) i = Some v ->
  timer_pool_addr sg i # UChar |-> v.(timerImageType) **
    (timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1) # UChar |->
      v.(timerImageState) **
    timer_raw_rep_without_type_state sg s i v |-- timer_raw_rep sg s.
Proof.
  intros sg s i v Himage; unfold timer_raw_rep, timer_raw_rep_without_type_state.
  sep_apply_l_atomic
    (timer_object_rep_merge_type_state sg.(osKernelConfig)
      (timer_pool_addr sg i) v).
  sep_apply_l_atomic (timer_images_merge_object sg s i v Himage).
  entailer!.
Qed.

Lemma timer_raw_rep_merge_type : forall sg s i v,
  s.(timerImages) i = Some v ->
  timer_pool_addr sg i # UChar |-> v.(timerImageType) **
    timer_raw_rep_without_type sg s i v |-- timer_raw_rep sg s.
Proof.
  intros sg s i v Himage; unfold timer_raw_rep, timer_raw_rep_without_type.
  sep_apply_l_atomic (timer_object_rep_merge_type sg.(osKernelConfig) (timer_pool_addr sg i) v).
  sep_apply_l_atomic (timer_images_merge_object sg s i v Himage); entailer!.
Qed.

Lemma timer_configured_rep_split_type : forall sg s i v,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s ->
  s.(timerImages) i = Some v ->
  timer_configured_rep sg s |--
    timer_pool_addr sg i # UChar |-> v.(timerImageType) **
    timer_raw_rep_without_type sg s i v.
Proof.
  intros sg s i v Henabled Hinitialized Himage.
  rewrite (timer_initialized_configured_rep_eq sg s Henabled Hinitialized).
  apply timer_raw_rep_split_type; exact Himage.
Qed.

Lemma timer_configured_rep_merge_type : forall sg s i v,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s ->
  s.(timerImages) i = Some v ->
  timer_pool_addr sg i # UChar |-> v.(timerImageType) **
    timer_raw_rep_without_type sg s i v |-- timer_configured_rep sg s.
Proof.
  intros sg s i v Henabled Hinitialized Himage.
  rewrite (timer_initialized_configured_rep_eq sg s Henabled Hinitialized).
  apply timer_raw_rep_merge_type; exact Himage.
Qed.

Definition timer_initial_image (sg : StableGlobVars) (name : addr) (i : TimerID) : TimerImage :=
  {| timerImageType := 100; timerImageCallback := 0; timerImageArg := 0;
     timerImageNext := match kernel_list_next (Zrange 0 sg.(osKernelConfig).(cfgMaxTimers)) i with
       | None => 0 | Some j => timer_pool_addr sg j end;
     timerImagePrev := 0; timerImageMatch := 0; timerImageDelay := 0; timerImagePeriod := 0;
     timerImageName := name; timerImageOption := 0; timerImageState := 0;
     timerImagePadding := repeat (Some 0) 5 |}.
Definition timer_initial (sg : StableGlobVars) (name sem signal_sem : addr)
  (task : option (TaskID * nat)) : GlobTimerState :=
  {| timerUsed := fun _ => None; timerFree := Zrange 0 sg.(osKernelConfig).(cfgMaxTimers);
     timerImages := fun i => if andb (0 <=? i) (i <? sg.(osKernelConfig).(cfgMaxTimers))
       then Some (timer_initial_image sg name i) else None;
     timerPrivate := fun _ => None;
     timerWheel := repeat [] (Z.to_nat sg.(osKernelConfig).(cfgTimerWheelSize));
     timerTime := 0; timerFreeCount := sg.(osKernelConfig).(cfgMaxTimers); timerUsedCount := 0;
     timerSem := sem; timerSignalSem := signal_sem; timerTask := task; timerNextGeneration := 0;
     timerInitPhase := TimerInitializationFinished |}.
Lemma timer_empty_wheel_concat : forall n, concat (repeat (@nil TimerID) n) = [].
Proof. induction n; simpl; auto. Qed.
Lemma timer_initial_wheel_valid : forall sg name sem signal_sem task,
  0 <= sg.(osKernelConfig).(cfgTimerWheelSize) ->
  timer_wheel_valid sg (timer_initial sg name sem signal_sem task).
Proof.
  intros sg name sem signal_sem task Hwheel; unfold timer_wheel_valid, timer_initial; simpl.
  rewrite timer_empty_wheel_concat; split; [rewrite repeat_length, Z2Nat.id by lia; reflexivity|].
  split; [constructor|]. split.
  - intro i; unfold timer_wheel_member, timer_initial; simpl; rewrite timer_empty_wheel_concat.
    split; [contradiction|intros [t [H _]]; discriminate].
  - intros n row pre i rest Hrow Hlist.
    apply nth_error_In in Hrow; apply repeat_spec in Hrow; subst row.
    symmetry in Hlist; apply app_eq_nil in Hlist; destruct Hlist as [_ H]; discriminate.
Qed.
Lemma timer_initial_valid : forall sg name sem signal_sem task,
  0 <= sg.(osKernelConfig).(cfgMaxTimers) < 65536 ->
  0 <= sg.(osKernelConfig).(cfgTimerWheelSize) ->
  valid_timer_state sg (timer_initial sg name sem signal_sem task).
Proof.
  intros sg name sem signal_sem task Hcap Hwheel; unfold valid_timer_state.
  split; [apply kernel_pool_initial_partition|]. split; [apply timer_initial_wheel_valid; exact Hwheel|].
  cbv beta iota zeta delta [timer_initial timerTime timerFreeCount timerUsedCount
    timerFree timerUsed timerPrivate timerImages].
  split; [change (0 <= 0 < 4294967296); lia|]. split.
  - change (cfgMaxTimers (osKernelConfig sg) =
      Z.of_nat (List.length (Zrange 0 (cfgMaxTimers (osKernelConfig sg))))).
    rewrite kernel_zrange_length, Z2Nat.id by lia; lia.
  - split; [change (0 + cfgMaxTimers (osKernelConfig sg) = cfgMaxTimers (osKernelConfig sg)); lia|].
    split; [exact Hcap|]. split; [change (0 <= 0 < 65536); lia|].
    split; [intros; discriminate|]. split; [intros; discriminate|]. split.
    + intros i _; destruct (andb (0 <=? i) (i <? cfgMaxTimers (osKernelConfig sg))) eqn:E.
      * apply Bool.andb_true_iff in E; destruct E as [Hl Hh].
        apply Z.leb_le in Hl; apply Z.ltb_lt in Hh; split; [intros; lia|eauto].
      * split; [intros [v H]; discriminate|]. intros [Hl Hh].
        assert (andb (0 <=? i) (i <? cfgMaxTimers (osKernelConfig sg)) = true)
          by (apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia); congruence.
    + split.
      * intros i v H; destruct (andb (0 <=? i) (i <? cfgMaxTimers (osKernelConfig sg))); [|discriminate].
        inversion H; reflexivity.
      * intros pre i rest Hlist.
        assert (Hi : 0 <= i < cfgMaxTimers (osKernelConfig sg)).
        { apply In_Zrange; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
        assert (Hb : andb (0 <=? i) (i <? cfgMaxTimers (osKernelConfig sg)) = true)
          by (apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        rewrite Hb; exists (timer_initial_image sg name i); split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
        unfold timer_initial_image; simpl; rewrite Hlist, kernel_list_next_at.
        -- destruct rest; reflexivity.
        -- pose proof (NoDup_Zrange 0 (cfgMaxTimers (osKernelConfig sg))) as Hnd.
           rewrite Hlist in Hnd; exact Hnd.
Qed.
Lemma timer_initial_has_object : forall sg name sem signal_sem task,
  0 < sg.(osKernelConfig).(cfgMaxTimers) ->
  exists v, (timer_initial sg name sem signal_sem task).(timerImages) 0 = Some v.
Proof.
  intros sg name sem signal_sem task H; unfold timer_initial; simpl.
  assert (Hlt : (0 <? cfgMaxTimers (osKernelConfig sg)) = true) by (apply Z.ltb_lt; lia).
  rewrite Hlt; eauto.
Qed.

Definition timer_allocate (s : GlobTimerState)
  : option (TimerID * TimerPrivateAllocation * GlobTimerState) :=
  match s.(timerFree) with
  | [] => None
  | i :: rest => match s.(timerImages) i with
    | None => None
    | Some old =>
      let private := {| timerPrivateGeneration := s.(timerNextGeneration);
        timerPrivateImage := timer_image_set_links old 0 0 |} in
      Some (i, private, {| timerUsed := s.(timerUsed); timerFree := rest;
        timerImages := kernel_map_set s.(timerImages) i None;
        timerPrivate := kernel_map_set s.(timerPrivate) i (Some private);
        timerWheel := s.(timerWheel); timerTime := s.(timerTime);
        timerFreeCount := kernel_u16 (s.(timerFreeCount) - 1);
        timerUsedCount := kernel_u16 (s.(timerUsedCount) + 1);
        timerSem := s.(timerSem); timerSignalSem := s.(timerSignalSem); timerTask := s.(timerTask);
        timerNextGeneration := S s.(timerNextGeneration); timerInitPhase := s.(timerInitPhase) |})
    end
  end.
Lemma timer_allocate_excludes_global_image : forall s i private post,
  timer_allocate s = Some (i, private, post) ->
  post.(timerImages) i = None /\ post.(timerPrivate) i = Some private /\
  private.(timerPrivateImage).(timerImageNext) = 0 /\ private.(timerPrivateImage).(timerImagePrev) = 0.
Proof.
  intros s i private post H; unfold timer_allocate in H.
  destruct (timerFree s) as [|j rest]; [discriminate|].
  destruct (timerImages s j); [|discriminate].
  inversion H; subst; simpl; rewrite !kernel_map_set_same; auto.
Qed.
Definition timer_private_rep (sg : StableGlobVars) (i : TimerID) (private : TimerPrivateAllocation) : Assertion :=
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) private.(timerPrivateImage).
Definition timer_create_object (private : TimerPrivateAllocation) (delay period : Z)
  (mode : TimerMode) (callback arg name : addr) : TimerObjectState :=
  {| timerGeneration := private.(timerPrivateGeneration); timerDelay := delay; timerPeriod := period;
     timerMatch := private.(timerPrivateImage).(timerImageMatch); timerMode := mode; timerState := TimerStopped;
     timerCallback := callback; timerCallbackArg := arg; timerName := name |}.
Definition timer_publish (s : GlobTimerState) (i : TimerID) (private : TimerPrivateAllocation)
  (delay period : Z) (mode : TimerMode) (callback arg name : addr) : GlobTimerState :=
  let t := timer_create_object private delay period mode callback arg name in
  {| timerUsed := kernel_map_set s.(timerUsed) i (Some t); timerFree := s.(timerFree);
     timerImages := kernel_map_set s.(timerImages) i
       (Some (timer_object_image t 0 0 private.(timerPrivateImage).(timerImagePadding)));
     timerPrivate := kernel_map_set s.(timerPrivate) i None;
     timerWheel := s.(timerWheel); timerTime := s.(timerTime);
     timerFreeCount := s.(timerFreeCount); timerUsedCount := s.(timerUsedCount);
     timerSem := s.(timerSem); timerSignalSem := s.(timerSignalSem); timerTask := s.(timerTask);
     timerNextGeneration := s.(timerNextGeneration); timerInitPhase := s.(timerInitPhase) |}.
Lemma timer_publish_records_object : forall s i private delay period mode callback arg name,
  (timer_publish s i private delay period mode callback arg name).(timerUsed) i =
    Some (timer_create_object private delay period mode callback arg name) /\
  (timer_publish s i private delay period mode callback arg name).(timerPrivate) i = None.
Proof. intros; split; apply kernel_map_set_same. Qed.
Definition timer_release (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID)
  (old : TimerImage) (name : addr) : GlobTimerState :=
  {| timerUsed := kernel_map_set s.(timerUsed) i None; timerFree := i :: s.(timerFree);
     timerImages := kernel_map_set s.(timerImages) i
       (Some (timer_free_image old (timer_id_pointer sg s.(timerFree)) name));
     timerPrivate := s.(timerPrivate); timerWheel := s.(timerWheel); timerTime := s.(timerTime);
     timerFreeCount := kernel_u16 (s.(timerFreeCount) + 1);
     timerUsedCount := kernel_u16 (s.(timerUsedCount) - 1);
     timerSem := s.(timerSem); timerSignalSem := s.(timerSignalSem); timerTask := s.(timerTask);
     timerNextGeneration := s.(timerNextGeneration); timerInitPhase := s.(timerInitPhase) |}.
Lemma timer_release_removes_live_object : forall sg s i old name,
  (timer_release sg s i old name).(timerUsed) i = None.
Proof. intros; apply kernel_map_set_same. Qed.

Lemma timer_release_image_types_eq : forall sg s i old name,
  s.(timerImages) i = Some old ->
  timer_image_types (timer_release sg s i old name).(timerImages) =
    timer_image_types s.(timerImages).
Proof.
  intros sg s i old name Hlookup; apply functional_extensionality; intro j.
  unfold timer_image_types, timer_release; cbn [timerImages].
  destruct (Z.eq_dec j i) as [->|Hji].
  - rewrite kernel_map_set_same, Hlookup; reflexivity.
  - rewrite kernel_map_set_other by exact Hji; reflexivity.
Qed.

Fixpoint timer_wheel_update (wheel : list (list TimerID)) (n : nat) (row : list TimerID)
  : list (list TimerID) :=
  match wheel, n with
  | [], _ => [] | _ :: rest, O => row :: rest
  | old :: rest, S n' => old :: timer_wheel_update rest n' row
  end.
Lemma timer_wheel_update_length : forall wheel n row,
  List.length (timer_wheel_update wheel n row) = List.length wheel.
Proof. induction wheel; intros [|n] row; simpl; auto. Qed.
Lemma timer_wheel_update_same : forall wheel n row,
  (n < List.length wheel)%nat -> nth_error (timer_wheel_update wheel n row) n = Some row.
Proof.
  induction wheel; intros [|n] row H; simpl in *; try lia; auto.
  apply IHwheel; lia.
Qed.
Lemma timer_wheel_update_other : forall wheel n k row,
  k <> n -> nth_error (timer_wheel_update wheel n row) k = nth_error wheel k.
Proof.
  induction wheel; intros [|n] [|k] row H; simpl; try reflexivity; try contradiction.
  apply IHwheel; congruence.
Qed.
Definition timer_replace_wheel_objects (s : GlobTimerState)
  (used : TimerID -> option TimerObjectState) (images : TimerID -> option TimerImage)
  (wheel : list (list TimerID)) : GlobTimerState :=
  {| timerUsed := used; timerFree := s.(timerFree); timerImages := images; timerPrivate := s.(timerPrivate);
     timerWheel := wheel; timerTime := s.(timerTime); timerFreeCount := s.(timerFreeCount);
     timerUsedCount := s.(timerUsedCount); timerSem := s.(timerSem); timerSignalSem := s.(timerSignalSem);
     timerTask := s.(timerTask); timerNextGeneration := s.(timerNextGeneration);
     timerInitPhase := s.(timerInitPhase) |}.
Definition timer_pointer_index (sg : StableGlobVars) (p : addr) : TimerID :=
  (p - sg.(g_OSTmrTbl)) / timer_object_size sg.(osKernelConfig).
Lemma timer_object_size_positive : forall c, 0 < timer_object_size c.
Proof. intro c; unfold timer_object_size, timer_option_offset; destruct (cfgTimerNames c); lia. Qed.
Lemma timer_pointer_index_addr : forall sg i, timer_pointer_index sg (timer_pool_addr sg i) = i.
Proof.
  intros; unfold timer_pointer_index, timer_pool_addr.
  replace (g_OSTmrTbl sg + i * timer_object_size (osKernelConfig sg) -
    g_OSTmrTbl sg) with (i * timer_object_size (osKernelConfig sg)) by lia.
  apply Z.div_mul; pose proof (timer_object_size_positive (osKernelConfig sg)); lia.
Qed.
Definition timer_images_set_next (images : TimerID -> option TimerImage) (i : TimerID) (next : addr) :=
  kernel_map_set images i (option_map (fun v => timer_image_set_links v next v.(timerImagePrev)) (images i)).
Definition timer_images_set_prev (images : TimerID -> option TimerImage) (i : TimerID) (prev : addr) :=
  kernel_map_set images i (option_map (fun v => timer_image_set_links v v.(timerImageNext) prev) (images i)).
Definition timer_link_image (v : TimerImage) (time next : Z) : TimerImage :=
  {| timerImageType := v.(timerImageType); timerImageCallback := v.(timerImageCallback);
     timerImageArg := v.(timerImageArg); timerImageNext := next; timerImagePrev := 0;
     timerImageMatch := time; timerImageDelay := v.(timerImageDelay); timerImagePeriod := v.(timerImagePeriod);
     timerImageName := v.(timerImageName); timerImageOption := v.(timerImageOption);
     timerImageState := 3; timerImagePadding := v.(timerImagePadding) |}.
Definition timer_unlink_image (v : TimerImage) : TimerImage :=
  {| timerImageType := v.(timerImageType); timerImageCallback := v.(timerImageCallback);
     timerImageArg := v.(timerImageArg); timerImageNext := 0; timerImagePrev := 0;
     timerImageMatch := v.(timerImageMatch); timerImageDelay := v.(timerImageDelay);
     timerImagePeriod := v.(timerImagePeriod); timerImageName := v.(timerImageName);
     timerImageOption := v.(timerImageOption); timerImageState := 1; timerImagePadding := v.(timerImagePadding) |}.
(** Final image map after the new link fields and the old head's Prev
    field have been written.  This helper owns no additional resources. *)
Definition timer_wheel_prepend_images (sg : StableGlobVars)
  (images : TimerID -> option TimerImage) (i : TimerID) (v : TimerImage) (row : list TimerID) :=
  kernel_map_set (match row with [] => images | head :: _ =>
    timer_images_set_prev images head (timer_pool_addr sg i) end) i (Some v).

Definition timer_link (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID) (periodic : bool)
  : option GlobTimerState :=
  match s.(timerUsed) i, s.(timerImages) i with
  | Some t, Some old =>
    let post_t := timer_link_object s.(timerTime) periodic t in
    let spoke := Z.to_nat (timer_spoke sg.(osKernelConfig) post_t.(timerMatch)) in
    let row := nth spoke s.(timerWheel) [] in
    Some (timer_replace_wheel_objects s (kernel_map_set s.(timerUsed) i (Some post_t))
      (timer_wheel_prepend_images sg s.(timerImages) i
        (timer_link_image old post_t.(timerMatch) (timer_id_pointer sg row)) row)
      (timer_wheel_update s.(timerWheel) spoke (i :: row)))
  | _, _ => None
  end.
Definition timer_wheel_unlink_images (sg : StableGlobVars) (images : TimerID -> option TimerImage)
  (i : TimerID) (old : TimerImage) (row : list TimerID) :=
  let is_head := Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i) in
  let images1 := if is_head then images else
    timer_images_set_next images (timer_pointer_index sg old.(timerImagePrev)) old.(timerImageNext) in
  let images2 := if Z.eqb old.(timerImageNext) 0 then images1 else
    timer_images_set_prev images1 (timer_pointer_index sg old.(timerImageNext))
      (if is_head then 0 else old.(timerImagePrev)) in
  kernel_map_set images2 i (Some (timer_unlink_image old)).

Definition timer_unlink (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID) : option GlobTimerState :=
  match s.(timerUsed) i, s.(timerImages) i with
  | Some t, Some old =>
    let spoke := Z.to_nat (timer_spoke sg.(osKernelConfig) old.(timerImageMatch)) in
    let row := nth spoke s.(timerWheel) [] in
    Some (timer_replace_wheel_objects s
      (kernel_map_set s.(timerUsed) i (Some (timer_set_status t TimerStopped)))
      (timer_wheel_unlink_images sg s.(timerImages) i old row)
      (timer_wheel_update s.(timerWheel) spoke (remove Z.eq_dec i row)))
  | _, _ => None
  end.
Lemma timer_link_sets_running_match : forall sg s i periodic post,
  timer_link sg s i periodic = Some post ->
  exists t v, post.(timerUsed) i = Some t /\ post.(timerImages) i = Some v /\
    t.(timerState) = TimerRunning /\ v.(timerImageState) = 3 /\
    v.(timerImageMatch) = t.(timerMatch) /\ v.(timerImagePrev) = 0.
Proof.
  intros sg s i periodic post H; unfold timer_link in H.
  destruct (timerUsed s i), (timerImages s i); try discriminate.
  inversion H; subst; clear H.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerUsed timerImages].
  unfold timer_wheel_prepend_images.
  rewrite !kernel_map_set_same; eexists; eexists; repeat split; reflexivity.
Qed.
Lemma timer_unlink_clears_links_and_stops : forall sg s i post,
  timer_unlink sg s i = Some post ->
  exists t v, post.(timerUsed) i = Some t /\ post.(timerImages) i = Some v /\
    t.(timerState) = TimerStopped /\ v.(timerImageState) = 1 /\
    v.(timerImageNext) = 0 /\ v.(timerImagePrev) = 0.
Proof.
  intros sg s i post H; unfold timer_unlink in H.
  destruct (timerUsed s i), (timerImages s i); try discriminate.
  inversion H; subst; clear H.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerUsed timerImages].
  unfold timer_wheel_unlink_images.
  rewrite !kernel_map_set_same; eexists; eexists; repeat split; reflexivity.
Qed.
Lemma timer_link_preserves_wheel_extent : forall sg s i periodic post,
  timer_link sg s i periodic = Some post -> List.length post.(timerWheel) = List.length s.(timerWheel).
Proof.
  intros sg s i periodic post H; unfold timer_link in H.
  destruct (timerUsed s i), (timerImages s i); try discriminate.
  inversion H; subst; apply timer_wheel_update_length.
Qed.
Lemma timer_unlink_preserves_wheel_extent : forall sg s i post,
  timer_unlink sg s i = Some post -> List.length post.(timerWheel) = List.length s.(timerWheel).
Proof.
  intros sg s i post H; unfold timer_unlink in H.
  destruct (timerUsed s i), (timerImages s i); try discriminate.
  inversion H; subst; apply timer_wheel_update_length.
Qed.
Definition timer_service_advance (s : GlobTimerState) : GlobTimerState :=
  {| timerUsed := s.(timerUsed); timerFree := s.(timerFree); timerImages := s.(timerImages);
     timerPrivate := s.(timerPrivate); timerWheel := s.(timerWheel); timerTime := kernel_u32 (s.(timerTime) + 1);
     timerFreeCount := s.(timerFreeCount); timerUsedCount := s.(timerUsedCount);
     timerSem := s.(timerSem); timerSignalSem := s.(timerSignalSem); timerTask := s.(timerTask);
     timerNextGeneration := s.(timerNextGeneration); timerInitPhase := s.(timerInitPhase) |}.
Lemma timer_service_advance_time_in_range : forall s,
  0 <= (timer_service_advance s).(timerTime) < 4294967296.
Proof. intros; apply kernel_u32_in_range. Qed.
Lemma timer_service_advance_preserves_validity : forall sg s,
  valid_timer_state sg s -> valid_timer_state sg (timer_service_advance s).
Proof.
  intros sg s [Hpool [Hwheel [Htime Hrest]]]; unfold valid_timer_state.
  split; [exact Hpool|]. split; [exact Hwheel|]. split; [apply kernel_u32_in_range|exact Hrest].
Qed.
Lemma timer_allocate_preserves_counter_sum : forall s i private post,
  0 < s.(timerFreeCount) < 65536 -> 0 <= s.(timerUsedCount) < 65535 ->
  timer_allocate s = Some (i, private, post) ->
  post.(timerFreeCount) + post.(timerUsedCount) = s.(timerFreeCount) + s.(timerUsedCount).
Proof.
  intros s i private post Hfree Hused H; unfold timer_allocate in H.
  destruct (timerFree s) as [|j rest]; [discriminate|].
  destruct (timerImages s j); [|discriminate]. inversion H; subst; clear H.
  change (kernel_u16 (timerFreeCount s - 1) + kernel_u16 (timerUsedCount s + 1) =
    timerFreeCount s + timerUsedCount s).
  rewrite !kernel_u16_identity; lia.
Qed.
Lemma timer_release_preserves_counter_sum : forall sg s i old name,
  0 <= s.(timerFreeCount) < 65535 -> 0 < s.(timerUsedCount) < 65536 ->
  (timer_release sg s i old name).(timerFreeCount) + (timer_release sg s i old name).(timerUsedCount) =
  s.(timerFreeCount) + s.(timerUsedCount).
Proof.
  intros sg s i old name Hfree Hused.
  change (kernel_u16 (timerFreeCount s + 1) + kernel_u16 (timerUsedCount s - 1) =
    timerFreeCount s + timerUsedCount s).
  rewrite !kernel_u16_identity; lia.
Qed.

Lemma timer_allocate_preserves_validity : forall sg s i private post,
  sg.(osKernelConfig).(cfgMaxTimers) < 65536 -> valid_timer_state sg s ->
  timer_allocate s = Some (i, private, post) -> valid_timer_state sg post.
Proof.
  intros sg s i private post Hcap
    [[Hnd [Hrange Hslots]] [Hwheel [Htime [Hfreecount [Hsum [Hfc [Huc
      [Hused [Hprivate [Hdomain [Hpadding Hlinks]]]]]]]]]]] Hstep.
  unfold timer_allocate in Hstep.
  destruct (timerFree s) as [|j rest] eqn:E; [discriminate|].
  destruct (timerImages s j) as [old|] eqn:Ej; [|discriminate].
  inversion Hstep; subst i private post; clear Hstep.
  inversion Hnd as [|? ? Hnot Hrest]; subst.
  assert (Hj : 0 <= j < cfgMaxTimers (osKernelConfig sg)) by (apply Hrange; left; reflexivity).
  assert (Hempty : timerUsed s j = None /\ timerPrivate s j = None).
  { destruct (timerUsed s j) eqn:Eu, (timerPrivate s j) eqn:Ep; try (split; reflexivity);
      exfalso; apply (proj2 (proj1 (Hslots j) ltac:(unfold timer_allocated_slots; rewrite Eu, ?Ep; eauto))); left; reflexivity. }
  destruct Hempty as [Hempty Hprivate_empty].
  assert (Hfcpos : 0 < timerFreeCount s) by (rewrite Hfreecount; simpl; lia).
  assert (Hucnext : timerUsedCount s + 1 < 65536) by lia.
  unfold valid_timer_state; simpl.
  split.
  - unfold kernel_pool_partition, timer_allocated_slots; simpl.
    split; [exact Hrest|]. split; [intros; apply Hrange; right; assumption|].
    intros k; destruct (Z.eq_dec k j) as [->|Hne].
    + rewrite kernel_map_set_same, Hempty; split; [intros; auto|eauto].
    + rewrite kernel_map_set_other by exact Hne.
      unfold timer_allocated_slots in Hslots; rewrite Hslots; simpl; intuition congruence.
  - split.
    + destruct Hwheel as [Hlen [Hwnd [Hmember Hrow]]].
      unfold timer_wheel_valid, timer_wheel_member; simpl.
      split; [exact Hlen|]. split; [exact Hwnd|]. split; [exact Hmember|].
      intros n row pre k suffix Hn Hr; destruct (Hrow n row pre k suffix Hn Hr) as
        [t [v [Ht [Hv Hprops]]]].
      assert (Hne : k <> j) by (intro Heq; subst k; congruence).
      exists t, v; split; [exact Ht|]. split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hprops].
    + split; [exact Htime|].
      rewrite !kernel_u16_identity by lia.
      split.
      * rewrite Hfreecount; change (Z.of_nat (S (List.length rest)) - 1 = Z.of_nat (List.length rest)).
        rewrite Nat2Z.inj_succ; lia.
      * split; [lia|]. split; [lia|]. split; [lia|]. split.
        -- intros k t Ht; destruct (Hused k t Ht) as [Htvalid [Htgen [Hp [v [Hv Himage]]]]].
           assert (Hne : k <> j) by (intro Heq; subst k; congruence).
           split; [exact Htvalid|]. split; [simpl; lia|]. split.
           ++ rewrite kernel_map_set_other by exact Hne; exact Hp.
           ++ exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Himage].
        -- split.
           ++ intros k p Hp; unfold kernel_map_set in Hp; destruct (Z.eq_dec k j) as [->|Hne].
              ** split; [exact Hempty|apply kernel_map_set_same].
              ** destruct (Hprivate k p Hp) as [Hu Hv]; split; [exact Hu|].
                 rewrite kernel_map_set_other by exact Hne; exact Hv.
           ++ split.
              ** intros k Hp; unfold kernel_map_set in Hp; destruct (Z.eq_dec k j) as [->|Hne]; [discriminate|].
                 rewrite kernel_map_set_other by exact Hne; apply Hdomain; exact Hp.
              ** split.
                 --- intros k v Hv; unfold kernel_map_set in Hv.
                     destruct (Z.eq_dec k j); [discriminate|eapply Hpadding; eauto].
                 --- intros pre k suffix Hlist.
                     assert (Hne : k <> j).
                     { intro Heq; subst k; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
                     destruct (Hlinks (j :: pre) k suffix ltac:(simpl; rewrite Hlist; reflexivity)) as
                       [v [Hv Hprops]].
                     exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hprops].
Qed.

Lemma timer_publish_preserves_validity : forall sg s i private delay period mode callback arg name,
  valid_timer_state sg s -> s.(timerPrivate) i = Some private ->
  valid_timer_object (timer_create_object private delay period mode callback arg name) ->
  (private.(timerPrivateGeneration) < s.(timerNextGeneration))%nat ->
  List.length private.(timerPrivateImage).(timerImagePadding) = 5%nat ->
  valid_timer_state sg (timer_publish s i private delay period mode callback arg name).
Proof.
  intros sg s i private delay period mode callback arg name
    [[Hnd [Hrange Hslots]] [Hwheel [Htime [Hfreecount [Hsum [Hfc [Huc
      [Hused [Hprivate [Hdomain [Hpadding Hlinks]]]]]]]]]]] Hp Ht Hgen Hpad.
  destruct (Hprivate i private Hp) as [Hnone Himage_none].
  assert (Hi : 0 <= i < cfgMaxTimers (osKernelConfig sg) /\ ~ In i (timerFree s)).
  { apply (proj1 (Hslots i)); unfold timer_allocated_slots; rewrite Hnone, Hp; eauto. }
  destruct Hi as [Hi Hnot].
  unfold valid_timer_state, timer_publish; simpl.
  split.
  - unfold kernel_pool_partition, timer_allocated_slots; simpl.
    split; [exact Hnd|]. split; [exact Hrange|].
    intros j; destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite kernel_map_set_same; split; [intros; auto|eauto].
    + rewrite !kernel_map_set_other by exact Hne; exact (Hslots j).
  - split.
    + destruct Hwheel as [Hlen [Hwnd [Hmember Hrow]]].
      unfold timer_wheel_valid, timer_wheel_member; simpl.
      split; [exact Hlen|]. split; [exact Hwnd|]. split.
      * intros j; destruct (Z.eq_dec j i) as [->|Hne].
        -- rewrite kernel_map_set_same; split.
           ++ intros Hin; apply (proj1 (Hmember i)) in Hin; destruct Hin as [t [Hbad _]]; congruence.
           ++ intros [t [Heq Hrun]]; inversion Heq; subst t; discriminate.
        -- rewrite kernel_map_set_other by exact Hne; exact (Hmember j).
      * intros n row pre j rest Hn Hr; destruct (Hrow n row pre j rest Hn Hr) as
          [t [v [Ht' [Hv Hprops]]]].
        assert (Hne : j <> i) by (intro Heq; subst j; congruence).
        exists t, v; rewrite !kernel_map_set_other by exact Hne; auto.
    + split; [exact Htime|]. split; [exact Hfreecount|]. split; [exact Hsum|].
      split; [exact Hfc|]. split; [exact Huc|]. split.
      * intros j t H; unfold kernel_map_set in H; destruct (Z.eq_dec j i) as [->|Hne].
        -- inversion H; subst t; split; [exact Ht|]. split; [exact Hgen|].
           split; [apply kernel_map_set_same|]. eexists; split; [apply kernel_map_set_same|reflexivity].
        -- destruct (Hused j t H) as [Ht' [Hg [Hpr [v [Hv Hobj]]]]].
           split; [exact Ht'|]. split; [exact Hg|]. split.
           ++ rewrite kernel_map_set_other by exact Hne; exact Hpr.
           ++ exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hobj].
      * split.
        -- intros j p H; unfold kernel_map_set in H; destruct (Z.eq_dec j i) as [->|Hne]; [discriminate|].
           rewrite !kernel_map_set_other by exact Hne; eapply Hprivate; eauto.
        -- split.
           ++ intros j H; destruct (Z.eq_dec j i) as [->|Hne].
              ** rewrite kernel_map_set_same; split; [intros; exact Hi|eauto].
              ** rewrite kernel_map_set_other in H |- * by exact Hne; apply Hdomain; exact H.
           ++ split.
              ** intros j v H; unfold kernel_map_set in H; destruct (Z.eq_dec j i) as [->|Hne].
                 --- inversion H; subst v; exact Hpad.
                 --- eapply Hpadding; eauto.
              ** intros pre j rest Hlist.
                 assert (Hne : j <> i).
                 { intro Heq; subst j; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
                 destruct (Hlinks pre j rest Hlist) as [v [Hv Hprops]].
                 exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hprops].
Qed.

(** The allocated generation and padding are derived from the actual Alloc
    step, not added as caller assumptions.  The caller still has to establish
    validity of the fields written during initialization before publication. *)
Lemma timer_allocate_publish_preserves_validity : forall sg s i private allocated
  delay period mode callback arg name,
  sg.(osKernelConfig).(cfgMaxTimers) < 65536 -> valid_timer_state sg s ->
  timer_allocate s = Some (i, private, allocated) ->
  valid_timer_object (timer_create_object private delay period mode callback arg name) ->
  valid_timer_state sg (timer_publish allocated i private delay period mode callback arg name).
Proof.
  intros sg s i private allocated delay period mode callback arg name Hcap Hvalid Hstep Hobject.
  pose proof (timer_allocate_preserves_validity sg s i private allocated Hcap Hvalid Hstep)
    as Hallocated.
  destruct (timer_allocate_excludes_global_image s i private allocated Hstep) as [_ [Hprivate _]].
  eapply timer_publish_preserves_validity; [exact Hallocated|exact Hprivate|exact Hobject| |].
  - unfold timer_allocate in Hstep.
    destruct (timerFree s) as [|j rest]; [discriminate|].
    destruct (timerImages s j) as [old|]; [|discriminate].
    inversion Hstep; subst; simpl; lia.
  - assert (Hpadding : forall j old, timerImages s j = Some old ->
        List.length old.(timerImagePadding) = 5%nat).
    { unfold valid_timer_state in Hvalid; tauto. }
    unfold timer_allocate in Hstep.
    destruct (timerFree s) as [|j rest]; [discriminate|].
    destruct (timerImages s j) as [old|] eqn:Hold; [|discriminate].
    inversion Hstep; subst; simpl; eapply Hpadding; exact Hold.
Qed.

Lemma timer_release_preserves_validity : forall sg s i t old name,
  sg.(osKernelConfig).(cfgMaxTimers) < 65536 -> valid_timer_state sg s ->
  s.(timerUsed) i = Some t -> s.(timerImages) i = Some old -> t.(timerState) <> TimerRunning ->
  valid_timer_state sg (timer_release sg s i old name).
Proof.
  intros sg s i t old name Hcap Hvalid Ht Hold Hst.
  destruct Hvalid as [Hpool [Hwheel [Htime [Hfreecount [Hsum [Hfc [Huc
    [Hused [Hprivate [Hdomain [Hpadding Hlinks]]]]]]]]]]].
  destruct Hpool as [Hnd [Hrange Hslots]].
  destruct (Hused i t Ht) as [Htvalid [Htgen [Hpriv [v [Hv Hobj]]]]].
  rewrite Hold in Hv; inversion Hv; subst v; clear Hv.
  assert (Halloc : timer_allocated_slots s i = Some tt) by (unfold timer_allocated_slots; rewrite Ht; reflexivity).
  destruct (proj1 (Hslots i) (ex_intro _ tt Halloc)) as [Hi Hnot].
  assert (Hcount_bound : Z.of_nat (List.length (i :: timerFree s)) <= cfgMaxTimers (osKernelConfig sg)).
  { apply (proj2 (kernel_pool_free_count_bound unit (cfgMaxTimers (osKernelConfig sg)) (i :: timerFree s)
      (kernel_map_set (timer_allocated_slots s) i None) ltac:(lia)
      (kernel_pool_release_preserves_partition unit (cfgMaxTimers (osKernelConfig sg))
        (timerFree s) (timer_allocated_slots s) i tt
        ltac:(split; [exact Hnd|]; split; assumption) Halloc))). }
  change (Z.of_nat (S (List.length (timerFree s))) <= cfgMaxTimers (osKernelConfig sg)) in Hcount_bound.
  rewrite Nat2Z.inj_succ in Hcount_bound.
  assert (Husedpos : 0 < timerUsedCount s) by lia.
  assert (Hfree_next : timerFreeCount s + 1 < 65536) by lia.
  destruct Hwheel as [Hlen [Hwnd [Hmember Hrow]]].
  assert (Hnotwheel : ~ In i (concat (timerWheel s))).
  { intro Hin; apply (proj1 (Hmember i)) in Hin; destruct Hin as [q [Hq Hrun]].
    rewrite Ht in Hq; inversion Hq; subst q; contradiction. }
  unfold valid_timer_state, timer_release; simpl.
  split.
  - unfold kernel_pool_partition, timer_allocated_slots; simpl.
    split; [constructor; assumption|]. split.
    + intros j [->|Hin]; [exact Hi|apply Hrange; exact Hin].
    + intros j; destruct (Z.eq_dec j i) as [->|Hne].
      * rewrite kernel_map_set_same, Hpriv; split.
        -- intros [x H]; discriminate.
        -- intros [_ H]; exfalso; apply H; left; reflexivity.
      * rewrite kernel_map_set_other by exact Hne.
        unfold timer_allocated_slots in Hslots; rewrite Hslots; simpl; intuition congruence.
  - split.
    + unfold timer_wheel_valid, timer_wheel_member; simpl.
      split; [exact Hlen|]. split; [exact Hwnd|]. split.
      * intros j; destruct (Z.eq_dec j i) as [->|Hne].
        -- rewrite kernel_map_set_same; split; [contradiction|intros [q [H _]]; discriminate].
        -- rewrite kernel_map_set_other by exact Hne; exact (Hmember j).
      * intros n row pre j rest Hn Hr.
        assert (Hne : j <> i).
        { intro Heq; subst j; apply Hnotwheel; apply in_concat; exists row; split.
          - eapply nth_error_In; exact Hn.
          - rewrite Hr; apply in_or_app; right; left; reflexivity. }
        destruct (Hrow n row pre j rest Hn Hr) as [q [v [Hq [Hv Hprops]]]].
        exists q, v; rewrite !kernel_map_set_other by exact Hne; auto.
    + split; [exact Htime|]. rewrite !kernel_u16_identity by lia.
      split.
      * change (timerFreeCount s + 1 = Z.of_nat (S (List.length (timerFree s)))).
        rewrite Nat2Z.inj_succ; lia.
      * split; [lia|]. split; [lia|]. split; [lia|]. split.
        -- intros j q Hq; unfold kernel_map_set in Hq; destruct (Z.eq_dec j i) as [->|Hne]; [discriminate|].
           destruct (Hused j q Hq) as [Hqv [Hqg [Hqp [v [Hv Himage]]]]].
           split; [exact Hqv|]. split; [exact Hqg|]. split; [exact Hqp|].
           exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Himage].
        -- split.
           ++ intros j p Hp; assert (Hne : j <> i) by (intro Heq; subst j; congruence).
              rewrite !kernel_map_set_other by exact Hne; eapply Hprivate; eauto.
           ++ split.
              ** intros j Hp; destruct (Z.eq_dec j i) as [->|Hne].
                 --- rewrite kernel_map_set_same; split; [intros; exact Hi|eauto].
                 --- rewrite kernel_map_set_other by exact Hne; apply Hdomain; exact Hp.
              ** split.
                 --- intros j v Hv; unfold kernel_map_set in Hv; destruct (Z.eq_dec j i) as [->|Hne].
                     +++ inversion Hv; subst v; exact (Hpadding i old Hold).
                     +++ eapply Hpadding; eauto.
                 --- intros pre j rest Hlist; destruct pre as [|k pre].
                     +++ inversion Hlist; subst j rest; eexists; split; [apply kernel_map_set_same|].
                         unfold timer_free_image; simpl; split; [rewrite Hobj; reflexivity|auto].
                     +++ inversion Hlist; subst k; clear Hlist.
                         assert (Hne : j <> i).
                         { intro Heq; subst j; apply Hnot; match goal with H : timerFree s = _ |- _ => rewrite H end.
                           apply in_or_app; right; left; reflexivity. }
                         destruct (Hlinks pre j rest ltac:(assumption)) as [v [Hv Hprops]].
                         exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hprops].
Qed.

Definition timer_set_initialization (s : GlobTimerState) (phase : TimerInitializationPhase)
  (sem signal_sem : Z) (task : option (TaskID * nat)) : GlobTimerState :=
  {| timerUsed := s.(timerUsed); timerFree := s.(timerFree); timerImages := s.(timerImages);
     timerPrivate := s.(timerPrivate); timerWheel := s.(timerWheel); timerTime := s.(timerTime);
     timerFreeCount := s.(timerFreeCount); timerUsedCount := s.(timerUsedCount);
     timerSem := sem; timerSignalSem := signal_sem; timerTask := task;
     timerNextGeneration := s.(timerNextGeneration); timerInitPhase := phase |}.
Lemma timer_set_initialization_preserves_pool_validity : forall sg s phase sem signal_sem task,
  valid_timer_state sg s -> valid_timer_state sg (timer_set_initialization s phase sem signal_sem task).
Proof. intros; exact H. Qed.

(** OS_MemClr, the free-link loop and four scalar stores precede the
    two OSSemCreate calls.  The C stores must establish the pool rep;
    constructing this pure state does not turn raw bytes into fields. *)
Definition timer_pool_initialize (sg : StableGlobVars) (name : Z) : GlobTimerState :=
  timer_set_initialization (timer_initial sg name 0 0 None) TimerPoolInitialized 0 0 None.
Lemma timer_pool_initialize_configuration_valid : forall sg name,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  0 <= sg.(osKernelConfig).(cfgMaxTimers) < 65536 -> 0 <= sg.(osKernelConfig).(cfgTimerWheelSize) ->
  valid_timer_configuration sg (timer_pool_initialize sg name).
Proof.
  intros sg name He Hcap Hwheel; unfold valid_timer_configuration; rewrite He; simpl.
  split.
  - apply timer_set_initialization_preserves_pool_validity; apply timer_initial_valid; assumption.
  - repeat split; reflexivity.
Qed.
Definition timer_record_lock_result (s : GlobTimerState) (result : Z) : option GlobTimerState :=
  match s.(timerInitPhase) with
  | TimerPoolInitialized => Some (timer_set_initialization s TimerLockAttempted result s.(timerSignalSem) s.(timerTask))
  | _ => None
  end.
Definition timer_record_signal_result (s : GlobTimerState) (result : Z) : option GlobTimerState :=
  match s.(timerInitPhase) with
  | TimerLockAttempted => Some (timer_set_initialization s TimerSignalAttempted s.(timerSem) result s.(timerTask))
  | _ => None
  end.
Definition timer_finish_initialization (s : GlobTimerState) (task_result : option (TaskID * nat))
  : option GlobTimerState :=
  match s.(timerInitPhase) with
  | TimerSignalAttempted => Some (timer_set_initialization s TimerInitializationFinished
      s.(timerSem) s.(timerSignalSem) task_result)
  | _ => None
  end.
Lemma timer_record_lock_preserves_configuration : forall sg s result post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> valid_timer_configuration sg s ->
  timer_record_lock_result s result = Some post -> valid_timer_configuration sg post.
Proof.
  intros sg s result post He Hvalid Hstep; unfold timer_record_lock_result in Hstep.
  destruct (timerInitPhase s) eqn:E; try discriminate.
  inversion Hstep; subst post; clear Hstep.
  unfold valid_timer_configuration in Hvalid |- *; rewrite He, E in Hvalid; rewrite He; simpl.
  destruct Hvalid as [Hv Hphase]; unfold valid_timer_initialization_phase in Hphase; rewrite E in Hphase.
  split; [apply timer_set_initialization_preserves_pool_validity; exact Hv|].
  unfold valid_timer_initialization_phase, timer_set_initialization; simpl; tauto.
Qed.
Lemma timer_record_signal_preserves_configuration : forall sg s result post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> valid_timer_configuration sg s ->
  timer_record_signal_result s result = Some post -> valid_timer_configuration sg post.
Proof.
  intros sg s result post He Hvalid Hstep; unfold timer_record_signal_result in Hstep.
  destruct (timerInitPhase s) eqn:E; try discriminate.
  inversion Hstep; subst post; clear Hstep.
  unfold valid_timer_configuration in Hvalid |- *; rewrite He, E in Hvalid; rewrite He; simpl.
  destruct Hvalid as [Hv Hphase]; unfold valid_timer_initialization_phase in Hphase; rewrite E in Hphase.
  split; [apply timer_set_initialization_preserves_pool_validity; exact Hv|].
  unfold valid_timer_initialization_phase, timer_set_initialization; simpl; tauto.
Qed.
Lemma timer_finish_initialization_preserves_configuration : forall sg s task_result post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> valid_timer_configuration sg s ->
  timer_finish_initialization s task_result = Some post ->
  valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s task_result post He Hvalid Hstep; unfold timer_finish_initialization in Hstep.
  destruct (timerInitPhase s) eqn:E; try discriminate.
  inversion Hstep; subst post; clear Hstep.
  unfold valid_timer_configuration in Hvalid; rewrite He, E in Hvalid; destruct Hvalid as [Hv _].
  split; [|reflexivity]. apply (proj2 (timer_initialized_configuration_iff sg
    (timer_set_initialization s TimerInitializationFinished (timerSem s) (timerSignalSem s) task_result) He eq_refl)).
  apply timer_set_initialization_preserves_pool_validity; exact Hv.
Qed.
Lemma timer_initialization_records_nullable_results : forall sg name lock signal task_result,
  exists after_lock after_signal,
    timer_record_lock_result (timer_pool_initialize sg name) lock = Some after_lock /\
    timer_record_signal_result after_lock signal = Some after_signal /\
    timer_finish_initialization after_signal task_result = Some (timer_initial sg name lock signal task_result).
Proof. intros; eexists; eexists; repeat split; reflexivity. Qed.
Lemma timer_initialization_finished_with_null_handles : forall sg name,
  timer_api_initialized (timer_initial sg name 0 0 None) /\
  (timer_initial sg name 0 0 None).(timerSem) = 0 /\
  (timer_initial sg name 0 0 None).(timerSignalSem) = 0 /\
  (timer_initial sg name 0 0 None).(timerTask) = None.
Proof. intros; repeat split; reflexivity. Qed.

Lemma timer_allocate_preserves_initialization_phase : forall s i private post,
  timer_allocate s = Some (i, private, post) -> post.(timerInitPhase) = s.(timerInitPhase).
Proof.
  intros s i private post H; unfold timer_allocate in H.
  destruct (timerFree s) as [|j rest]; [discriminate|].
  destruct (timerImages s j); [|discriminate]. inversion H; reflexivity.
Qed.
Lemma timer_allocate_preserves_configuration : forall sg s i private post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> sg.(osKernelConfig).(cfgMaxTimers) < 65536 ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  timer_allocate s = Some (i, private, post) ->
  valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i private post He Hcap Hv Hp Hstep.
  assert (Hpost : timer_api_initialized post).
  { unfold timer_api_initialized; rewrite (timer_allocate_preserves_initialization_phase _ _ _ _ Hstep); exact Hp. }
  split; [|exact Hpost]. apply (proj2 (timer_initialized_configuration_iff _ _ He Hpost)).
  eapply timer_allocate_preserves_validity; [exact Hcap| |exact Hstep].
  apply (proj1 (timer_initialized_configuration_iff _ _ He Hp)); exact Hv.
Qed.
Lemma timer_publish_preserves_configuration : forall sg s i private delay period mode callback arg name,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> valid_timer_configuration sg s -> timer_api_initialized s ->
  s.(timerPrivate) i = Some private ->
  valid_timer_object (timer_create_object private delay period mode callback arg name) ->
  (private.(timerPrivateGeneration) < s.(timerNextGeneration))%nat ->
  List.length private.(timerPrivateImage).(timerImagePadding) = 5%nat ->
  valid_timer_configuration sg (timer_publish s i private delay period mode callback arg name) /\
  timer_api_initialized (timer_publish s i private delay period mode callback arg name).
Proof.
  intros sg s i private delay period mode callback arg name He Hv Hp Hprivate Ht Hgen Hpad.
  split; [|exact Hp]. apply (proj2 (timer_initialized_configuration_iff sg
    (timer_publish s i private delay period mode callback arg name) He Hp)).
  eapply timer_publish_preserves_validity; try eassumption.
  apply (proj1 (timer_initialized_configuration_iff _ _ He Hp)); exact Hv.
Qed.
Lemma timer_release_preserves_configuration : forall sg s i t old name,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> sg.(osKernelConfig).(cfgMaxTimers) < 65536 ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  s.(timerUsed) i = Some t -> s.(timerImages) i = Some old -> t.(timerState) <> TimerRunning ->
  valid_timer_configuration sg (timer_release sg s i old name) /\
  timer_api_initialized (timer_release sg s i old name).
Proof.
  intros sg s i t old name He Hcap Hv Hp Ht Hold Hst; split; [|exact Hp].
  apply (proj2 (timer_initialized_configuration_iff sg (timer_release sg s i old name) He Hp)).
  eapply timer_release_preserves_validity; try eassumption.
  apply (proj1 (timer_initialized_configuration_iff _ _ He Hp)); exact Hv.
Qed.
Lemma timer_service_advance_preserves_configuration : forall sg s,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> valid_timer_configuration sg s -> timer_api_initialized s ->
  valid_timer_configuration sg (timer_service_advance s) /\ timer_api_initialized (timer_service_advance s).
Proof.
  intros sg s He Hv Hp; split; [|exact Hp].
  apply (proj2 (timer_initialized_configuration_iff sg (timer_service_advance s) He Hp)).
  apply timer_service_advance_preserves_validity.
  apply (proj1 (timer_initialized_configuration_iff _ _ He Hp)); exact Hv.
Qed.
Lemma timer_pool_initialized_configuration_iff : forall sg s,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> s.(timerInitPhase) <> TimerUninitialized ->
  (valid_timer_configuration sg s <-> valid_timer_state sg s /\ valid_timer_initialization_phase s).
Proof.
  intros sg s He Hp; unfold valid_timer_configuration; rewrite He; destruct (timerInitPhase s); tauto.
Qed.
Lemma timer_pool_initialized_configured_rep_eq : forall sg s,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> s.(timerInitPhase) <> TimerUninitialized ->
  timer_configured_rep sg s = timer_raw_rep sg s.
Proof.
  intros sg s He Hp; unfold timer_configured_rep; rewrite He; destruct (timerInitPhase s); tauto.
Qed.
Lemma timer_link_preserves_initialization_phase : forall sg s i periodic post,
  timer_link sg s i periodic = Some post -> post.(timerInitPhase) = s.(timerInitPhase).
Proof.
  intros sg s i periodic post H; unfold timer_link in H.
  destruct (timerUsed s i), (timerImages s i); try discriminate; inversion H; reflexivity.
Qed.
Lemma timer_unlink_preserves_initialization_phase : forall sg s i post,
  timer_unlink sg s i = Some post -> post.(timerInitPhase) = s.(timerInitPhase).
Proof.
  intros sg s i post H; unfold timer_unlink in H.
  destruct (timerUsed s i), (timerImages s i); try discriminate; inversion H; reflexivity.
Qed.

Lemma timer_wheel_update_at : forall pre row rest new,
  timer_wheel_update (pre ++ row :: rest) (List.length pre) new = pre ++ new :: rest.
Proof. induction pre; intros; simpl; [reflexivity|rewrite IHpre; reflexivity]. Qed.

Lemma timer_wheel_prepend_members : forall wheel n row i j,
  nth_error wheel n = Some row ->
  (In j (concat (timer_wheel_update wheel n (i :: row))) <-> j = i \/ In j (concat wheel)).
Proof.
  intros wheel n row i j Hrow; apply nth_error_split in Hrow.
  destruct Hrow as [pre [rest [Hwheel Hn]]]; subst wheel n.
  rewrite timer_wheel_update_at, !concat_app; simpl; rewrite !in_app_iff; simpl;
    rewrite ?in_app_iff; intuition congruence.
Qed.

Lemma timer_wheel_member_spoke : forall sg s n row i,
  timer_wheel_valid sg s -> nth_error s.(timerWheel) n = Some row -> In i row ->
  exists t, s.(timerUsed) i = Some t /\ timer_spoke sg.(osKernelConfig) t.(timerMatch) = Z.of_nat n.
Proof.
  intros sg s n row i [_ [_ [_ Hrows]]] Hrow Hin.
  apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
  destruct (Hrows n row pre i rest Hrow Hlist) as [t [v [Ht [_ [Hspoke _]]]]]; eauto.
Qed.

Lemma timer_wheel_member_unique_spoke : forall sg s n row m other i,
  timer_wheel_valid sg s -> nth_error s.(timerWheel) n = Some row ->
  nth_error s.(timerWheel) m = Some other -> In i row -> In i other -> n = m.
Proof.
  intros sg s n row m other i Hv Hrow Hother Hin Hotherin.
  destruct (timer_wheel_member_spoke _ _ _ _ _ Hv Hrow Hin) as [t [Ht Hn]].
  destruct (timer_wheel_member_spoke _ _ _ _ _ Hv Hother Hotherin) as [u [Hu Hm]].
  rewrite Ht in Hu; inversion Hu; subst u; apply Nat2Z.inj; congruence.
Qed.

Lemma timer_pool_addr_injective : forall sg i j,
  timer_pool_addr sg i = timer_pool_addr sg j -> i = j.
Proof.
  intros sg i j H; apply (f_equal (timer_pointer_index sg)) in H;
    rewrite !timer_pointer_index_addr in H; exact H.
Qed.

Lemma timer_pool_addr_in_range : forall sg i,
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  0 <= i < sg.(osKernelConfig).(cfgMaxTimers) ->
  0 < timer_pool_addr sg i /\
    timer_pool_addr sg i + timer_object_size sg.(osKernelConfig) <= 4294967296.
Proof.
  intros sg i Hlayout Hi; unfold kernel_region_valid in Hlayout; simpl in Hlayout.
  unfold timer_pool_addr; pose proof (timer_object_size_positive (osKernelConfig sg)); nia.
Qed.

Lemma timer_id_pointer_null_iff : forall sg row,
  (forall i, In i row -> timer_pool_addr sg i <> 0) ->
  (timer_id_pointer sg row = 0 <-> row = []).
Proof.
  intros sg [|i rest] H; simpl; [tauto|].
  split; [intro E; exfalso; apply (H i); [left; reflexivity|exact E]|discriminate].
Qed.

Definition timer_image_link_identity (v : TimerImage) :=
  (v.(timerImageType), v.(timerImageCallback), v.(timerImageArg), v.(timerImageMatch),
   v.(timerImageDelay), v.(timerImagePeriod), v.(timerImageName), v.(timerImageOption),
   v.(timerImageState), v.(timerImagePadding)).

Lemma timer_image_set_links_identity_eq : forall v next prev,
  timer_image_link_identity (timer_image_set_links v next prev) = timer_image_link_identity v.
Proof. reflexivity. Qed.

Lemma timer_image_set_links_object_eq : forall v t next prev,
  v = timer_object_image t v.(timerImageNext) v.(timerImagePrev) v.(timerImagePadding) ->
  timer_image_set_links v next prev = timer_object_image t next prev v.(timerImagePadding).
Proof. intros v t next prev H; rewrite H; reflexivity. Qed.

Lemma timer_link_image_object_eq : forall v t time periodic next,
  v = timer_object_image t v.(timerImageNext) v.(timerImagePrev) v.(timerImagePadding) ->
  timer_link_image v (timer_link_object time periodic t).(timerMatch) next =
    timer_object_image (timer_link_object time periodic t) next 0 v.(timerImagePadding).
Proof. intros v t time periodic next H; rewrite H; reflexivity. Qed.

Lemma timer_wheel_prepend_preserves_nodup : forall wheel n row i,
  nth_error wheel n = Some row -> NoDup (concat wheel) -> ~ In i (concat wheel) ->
  NoDup (concat (timer_wheel_update wheel n (i :: row))).
Proof.
  intros wheel n row i Hrow Hnd Hnot; apply nth_error_split in Hrow.
  destruct Hrow as [pre [rest [Hwheel Hn]]]; subst wheel n.
  rewrite timer_wheel_update_at, !concat_app; simpl.
  apply (proj2 (NoDup_Add (Add_app i (concat pre) (row ++ concat rest))));
    rewrite concat_app in Hnd, Hnot; simpl in Hnd, Hnot; auto.
Qed.

Lemma timer_wheel_row_member : forall (wheel : list (list TimerID)) n row i,
  nth_error wheel n = Some row -> In i row -> In i (concat wheel).
Proof. intros; apply in_concat; exists row; split; [eapply nth_error_In; eauto|assumption]. Qed.

Lemma timer_wheel_row_nodup : forall (wheel : list (list TimerID)) n row,
  NoDup (concat wheel) -> nth_error wheel n = Some row -> NoDup row.
Proof.
  intros wheel n row Hnd Hrow; apply nth_error_split in Hrow.
  destruct Hrow as [pre [rest [Hwheel Hn]]]; rewrite Hwheel, concat_app in Hnd; simpl in Hnd.
  apply NoDup_app_remove_l in Hnd; apply NoDup_app_remove_r in Hnd; exact Hnd.
Qed.

Lemma timer_wheel_spoke_index_in_range : forall sg s time,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 -> timer_wheel_valid sg s ->
  (Z.to_nat (timer_spoke sg.(osKernelConfig) time) < List.length s.(timerWheel))%nat.
Proof.
  intros sg s time Hsize [Hlen _]; pose proof (timer_spoke_in_range _ time Hsize) as Hr.
  apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia.
Qed.

Lemma timer_images_set_prev_lookup : forall images target prev i,
  timer_images_set_prev images target prev i = option_map (fun v =>
    if Z.eq_dec i target then timer_image_set_links v v.(timerImageNext) prev else v) (images i).
Proof.
  intros; unfold timer_images_set_prev, kernel_map_set.
  destruct (Z.eq_dec i target) as [->|Hne]; [destruct (images target)|destruct (images i)]; reflexivity.
Qed.

Lemma timer_images_set_next_lookup : forall images target next i,
  timer_images_set_next images target next i = option_map (fun v =>
    if Z.eq_dec i target then timer_image_set_links v next v.(timerImagePrev) else v) (images i).
Proof.
  intros; unfold timer_images_set_next, kernel_map_set.
  destruct (Z.eq_dec i target) as [->|Hne]; [destruct (images target)|destruct (images i)]; reflexivity.
Qed.

(** The final image map after the new timer's link fields and the old
    head's Prev field have been written.  It does not introduce another
    timer state or an ownership assumption. *)

Lemma timer_wheel_prepend_images_same : forall sg images i v row,
  timer_wheel_prepend_images sg images i v row i = Some v.
Proof. intros; apply kernel_map_set_same. Qed.

Lemma timer_wheel_prepend_images_other : forall sg images i v row j,
  j <> i -> timer_wheel_prepend_images sg images i v row j =
    option_map (fun old => match row with [] => old | head :: _ =>
      if Z.eq_dec j head then timer_image_set_links old old.(timerImageNext) (timer_pool_addr sg i)
      else old end) (images j).
Proof.
  intros sg images i v row j Hne; unfold timer_wheel_prepend_images.
  rewrite kernel_map_set_other by exact Hne; destruct row as [|head rest].
  - destruct (images j); reflexivity.
  - apply timer_images_set_prev_lookup.
Qed.

Lemma timer_id_pointer_rev_prepend : forall sg pre i,
  pre <> [] -> timer_id_pointer sg (rev (i :: pre)) = timer_id_pointer sg (rev pre).
Proof.
  intros sg pre i Hnot; simpl; destruct (rev pre) as [|j rest] eqn:E; [|reflexivity].
  exfalso; apply Hnot; apply (f_equal (@rev TimerID)) in E; rewrite rev_involutive in E; exact E.
Qed.

Lemma timer_wheel_prepend_preserves_wheel_validity : forall sg s i t new_t new_v n row,
  timer_wheel_valid sg s -> s.(timerUsed) i = Some t -> t.(timerState) <> TimerRunning ->
  nth_error s.(timerWheel) n = Some row -> new_t.(timerState) = TimerRunning ->
  timer_spoke sg.(osKernelConfig) new_t.(timerMatch) = Z.of_nat n ->
  new_v.(timerImageNext) = timer_id_pointer sg row -> new_v.(timerImagePrev) = 0 ->
  timer_wheel_valid sg (timer_replace_wheel_objects s
    (kernel_map_set s.(timerUsed) i (Some new_t))
    (timer_wheel_prepend_images sg s.(timerImages) i new_v row)
    (timer_wheel_update s.(timerWheel) n (i :: row))).
Proof.
  intros sg s i t new_t new_v n row Hvalid Ht Hst Hrow Hnewst Hnewspoke Hnewnext Hnewprev.
  pose proof Hvalid as [Hlen [Hnd [Hmembers Hrows]]].
  assert (Hnot : ~ In i (concat (timerWheel s))).
  { intro Hin; destruct (proj1 (Hmembers i) Hin) as [u [Hu Hrun]]; rewrite Ht in Hu;
      inversion Hu; subst u; contradiction. }
  assert (Hindex : (n < List.length (timerWheel s))%nat).
  { apply nth_error_Some; rewrite Hrow; discriminate. }
  assert (Hnotrow : ~ In i row) by (intro Hin; apply Hnot; eapply timer_wheel_row_member; eauto).
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  unfold timer_wheel_valid, timer_wheel_member, timer_replace_wheel_objects; simpl.
  split; [rewrite timer_wheel_update_length; exact Hlen|].
  split; [eapply timer_wheel_prepend_preserves_nodup; eauto|]. split.
  - intros j; rewrite timer_wheel_prepend_members by exact Hrow.
    destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite kernel_map_set_same; split; [intros; exists new_t; auto|auto].
    + rewrite kernel_map_set_other by exact Hne; rewrite <- Hmembers; intuition congruence.
  - intros m other pre j rest Hother Hlist; destruct (Nat.eq_dec m n) as [->|Hmn].
    + rewrite timer_wheel_update_same in Hother by exact Hindex; injection Hother as Hsame.
      rewrite <- Hsame in Hlist.
      destruct pre as [|a pre].
      * simpl in Hlist; inversion Hlist; subst j rest.
        exists new_t, new_v; split; [apply kernel_map_set_same|].
        split; [apply timer_wheel_prepend_images_same|]; auto.
      * simpl in Hlist; inversion Hlist as [[Ha Htail]]; subst a.
        destruct (Hrows n row pre j rest Hrow Htail) as [u [v [Hu [Hv [Hspoke [Hnext Hprev]]]]]].
        assert (Hji : j <> i).
        { intro E; subst j; apply Hnotrow; rewrite Htail; apply in_or_app; right; left; reflexivity. }
        rewrite kernel_map_set_other by exact Hji.
        destruct pre as [|a pre].
        -- simpl in Htail; subst row.
           exists u, (timer_image_set_links v (timerImageNext v) (timer_pool_addr sg i)); split; [exact Hu|].
           split.
           ++ rewrite timer_wheel_prepend_images_other by exact Hji; rewrite Hv; simpl.
              destruct (Z.eq_dec j j); [reflexivity|contradiction].
           ++ simpl; auto.
        -- assert (Hja : j <> a).
           { intro E; subst j; rewrite Htail in Hrownd; inversion Hrownd as [|? ? Hnothead Htailnd]; subst.
             apply Hnothead; apply in_or_app; right; left; reflexivity. }
           exists u, v; split; [exact Hu|]. split.
           ++ rewrite timer_wheel_prepend_images_other by exact Hji; rewrite Hv; rewrite ?Htail; simpl.
              destruct (Z.eq_dec j a); [contradiction|reflexivity].
           ++ split; [exact Hspoke|]. split; [exact Hnext|].
              change (timerImagePrev v = timer_id_pointer sg (rev (i :: a :: pre))).
              rewrite timer_id_pointer_rev_prepend by discriminate; exact Hprev.
    + rewrite timer_wheel_update_other in Hother by exact Hmn.
      destruct (Hrows m other pre j rest Hother Hlist) as [u [v [Hu [Hv Hfields]]]].
      assert (Hjin : In j other) by (rewrite Hlist; apply in_or_app; right; left; reflexivity).
      assert (Hji : j <> i) by (intro E; subst j; apply Hnot; eapply timer_wheel_row_member; eauto).
      exists u, v; split; [rewrite kernel_map_set_other by exact Hji; exact Hu|]. split; [|exact Hfields].
      rewrite timer_wheel_prepend_images_other by exact Hji; rewrite Hv; destruct row as [|head tail]; [reflexivity|].
      simpl; destruct (Z.eq_dec j head) as [->|Hne]; [|reflexivity].
      exfalso; apply Hmn; eapply timer_wheel_member_unique_spoke; eauto; left; reflexivity.
Qed.

Lemma timer_link_preserves_state_validity : forall sg s i t periodic post,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 -> valid_timer_state sg s ->
  s.(timerUsed) i = Some t -> t.(timerState) <> TimerRunning ->
  timer_link sg s i periodic = Some post -> valid_timer_state sg post.
Proof.
  intros sg s i t periodic post Hsize Hvalid Ht Hst Hstep.
  pose proof Hvalid as [Hpool [Hwheel [Htime [Hfreecount [Hsum [Hfc [Huc
    [Hused [Hprivate [Hdomain [Hpadding Hlinks]]]]]]]]]]].
  destruct (Hused i t Ht) as [Htvalid [Htgen [Hprivatei [old [Hold Himage]]]]].
  set (linked := timer_link_object (timerTime s) periodic t).
  set (n := Z.to_nat (timer_spoke (osKernelConfig sg) (timerMatch linked))).
  set (row := nth n (timerWheel s) []).
  assert (Hindex : (n < List.length (timerWheel s))%nat).
  { apply timer_wheel_spoke_index_in_range; assumption. }
  assert (Hrow : nth_error (timerWheel s) n = Some row) by (apply nth_error_nth'; exact Hindex).
  assert (Hspoke : timer_spoke (osKernelConfig sg) (timerMatch linked) = Z.of_nat n).
  { unfold n; rewrite Z2Nat.id; [reflexivity|pose proof (timer_spoke_in_range _ (timerMatch linked) Hsize); lia]. }
  assert (Husednotfree : forall j u, timerUsed s j = Some u -> ~ In j (timerFree s)).
  { intros j u Hu; destruct Hpool as [_ [_ Hslots]].
    assert (Hex : exists v, timer_allocated_slots s j = Some v).
    { exists tt; unfold timer_allocated_slots; rewrite Hu; reflexivity. }
    exact (proj2 (proj1 (Hslots j) Hex)). }
  assert (Hrownotfree : forall j, In j row -> ~ In j (timerFree s)).
  { intros j Hin; destruct (timer_wheel_member_spoke _ _ _ _ _ Hwheel Hrow Hin) as [u [Hu _]].
    eapply Husednotfree; eauto. }
  unfold timer_link in Hstep; rewrite Ht, Hold in Hstep; fold linked in Hstep; fold n in Hstep; fold row in Hstep.
  change (Some (timer_replace_wheel_objects s (kernel_map_set (timerUsed s) i (Some linked))
    (timer_wheel_prepend_images sg (timerImages s) i
      (timer_link_image old (timerMatch linked) (timer_id_pointer sg row)) row)
    (timer_wheel_update (timerWheel s) n (i :: row))) = Some post) in Hstep.
  injection Hstep as Hpost; rewrite <- Hpost; clear Hpost.
  unfold valid_timer_state; cbv beta iota zeta delta [timer_replace_wheel_objects timerFree timerUsed
    timerImages timerPrivate timerWheel timerTime timerFreeCount timerUsedCount timerNextGeneration].
  fold (timerUsed s) (timerFree s) (timerImages s) (timerPrivate s) (timerWheel s)
    (timerTime s) (timerFreeCount s) (timerUsedCount s) (timerNextGeneration s).
  split.
  - destruct Hpool as [Hnd [Hrange Hslots]]; split; [exact Hnd|]. split; [exact Hrange|].
    intros j; unfold timer_allocated_slots; simpl.
    destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite kernel_map_set_same; split.
      * intros; apply (proj1 (Hslots i)); exists tt; unfold timer_allocated_slots; rewrite Ht; reflexivity.
      * intros; eauto.
    + rewrite kernel_map_set_other by exact Hne; apply Hslots.
  - split.
    + apply timer_wheel_prepend_preserves_wheel_validity with t; try assumption; reflexivity.
    + split; [exact Htime|]. split; [exact Hfreecount|]. split; [exact Hsum|].
      split; [exact Hfc|]. split; [exact Huc|]. split.
      * intros j u Hu; unfold kernel_map_set in Hu; destruct (Z.eq_dec j i) as [->|Hne].
        -- injection Hu as Hueq; rewrite <- Hueq; split; [apply timer_link_preserves_object_validity; exact Htvalid|].
           split; [exact Htgen|]. split; [exact Hprivatei|].
           exists (timer_link_image old (timerMatch linked) (timer_id_pointer sg row)).
           split; [apply timer_wheel_prepend_images_same|].
           exact (timer_link_image_object_eq old t (timerTime s) periodic (timer_id_pointer sg row) Himage).
        -- destruct (Hused j u Hu) as [Huvalid [Hugen [Hpriv [v [Hv Hobject]]]]].
           split; [exact Huvalid|]. split; [exact Hugen|]. split; [exact Hpriv|].
           rewrite timer_wheel_prepend_images_other by exact Hne; rewrite Hv.
           destruct row as [|head tail]; [exists v; auto|].
           simpl; destruct (Z.eq_dec j head).
           ++ eexists; split; [reflexivity|].
              exact (timer_image_set_links_object_eq v u (timerImageNext v) (timer_pool_addr sg i) Hobject).
           ++ exists v; auto.
      * split.
        -- intros j p Hp; destruct (Hprivate j p Hp) as [Hu Hv].
           assert (Hne : j <> i) by (intro E; subst j; congruence).
           split; [rewrite kernel_map_set_other by exact Hne; exact Hu|].
           rewrite timer_wheel_prepend_images_other by exact Hne; rewrite Hv; reflexivity.
        -- split.
           ++ intros j Hp; destruct (Z.eq_dec j i) as [->|Hne].
              ** rewrite timer_wheel_prepend_images_same; split.
                 --- intros; apply (proj1 (Hdomain i Hprivatei)); eauto.
                 --- eauto.
              ** rewrite timer_wheel_prepend_images_other by exact Hne.
                 split.
                 --- intros [v Hv]; destruct (timerImages s j) as [oldj|] eqn:Ej; [|discriminate].
                     apply (proj1 (Hdomain j Hp)); eauto.
                 --- intros Hr; destruct (proj2 (Hdomain j Hp) Hr) as [v Hv]; rewrite Hv; eexists; reflexivity.
           ++ split.
              ** intros j v Hv; destruct (Z.eq_dec j i) as [->|Hne].
                 --- rewrite timer_wheel_prepend_images_same in Hv; inversion Hv; subst v; exact (Hpadding i old Hold).
                 --- rewrite timer_wheel_prepend_images_other in Hv by exact Hne.
                     destruct (timerImages s j) as [oldj|] eqn:Ej; [|discriminate].
                     destruct row as [|head tail]; simpl in Hv.
                     +++ inversion Hv; subst v; exact (Hpadding j oldj Ej).
                     +++ destruct (Z.eq_dec j head); inversion Hv; subst v; exact (Hpadding j oldj Ej).
              ** intros pre j rest Hlist.
                 assert (Hfreej : In j (timerFree s)) by (rewrite Hlist; apply in_or_app; right; left; reflexivity).
                 assert (Hne : j <> i) by (intro E; subst j; exact (Husednotfree i t Ht Hfreej)).
                 destruct (Hlinks pre j rest Hlist) as [v [Hv Hfields]].
                 exists v; split; [|exact Hfields].
                 rewrite timer_wheel_prepend_images_other by exact Hne; rewrite Hv.
                 destruct row as [|head tail]; [reflexivity|]. simpl.
                 destruct (Z.eq_dec j head) as [->|Hnehead]; [|reflexivity].
                 exfalso; apply (Hrownotfree head); [left; reflexivity|exact Hfreej].
Qed.

Lemma timer_wheel_row_ids_in_range : forall sg s n row i,
  valid_timer_state sg s -> nth_error s.(timerWheel) n = Some row -> In i row ->
  0 <= i < sg.(osKernelConfig).(cfgMaxTimers).
Proof.
  intros sg s n row i [[_ [_ Hslots]] [Hwheel _]] Hrow Hin.
  destruct (timer_wheel_member_spoke _ _ _ _ _ Hwheel Hrow Hin) as [t [Ht _]].
  apply (proj1 (proj1 (Hslots i) ltac:(exists tt; unfold timer_allocated_slots; rewrite Ht; reflexivity))).
Qed.

Lemma timer_wheel_row_entries_in_range : forall sg s n row,
  sg.(osKernelConfig).(cfgMaxTimers) < 65536 -> valid_timer_state sg s ->
  nth_error s.(timerWheel) n = Some row -> 0 <= Z.of_nat (List.length row) < 65536.
Proof.
  intros sg s n row Hcap Hvalid Hrow.
  pose proof Hvalid as [_ [[_ [Hnd _]] [_ [_ [Hsum [Hfc [Huc _]]]]]]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  assert (Hincl : incl row (Zrange 0 (cfgMaxTimers (osKernelConfig sg)))).
  { intros i Hin; apply In_Zrange; eapply timer_wheel_row_ids_in_range; eauto. }
  pose proof (NoDup_incl_length Hrownd Hincl) as Hlen.
  apply Nat2Z.inj_le in Hlen; rewrite kernel_zrange_length in Hlen.
  rewrite Z2Nat.id in Hlen by lia; lia.
Qed.

Lemma timer_wheel_row_pointer_null_iff : forall sg s n row,
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> nth_error s.(timerWheel) n = Some row ->
  (timer_id_pointer sg row = 0 <-> row = []).
Proof.
  intros sg s n row Hlayout Hvalid Hrow; apply timer_id_pointer_null_iff.
  intros i Hin; pose proof (timer_wheel_row_ids_in_range _ _ _ _ _ Hvalid Hrow Hin) as Hr.
  pose proof (timer_pool_addr_in_range _ _ Hlayout Hr); lia.
Qed.

Lemma timer_link_preserves_configuration : forall sg s i t periodic post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  s.(timerUsed) i = Some t -> t.(timerState) <> TimerRunning ->
  timer_link sg s i periodic = Some post ->
  valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i t periodic post He Hsize Hv Hp Ht Hst Hstep.
  assert (Hpostphase : timer_api_initialized post).
  { unfold timer_api_initialized in *; rewrite (timer_link_preserves_initialization_phase _ _ _ _ _ Hstep); exact Hp. }
  split; [|exact Hpostphase].
  apply (proj2 (timer_initialized_configuration_iff sg post He Hpostphase)).
  eapply timer_link_preserves_state_validity; eauto.
  apply (proj1 (timer_initialized_configuration_iff sg s He Hp)); exact Hv.
Qed.

Lemma timer_wheel_remove_concat : forall wheel n row i,
  nth_error wheel n = Some row -> In i row -> NoDup (concat wheel) ->
  concat (timer_wheel_update wheel n (remove Z.eq_dec i row)) = remove Z.eq_dec i (concat wheel).
Proof.
  intros wheel n row i Hrow Hin Hnd; apply nth_error_split in Hrow.
  destruct Hrow as [pre [rest [Hwheel Hn]]]; subst wheel n.
  rewrite concat_app in Hnd; simpl in Hnd.
  assert (Hnotpre : ~ In i (concat pre)).
  { intro H; eapply kernel_list_nodup_app_disjoint; [exact Hnd|exact H|].
    apply in_or_app; left; exact Hin. }
  assert (Hnotrest : ~ In i (concat rest)).
  { rewrite app_assoc in Hnd; eapply kernel_list_nodup_app_disjoint; [exact Hnd|].
    apply in_or_app; right; exact Hin. }
  rewrite timer_wheel_update_at, !concat_app; simpl; rewrite !remove_app.
  f_equal; [symmetry; apply notin_remove; exact Hnotpre|].
  f_equal; symmetry; apply notin_remove; exact Hnotrest.
Qed.

Lemma timer_row_addresses_nodup : forall sg row,
  NoDup row -> NoDup (map (timer_pool_addr sg) row).
Proof.
  intros sg row H; induction H as [|i row Hnot Hnd IH]; simpl; [constructor|].
  constructor; [|exact IH]. intro Hin; apply in_map_iff in Hin; destruct Hin as [j [Haddr Hin]].
  apply timer_pool_addr_injective in Haddr; subst j; contradiction.
Qed.

Lemma timer_row_remove_addresses : forall sg row i,
  map (timer_pool_addr sg) (remove Z.eq_dec i row) =
    remove Z.eq_dec (timer_pool_addr sg i) (map (timer_pool_addr sg) row).
Proof.
  intros sg row; induction row as [|j rest IH]; intros i; simpl; [reflexivity|].
  destruct (Z.eq_dec i j) as [->|Hne].
  - destruct (Z.eq_dec (timer_pool_addr sg j) (timer_pool_addr sg j)); [apply IH|contradiction].
  - destruct (Z.eq_dec (timer_pool_addr sg i) (timer_pool_addr sg j)).
    + exfalso; apply Hne; apply timer_pool_addr_injective with sg; assumption.
    + simpl; rewrite IH; reflexivity.
Qed.

Lemma timer_row_next_pointer_at : forall sg pre i rest,
  NoDup (pre ++ i :: rest) ->
  kernel_list_next_addr (map (timer_pool_addr sg) (pre ++ i :: rest)) (timer_pool_addr sg i) =
    timer_id_pointer sg rest.
Proof.
  intros sg pre i rest Hnd; rewrite map_app; simpl; rewrite kernel_list_next_addr_at.
  - destruct rest; reflexivity.
  - pose proof (timer_row_addresses_nodup sg _ Hnd) as H; rewrite map_app in H; exact H.
Qed.

Lemma timer_row_previous_pointer_at : forall sg pre i rest,
  NoDup (pre ++ i :: rest) ->
  kernel_list_previous_addr (map (timer_pool_addr sg) (pre ++ i :: rest)) (timer_pool_addr sg i) =
    timer_id_pointer sg (rev pre).
Proof.
  intros sg pre i rest Hnd; unfold kernel_list_previous_addr; rewrite map_app; simpl.
  rewrite kernel_list_previous_at.
  - rewrite <- map_rev; destruct (rev pre); reflexivity.
  - pose proof (timer_row_addresses_nodup sg _ Hnd) as H; rewrite map_app in H; exact H.
Qed.

Lemma timer_wheel_row_node_pointers : forall sg s n row i v,
  timer_wheel_valid sg s -> nth_error s.(timerWheel) n = Some row -> In i row ->
  s.(timerImages) i = Some v ->
  v.(timerImageNext) = kernel_list_next_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i) /\
  v.(timerImagePrev) = kernel_list_previous_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i).
Proof.
  intros sg s n row i v Hvalid Hrow Hin Hv; pose proof Hvalid as [_ [Hnd [_ Hrows]]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
  destruct (Hrows n row pre i rest Hrow Hlist) as [t [old [_ [Hold [_ [Hnext Hprev]]]]]].
  rewrite Hv in Hold; injection Hold as Heq; subst old.
  rewrite Hlist; pose proof Hrownd as Hndlist; rewrite Hlist in Hndlist.
  rewrite timer_row_next_pointer_at, timer_row_previous_pointer_at by exact Hndlist; auto.
Qed.

Lemma timer_row_head_test_eq_previous_null : forall sg row i,
  NoDup row -> In i row -> (forall j, In j row -> timer_pool_addr sg j <> 0) ->
  Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i) =
    Z.eqb (kernel_list_previous_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i)) 0.
Proof.
  intros sg row i Hnd Hin Hnonzero; apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
  subst row; rewrite timer_row_previous_pointer_at by exact Hnd.
  destruct pre as [|a pre]; [simpl; rewrite Z.eqb_refl; reflexivity|].
  assert (Hhead : timer_pool_addr sg a <> timer_pool_addr sg i).
  { intro E; apply timer_pool_addr_injective in E; subst a.
    inversion Hnd as [|? ? Hnot Htail]; subst; apply Hnot; apply in_or_app; right; left; reflexivity. }
  assert (Hprev : timer_id_pointer sg (rev (a :: pre)) <> 0).
  { intro E; apply (proj1 (timer_id_pointer_null_iff sg (rev (a :: pre)) ltac:(
      intros j Hj; apply Hnonzero; apply in_or_app; left; apply (proj2 (in_rev (a :: pre) j)); exact Hj))) in E.
    apply (f_equal (@rev TimerID)) in E; rewrite rev_involutive in E; discriminate. }
  change (Z.eqb (timer_pool_addr sg a) (timer_pool_addr sg i) = Z.eqb (timer_id_pointer sg (rev (a :: pre))) 0).
  destruct (Z.eqb (timer_pool_addr sg a) (timer_pool_addr sg i)) eqn:E;
    [apply Z.eqb_eq in E; contradiction|].
  symmetry; apply Z.eqb_neq; exact Hprev.
Qed.

Lemma timer_row_next_pointer_member : forall sg row i p,
  kernel_list_next_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i) = p -> p <> 0 ->
  exists j, p = timer_pool_addr sg j /\ In j row.
Proof.
  intros sg row i p H Hp; unfold kernel_list_next_addr in H.
  destruct (kernel_list_next (map (timer_pool_addr sg) row) (timer_pool_addr sg i)) as [q|] eqn:E; [|congruence].
  apply kernel_list_next_some_in in E; apply in_map_iff in E; destruct E as [j [Hj Hin]].
  exists j; split; [congruence|exact Hin].
Qed.

Lemma timer_row_previous_pointer_member : forall sg row i p,
  kernel_list_previous_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i) = p -> p <> 0 ->
  exists j, p = timer_pool_addr sg j /\ In j row.
Proof.
  intros sg row i p H Hp; unfold kernel_list_previous_addr in H.
  destruct (kernel_list_previous (map (timer_pool_addr sg) row) (timer_pool_addr sg i)) as [q|] eqn:E; [|congruence].
  apply kernel_list_previous_some_in in E; apply in_map_iff in E; destruct E as [j [Hj Hin]].
  exists j; split; [congruence|exact Hin].
Qed.

Lemma timer_images_set_next_pointer_lookup : forall sg images p next q,
  (exists j, p = timer_pool_addr sg j) ->
  timer_images_set_next images (timer_pointer_index sg p) next q = option_map (fun v =>
    if Z.eq_dec (timer_pool_addr sg q) p then timer_image_set_links v next v.(timerImagePrev) else v) (images q).
Proof.
  intros sg images p next q [j Hp]; subst p; rewrite timer_pointer_index_addr, timer_images_set_next_lookup.
  destruct (images q) as [v|]; simpl; [|reflexivity].
  destruct (Z.eq_dec q j) as [->|Hne].
  - destruct (Z.eq_dec (timer_pool_addr sg j) (timer_pool_addr sg j)); congruence.
  - destruct (Z.eq_dec (timer_pool_addr sg q) (timer_pool_addr sg j)); [|reflexivity].
    exfalso; apply Hne; eapply timer_pool_addr_injective; eauto.
Qed.

Lemma timer_images_set_prev_pointer_lookup : forall sg images p prev q,
  (exists j, p = timer_pool_addr sg j) ->
  timer_images_set_prev images (timer_pointer_index sg p) prev q = option_map (fun v =>
    if Z.eq_dec (timer_pool_addr sg q) p then timer_image_set_links v v.(timerImageNext) prev else v) (images q).
Proof.
  intros sg images p prev q [j Hp]; subst p; rewrite timer_pointer_index_addr, timer_images_set_prev_lookup.
  destruct (images q) as [v|]; simpl; [|reflexivity].
  destruct (Z.eq_dec q j) as [->|Hne].
  - destruct (Z.eq_dec (timer_pool_addr sg j) (timer_pool_addr sg j)); congruence.
  - destruct (Z.eq_dec (timer_pool_addr sg q) (timer_pool_addr sg j)); [|reflexivity].
    exfalso; apply Hne; eapply timer_pool_addr_injective; eauto.
Qed.

Lemma timer_images_set_next_identity_frame : forall images i next q,
  option_map timer_image_link_identity (timer_images_set_next images i next q) =
    option_map timer_image_link_identity (images q).
Proof.
  intros; rewrite timer_images_set_next_lookup; destruct (images q); [|reflexivity].
  simpl; destruct (Z.eq_dec q i); reflexivity.
Qed.

Lemma timer_images_set_prev_identity_frame : forall images i prev q,
  option_map timer_image_link_identity (timer_images_set_prev images i prev q) =
    option_map timer_image_link_identity (images q).
Proof.
  intros; rewrite timer_images_set_prev_lookup; destruct (images q); [|reflexivity].
  simpl; destruct (Z.eq_dec q i); reflexivity.
Qed.

Lemma timer_image_identity_implies_object_eq : forall before after t,
  timer_image_link_identity after = timer_image_link_identity before ->
  before = timer_object_image t before.(timerImageNext) before.(timerImagePrev) before.(timerImagePadding) ->
  after = timer_object_image t after.(timerImageNext) after.(timerImagePrev) after.(timerImagePadding).
Proof.
  intros before after t Hidentity Hobject; destruct before; destruct after.
  unfold timer_image_link_identity, timer_object_image in *; simpl in *.
  inversion Hidentity; inversion Hobject; subst; reflexivity.
Qed.

Lemma timer_wheel_unlink_images_same : forall sg images i old row,
  timer_wheel_unlink_images sg images i old row i = Some (timer_unlink_image old).
Proof. intros; apply kernel_map_set_same. Qed.

Lemma timer_wheel_unlink_images_identity_frame : forall sg images i old row q,
  q <> i -> option_map timer_image_link_identity (timer_wheel_unlink_images sg images i old row q) =
    option_map timer_image_link_identity (images q).
Proof.
  intros sg images i old row q Hne; unfold timer_wheel_unlink_images.
  rewrite kernel_map_set_other by exact Hne.
  destruct (Z.eqb (timerImageNext old) 0), (Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i));
    rewrite ?timer_images_set_prev_identity_frame, ?timer_images_set_next_identity_frame; reflexivity.
Qed.

Lemma timer_wheel_unlink_images_neighbor_links : forall sg images i old row q before,
  NoDup row -> In i row -> (forall j, In j row -> timer_pool_addr sg j <> 0) ->
  old.(timerImageNext) = kernel_list_next_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i) ->
  old.(timerImagePrev) = kernel_list_previous_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i) ->
  q <> i -> timer_pool_addr sg q <> 0 -> images q = Some before ->
  exists after, timer_wheel_unlink_images sg images i old row q = Some after /\
    timer_image_link_identity after = timer_image_link_identity before /\
    after.(timerImageNext) = (if Z.eq_dec (timer_pool_addr sg q) old.(timerImagePrev)
      then old.(timerImageNext) else before.(timerImageNext)) /\
    after.(timerImagePrev) = (if Z.eq_dec (timer_pool_addr sg q) old.(timerImageNext)
      then old.(timerImagePrev) else before.(timerImagePrev)).
Proof.
  intros sg images i old row q before Hnd Hin Hnonnull Hnext Hprev Hqi Hq0 Hbefore.
  assert (Hhead : Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i) = Z.eqb (timerImagePrev old) 0).
  { rewrite Hprev; apply timer_row_head_test_eq_previous_null; assumption. }
  assert (Hnextptr : timerImageNext old <> 0 -> exists j, timerImageNext old = timer_pool_addr sg j).
  { intro H; destruct (timer_row_next_pointer_member _ _ _ _ (eq_sym Hnext) H) as [j [Hj _]]; eauto. }
  assert (Hprevptr : timerImagePrev old <> 0 -> exists j, timerImagePrev old = timer_pool_addr sg j).
  { intro H; destruct (timer_row_previous_pointer_member _ _ _ _ (eq_sym Hprev) H) as [j [Hj _]]; eauto. }
  unfold timer_wheel_unlink_images; rewrite Hhead, kernel_map_set_other by exact Hqi.
  destruct (Z.eqb (timerImagePrev old) 0) eqn:Ep;
    destruct (Z.eqb (timerImageNext old) 0) eqn:En.
  - rewrite Hbefore; apply Z.eqb_eq in Ep; apply Z.eqb_eq in En.
    destruct (Z.eq_dec (timer_pool_addr sg q) (timerImagePrev old)),
      (Z.eq_dec (timer_pool_addr sg q) (timerImageNext old));
      try (exfalso; apply Hq0; congruence); exists before; repeat split; reflexivity.
  - apply Z.eqb_neq in En; rewrite timer_images_set_prev_pointer_lookup by (apply Hnextptr; exact En).
    rewrite Hbefore; simpl; apply Z.eqb_eq in Ep.
    destruct (Z.eq_dec (timer_pool_addr sg q) (timerImagePrev old)),
      (Z.eq_dec (timer_pool_addr sg q) (timerImageNext old));
      try (exfalso; apply Hq0; congruence); eexists; repeat split; simpl; congruence.
  - apply Z.eqb_neq in Ep; rewrite timer_images_set_next_pointer_lookup by (apply Hprevptr; exact Ep).
    rewrite Hbefore; simpl; apply Z.eqb_eq in En.
    destruct (Z.eq_dec (timer_pool_addr sg q) (timerImagePrev old)),
      (Z.eq_dec (timer_pool_addr sg q) (timerImageNext old));
      try (exfalso; apply Hq0; congruence); eexists; repeat split; reflexivity.
  - apply Z.eqb_neq in Ep; apply Z.eqb_neq in En.
    rewrite timer_images_set_prev_pointer_lookup by (apply Hnextptr; exact En).
    rewrite timer_images_set_next_pointer_lookup by (apply Hprevptr; exact Ep).
    rewrite Hbefore; simpl.
    destruct (Z.eq_dec (timer_pool_addr sg q) (timerImagePrev old)),
      (Z.eq_dec (timer_pool_addr sg q) (timerImageNext old)); eexists; repeat split; reflexivity.
Qed.

Lemma timer_image_identity_and_links_eq : forall before after,
  timer_image_link_identity after = timer_image_link_identity before ->
  after.(timerImageNext) = before.(timerImageNext) -> after.(timerImagePrev) = before.(timerImagePrev) ->
  after = before.
Proof.
  intros before after Hi Hn Hp; destruct before; destruct after.
  unfold timer_image_link_identity in Hi; simpl in *; inversion Hi; subst; reflexivity.
Qed.

Lemma timer_wheel_unlink_images_frame_outside_row : forall sg images i old row q before,
  NoDup row -> In i row -> (forall j, In j row -> timer_pool_addr sg j <> 0) ->
  old.(timerImageNext) = kernel_list_next_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i) ->
  old.(timerImagePrev) = kernel_list_previous_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i) ->
  ~ In q row -> timer_pool_addr sg q <> 0 -> images q = Some before ->
  timer_wheel_unlink_images sg images i old row q = Some before.
Proof.
  intros sg images i old row q before Hnd Hin Hnonnull Hnext Hprev Hnot Hq0 Hbefore.
  assert (Hqi : q <> i) by (intro E; subst q; contradiction).
  assert (Hqnext : timer_pool_addr sg q <> timerImageNext old).
  { intro E; destruct (timer_row_next_pointer_member sg row i (timer_pool_addr sg q) ltac:(congruence) Hq0)
      as [j [Hj Hjin]]; apply timer_pool_addr_injective in Hj; subst j; contradiction. }
  assert (Hqprev : timer_pool_addr sg q <> timerImagePrev old).
  { intro E; destruct (timer_row_previous_pointer_member sg row i (timer_pool_addr sg q) ltac:(congruence) Hq0)
      as [j [Hj Hjin]]; apply timer_pool_addr_injective in Hj; subst j; contradiction. }
  destruct (timer_wheel_unlink_images_neighbor_links _ _ _ _ _ _ _ Hnd Hin Hnonnull Hnext Hprev Hqi Hq0 Hbefore)
    as [after [Hafter [Hidentity [Hnewnext Hnewprev]]]].
  destruct (Z.eq_dec (timer_pool_addr sg q) (timerImagePrev old)); [contradiction|].
  destruct (Z.eq_dec (timer_pool_addr sg q) (timerImageNext old)); [contradiction|].
  rewrite (timer_image_identity_and_links_eq _ _ Hidentity Hnewnext Hnewprev) in Hafter; exact Hafter.
Qed.

Lemma timer_wheel_remove_preserves_wheel_validity : forall sg s i t old n row,
  timer_wheel_valid sg s -> s.(timerUsed) i = Some t -> s.(timerImages) i = Some old ->
  nth_error s.(timerWheel) n = Some row -> In i row ->
  (forall j, In j (concat s.(timerWheel)) -> timer_pool_addr sg j <> 0) ->
  timer_wheel_valid sg (timer_replace_wheel_objects s
    (kernel_map_set s.(timerUsed) i (Some (timer_set_status t TimerStopped)))
    (timer_wheel_unlink_images sg s.(timerImages) i old row)
    (timer_wheel_update s.(timerWheel) n (remove Z.eq_dec i row))).
Proof.
  intros sg s i t old n row Hvalid Ht Hold Hrow Hin Hnonnull.
  pose proof Hvalid as [Hlen [Hnd [Hmembers Hrows]]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  pose proof (kernel_list_remove_preserves_nodup _ i Hrownd) as Hremovednd.
  destruct (timer_wheel_row_node_pointers _ _ _ _ _ _ Hvalid Hrow Hin Hold) as [Hnext Hprev].
  assert (Hrow_nonnull : forall j, In j row -> timer_pool_addr sg j <> 0).
  { intros j Hj; apply Hnonnull; eapply timer_wheel_row_member; eauto. }
  assert (Hindex : (n < List.length (timerWheel s))%nat) by (apply nth_error_Some; rewrite Hrow; discriminate).
  unfold timer_wheel_valid, timer_wheel_member, timer_replace_wheel_objects; simpl.
  split; [rewrite timer_wheel_update_length; exact Hlen|]. split.
  - rewrite timer_wheel_remove_concat by assumption; apply kernel_list_remove_preserves_nodup; exact Hnd.
  - split.
    + intros j; rewrite timer_wheel_remove_concat by assumption.
      destruct (Z.eq_dec j i) as [->|Hne].
      * rewrite kernel_map_set_same; split.
        -- intro H; apply in_remove in H; tauto.
        -- intros [u [Hu Hrun]]; inversion Hu; subst u; discriminate.
      * rewrite kernel_map_set_other by exact Hne; rewrite <- Hmembers.
        split; [intro H; apply in_remove in H; tauto|intro H; apply in_in_remove; assumption].
    + intros m other pre j rest Hother Hlist; destruct (Nat.eq_dec m n) as [->|Hmn].
      * rewrite timer_wheel_update_same in Hother by exact Hindex; injection Hother as Hsame.
        rewrite <- Hsame in Hlist.
        assert (Hremovedin : In j (remove Z.eq_dec i row)) by (rewrite Hlist; apply in_or_app; right; left; reflexivity).
        apply in_remove in Hremovedin; destruct Hremovedin as [Hjin Hji].
        apply in_split in Hjin; destruct Hjin as [before [after Hposition]].
        assert (Hjin : In j row) by (rewrite Hposition; apply in_or_app; right; left; reflexivity).
        destruct (Hrows n row before j after Hrow Hposition) as [u [v [Hu [Hv [Hspoke _]]]]].
        destruct (timer_wheel_row_node_pointers _ _ _ _ _ _ Hvalid Hrow Hjin Hv) as [Hqnext Hqprev].
        pose proof (Hrow_nonnull j Hjin) as Hq0; pose proof (Hrow_nonnull i Hin) as Hi0.
        destruct (timer_wheel_unlink_images_neighbor_links _ _ _ _ _ _ _
          Hrownd Hin Hrow_nonnull Hnext Hprev Hji Hq0 Hv) as
          [vnew [Hvnew [Hidentity [Hvnext Hvprev]]]].
        assert (Haddrne : timer_pool_addr sg j <> timer_pool_addr sg i).
        { intro E; apply timer_pool_addr_injective in E; contradiction. }
        assert (Hnext_after : timerImageNext vnew =
          kernel_list_next_addr (map (timer_pool_addr sg) (remove Z.eq_dec i row)) (timer_pool_addr sg j)).
        { rewrite timer_row_remove_addresses, kernel_list_next_addr_remove by
            (try apply timer_row_addresses_nodup; assumption).
          rewrite <- Hprev, <- Hnext, <- Hqnext; exact Hvnext. }
        assert (Hprev_after : timerImagePrev vnew =
          kernel_list_previous_addr (map (timer_pool_addr sg) (remove Z.eq_dec i row)) (timer_pool_addr sg j)).
        { rewrite timer_row_remove_addresses, kernel_list_previous_addr_remove by
            (try apply timer_row_addresses_nodup; assumption).
          rewrite <- Hnext, <- Hprev, <- Hqprev; exact Hvprev. }
        exists u, vnew; split; [rewrite kernel_map_set_other by exact Hji; exact Hu|].
        split; [exact Hvnew|]. split; [exact Hspoke|].
        pose proof Hremovednd as Hndlist; rewrite Hlist in Hndlist.
        rewrite Hlist in Hnext_after, Hprev_after.
        rewrite timer_row_next_pointer_at in Hnext_after by exact Hndlist.
        rewrite timer_row_previous_pointer_at in Hprev_after by exact Hndlist; auto.
      * rewrite timer_wheel_update_other in Hother by exact Hmn.
        destruct (Hrows m other pre j rest Hother Hlist) as [u [v [Hu [Hv Hfields]]]].
        assert (Hjin : In j other) by (rewrite Hlist; apply in_or_app; right; left; reflexivity).
        assert (Hnotrow : ~ In j row).
        { intro Hj; apply Hmn; eapply timer_wheel_member_unique_spoke; eauto. }
        assert (Hji : j <> i) by (intro E; subst j; contradiction).
        assert (Hj0 : timer_pool_addr sg j <> 0) by (apply Hnonnull; eapply timer_wheel_row_member; eauto).
        exists u, v; split; [rewrite kernel_map_set_other by exact Hji; exact Hu|].
        split; [|exact Hfields]. apply timer_wheel_unlink_images_frame_outside_row; assumption.
Qed.

Lemma valid_timer_state_running_position : forall sg s i t,
  valid_timer_state sg s -> s.(timerUsed) i = Some t -> t.(timerState) = TimerRunning ->
  exists n row old, s.(timerImages) i = Some old /\ nth_error s.(timerWheel) n = Some row /\
    In i row /\ n = Z.to_nat (timer_spoke sg.(osKernelConfig) old.(timerImageMatch)).
Proof.
  intros sg s i t [_ [Hwheel [_ [_ [_ [_ [_ [Hused _]]]]]]]] Ht Hrun.
  pose proof Hwheel as [_ [_ [Hmembers Hrows]]].
  destruct (Hused i t Ht) as [_ [_ [_ [old [Hold Hobject]]]]].
  pose proof (proj2 (Hmembers i) (ex_intro _ t (conj Ht Hrun))) as Hin.
  apply in_concat in Hin; destruct Hin as [row [Hrowin Hin]].
  apply In_nth_error in Hrowin; destruct Hrowin as [n Hrow].
  destruct (timer_wheel_member_spoke _ _ _ _ _ Hwheel Hrow Hin) as [u [Hu Hspoke]].
  rewrite Ht in Hu; injection Hu as Heq; subst u.
  exists n, row, old; split; [exact Hold|]. split; [exact Hrow|]. split; [exact Hin|].
  assert (Hmatch : timerImageMatch old = timerMatch t) by (rewrite Hobject; reflexivity).
  rewrite Hmatch, Hspoke, Nat2Z.id; reflexivity.
Qed.

Lemma timer_wheel_unlink_images_existing : forall sg images i old row q before,
  q <> i -> images q = Some before -> exists after,
    timer_wheel_unlink_images sg images i old row q = Some after /\
      timer_image_link_identity after = timer_image_link_identity before.
Proof.
  intros sg images i old row q before Hne Hbefore.
  pose proof (timer_wheel_unlink_images_identity_frame sg images i old row q Hne) as Hidentity.
  rewrite Hbefore in Hidentity.
  destruct (timer_wheel_unlink_images sg images i old row q) as [after|] eqn:E; [|discriminate].
  exists after; split; [reflexivity|].
  exact (f_equal (fun o => match o with Some identity => identity | None => timer_image_link_identity before end) Hidentity).
Qed.

Lemma timer_wheel_unlink_images_origin : forall sg images i old row q after,
  q <> i -> timer_wheel_unlink_images sg images i old row q = Some after -> exists before,
    images q = Some before /\ timer_image_link_identity after = timer_image_link_identity before.
Proof.
  intros sg images i old row q after Hne Hafter.
  pose proof (timer_wheel_unlink_images_identity_frame sg images i old row q Hne) as Hidentity.
  rewrite Hafter in Hidentity; destruct (images q) as [before|] eqn:E; [|discriminate].
  exists before; split; [reflexivity|].
  exact (f_equal (fun o => match o with Some identity => identity | None => timer_image_link_identity before end) Hidentity).
Qed.

Lemma timer_unlink_image_object_eq : forall old t,
  old = timer_object_image t old.(timerImageNext) old.(timerImagePrev) old.(timerImagePadding) ->
  timer_unlink_image old = timer_object_image (timer_set_status t TimerStopped) 0 0 old.(timerImagePadding).
Proof. intros old t H; rewrite H; reflexivity. Qed.

Lemma timer_unlink_preserves_state_validity : forall sg s i t post,
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> s.(timerUsed) i = Some t -> t.(timerState) = TimerRunning ->
  timer_unlink sg s i = Some post -> valid_timer_state sg post.
Proof.
  intros sg s i t post Hlayout Hvalid Ht Hrun Hstep.
  pose proof Hvalid as [Hpool [Hwheel [Htime [Hfreecount [Hsum [Hfc [Huc
    [Hused [Hprivate [Hdomain [Hpadding Hlinks]]]]]]]]]]].
  destruct (Hused i t Ht) as [Htvalid [Htgen [Hprivatei [old [Hold Himage]]]]].
  destruct (valid_timer_state_running_position _ _ _ _ Hvalid Ht Hrun) as
    [n [row [old0 [Hold0 [Hrow [Hin Hn]]]]]].
  rewrite Hold in Hold0; injection Hold0 as Heq; subst old0.
  assert (Hnth : nth n (timerWheel s) [] = row) by (eapply nth_error_nth; exact Hrow).
  assert (Husednotfree : forall j u, timerUsed s j = Some u -> ~ In j (timerFree s)).
  { intros j u Hu; destruct Hpool as [_ [_ Hslots]].
    assert (Hex : exists v, timer_allocated_slots s j = Some v).
    { exists tt; unfold timer_allocated_slots; rewrite Hu; reflexivity. }
    exact (proj2 (proj1 (Hslots j) Hex)). }
  assert (Hrownotfree : forall j, In j row -> ~ In j (timerFree s)).
  { intros j Hj; destruct (timer_wheel_member_spoke _ _ _ _ _ Hwheel Hrow Hj) as [u [Hu _]].
    eapply Husednotfree; eauto. }
  assert (Hrow_nonnull : forall j, In j row -> timer_pool_addr sg j <> 0).
  { intros j Hj; pose proof (timer_wheel_row_ids_in_range _ _ _ _ _ Hvalid Hrow Hj) as Hr.
    pose proof (timer_pool_addr_in_range _ _ Hlayout Hr); lia. }
  pose proof Hwheel as [_ [Hnd [Hmembers Hrows]]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  destruct (timer_wheel_row_node_pointers _ _ _ _ _ _ Hwheel Hrow Hin Hold) as [Hnext Hprev].
  unfold timer_unlink in Hstep; rewrite Ht, Hold, <- Hn, Hnth in Hstep.
  change (Some (timer_replace_wheel_objects s
    (kernel_map_set (timerUsed s) i (Some (timer_set_status t TimerStopped)))
    (timer_wheel_unlink_images sg (timerImages s) i old row)
    (timer_wheel_update (timerWheel s) n (remove Z.eq_dec i row))) = Some post) in Hstep.
  injection Hstep as Hpost; rewrite <- Hpost; clear Hpost.
  unfold valid_timer_state; cbv beta iota zeta delta [timer_replace_wheel_objects timerFree timerUsed
    timerImages timerPrivate timerWheel timerTime timerFreeCount timerUsedCount timerNextGeneration].
  fold (timerUsed s) (timerFree s) (timerImages s) (timerPrivate s) (timerWheel s)
    (timerTime s) (timerFreeCount s) (timerUsedCount s) (timerNextGeneration s).
  split.
  - destruct Hpool as [Hfreend [Hrange Hslots]]; split; [exact Hfreend|]. split; [exact Hrange|].
    intros j; unfold timer_allocated_slots; simpl; destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite kernel_map_set_same; split.
      * intros; apply (proj1 (Hslots i)); exists tt; unfold timer_allocated_slots; rewrite Ht; reflexivity.
      * intros; eauto.
    + rewrite kernel_map_set_other by exact Hne; apply Hslots.
  - split.
    + apply timer_wheel_remove_preserves_wheel_validity; try assumption.
      intros j Hj; apply in_concat in Hj; destruct Hj as [r [Hr Hj]].
      apply In_nth_error in Hr; destruct Hr as [m Hr].
      pose proof (timer_wheel_row_ids_in_range _ _ _ _ _ Hvalid Hr Hj) as Hrange.
      pose proof (timer_pool_addr_in_range _ _ Hlayout Hrange); lia.
    + split; [exact Htime|]. split; [exact Hfreecount|]. split; [exact Hsum|].
      split; [exact Hfc|]. split; [exact Huc|]. split.
      * intros j u Hu; unfold kernel_map_set in Hu; destruct (Z.eq_dec j i) as [->|Hne].
        -- injection Hu as Hueq; rewrite <- Hueq; split.
           ++ apply timer_set_status_preserves_object_validity; [exact Htvalid|discriminate].
           ++ split; [exact Htgen|]. split; [exact Hprivatei|].
              exists (timer_unlink_image old); split; [apply timer_wheel_unlink_images_same|].
              exact (timer_unlink_image_object_eq old t Himage).
        -- destruct (Hused j u Hu) as [Huvalid [Hugen [Hpriv [v [Hv Hobject]]]]].
           split; [exact Huvalid|]. split; [exact Hugen|]. split; [exact Hpriv|].
           destruct (timer_wheel_unlink_images_existing sg (timerImages s) i old row j v Hne Hv) as [after [Ha Hid]].
           exists after; split; [exact Ha|]. eapply timer_image_identity_implies_object_eq; eauto.
      * split.
        -- intros j p Hp; destruct (Hprivate j p Hp) as [Hu Hv].
           assert (Hne : j <> i) by (intro E; subst j; congruence).
           split; [rewrite kernel_map_set_other by exact Hne; exact Hu|].
           pose proof (timer_wheel_unlink_images_identity_frame sg (timerImages s) i old row j Hne) as Hid.
           rewrite Hv in Hid; destruct (timer_wheel_unlink_images sg (timerImages s) i old row j);
             simpl in Hid; [discriminate|reflexivity].
        -- split.
           ++ intros j Hp; destruct (Z.eq_dec j i) as [->|Hne].
              ** rewrite timer_wheel_unlink_images_same; split.
                 --- intros; apply (proj1 (Hdomain i Hprivatei)); eauto.
                 --- eauto.
              ** split.
                 --- intros [after Ha]; destruct (timer_wheel_unlink_images_origin _ _ _ _ _ _ _ Hne Ha) as [v [Hv _]].
                     apply (proj1 (Hdomain j Hp)); eauto.
                 --- intros Hr; destruct (proj2 (Hdomain j Hp) Hr) as [v Hv].
                     destruct (timer_wheel_unlink_images_existing sg (timerImages s) i old row j v Hne Hv) as [a [Ha _]]; eauto.
           ++ split.
              ** intros j v Hv; destruct (Z.eq_dec j i) as [->|Hne].
                 --- rewrite timer_wheel_unlink_images_same in Hv; injection Hv as Heq; rewrite <- Heq.
                     exact (Hpadding i old Hold).
                 --- destruct (timer_wheel_unlink_images_origin _ _ _ _ _ _ _ Hne Hv) as [before [Hb Hid]].
                     pose proof (Hpadding j before Hb) as Hpad.
                     unfold timer_image_link_identity in Hid; inversion Hid; congruence.
              ** intros pre j rest Hlist.
                 assert (Hfreej : In j (timerFree s)) by (rewrite Hlist; apply in_or_app; right; left; reflexivity).
                 assert (Hnotrow : ~ In j row) by (intro Hj; exact (Hrownotfree j Hj Hfreej)).
                 assert (Hj0 : timer_pool_addr sg j <> 0).
                 { destruct Hpool as [_ [Hrange _]]; pose proof (timer_pool_addr_in_range _ _ Hlayout (Hrange j Hfreej)); lia. }
                 destruct (Hlinks pre j rest Hlist) as [v [Hv Hfields]].
                 exists v; split; [|exact Hfields]. apply timer_wheel_unlink_images_frame_outside_row; assumption.
Qed.

Lemma timer_unlink_preserves_configuration : forall sg s i t post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  s.(timerUsed) i = Some t -> t.(timerState) = TimerRunning ->
  timer_unlink sg s i = Some post -> valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i t post He Hlayout Hv Hp Ht Hrun Hstep.
  assert (Hpostphase : timer_api_initialized post).
  { unfold timer_api_initialized in *; rewrite (timer_unlink_preserves_initialization_phase _ _ _ _ Hstep); exact Hp. }
  split; [|exact Hpostphase].
  apply (proj2 (timer_initialized_configuration_iff sg post He Hpostphase)).
  eapply timer_unlink_preserves_state_validity; eauto.
  apply (proj1 (timer_initialized_configuration_iff sg s He Hp)); exact Hv.
Qed.

(** The locked switch bodies start after pointer/type/ISR checks.  Raw
    State bytes, including UNUSED and invalid values, select the branches.
    A missing image means this pool-focused model owns no such object. *)
Definition timer_start_locked (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID)
  : option (bool * OSErrCode * GlobTimerState) :=
  match s.(timerImages) i with
  | None => None
  | Some v =>
    if Z.eqb v.(timerImageState) 3 then
      match timer_unlink sg s i with
      | None => None
      | Some stopped => option_map (fun post => (true, OS_ERR_NONE, post)) (timer_link sg stopped i false)
      end
    else if orb (Z.eqb v.(timerImageState) 1) (Z.eqb v.(timerImageState) 2) then
      option_map (fun post => (true, OS_ERR_NONE, post)) (timer_link sg s i false)
    else if Z.eqb v.(timerImageState) 0 then Some (false, OS_ERR_TMR_INACTIVE, s)
    else Some (false, OS_ERR_TMR_INVALID_STATE, s)
  end.

(** A callback request records all actual arguments: function, timer
    pointer, and callback argument.  It is not execution of user code. *)
Definition timer_stop_request (sg : StableGlobVars) (i : TimerID) (v : TimerImage) (opt arg : Z)
  : option (addr * addr * addr) * OSErrCode :=
  if Z.eqb opt 0 then (None, OS_ERR_NONE) else
  if orb (Z.eqb opt 3) (Z.eqb opt 4) then
    if Z.eqb v.(timerImageCallback) 0 then (None, OS_ERR_TMR_NO_CALLBACK) else
      (Some (v.(timerImageCallback), timer_pool_addr sg i,
        if Z.eqb opt 3 then v.(timerImageArg) else arg), OS_ERR_NONE)
  else (None, OS_ERR_TMR_INVALID_OPT).

(** The result is the state/error value at callback dispatch, before the
    callback and OSSchedUnlock.  A callback may restart or delete its own
    timer; this transformer does not claim the final API state is stopped. *)
Definition timer_stop_dispatch (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID) (opt arg : Z)
  : option (bool * OSErrCode * option (addr * addr * addr) * GlobTimerState) :=
  match s.(timerImages) i with
  | None => None
  | Some v =>
    if Z.eqb v.(timerImageState) 3 then
      match timer_unlink sg s i with
      | None => None
      | Some stopped => match stopped.(timerImages) i with
        | None => None
        | Some after => let '(request, err) := timer_stop_request sg i after opt arg in
          Some (true, err, request, stopped)
        end
      end
    else if orb (Z.eqb v.(timerImageState) 1) (Z.eqb v.(timerImageState) 2) then
      Some (true, OS_ERR_TMR_STOPPED, None, s)
    else if Z.eqb v.(timerImageState) 0 then Some (false, OS_ERR_TMR_INACTIVE, None, s)
    else Some (false, OS_ERR_TMR_INVALID_STATE, None, s)
  end.

Lemma valid_timer_state_image_live_or_free : forall sg s i v,
  valid_timer_state sg s -> s.(timerImages) i = Some v ->
  (In i s.(timerFree) /\ v.(timerImageType) = 100 /\ v.(timerImageState) = 0) \/
  exists t, s.(timerUsed) i = Some t /\
    v = timer_object_image t v.(timerImageNext) v.(timerImagePrev) v.(timerImagePadding).
Proof.
  intros sg s i v Hvalid Hv.
  destruct Hvalid as [Hpool [_ [_ [_ [_ [_ [_ [Hused [Hprivate [Hdomain [_ Hlinks]]]]]]]]]]].
  destruct (timerUsed s i) as [t|] eqn:Ht.
  - right; exists t; split; [reflexivity|].
    destruct (Hused i t Ht) as [_ [_ [_ [old [Hold Himage]]]]].
    rewrite Hv in Hold; injection Hold as E; subst old; exact Himage.
  - assert (Hpriv : timerPrivate s i = None).
    { destruct (timerPrivate s i) as [private|] eqn:Hp; [|reflexivity].
      destruct (Hprivate i private Hp) as [_ Hnone]; congruence. }
    assert (Hrange : 0 <= i < cfgMaxTimers (osKernelConfig sg))
      by (apply (proj1 (Hdomain i Hpriv)); eauto).
    assert (Hfree : In i (timerFree s)).
    { destruct (in_dec Z.eq_dec i (timerFree s)) as [Hin|Hnot]; [exact Hin|].
      destruct Hpool as [_ [_ Hslots]].
      destruct (proj2 (Hslots i) (conj Hrange Hnot)) as [u Hu].
      unfold timer_allocated_slots in Hu; rewrite Ht, Hpriv in Hu; discriminate. }
    left; split; [exact Hfree|].
    apply in_split in Hfree; destruct Hfree as [pre [rest Hfree]].
    destruct (Hlinks _ _ _ Hfree) as [old [Hold [Htype [Hstate _]]]].
    rewrite Hv in Hold; injection Hold as E; subst old; auto.
Qed.

Lemma valid_timer_state_nonunused_image : forall sg s i v,
  valid_timer_state sg s -> s.(timerImages) i = Some v -> v.(timerImageState) <> 0 ->
  exists t, s.(timerUsed) i = Some t /\ v.(timerImageState) = encode_timer_status t.(timerState).
Proof.
  intros sg s i v Hvalid Hv Hnonzero.
  destruct (valid_timer_state_image_live_or_free _ _ _ _ Hvalid Hv) as [[_ [_ Hz]]|[t [Ht Himage]]];
    [contradiction|].
  exists t; split; [exact Ht|]. rewrite Himage; reflexivity.
Qed.

Lemma valid_timer_state_image_type : forall sg s i v,
  valid_timer_state sg s -> s.(timerImages) i = Some v -> v.(timerImageType) = 100.
Proof.
  intros sg s i v Hvalid Hv.
  destruct (valid_timer_state_image_live_or_free _ _ _ _ Hvalid Hv) as [[_ [Htype _]]|[t [_ Himage]]];
    [exact Htype|rewrite Himage; reflexivity].
Qed.

Lemma valid_timer_state_image_status_in_range : forall sg s i v,
  valid_timer_state sg s -> s.(timerImages) i = Some v -> 0 <= v.(timerImageState) <= 3.
Proof.
  intros sg s i v Hvalid Hv.
  destruct (valid_timer_state_image_live_or_free _ _ _ _ Hvalid Hv) as [[_ [_ Hstate]]|[t [_ Himage]]].
  - rewrite Hstate; lia.
  - rewrite Himage; simpl; destruct (timerState t); simpl; lia.
Qed.

Lemma timer_start_locked_preserves_state_validity : forall sg s i ret err post,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> timer_start_locked sg s i = Some (ret, err, post) ->
  valid_timer_state sg post.
Proof.
  intros sg s i ret err post Hsize Hlayout Hvalid Hstep.
  unfold timer_start_locked in Hstep; destruct (timerImages s i) as [v|] eqn:Hv; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3) eqn:Hrun.
  - apply Z.eqb_eq in Hrun.
    destruct (valid_timer_state_nonunused_image _ _ _ _ Hvalid Hv ltac:(lia)) as [t [Ht Hstate]].
    assert (Hrunning : timerState t = TimerRunning) by (destruct (timerState t); simpl in Hstate; congruence).
    destruct (timer_unlink sg s i) as [stopped|] eqn:Hunlink; [|discriminate].
    destruct (timer_link sg stopped i false) as [linked|] eqn:Hlink; [|discriminate].
    inversion Hstep; subst ret err post.
    pose proof (timer_unlink_preserves_state_validity _ _ _ _ _ Hlayout Hvalid Ht Hrunning Hunlink) as Hstopped.
    destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hunlink) as [u [v0 [Hu [_ [Hustate _]]]]].
    eapply timer_link_preserves_state_validity; eauto; congruence.
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2)) eqn:Hstart.
    + apply Bool.orb_true_iff in Hstart; destruct Hstart as [Hstate|Hstate]; apply Z.eqb_eq in Hstate;
        destruct (valid_timer_state_nonunused_image _ _ _ _ Hvalid Hv ltac:(lia)) as [t [Ht Hencode]];
        assert (Hnotrun : timerState t <> TimerRunning) by (intros E; rewrite E in Hencode; simpl in Hencode; lia);
        destruct (timer_link sg s i false) as [linked|] eqn:Hlink; try discriminate;
        inversion Hstep; subst ret err post; eapply timer_link_preserves_state_validity; eauto.
    + destruct (Z.eqb (timerImageState v) 0); inversion Hstep; subst; exact Hvalid.
Qed.

Lemma timer_stop_dispatch_preserves_state_validity : forall sg s i opt arg ret err request post,
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> timer_stop_dispatch sg s i opt arg = Some (ret, err, request, post) ->
  valid_timer_state sg post.
Proof.
  intros sg s i opt arg ret err request post Hlayout Hvalid Hstep.
  unfold timer_stop_dispatch in Hstep; destruct (timerImages s i) as [v|] eqn:Hv; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3) eqn:Hrun.
  - apply Z.eqb_eq in Hrun.
    destruct (valid_timer_state_nonunused_image _ _ _ _ Hvalid Hv ltac:(lia)) as [t [Ht Hstate]].
    assert (Hrunning : timerState t = TimerRunning) by (destruct (timerState t); simpl in Hstate; congruence).
    destruct (timer_unlink sg s i) as [stopped|] eqn:Hunlink; [|discriminate].
    destruct (timerImages stopped i) as [after|]; [|discriminate].
    destruct (timer_stop_request sg i after opt arg) as [callback error]; inversion Hstep; subst ret err request post.
    eapply timer_unlink_preserves_state_validity; eauto.
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2));
      [|destruct (Z.eqb (timerImageState v) 0)]; inversion Hstep; subst; exact Hvalid.
Qed.

Lemma timer_start_locked_preserves_initialization_phase : forall sg s i ret err post,
  timer_start_locked sg s i = Some (ret, err, post) -> post.(timerInitPhase) = s.(timerInitPhase).
Proof.
  intros sg s i ret err post Hstep; unfold timer_start_locked in Hstep.
  destruct (timerImages s i) as [v|]; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3).
  - destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
    destruct (timer_link sg stopped i false) as [linked|] eqn:Hl; [|discriminate].
    inversion Hstep; subst; rewrite (timer_link_preserves_initialization_phase _ _ _ _ _ Hl).
    exact (timer_unlink_preserves_initialization_phase _ _ _ _ Hu).
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2)).
    + destruct (timer_link sg s i false) as [linked|] eqn:Hl; [|discriminate].
      inversion Hstep; subst; exact (timer_link_preserves_initialization_phase _ _ _ _ _ Hl).
    + destruct (Z.eqb (timerImageState v) 0); inversion Hstep; reflexivity.
Qed.

Lemma timer_stop_dispatch_preserves_initialization_phase : forall sg s i opt arg ret err request post,
  timer_stop_dispatch sg s i opt arg = Some (ret, err, request, post) ->
  post.(timerInitPhase) = s.(timerInitPhase).
Proof.
  intros sg s i opt arg ret err request post Hstep; unfold timer_stop_dispatch in Hstep.
  destruct (timerImages s i) as [v|]; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3).
  - destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
    destruct (timerImages stopped i) as [after|]; [|discriminate].
    destruct (timer_stop_request sg i after opt arg); inversion Hstep; subst;
      exact (timer_unlink_preserves_initialization_phase _ _ _ _ Hu).
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2));
      [|destruct (Z.eqb (timerImageState v) 0)]; inversion Hstep; reflexivity.
Qed.

Lemma timer_start_locked_preserves_configuration : forall sg s i ret err post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  timer_start_locked sg s i = Some (ret, err, post) ->
  valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i ret err post He Hsize Hlayout Hv Hp Hstep.
  assert (Hpostphase : timer_api_initialized post).
  { unfold timer_api_initialized in *; rewrite (timer_start_locked_preserves_initialization_phase _ _ _ _ _ _ Hstep); exact Hp. }
  split; [|exact Hpostphase]. apply (proj2 (timer_initialized_configuration_iff sg post He Hpostphase)).
  eapply timer_start_locked_preserves_state_validity; eauto.
  apply (proj1 (timer_initialized_configuration_iff sg s He Hp)); exact Hv.
Qed.

Lemma timer_stop_dispatch_preserves_configuration : forall sg s i opt arg ret err request post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  timer_stop_dispatch sg s i opt arg = Some (ret, err, request, post) ->
  valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i opt arg ret err request post He Hlayout Hv Hp Hstep.
  assert (Hpostphase : timer_api_initialized post).
  { unfold timer_api_initialized in *; rewrite (timer_stop_dispatch_preserves_initialization_phase _ _ _ _ _ _ _ _ _ Hstep); exact Hp. }
  split; [|exact Hpostphase]. apply (proj2 (timer_initialized_configuration_iff sg post He Hpostphase)).
  eapply timer_stop_dispatch_preserves_state_validity; eauto.
  apply (proj1 (timer_initialized_configuration_iff sg s He Hp)); exact Hv.
Qed.

Lemma timer_start_locked_unused : forall sg s i v,
  s.(timerImages) i = Some v -> v.(timerImageState) = 0 ->
  timer_start_locked sg s i = Some (false, OS_ERR_TMR_INACTIVE, s).
Proof. intros; unfold timer_start_locked; rewrite H, H0; reflexivity. Qed.

Lemma timer_stop_dispatch_unused : forall sg s i v opt arg,
  s.(timerImages) i = Some v -> v.(timerImageState) = 0 ->
  timer_stop_dispatch sg s i opt arg = Some (false, OS_ERR_TMR_INACTIVE, None, s).
Proof. intros; unfold timer_stop_dispatch; rewrite H, H0; reflexivity. Qed.

Lemma timer_stop_dispatch_stopped_completed : forall sg s i v opt arg,
  s.(timerImages) i = Some v -> (v.(timerImageState) = 1 \/ v.(timerImageState) = 2) ->
  timer_stop_dispatch sg s i opt arg = Some (true, OS_ERR_TMR_STOPPED, None, s).
Proof. intros; unfold timer_stop_dispatch; rewrite H; destruct H0; rewrite H0; reflexivity. Qed.

Lemma timer_start_locked_invalid_state : forall sg s i v,
  s.(timerImages) i = Some v ->
  v.(timerImageState) <> 0 -> v.(timerImageState) <> 1 ->
  v.(timerImageState) <> 2 -> v.(timerImageState) <> 3 ->
  timer_start_locked sg s i = Some (false, OS_ERR_TMR_INVALID_STATE, s).
Proof.
  intros sg s i v Hv H0 H1 H2 H3; unfold timer_start_locked; rewrite Hv.
  apply Z.eqb_neq in H0; apply Z.eqb_neq in H1; apply Z.eqb_neq in H2; apply Z.eqb_neq in H3.
  rewrite H0, H1, H2, H3; reflexivity.
Qed.

Lemma timer_stop_dispatch_invalid_state : forall sg s i v opt arg,
  s.(timerImages) i = Some v ->
  v.(timerImageState) <> 0 -> v.(timerImageState) <> 1 ->
  v.(timerImageState) <> 2 -> v.(timerImageState) <> 3 ->
  timer_stop_dispatch sg s i opt arg = Some (false, OS_ERR_TMR_INVALID_STATE, None, s).
Proof.
  intros sg s i v opt arg Hv H0 H1 H2 H3; unfold timer_stop_dispatch; rewrite Hv.
  apply Z.eqb_neq in H0; apply Z.eqb_neq in H1; apply Z.eqb_neq in H2; apply Z.eqb_neq in H3.
  rewrite H0, H1, H2, H3; reflexivity.
Qed.

Lemma timer_stop_request_none : forall sg i v arg,
  timer_stop_request sg i v 0 arg = (None, OS_ERR_NONE).
Proof. reflexivity. Qed.

Lemma timer_stop_request_default_argument : forall sg i v arg,
  v.(timerImageCallback) <> 0 -> timer_stop_request sg i v 3 arg =
    (Some (v.(timerImageCallback), timer_pool_addr sg i, v.(timerImageArg)), OS_ERR_NONE).
Proof. intros; unfold timer_stop_request; apply Z.eqb_neq in H; rewrite H; reflexivity. Qed.

Lemma timer_stop_request_explicit_argument : forall sg i v arg,
  v.(timerImageCallback) <> 0 -> timer_stop_request sg i v 4 arg =
    (Some (v.(timerImageCallback), timer_pool_addr sg i, arg), OS_ERR_NONE).
Proof. intros; unfold timer_stop_request; apply Z.eqb_neq in H; rewrite H; reflexivity. Qed.

Lemma timer_stop_request_missing_callback : forall sg i v opt arg,
  v.(timerImageCallback) = 0 -> (opt = 3 \/ opt = 4) ->
  timer_stop_request sg i v opt arg = (None, OS_ERR_TMR_NO_CALLBACK).
Proof. intros; unfold timer_stop_request; destruct H0; subst opt; rewrite H; reflexivity. Qed.

Lemma timer_stop_request_invalid_option : forall sg i v opt arg,
  opt <> 0 -> opt <> 3 -> opt <> 4 ->
  timer_stop_request sg i v opt arg = (None, OS_ERR_TMR_INVALID_OPT).
Proof.
  intros sg i v opt arg H0 H3 H4; unfold timer_stop_request.
  apply Z.eqb_neq in H0; apply Z.eqb_neq in H3; apply Z.eqb_neq in H4.
  rewrite H0, H3, H4; reflexivity.
Qed.

Lemma timer_stop_request_after_unlink_eq : forall sg i v opt arg,
  timer_stop_request sg i (timer_unlink_image v) opt arg = timer_stop_request sg i v opt arg.
Proof. reflexivity. Qed.

Lemma timer_stop_dispatch_invalid_option_still_unlinks : forall sg s i v opt arg ret err request post,
  s.(timerImages) i = Some v -> v.(timerImageState) = 3 ->
  opt <> 0 -> opt <> 3 -> opt <> 4 ->
  timer_stop_dispatch sg s i opt arg = Some (ret, err, request, post) ->
  ret = true /\ err = OS_ERR_TMR_INVALID_OPT /\ request = None /\ timer_unlink sg s i = Some post.
Proof.
  intros sg s i v opt arg ret err request post Hv Hstate H0 H3 H4 Hstep.
  unfold timer_stop_dispatch in Hstep; rewrite Hv, Hstate in Hstep; simpl in Hstep.
  destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
  destruct (timerImages stopped i) as [after|]; [|discriminate].
  rewrite (timer_stop_request_invalid_option sg i after opt arg H0 H3 H4) in Hstep.
  inversion Hstep; subst; auto.
Qed.

Lemma timer_unlink_target_object_eq : forall sg s i t post,
  s.(timerUsed) i = Some t -> timer_unlink sg s i = Some post ->
  post.(timerUsed) i = Some (timer_set_status t TimerStopped).
Proof.
  intros sg s i t post Ht Hstep; unfold timer_unlink in Hstep; rewrite Ht in Hstep.
  destruct (timerImages s i); [|discriminate]. inversion Hstep; subst.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerUsed]; apply kernel_map_set_same.
Qed.

Lemma timer_unlink_target_image_eq : forall sg s i v post,
  s.(timerImages) i = Some v -> timer_unlink sg s i = Some post ->
  post.(timerImages) i = Some (timer_unlink_image v).
Proof.
  intros sg s i v post Hv Hstep; unfold timer_unlink in Hstep; rewrite Hv in Hstep.
  destruct (timerUsed s i); [|discriminate]. inversion Hstep; subst.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerImages].
  apply timer_wheel_unlink_images_same.
Qed.

Lemma timer_link_target_object_eq : forall sg s i t periodic post,
  s.(timerUsed) i = Some t -> timer_link sg s i periodic = Some post ->
  post.(timerUsed) i = Some (timer_link_object s.(timerTime) periodic t).
Proof.
  intros sg s i t periodic post Ht Hstep; unfold timer_link in Hstep; rewrite Ht in Hstep.
  destruct (timerImages s i); [|discriminate]. inversion Hstep; subst.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerUsed]; apply kernel_map_set_same.
Qed.

Lemma timer_unlink_preserves_time : forall sg s i post,
  timer_unlink sg s i = Some post -> post.(timerTime) = s.(timerTime).
Proof.
  intros sg s i post Hstep; unfold timer_unlink in Hstep.
  destruct (timerUsed s i), (timerImages s i); try discriminate; inversion Hstep; reflexivity.
Qed.

Lemma timer_link_after_stop_object_eq : forall time periodic t,
  timer_link_object time periodic (timer_set_status t TimerStopped) = timer_link_object time periodic t.
Proof. reflexivity. Qed.

Lemma timer_start_locked_updates_live_object : forall sg s i t ret err post,
  valid_timer_state sg s -> s.(timerUsed) i = Some t ->
  timer_start_locked sg s i = Some (ret, err, post) ->
  ret = true /\ err = OS_ERR_NONE /\
    post.(timerUsed) i = Some (timer_link_object s.(timerTime) false t).
Proof.
  intros sg s i t ret err post Hvalid Ht Hstep.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused i t Ht) as [Htvalid [_ [_ [v [Hv Himage]]]]].
  assert (Hstate : timerImageState v = encode_timer_status (timerState t)) by (rewrite Himage; reflexivity).
  destruct Htvalid as [_ [_ [_ [Hnotunused _]]]].
  unfold timer_start_locked in Hstep; rewrite Hv, Hstate in Hstep.
  destruct (timerState t) eqn:Htstate; [contradiction| | |].
  - simpl in Hstep; destruct (timer_link sg s i false) as [linked|] eqn:Hl; [|discriminate].
    inversion Hstep; subst; split; [reflexivity|]; split; [reflexivity|].
    exact (timer_link_target_object_eq _ _ _ _ _ _ Ht Hl).
  - simpl in Hstep; destruct (timer_link sg s i false) as [linked|] eqn:Hl; [|discriminate].
    inversion Hstep; subst; split; [reflexivity|]; split; [reflexivity|].
    exact (timer_link_target_object_eq _ _ _ _ _ _ Ht Hl).
  - simpl in Hstep; destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
    destruct (timer_link sg stopped i false) as [linked|] eqn:Hl; [|discriminate].
    inversion Hstep; subst; split; [reflexivity|]; split; [reflexivity|].
    pose proof (timer_unlink_target_object_eq _ _ _ _ _ Ht Hu) as Hstopped.
    rewrite (timer_link_target_object_eq _ _ _ _ _ _ Hstopped Hl).
    rewrite (timer_unlink_preserves_time _ _ _ _ Hu), timer_link_after_stop_object_eq; reflexivity.
Qed.

Lemma timer_stop_dispatch_running : forall sg s i v opt arg post,
  s.(timerImages) i = Some v -> v.(timerImageState) = 3 -> timer_unlink sg s i = Some post ->
  timer_stop_dispatch sg s i opt arg =
    let '(request, err) := timer_stop_request sg i v opt arg in Some (true, err, request, post).
Proof.
  intros sg s i v opt arg post Hv Hstate Hu; unfold timer_stop_dispatch.
  rewrite Hv, Hstate; simpl; rewrite Hu.
  rewrite (timer_unlink_target_image_eq _ _ _ _ _ Hv Hu), timer_stop_request_after_unlink_eq; reflexivity.
Qed.

Lemma timer_link_result_exists : forall sg s i t v periodic,
  s.(timerUsed) i = Some t -> s.(timerImages) i = Some v ->
  exists post, timer_link sg s i periodic = Some post.
Proof. intros; unfold timer_link; rewrite H, H0; eexists; reflexivity. Qed.

Lemma timer_unlink_result_exists : forall sg s i t v,
  s.(timerUsed) i = Some t -> s.(timerImages) i = Some v ->
  exists post, timer_unlink sg s i = Some post.
Proof. intros; unfold timer_unlink; rewrite H, H0; eexists; reflexivity. Qed.

Lemma timer_start_locked_live_result_exists : forall sg s i t,
  valid_timer_state sg s -> s.(timerUsed) i = Some t ->
  exists post, timer_start_locked sg s i = Some (true, OS_ERR_NONE, post).
Proof.
  intros sg s i t Hvalid Ht.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused i t Ht) as [Htvalid [_ [_ [v [Hv Himage]]]]].
  assert (Hstate : timerImageState v = encode_timer_status (timerState t)) by (rewrite Himage; reflexivity).
  destruct Htvalid as [_ [_ [_ [Hnotunused _]]]].
  unfold timer_start_locked; rewrite Hv, Hstate.
  destruct (timerState t) eqn:Htstate; [contradiction| | |].
  - simpl; destruct (timer_link_result_exists sg s i t v false Ht Hv) as [post Hp].
    rewrite Hp; eexists; reflexivity.
  - simpl; destruct (timer_link_result_exists sg s i t v false Ht Hv) as [post Hp].
    rewrite Hp; eexists; reflexivity.
  - simpl; destruct (timer_unlink_result_exists sg s i t v Ht Hv) as [stopped Hu].
    rewrite Hu.
    pose proof (timer_unlink_target_object_eq _ _ _ _ _ Ht Hu) as Htstop.
    pose proof (timer_unlink_target_image_eq _ _ _ _ _ Hv Hu) as Hvstop.
    destruct (timer_link_result_exists sg stopped i _ _ false Htstop Hvstop) as [post Hp].
    rewrite Hp; eexists; reflexivity.
Qed.

Lemma timer_stop_dispatch_live_result_exists : forall sg s i t opt arg,
  valid_timer_state sg s -> s.(timerUsed) i = Some t ->
  exists err request post, timer_stop_dispatch sg s i opt arg = Some (true, err, request, post).
Proof.
  intros sg s i t opt arg Hvalid Ht.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused i t Ht) as [Htvalid [_ [_ [v [Hv Himage]]]]].
  assert (Hstate : timerImageState v = encode_timer_status (timerState t)) by (rewrite Himage; reflexivity).
  destruct Htvalid as [_ [_ [_ [Hnotunused _]]]].
  unfold timer_stop_dispatch; rewrite Hv, Hstate.
  destruct (timerState t) eqn:Htstate; [contradiction| | |].
  - simpl; eexists; eexists; eexists; reflexivity.
  - simpl; eexists; eexists; eexists; reflexivity.
  - simpl; destruct (timer_unlink_result_exists sg s i t v Ht Hv) as [stopped Hu].
    rewrite Hu, (timer_unlink_target_image_eq _ _ _ _ _ Hv Hu).
    destruct (timer_stop_request sg i (timer_unlink_image v) opt arg) as [request err].
    eexists; eexists; eexists; reflexivity.
Qed.

Definition timer_complete_image (v : TimerImage) : TimerImage :=
  {| timerImageType := v.(timerImageType); timerImageCallback := v.(timerImageCallback);
     timerImageArg := v.(timerImageArg); timerImageNext := v.(timerImageNext); timerImagePrev := v.(timerImagePrev);
     timerImageMatch := v.(timerImageMatch); timerImageDelay := v.(timerImageDelay);
     timerImagePeriod := v.(timerImagePeriod); timerImageName := v.(timerImageName);
     timerImageOption := v.(timerImageOption); timerImageState := 2; timerImagePadding := v.(timerImagePadding) |}.

(** OSTmr_Task's one-shot state store, after the timer has been unlinked.
    The raw operation has no invariant guard; the caller establishes that
    the object is absent from the wheel before using its preservation law. *)
Definition timer_complete (s : GlobTimerState) (i : TimerID) : option GlobTimerState :=
  match s.(timerUsed) i, s.(timerImages) i with
  | Some t, Some v => Some (timer_replace_wheel_objects s
      (kernel_map_set s.(timerUsed) i (Some (timer_set_status t TimerCompleted)))
      (kernel_map_set s.(timerImages) i (Some (timer_complete_image v))) s.(timerWheel))
  | _, _ => None
  end.

Lemma timer_complete_image_object_eq : forall v t,
  v = timer_object_image t v.(timerImageNext) v.(timerImagePrev) v.(timerImagePadding) ->
  timer_complete_image v = timer_object_image (timer_set_status t TimerCompleted)
    v.(timerImageNext) v.(timerImagePrev) v.(timerImagePadding).
Proof. intros v t H; rewrite H; reflexivity. Qed.

Lemma timer_complete_preserves_state_validity : forall sg s i t post,
  valid_timer_state sg s -> s.(timerUsed) i = Some t -> t.(timerState) <> TimerRunning ->
  timer_complete s i = Some post -> valid_timer_state sg post.
Proof.
  intros sg s i t post Hvalid Ht Hnotrunning Hstep.
  pose proof Hvalid as [Hpool [Hwheel [Htime [Hfreecount [Hsum [Hfc [Huc
    [Hused [Hprivate [Hdomain [Hpadding Hlinks]]]]]]]]]]].
  destruct (Hused i t Ht) as [Htvalid [Htgen [Hprivatei [old [Hold Himage]]]]].
  pose proof Hwheel as [Hlength [Hnd [Hmembers Hrows]]].
  assert (Hnotwheel : ~ In i (concat (timerWheel s))).
  { intros Hin; destruct (proj1 (Hmembers i) Hin) as [u [Hu Hrun]].
    rewrite Ht in Hu; injection Hu as E; subst u; contradiction. }
  assert (Hnotfree : ~ In i (timerFree s)).
  { destruct Hpool as [_ [_ Hslots]]; apply (proj2 (proj1 (Hslots i) ltac:(
      exists tt; unfold timer_allocated_slots; rewrite Ht; reflexivity))). }
  unfold timer_complete in Hstep; rewrite Ht, Hold in Hstep; injection Hstep as Hpost; rewrite <- Hpost.
  unfold valid_timer_state; cbv beta iota zeta delta [timer_replace_wheel_objects timerFree timerUsed
    timerImages timerPrivate timerWheel timerTime timerFreeCount timerUsedCount timerNextGeneration].
  fold (timerUsed s) (timerFree s) (timerImages s) (timerPrivate s) (timerWheel s)
    (timerTime s) (timerFreeCount s) (timerUsedCount s) (timerNextGeneration s).
  split.
  - destruct Hpool as [Hfreend [Hrange Hslots]]; split; [exact Hfreend|]; split; [exact Hrange|].
    intros j; unfold timer_allocated_slots; simpl; destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite kernel_map_set_same; split.
      * intros; apply (proj1 (Hslots i)); exists tt; unfold timer_allocated_slots; rewrite Ht; reflexivity.
      * intros; eauto.
    + rewrite kernel_map_set_other by exact Hne; apply Hslots.
  - split.
    + unfold timer_wheel_valid; simpl; split; [exact Hlength|]; split; [exact Hnd|]; split.
      * intros j; unfold timer_wheel_member; simpl; split.
        -- intros Hin; assert (Hne : j <> i) by (intros E; subst j; contradiction).
           destruct (proj1 (Hmembers j) Hin) as [u [Hu Hrun]].
           exists u; split; [rewrite kernel_map_set_other by exact Hne; exact Hu|exact Hrun].
        -- intros [u [Hu Hrun]]; destruct (Z.eq_dec j i) as [->|Hne].
           ++ rewrite kernel_map_set_same in Hu; injection Hu as E; subst u; discriminate.
           ++ rewrite kernel_map_set_other in Hu by exact Hne; apply (proj2 (Hmembers j)); eauto.
      * intros n row pre j rest Hrow Hlist.
        assert (Hne : j <> i).
        { intros E; subst j; apply Hnotwheel; eapply timer_wheel_row_member; [exact Hrow|].
          rewrite Hlist; apply in_or_app; right; left; reflexivity. }
        destruct (Hrows n row pre j rest Hrow Hlist) as [u [v [Hu [Hv Hfields]]]].
        exists u, v; split; [rewrite kernel_map_set_other by exact Hne; exact Hu|].
        split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hfields].
    + split; [exact Htime|]; split; [exact Hfreecount|]; split; [exact Hsum|].
      split; [exact Hfc|]; split; [exact Huc|]; split.
      * intros j u Hu; destruct (Z.eq_dec j i) as [->|Hne].
        -- rewrite kernel_map_set_same in Hu; injection Hu as E; subst u.
           split; [apply timer_set_status_preserves_object_validity; [exact Htvalid|discriminate]|].
           split; [exact Htgen|]; split; [exact Hprivatei|].
           exists (timer_complete_image old); split; [apply kernel_map_set_same|].
           exact (timer_complete_image_object_eq old t Himage).
        -- rewrite kernel_map_set_other in Hu by exact Hne.
           destruct (Hused j u Hu) as [Huvalid [Hugen [Hpriv [v [Hv Hobject]]]]].
           split; [exact Huvalid|]; split; [exact Hugen|]; split; [exact Hpriv|].
           exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hobject].
      * split.
        -- intros j private Hp; destruct (Hprivate j private Hp) as [Hu Hv].
           assert (Hne : j <> i) by (intros E; subst j; congruence).
           rewrite !kernel_map_set_other by exact Hne; auto.
        -- split.
           ++ intros j Hp; destruct (Z.eq_dec j i) as [->|Hne].
              ** rewrite kernel_map_set_same; split.
                 --- intros; apply (proj1 (Hdomain i Hprivatei)); eauto.
                 --- eauto.
              ** rewrite kernel_map_set_other by exact Hne; apply Hdomain; exact Hp.
           ++ split.
              ** intros j v Hv; destruct (Z.eq_dec j i) as [->|Hne].
                 --- rewrite kernel_map_set_same in Hv; injection Hv as E; subst v; exact (Hpadding i old Hold).
                 --- rewrite kernel_map_set_other in Hv by exact Hne; eapply Hpadding; eauto.
              ** intros pre j rest Hlist.
                 assert (Hne : j <> i).
                 { intros E; subst j; apply Hnotfree; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
                 destruct (Hlinks pre j rest Hlist) as [v [Hv Hfields]].
                 exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hfields].
Qed.

Lemma timer_complete_preserves_initialization_phase : forall s i post,
  timer_complete s i = Some post -> post.(timerInitPhase) = s.(timerInitPhase).
Proof.
  intros s i post H; unfold timer_complete in H.
  destruct (timerUsed s i), (timerImages s i); try discriminate; inversion H; reflexivity.
Qed.

(** One inner-loop visit, up to callback dispatch.  Next is captured before
    unlink/relink; advancing OSTmrTime and obtaining the wheel head are
    separate service steps.  No callback execution is hidden here. *)
Definition timer_expire_dispatch (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID)
  : option (addr * option (addr * addr * addr) * GlobTimerState) :=
  match s.(timerImages) i with
  | None => None
  | Some v =>
    if Z.eqb s.(timerTime) v.(timerImageMatch) then
      match timer_unlink sg s i with
      | None => None
      | Some unlinked => match unlinked.(timerImages) i with
        | None => None
        | Some after =>
          let updated := if Z.eqb after.(timerImageOption) 2 then timer_link sg unlinked i true
            else timer_complete unlinked i in
          match updated with
          | None => None
          | Some post => match post.(timerImages) i with
            | None => None
            | Some callv => Some (v.(timerImageNext),
              if Z.eqb callv.(timerImageCallback) 0 then None else
                Some (callv.(timerImageCallback), timer_pool_addr sg i, callv.(timerImageArg)), post)
            end
          end
        end
      end
    else Some (v.(timerImageNext), None, s)
  end.

Lemma timer_expire_dispatch_preserves_state_validity : forall sg s i t next request post,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> s.(timerUsed) i = Some t -> t.(timerState) = TimerRunning ->
  timer_expire_dispatch sg s i = Some (next, request, post) -> valid_timer_state sg post.
Proof.
  intros sg s i t next request post Hsize Hlayout Hvalid Ht Hrun Hstep.
  unfold timer_expire_dispatch in Hstep; destruct (timerImages s i) as [v|]; [|discriminate].
  destruct (Z.eqb (timerTime s) (timerImageMatch v)).
  - destruct (timer_unlink sg s i) as [unlinked|] eqn:Hu; [|discriminate].
    pose proof (timer_unlink_preserves_state_validity _ _ _ _ _ Hlayout Hvalid Ht Hrun Hu) as Hvu.
    destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hu) as [u [uv [Hut [_ [Hustate _]]]]].
    destruct (timerImages unlinked i) as [after|]; [|discriminate].
    destruct (Z.eqb (timerImageOption after) 2).
    + destruct (timer_link sg unlinked i true) as [linked|] eqn:Hl; [|discriminate].
      destruct (timerImages linked i); [|discriminate]; inversion Hstep; subst.
      eapply timer_link_preserves_state_validity; eauto; congruence.
    + destruct (timer_complete unlinked i) as [completed|] eqn:Hc; [|discriminate].
      destruct (timerImages completed i); [|discriminate]; inversion Hstep; subst.
      eapply timer_complete_preserves_state_validity; eauto; congruence.
  - inversion Hstep; subst; exact Hvalid.
Qed.

Lemma timer_expire_dispatch_preserves_initialization_phase : forall sg s i next request post,
  timer_expire_dispatch sg s i = Some (next, request, post) -> post.(timerInitPhase) = s.(timerInitPhase).
Proof.
  intros sg s i next request post Hstep; unfold timer_expire_dispatch in Hstep.
  destruct (timerImages s i) as [v|]; [|discriminate].
  destruct (Z.eqb (timerTime s) (timerImageMatch v)).
  - destruct (timer_unlink sg s i) as [unlinked|] eqn:Hu; [|discriminate].
    destruct (timerImages unlinked i) as [after|]; [|discriminate].
    destruct (Z.eqb (timerImageOption after) 2).
    + destruct (timer_link sg unlinked i true) as [linked|] eqn:Hl; [|discriminate].
      destruct (timerImages linked i); [|discriminate]; inversion Hstep; subst.
      rewrite (timer_link_preserves_initialization_phase _ _ _ _ _ Hl).
      exact (timer_unlink_preserves_initialization_phase _ _ _ _ Hu).
    + destruct (timer_complete unlinked i) as [completed|] eqn:Hc; [|discriminate].
      destruct (timerImages completed i); [|discriminate]; inversion Hstep; subst.
      rewrite (timer_complete_preserves_initialization_phase _ _ _ Hc).
      exact (timer_unlink_preserves_initialization_phase _ _ _ _ Hu).
  - inversion Hstep; reflexivity.
Qed.

Lemma timer_expire_dispatch_preserves_configuration : forall sg s i t next request post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  s.(timerUsed) i = Some t -> t.(timerState) = TimerRunning ->
  timer_expire_dispatch sg s i = Some (next, request, post) ->
  valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i t next request post He Hsize Hlayout Hv Hp Ht Hrun Hstep.
  assert (Hpostphase : timer_api_initialized post).
  { unfold timer_api_initialized in *; rewrite (timer_expire_dispatch_preserves_initialization_phase _ _ _ _ _ _ Hstep); exact Hp. }
  split; [|exact Hpostphase]. apply (proj2 (timer_initialized_configuration_iff sg post He Hpostphase)).
  eapply timer_expire_dispatch_preserves_state_validity; eauto.
  apply (proj1 (timer_initialized_configuration_iff sg s He Hp)); exact Hv.
Qed.

Lemma timer_expire_dispatch_cached_next : forall sg s i v next request post,
  s.(timerImages) i = Some v -> timer_expire_dispatch sg s i = Some (next, request, post) ->
  next = v.(timerImageNext).
Proof.
  intros sg s i v next request post Hv Hstep; unfold timer_expire_dispatch in Hstep; rewrite Hv in Hstep.
  destruct (Z.eqb (timerTime s) (timerImageMatch v)); [|inversion Hstep; reflexivity].
  destruct (timer_unlink sg s i) as [unlinked|]; [|discriminate].
  destruct (timerImages unlinked i) as [after|]; [|discriminate].
  destruct (Z.eqb (timerImageOption after) 2).
  - destruct (timer_link sg unlinked i true) as [linked|]; [|discriminate].
    destruct (timerImages linked i); [|discriminate]; inversion Hstep; reflexivity.
  - destruct (timer_complete unlinked i) as [completed|]; [|discriminate].
    destruct (timerImages completed i); [|discriminate]; inversion Hstep; reflexivity.
Qed.

Lemma timer_expire_dispatch_not_due : forall sg s i v,
  s.(timerImages) i = Some v -> s.(timerTime) <> v.(timerImageMatch) ->
  timer_expire_dispatch sg s i = Some (v.(timerImageNext), None, s).
Proof. intros; unfold timer_expire_dispatch; rewrite H; apply Z.eqb_neq in H0; rewrite H0; reflexivity. Qed.

Lemma timer_complete_target_object_eq : forall s i t post,
  s.(timerUsed) i = Some t -> timer_complete s i = Some post ->
  post.(timerUsed) i = Some (timer_set_status t TimerCompleted).
Proof.
  intros s i t post Ht Hstep; unfold timer_complete in Hstep; rewrite Ht in Hstep.
  destruct (timerImages s i); [|discriminate]; inversion Hstep; subst.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerUsed]; apply kernel_map_set_same.
Qed.

Lemma timer_complete_target_image_eq : forall s i v post,
  s.(timerImages) i = Some v -> timer_complete s i = Some post ->
  post.(timerImages) i = Some (timer_complete_image v).
Proof.
  intros s i v post Hv Hstep; unfold timer_complete in Hstep; rewrite Hv in Hstep.
  destruct (timerUsed s i); [|discriminate]; inversion Hstep; subst.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerImages]; apply kernel_map_set_same.
Qed.

Lemma timer_set_status_last_write : forall t first last,
  timer_set_status (timer_set_status t first) last = timer_set_status t last.
Proof. reflexivity. Qed.

Lemma timer_expire_dispatch_due_updates_live_object : forall sg s i t next request post,
  valid_timer_state sg s -> s.(timerUsed) i = Some t -> s.(timerTime) = t.(timerMatch) ->
  timer_expire_dispatch sg s i = Some (next, request, post) ->
  post.(timerUsed) i = Some (timer_expire_object s.(timerTime) t).
Proof.
  intros sg s i t next request post Hvalid Ht Hdue Hstep.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused i t Ht) as [_ [_ [_ [v [Hv Himage]]]]].
  assert (Hmatch : timerImageMatch v = timerMatch t) by (rewrite Himage; reflexivity).
  assert (Hopt : timerImageOption v = encode_timer_mode (timerMode t)) by (rewrite Himage; reflexivity).
  unfold timer_expire_dispatch in Hstep; rewrite Hv, Hmatch, Hdue, Z.eqb_refl in Hstep.
  destruct (timer_unlink sg s i) as [unlinked|] eqn:Hu; [|discriminate].
  rewrite (timer_unlink_target_image_eq _ _ _ _ _ Hv Hu) in Hstep.
  change (timerImageOption v) with (timerImageOption (timer_unlink_image v)) in Hopt.
  rewrite Hopt in Hstep.
  pose proof (timer_unlink_target_object_eq _ _ _ _ _ Ht Hu) as Htu.
  unfold timer_expire_object; destruct (timerMode t) eqn:Hmode.
  - simpl in Hstep; destruct (timer_complete unlinked i) as [completed|] eqn:Hc; [|discriminate].
    destruct (timerImages completed i); [|discriminate]; inversion Hstep; subst.
    rewrite (timer_complete_target_object_eq _ _ _ _ Htu Hc), timer_set_status_last_write; reflexivity.
  - simpl in Hstep; destruct (timer_link sg unlinked i true) as [linked|] eqn:Hl; [|discriminate].
    destruct (timerImages linked i); [|discriminate]; inversion Hstep; subst.
    rewrite (timer_link_target_object_eq _ _ _ _ _ _ Htu Hl), (timer_unlink_preserves_time _ _ _ _ Hu).
    rewrite timer_link_after_stop_object_eq; reflexivity.
Qed.

Definition timer_object_rep_without_state (c : KernelConfiguration) (p : addr) (v : TimerImage) : Assertion :=
  p # UChar |-> v.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) ** (p + 8) # Ptr |-> v.(timerImageArg) **
  (p + 12) # Ptr |-> v.(timerImageNext) ** (p + 16) # Ptr |-> v.(timerImagePrev) **
  (p + 20) # UInt |-> v.(timerImageMatch) ** (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (if c.(cfgTimerNames) then (p + 32) # Ptr |-> v.(timerImageName) else emp) **
  (p + timer_option_offset c) # UChar |-> v.(timerImageOption) **
  store_optional_bytes (p + timer_option_offset c + 2) (skipn 3 v.(timerImagePadding)).

Lemma timer_object_rep_split_state : forall c p v,
  timer_object_rep c p v |--
    (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) ** timer_object_rep_without_state c p v.
Proof. intros; unfold timer_object_rep, timer_object_rep_without_state; entailer!. Qed.

Lemma timer_object_rep_merge_completed_state : forall c p v,
  (p + timer_option_offset c + 1) # UChar |-> 2 ** timer_object_rep_without_state c p v |--
    timer_object_rep c p (timer_complete_image v).
Proof. intros; unfold timer_object_rep, timer_object_rep_without_state, timer_complete_image; simpl; entailer!. Qed.

Definition timer_complete_rep_without_state (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID)
  (v : TimerImage) : Assertion :=
  timer_object_rep_without_state sg.(osKernelConfig) (timer_pool_addr sg i) v ** timer_images_without sg s i **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) ** timer_globals_rep sg s.

Lemma timer_complete_split_state : forall sg s i v,
  s.(timerImages) i = Some v -> timer_raw_rep sg s |--
    (timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1) # UChar |-> v.(timerImageState) **
    timer_complete_rep_without_state sg s i v.
Proof.
  intros sg s i v Hv; unfold timer_raw_rep, timer_complete_rep_without_state.
  sep_apply_l_atomic (timer_images_split_object sg s i v Hv).
  sep_apply_l_atomic (timer_object_rep_split_state sg.(osKernelConfig) (timer_pool_addr sg i) v); entailer!.
Qed.

Lemma timer_complete_merge_state : forall sg s i v post,
  s.(timerImages) i = Some v -> timer_complete s i = Some post ->
  (timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1) # UChar |-> 2 **
    timer_complete_rep_without_state sg s i v |-- timer_raw_rep sg post.
Proof.
  intros sg s i v post Hv Hstep.
  unfold timer_complete in Hstep; rewrite Hv in Hstep; destruct (timerUsed s i) as [t|]; [|discriminate].
  injection Hstep as Hpost.
  assert (Himages : timerImages post = kernel_map_set (timerImages s) i (Some (timer_complete_image v)))
    by (rewrite <- Hpost; reflexivity).
  assert (Hwheel : timerWheel post = timerWheel s) by (rewrite <- Hpost; reflexivity).
  assert (Hglobals : timer_globals_rep sg post = timer_globals_rep sg s) by (rewrite <- Hpost; reflexivity).
  unfold timer_complete_rep_without_state.
  sep_apply_l_atomic (timer_object_rep_merge_completed_state sg.(osKernelConfig) (timer_pool_addr sg i) v).
  sep_apply_l_atomic (timer_images_merge_updated_object sg s post i (timer_complete_image v)
    ltac:(rewrite Himages; apply kernel_map_set_same)
    ltac:(intros; rewrite Himages; symmetry; apply kernel_map_set_other; assumption)).
  unfold timer_raw_rep; rewrite Hwheel, Hglobals; entailer!.
Qed.

(** The local traversal records the successor chain still to be read.
    Prev is intentionally absent: unlinking/restarting the current timer
    can update a future node's Prev without changing this traversal. *)
Definition timer_scan_chain_valid (sg : StableGlobVars) (s : GlobTimerState)
  (remaining : list TimerID) : Prop :=
  NoDup remaining /\
  forall pre i rest, remaining = pre ++ i :: rest ->
    exists t v, s.(timerUsed) i = Some t /\ t.(timerState) = TimerRunning /\
      s.(timerImages) i = Some v /\ v.(timerImageNext) = timer_id_pointer sg rest.

Definition timer_scan_continuation_valid (sg : StableGlobVars) (s : GlobTimerState)
  (scan : TimerScanState) : Prop :=
  s.(timerTime) = scan.(timerScanTime) /\
  timer_scan_chain_valid sg s scan.(timerScanRemaining) /\
  match scan.(timerScanNext) with
  | None => scan.(timerScanRemaining) = []
  | Some (i, generation) => exists t rest,
      scan.(timerScanRemaining) = i :: rest /\ s.(timerUsed) i = Some t /\
      t.(timerGeneration) = generation
  end.

(** This is a proved callback-body obligation, not a universal property
    of C callbacks.  Generation/Running protect later unlink operations;
    Next protects their order.  The next visit reads other fields afresh. *)
Definition timer_callback_preserves_scan (before after : GlobTimerState) (scan : TimerScanState) : Prop :=
  after.(timerTime) = before.(timerTime) /\
  forall i, In i scan.(timerScanRemaining) ->
    option_map (fun t => (t.(timerGeneration), t.(timerState))) (after.(timerUsed) i) =
      option_map (fun t => (t.(timerGeneration), t.(timerState))) (before.(timerUsed) i) /\
    option_map timerImageNext (after.(timerImages) i) =
      option_map timerImageNext (before.(timerImages) i).

Lemma timer_callback_preserves_scan_reflexive : forall s scan,
  timer_callback_preserves_scan s s scan.
Proof. intros; split; [reflexivity|intros; split; reflexivity]. Qed.

Lemma timer_callback_preserves_scan_transitive : forall first middle last scan,
  timer_callback_preserves_scan first middle scan ->
  timer_callback_preserves_scan middle last scan ->
  timer_callback_preserves_scan first last scan.
Proof.
  intros first middle last scan [Ht Hf] [Ht' Hf']; split; [congruence|].
  intros i Hi; destruct (Hf i Hi), (Hf' i Hi); split; congruence.
Qed.

Lemma timer_callback_preserves_continuation : forall sg before after scan,
  timer_scan_continuation_valid sg before scan -> timer_callback_preserves_scan before after scan ->
  timer_scan_continuation_valid sg after scan.
Proof.
  intros sg before after scan [Htime [[Hnd Hchain] Hcached]] [Ht Hframe].
  split; [congruence|]. split.
  - split; [exact Hnd|]. intros pre i rest Hlist.
    destruct (Hchain pre i rest Hlist) as [t [v [Htold [Hrun [Hvold Hnext]]]]].
    assert (Hin : In i (timerScanRemaining scan)) by (rewrite Hlist; apply in_or_app; right; left; reflexivity).
    destruct (Hframe i Hin) as [Hused Himage]; rewrite Htold in Hused; rewrite Hvold in Himage.
    destruct (timerUsed after i) as [t'|] eqn:Htnew; [|discriminate].
    destruct (timerImages after i) as [v'|] eqn:Hvnew; [|discriminate].
    simpl in Hused, Himage; inversion Hused; inversion Himage.
    exists t', v'; split; [reflexivity|]. split; [congruence|]. split; [reflexivity|congruence].
  - destruct (timerScanNext scan) as [[i generation]|]; [|exact Hcached].
    destruct Hcached as [t [rest [Hlist [Htold Hgen]]]].
    destruct (Hframe i ltac:(rewrite Hlist; left; reflexivity)) as [Hused _].
    rewrite Htold in Hused; destruct (timerUsed after i) as [t'|] eqn:Htnew; [|discriminate].
    simpl in Hused; inversion Hused.
    exists t', rest; split; [exact Hlist|]. split; [reflexivity|congruence].
Qed.

Lemma timer_scan_continuation_remaining_running : forall sg s scan i,
  timer_scan_continuation_valid sg s scan -> In i scan.(timerScanRemaining) ->
  exists t, s.(timerUsed) i = Some t /\ t.(timerState) = TimerRunning.
Proof.
  intros sg s scan i [_ [[_ Hchain] _]] Hin.
  apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
  destruct (Hchain pre i rest Hlist) as [t [v [Ht [Hrun _]]]]; exists t; auto.
Qed.

Lemma timer_images_set_prev_next_frame : forall images i prev q,
  option_map timerImageNext (timer_images_set_prev images i prev q) =
    option_map timerImageNext (images q).
Proof.
  intros; rewrite timer_images_set_prev_lookup.
  destruct (images q); [|reflexivity]; simpl; destruct (Z.eq_dec q i); reflexivity.
Qed.

Lemma timer_wheel_prepend_images_next_frame : forall sg images i v row q,
  q <> i ->
  option_map timerImageNext (timer_wheel_prepend_images sg images i v row q) =
    option_map timerImageNext (images q).
Proof.
  intros; unfold timer_wheel_prepend_images; rewrite kernel_map_set_other by assumption.
  destruct row; [reflexivity|apply timer_images_set_prev_next_frame].
Qed.

Lemma timer_link_preserves_scan : forall sg s scan i periodic post,
  ~ In i scan.(timerScanRemaining) -> timer_link sg s i periodic = Some post ->
  timer_callback_preserves_scan s post scan.
Proof.
  intros sg s scan i periodic post Houtside Hstep.
  unfold timer_link in Hstep; destruct (timerUsed s i), (timerImages s i); try discriminate.
  inversion Hstep; subst post.
  unfold timer_callback_preserves_scan.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerTime timerUsed timerImages].
  fold (timerTime s) (timerUsed s) (timerImages s).
  split; [reflexivity|]. intros q Hq.
  assert (Hne : q <> i) by (intro H; subst q; contradiction).
  split; [rewrite kernel_map_set_other by exact Hne; reflexivity|].
  apply timer_wheel_prepend_images_next_frame; exact Hne.
Qed.

(** Only the non-head branch writes a predecessor's Next.  A successor's
    Prev update is not a scan-read conflict. *)
Definition timer_unlink_scan_footprint (sg : StableGlobVars) (s : GlobTimerState)
  (i : TimerID) (scan : TimerScanState) : Prop :=
  forall old, s.(timerImages) i = Some old ->
    timer_id_pointer sg (nth (Z.to_nat (timer_spoke sg.(osKernelConfig) old.(timerImageMatch))) s.(timerWheel) []) = timer_pool_addr sg i \/
    ~ In (timer_pointer_index sg old.(timerImagePrev)) scan.(timerScanRemaining).

Lemma timer_unlink_preserves_scan : forall sg s scan i post,
  ~ In i scan.(timerScanRemaining) -> timer_unlink_scan_footprint sg s i scan ->
  timer_unlink sg s i = Some post -> timer_callback_preserves_scan s post scan.
Proof.
  intros sg s scan i post Houtside Hfoot Hstep.
  unfold timer_unlink in Hstep; destruct (timerUsed s i) as [t|]; [|discriminate].
  destruct (timerImages s i) as [old|] eqn:Hold; [|discriminate].
  inversion Hstep; subst post.
  unfold timer_callback_preserves_scan.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerTime timerUsed timerImages].
  fold (timerTime s) (timerUsed s) (timerImages s) (timerWheel s).
  split; [reflexivity|]. intros q Hq.
  assert (Hne : q <> i) by (intro H; subst q; contradiction).
  split; [rewrite kernel_map_set_other by exact Hne; reflexivity|].
  unfold timer_wheel_unlink_images; rewrite kernel_map_set_other by exact Hne.
  destruct (Z.eqb (timerImageNext old) 0); rewrite ?timer_images_set_prev_next_frame;
    destruct (Z.eqb (timer_id_pointer sg (nth (Z.to_nat (timer_spoke (osKernelConfig sg) (timerImageMatch old)))
      (timerWheel s) [])) (timer_pool_addr sg i)) eqn:Hhead; [reflexivity| |reflexivity|].
  all: destruct (Hfoot old Hold) as [Hfirst|Hprev].
  all: try (apply Z.eqb_neq in Hhead; contradiction).
  all: unfold timer_images_set_next; rewrite kernel_map_set_other; [reflexivity|congruence].
Qed.

Lemma timer_release_preserves_scan : forall sg s scan i old name,
  ~ In i scan.(timerScanRemaining) ->
  timer_callback_preserves_scan s (timer_release sg s i old name) scan.
Proof.
  intros; unfold timer_callback_preserves_scan, timer_release; simpl.
  split; [reflexivity|]. intros q Hq; assert (Hne : q <> i) by (intro Heq; subst q; contradiction).
  rewrite !kernel_map_set_other by exact Hne; split; reflexivity.
Qed.

Lemma timer_release_invalidates_remaining_scan : forall sg s scan i old name,
  In i scan.(timerScanRemaining) ->
  ~ timer_scan_continuation_valid sg (timer_release sg s i old name) scan.
Proof.
  intros sg s scan i old name Hin Hscan.
  destruct (timer_scan_continuation_remaining_running _ _ _ _ Hscan Hin) as [t [Ht _]].
  rewrite timer_release_removes_live_object in Ht; discriminate.
Qed.

Lemma timer_unlink_invalidates_remaining_scan : forall sg s scan i post,
  In i scan.(timerScanRemaining) -> timer_unlink sg s i = Some post ->
  ~ timer_scan_continuation_valid sg post scan.
Proof.
  intros sg s scan i post Hin Hstep Hscan.
  destruct (timer_scan_continuation_remaining_running _ _ _ _ Hscan Hin) as [t [Ht Hrun]].
  destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hstep) as [u [v [Hu [_ [Hstop _]]]]].
  rewrite Ht in Hu; inversion Hu; subst u; congruence.
Qed.

Lemma timer_start_locked_preserves_scan : forall sg s scan i ret err post,
  ~ In i scan.(timerScanRemaining) ->
  (forall v, s.(timerImages) i = Some v -> v.(timerImageState) = 3 ->
    timer_unlink_scan_footprint sg s i scan) ->
  timer_start_locked sg s i = Some (ret, err, post) ->
  timer_callback_preserves_scan s post scan.
Proof.
  intros sg s scan i ret err post Houtside Hfoot Hstep.
  unfold timer_start_locked in Hstep; destruct (timerImages s i) as [v|] eqn:Hv; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3) eqn:Hrun.
  - destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
    destruct (timer_link sg stopped i false) as [linked|] eqn:Hl; [|discriminate].
    inversion Hstep; subst post; eapply timer_callback_preserves_scan_transitive.
    + eapply timer_unlink_preserves_scan; [exact Houtside| |exact Hu].
      apply (Hfoot v eq_refl); apply Z.eqb_eq; exact Hrun.
    + eapply timer_link_preserves_scan; eauto.
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2)).
    + destruct (timer_link sg s i false) as [linked|] eqn:Hl; [|discriminate].
      inversion Hstep; subst post; eapply timer_link_preserves_scan; eauto.
    + destruct (Z.eqb (timerImageState v) 0); inversion Hstep; subst post;
        apply timer_callback_preserves_scan_reflexive.
Qed.

Lemma timer_stop_dispatch_preserves_scan : forall sg s scan i opt arg ret err request post,
  ~ In i scan.(timerScanRemaining) ->
  (forall v, s.(timerImages) i = Some v -> v.(timerImageState) = 3 ->
    timer_unlink_scan_footprint sg s i scan) ->
  timer_stop_dispatch sg s i opt arg = Some (ret, err, request, post) ->
  timer_callback_preserves_scan s post scan.
Proof.
  intros sg s scan i opt arg ret err request post Houtside Hfoot Hstep.
  unfold timer_stop_dispatch in Hstep; destruct (timerImages s i) as [v|] eqn:Hv; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3) eqn:Hrun.
  - destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
    destruct (timerImages stopped i); [|discriminate]; destruct (timer_stop_request sg i t opt arg).
    inversion Hstep; subst post; eapply timer_unlink_preserves_scan; [exact Houtside| |exact Hu].
    apply (Hfoot v eq_refl); apply Z.eqb_eq; exact Hrun.
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2));
      [|destruct (Z.eqb (timerImageState v) 0)]; inversion Hstep; subst post;
      apply timer_callback_preserves_scan_reflexive.
Qed.

(** The locked state switch of OSTmrDel.  Pointer/type/ISR/safety guards
    are outside this cutpoint.  The name argument denotes the source's
    static default-name literal used by OSTmr_Free. *)
Definition timer_delete_locked (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID) (name : addr)
  : option (bool * OSErrCode * GlobTimerState) :=
  match s.(timerImages) i with
  | None => None
  | Some v =>
    if Z.eqb v.(timerImageState) 3 then
      match timer_unlink sg s i with
      | None => None
      | Some stopped => match stopped.(timerImages) i with
        | None => None
        | Some after => Some (true, OS_ERR_NONE, timer_release sg stopped i after name)
        end
      end
    else if orb (Z.eqb v.(timerImageState) 1) (Z.eqb v.(timerImageState) 2) then
      Some (true, OS_ERR_NONE, timer_release sg s i v name)
    else if Z.eqb v.(timerImageState) 0 then Some (false, OS_ERR_TMR_INACTIVE, s)
    else Some (false, OS_ERR_TMR_INVALID_STATE, s)
  end.

Lemma timer_unlink_service_globals_eq : forall sg before i after,
  timer_unlink sg before i = Some after ->
  timer_service_globals_rep sg after = timer_service_globals_rep sg before.
Proof.
  intros sg before i after Hstep; unfold timer_unlink in Hstep.
  destruct (timerUsed before i), (timerImages before i); try discriminate.
  inversion Hstep; reflexivity.
Qed.

Lemma timer_images_set_next_types_eq : forall images i next,
  timer_image_types (timer_images_set_next images i next) = timer_image_types images.
Proof.
  intros; apply functional_extensionality; intro j.
  unfold timer_image_types; rewrite timer_images_set_next_lookup.
  destruct (images j); destruct (Z.eq_dec j i); reflexivity.
Qed.

Lemma timer_images_set_prev_types_eq : forall images i prev,
  timer_image_types (timer_images_set_prev images i prev) = timer_image_types images.
Proof.
  intros; apply functional_extensionality; intro j.
  unfold timer_image_types; rewrite timer_images_set_prev_lookup.
  destruct (images j); destruct (Z.eq_dec j i); reflexivity.
Qed.

Lemma timer_wheel_unlink_image_types_eq : forall sg images i old row,
  images i = Some old ->
  timer_image_types (timer_wheel_unlink_images sg images i old row) = timer_image_types images.
Proof.
  intros sg images i old row Hlookup.
  unfold timer_wheel_unlink_images.
  set (images1 := if Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i)
    then images else timer_images_set_next images (timer_pointer_index sg (timerImagePrev old))
      (timerImageNext old)).
  set (images2 := if Z.eqb (timerImageNext old) 0 then images1 else
    timer_images_set_prev images1 (timer_pointer_index sg (timerImageNext old))
      (if Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i) then 0 else timerImagePrev old)).
  assert (Htypes : timer_image_types images2 = timer_image_types images).
  { unfold images2; destruct (Z.eqb (timerImageNext old) 0);
      [|rewrite timer_images_set_prev_types_eq];
      unfold images1; destruct (Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i));
      [reflexivity|apply timer_images_set_next_types_eq|reflexivity|apply timer_images_set_next_types_eq]. }
  apply functional_extensionality; intro j.
  unfold timer_image_types at 1.
  destruct (Z.eq_dec j i) as [->|Hji].
  - rewrite kernel_map_set_same; unfold timer_image_types; rewrite Hlookup; reflexivity.
  - rewrite kernel_map_set_other by exact Hji; exact (f_equal (fun m => m j) Htypes).
Qed.

Lemma timer_unlink_image_types_eq : forall sg before i after,
  timer_unlink sg before i = Some after ->
  timer_image_types after.(timerImages) = timer_image_types before.(timerImages).
Proof.
  intros sg before i after Hstep; unfold timer_unlink in Hstep.
  destruct (timerUsed before i) as [t|]; [|discriminate].
  destruct (timerImages before i) as [old|] eqn:Hlookup; [|discriminate].
  inversion Hstep; subst after; cbn [timer_replace_wheel_objects timerImages].
  apply timer_wheel_unlink_image_types_eq; exact Hlookup.
Qed.

Lemma timer_delete_locked_image_types_eq : forall sg before i name ret err after,
  timer_delete_locked sg before i name = Some (ret, err, after) ->
  timer_image_types after.(timerImages) = timer_image_types before.(timerImages).
Proof.
  intros sg before i name ret err after Hstep; unfold timer_delete_locked in Hstep.
  destruct (timerImages before i) as [old|] eqn:Hlookup; [|discriminate].
  destruct (Z.eqb (timerImageState old) 3).
  - destruct (timer_unlink sg before i) as [stopped|] eqn:Hunlink; [|discriminate].
    destruct (timerImages stopped i) as [image|] eqn:Himage; [|discriminate].
    inversion Hstep; subst after.
    rewrite timer_release_image_types_eq by exact Himage.
    eapply timer_unlink_image_types_eq; exact Hunlink.
  - destruct (orb (Z.eqb (timerImageState old) 1) (Z.eqb (timerImageState old) 2)).
    + inversion Hstep; subst after; apply timer_release_image_types_eq; exact Hlookup.
    + destruct (Z.eqb (timerImageState old) 0); inversion Hstep; reflexivity.
Qed.

Lemma timer_delete_locked_service_globals_eq : forall sg before i name ret err after,
  timer_delete_locked sg before i name = Some (ret, err, after) ->
  timer_service_globals_rep sg after = timer_service_globals_rep sg before.
Proof.
  intros sg before i name ret err after Hstep; unfold timer_delete_locked in Hstep.
  destruct (timerImages before i) as [image|]; [|discriminate].
  destruct (Z.eqb (timerImageState image) 3).
  - destruct (timer_unlink sg before i) as [stopped|] eqn:Hunlink; [|discriminate].
    destruct (timerImages stopped i); [|discriminate].
    inversion Hstep; subst after.
    change (timer_service_globals_rep sg stopped = timer_service_globals_rep sg before).
    eapply timer_unlink_service_globals_eq; exact Hunlink.
  - destruct (orb (Z.eqb (timerImageState image) 1) (Z.eqb (timerImageState image) 2));
      [|destruct (Z.eqb (timerImageState image) 0)]; inversion Hstep; reflexivity.
Qed.

Lemma timer_delete_locked_preserves_state_validity : forall sg s i name ret err post,
  sg.(osKernelConfig).(cfgMaxTimers) < 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> timer_delete_locked sg s i name = Some (ret, err, post) ->
  valid_timer_state sg post.
Proof.
  intros sg s i name ret err post Hcap Hlayout Hvalid Hstep.
  unfold timer_delete_locked in Hstep; destruct (timerImages s i) as [v|] eqn:Hv; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3) eqn:Hrun.
  - apply Z.eqb_eq in Hrun.
    destruct (valid_timer_state_nonunused_image _ _ _ _ Hvalid Hv ltac:(lia)) as [t [Ht Hstate]].
    assert (Hrunning : timerState t = TimerRunning) by (destruct (timerState t); simpl in Hstate; congruence).
    destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
    destruct (timerImages stopped i) as [after|] eqn:Ha; [|discriminate].
    inversion Hstep; subst post.
    pose proof (timer_unlink_preserves_state_validity _ _ _ _ _ Hlayout Hvalid Ht Hrunning Hu) as Hstopped.
    destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hu) as [u [uv [Hut [_ [Hustate _]]]]].
    eapply timer_release_preserves_validity; eauto; congruence.
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2)) eqn:Hstop.
    + apply Bool.orb_true_iff in Hstop; destruct Hstop as [Hstate|Hstate]; apply Z.eqb_eq in Hstate;
        destruct (valid_timer_state_nonunused_image _ _ _ _ Hvalid Hv ltac:(lia)) as [t [Ht Hencode]];
        assert (Hnotrun : timerState t <> TimerRunning) by (intro E; rewrite E in Hencode; simpl in Hencode; lia);
        inversion Hstep; subst post; eapply timer_release_preserves_validity; eauto.
    + destruct (Z.eqb (timerImageState v) 0); inversion Hstep; subst post; exact Hvalid.
Qed.

Lemma timer_delete_locked_preserves_scan : forall sg s scan i name ret err post,
  ~ In i scan.(timerScanRemaining) ->
  (forall v, s.(timerImages) i = Some v -> v.(timerImageState) = 3 ->
    timer_unlink_scan_footprint sg s i scan) ->
  timer_delete_locked sg s i name = Some (ret, err, post) ->
  timer_callback_preserves_scan s post scan.
Proof.
  intros sg s scan i name ret err post Houtside Hfoot Hstep.
  unfold timer_delete_locked in Hstep; destruct (timerImages s i) as [v|] eqn:Hv; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3) eqn:Hrun.
  - destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
    destruct (timerImages stopped i) as [after|]; [|discriminate].
    inversion Hstep; subst post; eapply timer_callback_preserves_scan_transitive.
    + eapply timer_unlink_preserves_scan; [exact Houtside| |exact Hu].
      apply (Hfoot v eq_refl); apply Z.eqb_eq; exact Hrun.
    + apply timer_release_preserves_scan; exact Houtside.
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2)).
    + inversion Hstep; subst post; apply timer_release_preserves_scan; exact Houtside.
    + destruct (Z.eqb (timerImageState v) 0); inversion Hstep; subst post;
        apply timer_callback_preserves_scan_reflexive.
Qed.

Lemma timer_delete_locked_removes_live_object : forall sg s i name err post,
  timer_delete_locked sg s i name = Some (true, err, post) -> post.(timerUsed) i = None.
Proof.
  intros sg s i name err post Hstep; unfold timer_delete_locked in Hstep.
  destruct (timerImages s i) as [v|]; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3).
  - destruct (timer_unlink sg s i) as [stopped|]; [|discriminate].
    destruct (timerImages stopped i); [|discriminate].
    inversion Hstep; subst post; apply timer_release_removes_live_object.
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2)).
    + inversion Hstep; subst post; apply timer_release_removes_live_object.
    + destruct (Z.eqb (timerImageState v) 0); discriminate.
Qed.

Lemma timer_delete_locked_invalidates_remaining_scan : forall sg s scan i name err post,
  In i scan.(timerScanRemaining) -> timer_delete_locked sg s i name = Some (true, err, post) ->
  ~ timer_scan_continuation_valid sg post scan.
Proof.
  intros sg s scan i name err post Hin Hstep Hscan.
  destruct (timer_scan_continuation_remaining_running _ _ _ _ Hscan Hin) as [t [Ht _]].
  rewrite (timer_delete_locked_removes_live_object _ _ _ _ _ _ Hstep) in Ht; discriminate.
Qed.

Lemma timer_scan_chain_of_wheel_suffix : forall sg s n pre remaining,
  timer_wheel_valid sg s -> nth_error s.(timerWheel) n = Some (pre ++ remaining) ->
  timer_scan_chain_valid sg s remaining.
Proof.
  intros sg s n pre remaining Hvalid Hrow.
  destruct Hvalid as [Hlength [Hnd [Hmember Hrows]]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  split; [apply NoDup_app_remove_l in Hrownd; exact Hrownd|].
  intros prefix i rest Hlist.
  assert (Hrowlist : pre ++ remaining = (pre ++ prefix) ++ i :: rest)
    by (rewrite Hlist, app_assoc; reflexivity).
  destruct (Hrows n (pre ++ remaining) (pre ++ prefix) i rest Hrow Hrowlist)
    as [t [v [Ht [Hv [_ [Hnext _]]]]]].
  assert (Hin : timer_wheel_member s i).
  { eapply timer_wheel_row_member; [exact Hrow|]. rewrite Hrowlist.
    apply in_or_app; right; left; reflexivity. }
  destruct (proj1 (Hmember i) Hin) as [u [Hu Hrun]].
  rewrite Ht in Hu; inversion Hu; subst u.
  exists t, v; auto.
Qed.

Lemma timer_used_image_eq : forall sg s i t v,
  valid_timer_state sg s -> s.(timerUsed) i = Some t -> s.(timerImages) i = Some v ->
  v = timer_object_image t v.(timerImageNext) v.(timerImagePrev) v.(timerImagePadding).
Proof.
  intros sg s i t v [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]] Ht Hv.
  destruct (Hused i t Ht) as [_ [_ [_ [old [Hold Himage]]]]].
  rewrite Hv in Hold; inversion Hold; subst old; exact Himage.
Qed.

Lemma timer_unlink_scan_footprint_of_wheel_suffix : forall sg s n pre i scan,
  valid_timer_state sg s ->
  nth_error s.(timerWheel) n = Some (pre ++ i :: scan.(timerScanRemaining)) ->
  timer_unlink_scan_footprint sg s i scan.
Proof.
  intros sg s n pre i scan Hvalid Hrow old Hold.
  pose proof Hvalid as [_ [Hwheel _]].
  destruct Hwheel as [Hlength [Hnd [Hmember Hrows]]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  destruct (Hrows n (pre ++ i :: timerScanRemaining scan) pre i (timerScanRemaining scan) Hrow eq_refl)
    as [t [v [Ht [Hv [Hspoke [_ Hprev]]]]]].
  rewrite Hold in Hv; inversion Hv; subst v.
  pose proof (timer_used_image_eq _ _ _ _ _ Hvalid Ht Hold) as Himage.
  assert (Hmatch : timerImageMatch old = timerMatch t) by (rewrite Himage; reflexivity).
  rewrite Hmatch, Hspoke, Nat2Z.id.
  pose proof (nth_error_nth (timerWheel s) n [] Hrow) as Hnth.
  rewrite Hnth.
  destruct pre as [|a pre].
  - left; reflexivity.
  - right; rewrite Hprev.
    destruct (rev (a :: pre)) as [|j tail] eqn:E.
    + apply (f_equal (@rev TimerID)) in E; rewrite rev_involutive in E; discriminate.
    + rewrite timer_pointer_index_addr.
      assert (Hj : In j (a :: pre)).
      { apply (proj2 (in_rev (a :: pre) j)); rewrite E; left; reflexivity. }
      intro Hin; eapply kernel_list_nodup_app_disjoint; [exact Hrownd|exact Hj|].
      right; exact Hin.
Qed.

Lemma timer_start_completed_preserves_continuation : forall sg s scan i v ret err post,
  timer_scan_continuation_valid sg s scan -> ~ In i scan.(timerScanRemaining) ->
  s.(timerImages) i = Some v -> v.(timerImageState) = 2 ->
  timer_start_locked sg s i = Some (ret, err, post) ->
  timer_scan_continuation_valid sg post scan.
Proof.
  intros sg s scan i v ret err post Hscan Houtside Hv Hcomplete Hstep.
  eapply timer_callback_preserves_continuation; [exact Hscan|].
  eapply timer_start_locked_preserves_scan; [exact Houtside| |exact Hstep].
  intros old Hold Hrun; rewrite Hv in Hold; inversion Hold; subst old; congruence.
Qed.

Lemma timer_stop_dispatch_invalidates_remaining_scan : forall sg s scan i opt arg ret err request post,
  valid_timer_state sg s -> timer_scan_continuation_valid sg s scan -> In i scan.(timerScanRemaining) ->
  timer_stop_dispatch sg s i opt arg = Some (ret, err, request, post) ->
  ~ timer_scan_continuation_valid sg post scan.
Proof.
  intros sg s scan i opt arg ret err request post Hv Hscan Hin Hstep.
  destruct (timer_scan_continuation_remaining_running _ _ _ _ Hscan Hin) as [t [Ht Hrun]].
  unfold timer_stop_dispatch in Hstep; destruct (timerImages s i) as [v|] eqn:Himage; [|discriminate].
  pose proof (timer_used_image_eq _ _ _ _ _ Hv Ht Himage) as Hencode.
  assert (Hstate : timerImageState v = 3) by (rewrite Hencode; simpl; rewrite Hrun; reflexivity).
  rewrite Hstate in Hstep; simpl in Hstep.
  destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
  destruct (timerImages stopped i) as [after|]; [|discriminate].
  destruct (timer_stop_request sg i after opt arg); inversion Hstep; subst post.
  eapply timer_unlink_invalidates_remaining_scan; eauto.
Qed.

(** These are local ghost cursor constructors, not additional C guards.
    The chain proof justifies resolving a non-null cached pointer to a
    currently live generation. *)
Definition timer_scan_cursor (s : GlobTimerState) (time : Z) (remaining : list TimerID) : TimerScanState :=
  {| timerScanTime := time;
     timerScanNext := match remaining with
       | [] => None
       | i :: _ => option_map (fun t => (i, t.(timerGeneration))) (s.(timerUsed) i)
       end;
     timerScanRemaining := remaining |}.

Definition timer_scan_begin (sg : StableGlobVars) (s : GlobTimerState) : TimerScanState :=
  timer_scan_cursor s s.(timerTime)
    (nth (Z.to_nat (timer_spoke sg.(osKernelConfig) s.(timerTime))) s.(timerWheel) []).

Definition timer_scan_advance (s : GlobTimerState) (scan : TimerScanState) : option TimerScanState :=
  match scan.(timerScanRemaining) with
  | [] => None
  | _ :: rest => Some (timer_scan_cursor s scan.(timerScanTime) rest)
  end.

Definition timer_scan_next_pointer (sg : StableGlobVars) (scan : TimerScanState) : addr :=
  match scan.(timerScanNext) with None => 0 | Some (i, _) => timer_pool_addr sg i end.

Lemma timer_scan_cursor_valid : forall sg s time remaining,
  s.(timerTime) = time -> timer_scan_chain_valid sg s remaining ->
  timer_scan_continuation_valid sg s (timer_scan_cursor s time remaining).
Proof.
  intros sg s time remaining Htime Hchain.
  unfold timer_scan_continuation_valid, timer_scan_cursor; simpl.
  split; [exact Htime|]. split; [exact Hchain|].
  destruct remaining as [|i rest]; [reflexivity|].
  destruct Hchain as [_ Hchain].
  destruct (Hchain [] i rest eq_refl) as [t [v [Ht _]]].
  rewrite Ht; simpl; exists t, rest; auto.
Qed.

Lemma timer_scan_cursor_pointer_eq : forall sg s time remaining,
  timer_scan_chain_valid sg s remaining ->
  timer_scan_next_pointer sg (timer_scan_cursor s time remaining) = timer_id_pointer sg remaining.
Proof.
  intros sg s time remaining [_ Hchain].
  destruct remaining as [|i rest]; [reflexivity|].
  destruct (Hchain [] i rest eq_refl) as [t [v [Ht _]]].
  unfold timer_scan_next_pointer, timer_scan_cursor; simpl; rewrite Ht; reflexivity.
Qed.

Lemma timer_scan_begin_valid : forall sg s,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 -> timer_wheel_valid sg s ->
  timer_scan_continuation_valid sg s (timer_scan_begin sg s).
Proof.
  intros sg s Hsize Hwheel; unfold timer_scan_begin; apply timer_scan_cursor_valid; [reflexivity|].
  pose proof (timer_wheel_spoke_index_in_range sg s (timerTime s) Hsize Hwheel) as Hindex.
  assert (Hrow : nth_error (timerWheel s) (Z.to_nat (timer_spoke (osKernelConfig sg) (timerTime s))) =
    Some (nth (Z.to_nat (timer_spoke (osKernelConfig sg) (timerTime s))) (timerWheel s) [])).
  { apply nth_error_nth'; exact Hindex. }
  eapply timer_scan_chain_of_wheel_suffix with (pre := []); eauto.
Qed.

Lemma timer_scan_chain_tail_valid : forall sg s i rest,
  timer_scan_chain_valid sg s (i :: rest) -> timer_scan_chain_valid sg s rest.
Proof.
  intros sg s i rest [Hnd Hchain]; inversion Hnd; subst; split; [assumption|].
  intros pre j tail Hrest.
  apply (Hchain (i :: pre) j tail); simpl; rewrite Hrest; reflexivity.
Qed.

Lemma timer_scan_advance_valid : forall sg s scan post,
  timer_scan_continuation_valid sg s scan -> timer_scan_advance s scan = Some post ->
  timer_scan_continuation_valid sg s post.
Proof.
  intros sg s scan post [Htime [Hchain Hcached]] Hstep.
  unfold timer_scan_advance in Hstep.
  destruct (timerScanRemaining scan) as [|i rest] eqn:E; [discriminate|].
  inversion Hstep; subst post; apply timer_scan_cursor_valid; [exact Htime|].
  eapply timer_scan_chain_tail_valid; exact Hchain.
Qed.

Lemma timer_scan_advance_decreases_remaining : forall s scan post,
  timer_scan_advance s scan = Some post ->
  S (List.length post.(timerScanRemaining)) = List.length scan.(timerScanRemaining).
Proof.
  intros s scan post Hstep; unfold timer_scan_advance in Hstep.
  destruct (timerScanRemaining scan); [discriminate|].
  inversion Hstep; reflexivity.
Qed.

Lemma timer_scan_advance_cached_pointer_eq : forall sg s scan i rest v post,
  timer_scan_continuation_valid sg s scan -> scan.(timerScanRemaining) = i :: rest ->
  s.(timerImages) i = Some v -> timer_scan_advance s scan = Some post ->
  timer_scan_next_pointer sg post = v.(timerImageNext).
Proof.
  intros sg s scan i rest v post [_ [Hchain _]] Hremaining Hv Hstep.
  rewrite Hremaining in Hchain.
  pose proof Hchain as [_ Hlookup].
  destruct (Hlookup [] i rest eq_refl) as [t [old [_ [_ [Hold Hnext]]]]].
  rewrite Hv in Hold; inversion Hold; subst old.
  unfold timer_scan_advance in Hstep; rewrite Hremaining in Hstep; inversion Hstep; subst post.
  rewrite timer_scan_cursor_pointer_eq by (eapply timer_scan_chain_tail_valid; exact Hchain).
  symmetry; exact Hnext.
Qed.

Lemma timer_complete_preserves_scan : forall s scan i post,
  ~ In i scan.(timerScanRemaining) -> timer_complete s i = Some post ->
  timer_callback_preserves_scan s post scan.
Proof.
  intros s scan i post Houtside Hstep.
  unfold timer_complete in Hstep; destruct (timerUsed s i), (timerImages s i); try discriminate.
  inversion Hstep; subst post.
  unfold timer_callback_preserves_scan.
  cbv beta iota zeta delta [timer_replace_wheel_objects timerTime timerUsed timerImages].
  fold (timerTime s) (timerUsed s) (timerImages s).
  split; [reflexivity|]. intros q Hq; assert (Hne : q <> i) by (intro E; subst q; contradiction).
  rewrite !kernel_map_set_other by exact Hne; split; reflexivity.
Qed.

Lemma timer_expire_dispatch_preserves_scan : forall sg s scan i next request post,
  ~ In i scan.(timerScanRemaining) -> timer_unlink_scan_footprint sg s i scan ->
  timer_expire_dispatch sg s i = Some (next, request, post) ->
  timer_callback_preserves_scan s post scan.
Proof.
  intros sg s scan i next request post Houtside Hfoot Hstep.
  unfold timer_expire_dispatch in Hstep; destruct (timerImages s i) as [v|]; [|discriminate].
  destruct (Z.eqb (timerTime s) (timerImageMatch v)).
  - destruct (timer_unlink sg s i) as [unlinked|] eqn:Hu; [|discriminate].
    pose proof (timer_unlink_preserves_scan sg s scan i unlinked Houtside Hfoot Hu) as Huframe.
    destruct (timerImages unlinked i) as [after|]; [|discriminate].
    destruct (Z.eqb (timerImageOption after) 2).
    + destruct (timer_link sg unlinked i true) as [linked|] eqn:Hl; [|discriminate].
      destruct (timerImages linked i); [|discriminate]; inversion Hstep; subst post.
      eapply timer_callback_preserves_scan_transitive; [exact Huframe|].
      eapply timer_link_preserves_scan; eauto.
    + destruct (timer_complete unlinked i) as [completed|] eqn:Hc; [|discriminate].
      destruct (timerImages completed i); [|discriminate]; inversion Hstep; subst post.
      eapply timer_callback_preserves_scan_transitive; [exact Huframe|].
      eapply timer_complete_preserves_scan; eauto.
  - inversion Hstep; subst post; apply timer_callback_preserves_scan_reflexive.
Qed.

(** The callback body must prove this condition from its own execution.
    This is the point immediately after its return, before the caller's
    OSSchedUnlock; no lock balance or error-output-cell frame is implied. *)
Definition valid_timer_callback_return (sg : StableGlobVars) (before after : GlobTimerState)
  (scan : TimerScanState) (request : option (addr * addr * addr)) : Prop :=
  match request with
  | None => after = before
  | Some _ => valid_timer_state sg after /\ timer_callback_preserves_scan before after scan
  end.

Lemma timer_callback_return_preserves_continuation : forall sg before after scan request,
  valid_timer_state sg before -> timer_scan_continuation_valid sg before scan ->
  valid_timer_callback_return sg before after scan request ->
  valid_timer_state sg after /\ timer_scan_continuation_valid sg after scan.
Proof.
  intros sg before after scan request Hbefore Hscan Hreturn.
  unfold valid_timer_callback_return in Hreturn.
  destruct request as [call|].
  - destruct Hreturn as [Hvalid Hframe]; split; [exact Hvalid|].
    eapply timer_callback_preserves_continuation; eauto.
  - subst after; split; assumption.
Qed.

Lemma timer_scan_chain_member_running : forall sg s remaining i,
  timer_scan_chain_valid sg s remaining -> In i remaining ->
  exists t, s.(timerUsed) i = Some t /\ t.(timerState) = TimerRunning.
Proof.
  intros sg s remaining i [_ Hchain] Hin.
  apply in_split in Hin; destruct Hin as [pre [rest Hlist]].
  destruct (Hchain pre i rest Hlist) as [t [v [Ht [Hrun _]]]]; exists t; auto.
Qed.

Lemma timer_used_id_in_range : forall sg s i t,
  valid_timer_state sg s -> s.(timerUsed) i = Some t ->
  0 <= i < sg.(osKernelConfig).(cfgMaxTimers).
Proof.
  intros sg s i t [[_ [_ Hslots]] _] Ht.
  apply (proj1 (Hslots i)); exists tt.
  unfold timer_allocated_slots; rewrite Ht; reflexivity.
Qed.

Lemma timer_scan_chain_addresses_nonzero : forall sg s remaining,
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> timer_scan_chain_valid sg s remaining ->
  forall i, In i remaining -> timer_pool_addr sg i <> 0.
Proof.
  intros sg s remaining Hlayout Hv Hchain i Hin.
  destruct (timer_scan_chain_member_running _ _ _ _ Hchain Hin) as [t [Ht _]].
  pose proof (timer_pool_addr_in_range sg i Hlayout (timer_used_id_in_range _ _ _ _ Hv Ht)); lia.
Qed.

Lemma timer_scan_chain_same_head_implies_same_tail : forall sg s left i right,
  timer_scan_chain_valid sg s (i :: left) -> timer_scan_chain_valid sg s (i :: right) ->
  (forall j, In j left \/ In j right -> timer_pool_addr sg j <> 0) -> left = right.
Proof.
  intros sg s left; induction left as [|j left IH]; intros i right Hleft Hright Hnonzero.
  - pose proof Hleft as [_ Hl]; pose proof Hright as [_ Hr].
    destruct (Hl [] i [] eq_refl) as [t [v [_ [_ [Hv Hnext]]]]].
    destruct (Hr [] i right eq_refl) as [u [w [_ [_ [Hw Hother]]]]].
    rewrite Hv in Hw; inversion Hw; subst w.
    destruct right as [|k right]; [reflexivity|].
    exfalso; apply (Hnonzero k); [right; left; reflexivity|].
    change (timerImageNext v = timer_pool_addr sg k) in Hother.
    change (timerImageNext v = 0) in Hnext; congruence.
  - pose proof Hleft as [_ Hl]; pose proof Hright as [_ Hr].
    destruct (Hl [] i (j :: left) eq_refl) as [t [v [_ [_ [Hv Hnext]]]]].
    destruct (Hr [] i right eq_refl) as [u [w [_ [_ [Hw Hother]]]]].
    rewrite Hv in Hw; inversion Hw; subst w.
    destruct right as [|k right].
    + exfalso; apply (Hnonzero j); [left; left; reflexivity|].
      change (timerImageNext v = timer_pool_addr sg j) in Hnext.
      change (timerImageNext v = 0) in Hother; congruence.
    + assert (Hjk : j = k).
      { apply timer_pool_addr_injective with sg.
        change (timerImageNext v = timer_pool_addr sg j) in Hnext.
        change (timerImageNext v = timer_pool_addr sg k) in Hother; congruence. }
      subst k; f_equal; eapply IH with (i := j).
      * eapply timer_scan_chain_tail_valid; exact Hleft.
      * eapply timer_scan_chain_tail_valid; exact Hright.
      * intros q [Hq|Hq]; apply Hnonzero; [left|right]; right; exact Hq.
Qed.

Lemma timer_scan_chain_is_wheel_suffix : forall sg s i rest,
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> timer_scan_chain_valid sg s (i :: rest) ->
  exists n pre, nth_error s.(timerWheel) n = Some (pre ++ i :: rest).
Proof.
  intros sg s i rest Hlayout Hv Hchain.
  pose proof Hv as [_ [Hwheel _]]; pose proof Hwheel as [_ [_ [Hmember _]]].
  destruct (timer_scan_chain_member_running _ _ _ _ Hchain (or_introl eq_refl)) as [t [Ht Hrun]].
  assert (Hin : timer_wheel_member s i) by (apply (proj2 (Hmember i)); exists t; auto).
  unfold timer_wheel_member in Hin; apply in_concat in Hin; destruct Hin as [row [Hrow Hin]].
  apply In_nth_error in Hrow; destruct Hrow as [n Hrow].
  apply in_split in Hin; destruct Hin as [pre [tail Hlist]]; subst row.
  pose proof (timer_scan_chain_of_wheel_suffix sg s n pre (i :: tail) Hwheel Hrow) as Hactual.
  assert (Htail : rest = tail).
  { eapply timer_scan_chain_same_head_implies_same_tail; [exact Hchain|exact Hactual|].
    intros j [Hj|Hj].
    - eapply timer_scan_chain_addresses_nonzero; [exact Hlayout|exact Hv|exact Hchain|right; exact Hj].
    - eapply timer_scan_chain_addresses_nonzero; [exact Hlayout|exact Hv|exact Hactual|right; exact Hj]. }
  subst tail; exists n, pre; exact Hrow.
Qed.

Lemma timer_scan_continuation_is_wheel_suffix : forall sg s scan i rest,
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> timer_scan_continuation_valid sg s scan ->
  scan.(timerScanRemaining) = i :: rest ->
  exists n pre, nth_error s.(timerWheel) n = Some (pre ++ i :: rest).
Proof.
  intros sg s scan i rest Hlayout Hv [_ [Hchain _]] Hremaining.
  rewrite Hremaining in Hchain; eapply timer_scan_chain_is_wheel_suffix; eauto.
Qed.

Lemma timer_expire_visit_callback_return : forall sg s scan i rest future next request dispatched after,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> timer_scan_continuation_valid sg s scan ->
  scan.(timerScanRemaining) = i :: rest ->
  timer_scan_advance s scan = Some future ->
  timer_expire_dispatch sg s i = Some (next, request, dispatched) ->
  valid_timer_callback_return sg dispatched after future request ->
  valid_timer_state sg after /\ timer_scan_continuation_valid sg after future /\
  next = timer_scan_next_pointer sg future /\
  S (List.length future.(timerScanRemaining)) = List.length scan.(timerScanRemaining).
Proof.
  intros sg s scan i rest future next request dispatched after Hsize Hlayout Hv Hscan Hremaining Hadvance Hdispatch Hreturn.
  destruct (timer_scan_continuation_is_wheel_suffix _ _ _ _ _ Hlayout Hv Hscan Hremaining) as [n [pre Hrow]].
  assert (Hfuture : timerScanRemaining future = rest).
  { unfold timer_scan_advance in Hadvance; rewrite Hremaining in Hadvance; inversion Hadvance; reflexivity. }
  pose proof Hscan as [_ [[Hnd Hchain] _]]; rewrite Hremaining in Hnd, Hchain.
  assert (Houtside : ~ In i (timerScanRemaining future)) by (rewrite Hfuture; inversion Hnd; assumption).
  assert (Hfoot : timer_unlink_scan_footprint sg s i future).
  { eapply timer_unlink_scan_footprint_of_wheel_suffix; [exact Hv|]. rewrite Hfuture; exact Hrow. }
  pose proof (timer_scan_advance_valid _ _ _ _ Hscan Hadvance) as Hfuturevalid.
  pose proof (timer_expire_dispatch_preserves_scan _ _ _ _ _ _ _ Houtside Hfoot Hdispatch) as Hdispatchframe.
  pose proof (timer_callback_preserves_continuation _ _ _ _ Hfuturevalid Hdispatchframe) as Hdispatched.
  destruct (Hchain [] i rest eq_refl) as [t [v [Ht [Hrun [Himage Hnext]]]]].
  pose proof (timer_expire_dispatch_preserves_state_validity _ _ _ _ _ _ _ Hsize Hlayout Hv Ht Hrun Hdispatch) as Hdispatchvalid.
  destruct (timer_callback_return_preserves_continuation _ _ _ _ _ Hdispatchvalid Hdispatched Hreturn) as [Hafter Hafterscan].
  split; [exact Hafter|]. split; [exact Hafterscan|]. split.
  - rewrite (timer_expire_dispatch_cached_next _ _ _ _ _ _ _ Himage Hdispatch).
    symmetry; exact (timer_scan_advance_cached_pointer_eq sg s scan i rest v future Hscan Hremaining Himage Hadvance).
  - eapply timer_scan_advance_decreases_remaining; exact Hadvance.
Qed.

Lemma timer_delete_locked_preserves_initialization_phase : forall sg s i name ret err post,
  timer_delete_locked sg s i name = Some (ret, err, post) -> post.(timerInitPhase) = s.(timerInitPhase).
Proof.
  intros sg s i name ret err post Hstep; unfold timer_delete_locked in Hstep.
  destruct (timerImages s i) as [v|]; [|discriminate].
  destruct (Z.eqb (timerImageState v) 3).
  - destruct (timer_unlink sg s i) as [stopped|] eqn:Hu; [|discriminate].
    destruct (timerImages stopped i); [|discriminate]; inversion Hstep; subst post.
    change (timerInitPhase stopped = timerInitPhase s).
    eapply timer_unlink_preserves_initialization_phase; exact Hu.
  - destruct (orb (Z.eqb (timerImageState v) 1) (Z.eqb (timerImageState v) 2));
      [|destruct (Z.eqb (timerImageState v) 0)]; inversion Hstep; reflexivity.
Qed.

Lemma timer_delete_locked_preserves_configuration : forall sg s i name ret err post,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> sg.(osKernelConfig).(cfgMaxTimers) < 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_configuration sg s -> timer_api_initialized s ->
  timer_delete_locked sg s i name = Some (ret, err, post) ->
  valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i name ret err post He Hcap Hlayout Hv Hp Hstep.
  assert (Hpost : timer_api_initialized post).
  { unfold timer_api_initialized in *; rewrite (timer_delete_locked_preserves_initialization_phase _ _ _ _ _ _ _ Hstep); exact Hp. }
  split; [|exact Hpost]. apply (proj2 (timer_initialized_configuration_iff _ _ He Hpost)).
  eapply timer_delete_locked_preserves_state_validity; [exact Hcap|exact Hlayout| |exact Hstep].
  apply (proj1 (timer_initialized_configuration_iff _ _ He Hp)); exact Hv.
Qed.

Lemma timer_callback_generation_change_invalidates_scan_frame : forall before after scan i old fresh,
  In i scan.(timerScanRemaining) -> before.(timerUsed) i = Some old -> after.(timerUsed) i = Some fresh ->
  old.(timerGeneration) <> fresh.(timerGeneration) -> ~ timer_callback_preserves_scan before after scan.
Proof.
  intros before after scan i old fresh Hin Hold Hfresh Hdifferent [_ Hframe].
  destruct (Hframe i Hin) as [Hkey _]; rewrite Hold, Hfresh in Hkey; simpl in Hkey.
  inversion Hkey; congruence.
Qed.

Lemma timer_callback_next_change_invalidates_scan_frame : forall before after scan i old changed,
  In i scan.(timerScanRemaining) -> before.(timerImages) i = Some old -> after.(timerImages) i = Some changed ->
  old.(timerImageNext) <> changed.(timerImageNext) -> ~ timer_callback_preserves_scan before after scan.
Proof.
  intros before after scan i old changed Hin Hold Hchanged Hdifferent [_ Hframe].
  destruct (Hframe i Hin) as [_ Hnext]; rewrite Hold, Hchanged in Hnext; simpl in Hnext.
  inversion Hnext; congruence.
Qed.

Lemma timer_complete_result_exists : forall s i t v,
  s.(timerUsed) i = Some t -> s.(timerImages) i = Some v ->
  exists post, timer_complete s i = Some post.
Proof. intros; unfold timer_complete; rewrite H, H0; eexists; reflexivity. Qed.

Lemma timer_expire_dispatch_result_exists : forall sg s i t v,
  s.(timerUsed) i = Some t -> s.(timerImages) i = Some v ->
  exists next request post, timer_expire_dispatch sg s i = Some (next, request, post).
Proof.
  intros sg s i t v Ht Hv; unfold timer_expire_dispatch; rewrite Hv.
  destruct (Z.eqb (timerTime s) (timerImageMatch v)); [|eauto].
  destruct (timer_unlink_result_exists sg s i t v Ht Hv) as [unlinked Hu]; rewrite Hu.
  destruct (timer_unlink_clears_links_and_stops _ _ _ _ Hu) as [u [uv [Hut [Huv _]]]].
  rewrite Huv; destruct (Z.eqb (timerImageOption uv) 2).
  - destruct (timer_link_result_exists sg unlinked i u uv true Hut Huv) as [linked Hl]; rewrite Hl.
    destruct (timer_link_sets_running_match _ _ _ _ _ Hl) as [tnew [callv [_ [Himage _]]]].
    rewrite Himage; eauto.
  - destruct (timer_complete_result_exists unlinked i u uv Hut Huv) as [completed Hc]; rewrite Hc.
    rewrite (timer_complete_target_image_eq _ _ _ _ Huv Hc); eauto.
Qed.

Lemma timer_expire_dispatch_callback_request_fields : forall sg s i next fn self arg post,
  timer_expire_dispatch sg s i = Some (next, Some (fn, self, arg), post) ->
  self = timer_pool_addr sg i /\ fn <> 0 /\
  exists v, post.(timerImages) i = Some v /\ v.(timerImageCallback) = fn /\ v.(timerImageArg) = arg.
Proof.
  intros sg s i next fn self arg post Hstep; unfold timer_expire_dispatch in Hstep.
  destruct (timerImages s i) as [v|]; [|discriminate].
  destruct (Z.eqb (timerTime s) (timerImageMatch v)); [|discriminate].
  destruct (timer_unlink sg s i) as [unlinked|]; [|discriminate].
  destruct (timerImages unlinked i) as [after|]; [|discriminate].
  destruct (if Z.eqb (timerImageOption after) 2 then timer_link sg unlinked i true
    else timer_complete unlinked i) as [updated|]; [|discriminate].
  destruct (timerImages updated i) as [callv|] eqn:Himage; [|discriminate].
  destruct (Z.eqb (timerImageCallback callv) 0) eqn:Hnonzero; [|].
  - discriminate.
  - inversion Hstep; subst; split; [reflexivity|]. split.
    + apply Z.eqb_neq; exact Hnonzero.
    + exists callv; auto.
Qed.

(** The cursor parameter indexes the caller's logical continuation, not a
    new argument passed to C callbacks.  The relation describes actual
    returning calls; it makes no callback termination assumption. *)
Definition valid_timer_scan_callback (sg : StableGlobVars)
  (callback : TimerScanState -> (addr * addr * addr) -> GlobTimerState -> GlobTimerState -> Prop) : Prop :=
  forall scan call before after,
    valid_timer_state sg before -> timer_scan_continuation_valid sg before scan ->
    callback scan call before after ->
    valid_timer_callback_return sg before after scan (Some call).

(** A finite execution of the inner while loop, from an already selected
    wheel head through the last callback return, before OSSchedUnlock.
    Events record every visit and its optional callback request in source
    order.  No invariant or read-frame guard is built into the transition
    constructors; their preservation is a separate client obligation. *)
Inductive timer_scan_execution (sg : StableGlobVars)
  (callback : TimerScanState -> (addr * addr * addr) -> GlobTimerState -> GlobTimerState -> Prop)
  : GlobTimerState -> TimerScanState -> list (TimerID * option (addr * addr * addr)) ->
    GlobTimerState -> TimerScanState -> Prop :=
| TimerScanDone : forall s scan,
    scan.(timerScanRemaining) = [] -> timer_scan_execution sg callback s scan [] s scan
| TimerScanVisit : forall s scan i rest future next request dispatched after events post finish,
    scan.(timerScanRemaining) = i :: rest -> timer_scan_advance s scan = Some future ->
    timer_expire_dispatch sg s i = Some (next, request, dispatched) ->
    (match request with None => after = dispatched | Some call => callback future call dispatched after end) ->
    timer_scan_execution sg callback after future events post finish ->
    timer_scan_execution sg callback s scan ((i, request) :: events) post finish.

Lemma timer_scan_execution_visits_remaining : forall sg callback s scan events post finish,
  timer_scan_execution sg callback s scan events post finish ->
  map fst events = scan.(timerScanRemaining).
Proof.
  intros sg callback s scan events post finish Hexec; induction Hexec.
  - simpl; symmetry; exact H.
  - simpl; rewrite IHHexec, H.
    unfold timer_scan_advance in H0; rewrite H in H0; inversion H0; reflexivity.
Qed.

Lemma timer_scan_execution_finishes_empty : forall sg callback s scan events post finish,
  timer_scan_execution sg callback s scan events post finish -> finish.(timerScanRemaining) = [].
Proof. intros sg callback s scan events post finish Hexec; induction Hexec; assumption. Qed.

Lemma timer_scan_execution_preserves_cursor_time : forall sg callback s scan events post finish,
  timer_scan_execution sg callback s scan events post finish -> finish.(timerScanTime) = scan.(timerScanTime).
Proof.
  intros sg callback s scan events post finish Hexec; induction Hexec; [reflexivity|].
  rewrite IHHexec; unfold timer_scan_advance in H0; rewrite H in H0; inversion H0; reflexivity.
Qed.

Lemma timer_scan_execution_callback_requests : forall sg callback s scan events post finish,
  timer_scan_execution sg callback s scan events post finish ->
  Forall (fun event => match snd event with
    | None => True
    | Some (fn, self, _) => fn <> 0 /\ self = timer_pool_addr sg (fst event)
    end) events.
Proof.
  intros sg callback s scan events post finish Hexec; induction Hexec; [constructor|].
  constructor; [|exact IHHexec].
  destruct request as [[[fn self] arg]|]; [|exact I].
  destruct (timer_expire_dispatch_callback_request_fields _ _ _ _ _ _ _ _ H1) as [Hself [Hfn _]].
  simpl; split; assumption.
Qed.

Lemma timer_scan_execution_preserves_validity : forall sg callback s scan events post finish,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_scan_callback sg callback ->
  timer_scan_execution sg callback s scan events post finish ->
  valid_timer_state sg s -> timer_scan_continuation_valid sg s scan ->
  valid_timer_state sg post /\ timer_scan_continuation_valid sg post finish.
Proof.
  intros sg callback s scan events post finish Hsize Hlayout Hcallback Hexec.
  induction Hexec as [s scan Hempty|s scan i rest future next request dispatched after events post finish
    Hremaining Hadvance Hdispatch Hcall Htail IH]; intros Hv Hscan.
  - auto.
  - assert (Hin : In i (timerScanRemaining scan)) by (rewrite Hremaining; left; reflexivity).
    destruct (timer_scan_continuation_remaining_running _ _ _ _ Hscan Hin) as [t [Ht Hrun]].
    pose proof (timer_expire_dispatch_preserves_state_validity _ _ _ _ _ _ _ Hsize Hlayout Hv Ht Hrun Hdispatch) as Hdvalid.
    assert (Hidentity : valid_timer_callback_return sg dispatched dispatched future request).
    { destruct request; simpl; [split; [exact Hdvalid|apply timer_callback_preserves_scan_reflexive]|reflexivity]. }
    destruct (timer_expire_visit_callback_return _ _ _ _ _ _ _ _ _ _ Hsize Hlayout Hv Hscan Hremaining Hadvance Hdispatch Hidentity)
      as [_ [Hdscan _]].
    assert (Hreturn : valid_timer_callback_return sg dispatched after future request).
    { destruct request as [call|]; [eapply Hcallback; eauto|exact Hcall]. }
    destruct (timer_callback_return_preserves_continuation _ _ _ _ _ Hdvalid Hdscan Hreturn) as [Hafter Hafterscan].
    apply IH; assumption.
Qed.

Lemma timer_scan_continuation_pointer_null_iff : forall sg s scan,
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> timer_scan_continuation_valid sg s scan ->
  (timer_scan_next_pointer sg scan = 0 <-> scan.(timerScanRemaining) = []).
Proof.
  intros sg s scan Hlayout Hv [_ [Hchain Hcached]].
  unfold timer_scan_next_pointer; destruct (timerScanNext scan) as [[i generation]|].
  - destruct Hcached as [t [rest [Hremaining [Ht Hgen]]]].
    pose proof (timer_pool_addr_in_range sg i Hlayout (timer_used_id_in_range _ _ _ _ Hv Ht)) as Haddr.
    split; [lia|rewrite Hremaining; discriminate].
  - split; [intros; exact Hcached|intros; reflexivity].
Qed.

Lemma timer_scan_execution_visits_once : forall sg callback s scan events post finish,
  timer_scan_continuation_valid sg s scan -> timer_scan_execution sg callback s scan events post finish ->
  NoDup (map fst events) /\ List.length events = List.length scan.(timerScanRemaining).
Proof.
  intros sg callback s scan events post finish [_ [[Hnd _] _]] Hexec.
  pose proof (timer_scan_execution_visits_remaining _ _ _ _ _ _ _ Hexec) as Hids.
  split; [rewrite Hids; exact Hnd|rewrite <- Hids, length_map; reflexivity].
Qed.

Lemma timer_scan_execution_from_begin : forall sg callback s events post finish,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> valid_timer_scan_callback sg callback ->
  timer_scan_execution sg callback s (timer_scan_begin sg s) events post finish ->
  valid_timer_state sg post /\ timer_scan_next_pointer sg finish = 0 /\
  post.(timerTime) = s.(timerTime) /\
  map fst events = nth (Z.to_nat (timer_spoke sg.(osKernelConfig) s.(timerTime))) s.(timerWheel) [] /\
  NoDup (map fst events).
Proof.
  intros sg callback s events post finish Hsize Hlayout Hv Hcallback Hexec.
  pose proof Hv as [_ [Hwheel _]].
  pose proof (timer_scan_begin_valid _ _ Hsize Hwheel) as Hscan.
  destruct (timer_scan_execution_preserves_validity _ _ _ _ _ _ _ Hsize Hlayout Hcallback Hexec Hv Hscan) as [Hpost Hfinish].
  split; [exact Hpost|]. split.
  - apply (proj2 (timer_scan_continuation_pointer_null_iff _ _ _ Hlayout Hpost Hfinish)).
    eapply timer_scan_execution_finishes_empty; exact Hexec.
  - split.
    + pose proof Hfinish as [Htime _].
      pose proof (timer_scan_execution_preserves_cursor_time _ _ _ _ _ _ _ Hexec) as Hclock.
      rewrite Htime, Hclock; reflexivity.
    + split.
      * exact (timer_scan_execution_visits_remaining _ _ _ _ _ _ _ Hexec).
      * exact (proj1 (timer_scan_execution_visits_once _ _ _ _ _ _ _ Hscan Hexec)).
Qed.

(** OSTmr_Task advances time after OSSemPend returns, including error
    returns because that source ignores err.  Semaphore return, lock
    accounting and callback termination remain outside this Timer-local
    execution theorem. *)
Lemma timer_service_scan_preserves_validity : forall sg callback s events post finish,
  0 < sg.(osKernelConfig).(cfgTimerWheelSize) <= 65536 ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) ->
  valid_timer_state sg s -> valid_timer_scan_callback sg callback ->
  timer_scan_execution sg callback (timer_service_advance s)
    (timer_scan_begin sg (timer_service_advance s)) events post finish ->
  valid_timer_state sg post /\ timer_scan_next_pointer sg finish = 0 /\
  post.(timerTime) = kernel_u32 (s.(timerTime) + 1) /\
  map fst events = nth (Z.to_nat (timer_spoke sg.(osKernelConfig) (kernel_u32 (s.(timerTime) + 1)))) s.(timerWheel) [] /\
  NoDup (map fst events).
Proof.
  intros sg callback s events post finish Hsize Hlayout Hv Hcallback Hexec.
  exact (timer_scan_execution_from_begin _ _ _ _ _ _ Hsize Hlayout
    (timer_service_advance_preserves_validity _ _ Hv) Hcallback Hexec).
Qed.
