Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.timer.
Require Export Ucos2Verify.lib.timer_execution.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Export MonadLib.StateRelMonad.safeexec_lib.
Require Export Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import AUXLib.ListLib.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition TmrRemainGetOutput : Type := (Z * Z)%type.
Definition tmr_remain_get_type (v : TimerImage) : Z := v.(timerImageType).
Definition tmr_remain_get_state (v : TimerImage) : Z := v.(timerImageState).
Definition tmr_remain_get_option (v : TimerImage) : Z := v.(timerImageOption).
Definition tmr_remain_get_delay (v : TimerImage) : Z := v.(timerImageDelay).
Definition tmr_remain_get_period (v : TimerImage) : Z := v.(timerImagePeriod).
Definition tmr_remain_get_match (v : TimerImage) : Z := v.(timerImageMatch).
Definition tmr_remain_get_time (s : UCOS2_Verify_State) : Z := s.(TimerState).(timerTime).
Definition tmr_remain_get_ints (s : UCOS2_Verify_State) : Z := s.(IntrState).(intNesting).
Definition tmr_remain_get_time_address (sg : StableGlobVars) : Z := sg.(g_OSTmrTime).
Definition tmr_remain_get_int_address (sg : StableGlobVars) : Z := sg.(g_OSIntNesting).

(** Byte addresses in the selected names-enabled ARM32 layout. C passes actual
    field_addr terms; no typed pointer arithmetic stands for these offsets. *)
Definition tmr_remain_get_layout (p type_addr state_addr option_addr delay_addr
  period_addr match_addr : Z) : Prop :=
  type_addr = p /\ state_addr = p + 37 /\ option_addr = p + 36 /\
  delay_addr = p + 24 /\ period_addr = p + 28 /\ match_addr = p + 20.

Definition tmr_remain_get_calls (p ty nesting : Z) : bool :=
  andb (negb (Z.eqb p 0)) (andb (Z.eqb ty 100) (negb (Z.ltb 0 nesting))).

(** These raw-byte branches include unknown option bytes in the successful
    stopped fallback. The running result is UInt subtraction, not Z subtraction. *)
Definition tmr_remain_get_observe (time : Z) (v : TimerImage) : TmrRemainGetOutput :=
  if Z.eqb v.(timerImageState) 3 then (kernel_u32 (v.(timerImageMatch) - time), 0)
  else if Z.eqb v.(timerImageState) 1 then
    (if andb (Z.eqb v.(timerImageOption) 2) (Z.eqb v.(timerImageDelay) 0)
     then v.(timerImagePeriod) else v.(timerImageDelay), 0)
  else if Z.eqb v.(timerImageState) 2 then (0, 0)
  else if Z.eqb v.(timerImageState) 0 then (0, 135) else (0, 141).

Lemma tmr_remain_get_observe_object : forall time t next prev padding,
  tmr_remain_get_observe time (timer_object_image t next prev padding) =
  (fst (timer_remaining time t), encode_os_err_code (snd (timer_remaining time t))).
Proof.
  intros; unfold tmr_remain_get_observe, timer_object_image, timer_remaining;
    destruct (timerState t), (timerMode t); simpl; reflexivity.
Qed.

Definition tmr_remain_get_image_binding (raw : bool) (original : TimerImage)
  (i : TimerID) (s : UCOS2_Verify_State) (current : TimerImage) : Prop :=
  if raw then current = original else s.(TimerState).(timerImages) i = Some current.

(** This is the ordinary-return projection of the unchanged Unlock post.
    Its own entry and OS_Sched's later acquired entry remain distinct. *)
Definition tmr_remain_get_unlock_return (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State)
  (returned : OsSchedCallContext) (final : UCOS2_Verify_State) : Prop :=
  (before.(SchedState).(isRunning) = false /\ UCOS2_state_inv sg before /\
    returned = context /\ final = before) \/
  (exists entry,
    before.(SchedState).(isRunning) = true /\
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
    UCOS2_state_inv sg (os_sched_unlock_checkpoint true entry) /\
    ((os_sched_unlock_requests entry = true /\ exists sched_entry,
       critical_region_interval critical sg context.(os_sched_call_invocation)
         (os_sched_unlock_checkpoint true entry) sched_entry /\
       os_sched_c_return external critical sg sched_entry context returned final) \/
     (os_sched_unlock_requests entry = false /\ returned = context /\
       final = os_sched_unlock_checkpoint true entry))).

Definition tmr_remain_get_prefix (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (raw : bool)
  (p ty : Z) (original : TimerImage) (i : TimerID)
  (before locked : UCOS2_Verify_State) (output : TmrRemainGetOutput) : Prop :=
  p <> 0 /\ ty = 100 /\ tmr_remain_get_ints before = 0 /\
  exists acquired current,
    os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
      before acquired locked /\
    tmr_remain_get_image_binding raw original i locked current /\
    output = tmr_remain_get_observe (tmr_remain_get_time locked) current.

Definition tmr_remain_get_effect (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (raw : bool) (p ty : Z)
  (original : TimerImage) (i : TimerID) (before : UCOS2_Verify_State)
  (output : TmrRemainGetOutput) (returned : OsSchedCallContext)
  (final : UCOS2_Verify_State) : Prop :=
  if Z.eqb p 0 then output = (0, 138) /\ returned = context /\ final = before
  else if negb (Z.eqb ty 100) then output = (0, 137) /\ returned = context /\ final = before
  else if Z.ltb 0 (tmr_remain_get_ints before)
    then output = (0, 139) /\ returned = context /\ final = before
  else exists locked,
    tmr_remain_get_prefix critical sg context raw p ty original i before locked output /\
    tmr_remain_get_unlock_return external critical sg context locked returned final.

Definition tmr_remain_get_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (raw : bool) (p ty : Z)
  (original : TimerImage) (i : TimerID) : program UCOS2_Verify_State TmrRemainGetOutput :=
  fun before output final => exists returned,
    tmr_remain_get_effect external critical sg context raw p ty original i
      before output returned final.

Definition tmr_remain_get_at_state (s : UCOS2_Verify_State)
  : UCOS2_Verify_State -> Prop := fun current => current = s.
Definition tmr_remain_get_safe (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (raw : bool) (p ty : Z)
  (original : TimerImage) (i : TimerID) (before : UCOS2_Verify_State)
  (X : TmrRemainGetOutput -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (tmr_remain_get_at_state before)
    (tmr_remain_get_program external critical sg context raw p ty original i) X.

Lemma tmr_remain_get_program_safe_return : forall external critical sg context raw p ty
  original i before output returned final X,
  tmr_remain_get_effect external critical sg context raw p ty original i before output returned final ->
  tmr_remain_get_safe external critical sg context raw p ty original i before X ->
  safeExec (tmr_remain_get_at_state final) (StateRelMonad.ret output) X.
Proof.
  intros external critical sg context raw p ty original i before output returned final X Heffect Hsafe.
  eapply (highstependret_derive
    (tmr_remain_get_program external critical sg context raw p ty original i)
    (tmr_remain_get_at_state before) output (fun _ => tmr_remain_get_at_state final));
    [|exact Hsafe].
  unfold hs_eval, tmr_remain_get_at_state; intros initial ->.
  exists final; split; [exists returned; exact Heffect|reflexivity].
Qed.

(** The only caller protocol is the existing conditional Unlock acquire-safety,
    for endpoints of this actual Lock call after all three source guards. Its
    origin is the caller/context/source protocol, not Timer validity or a
    desired query result, and it does not require an eventual return. *)
Definition tmr_remain_get_entry_facts (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (raw : bool) (p ty : Z)
  (original : TimerImage) (i : TimerID) (before : UCOS2_Verify_State) : Prop :=
  UCOS2_state_inv sg before /\ sg.(osKernelConfig).(cfgTimerEnabled) = true /\
  sg.(osKernelConfig).(cfgTimerNames) = true /\
  (p <> 0 -> raw = false ->
    timer_api_initialized before.(TimerState) /\ p = timer_pool_addr sg i /\
    before.(TimerState).(timerImages) i = Some original /\ ty = original.(timerImageType)) /\
  (tmr_remain_get_calls p ty (tmr_remain_get_ints before) = true ->
    forall acquired locked,
      os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
        before acquired locked ->
      os_sched_unlock_acquire_safety external critical sg context locked).

(** Raw storage is exactly the branch read footprint. Unread ghost components
    of original carry no ownership and no range requirement. *)
Definition tmr_remain_get_payload_fields (p : Z) (v : TimerImage) : Assertion :=
  if Z.eqb v.(timerImageState) 3 then (p + 20) # UInt |-> v.(timerImageMatch)
  else if Z.eqb v.(timerImageState) 1 then
    (p + 36) # UChar |-> v.(timerImageOption) **
    (p + 24) # UInt |-> v.(timerImageDelay) **
    (if andb (Z.eqb v.(timerImageOption) 2) (Z.eqb v.(timerImageDelay) 0)
     then (p + 28) # UInt |-> v.(timerImagePeriod) else emp)
  else emp.

Definition tmr_remain_get_period_storage (p : Z) (v : TimerImage) : Assertion :=
  if andb (Z.eqb v.(timerImageOption) 2) (Z.eqb v.(timerImageDelay) 0)
  then (p + 28) # UInt |-> v.(timerImagePeriod) else emp.

Definition tmr_remain_get_private (raw : bool) (p ty nesting : Z)
  (v : TimerImage) : Assertion :=
  if raw then
    if Z.eqb p 0 then emp else
      p # UChar |-> ty **
      (if tmr_remain_get_calls p ty nesting then
         (p + 37) # UChar |-> v.(timerImageState) ** tmr_remain_get_payload_fields p v
       else emp)
  else emp.

Definition tmr_remain_get_call_resources (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask p ty nesting : Z) : Assertion :=
  if tmr_remain_get_calls p ty nesting then
    interrupt_platform_running platform context.(os_sched_call_invocation)
      context.(os_sched_call_origin) mask **
    os_sched_context_resources external context ** unmap_table_rep sg
  else emp.

Definition tmr_remain_get_input (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (raw : bool) (p ty : Z) (original : TimerImage) (i : TimerID)
  (before : UCOS2_Verify_State) : Assertion :=
  coq_prop (tmr_remain_get_entry_facts external critical sg context raw p ty original i before) &&
  (UCOS2_raw_rep sg before **
   tmr_remain_get_private raw p ty (tmr_remain_get_ints before) original **
   tmr_remain_get_call_resources external platform sg context mask p ty (tmr_remain_get_ints before)).

Definition tmr_remain_get_observation_rest (sg : StableGlobVars) (raw : bool)
  (p ty : Z) (original : TimerImage) (i : TimerID) (before : UCOS2_Verify_State) : Assertion :=
  if raw then
    interrupt_inv_no_int_nesting sg before.(IntrState) **
    UCOS2_raw_rep_missing_interrupt sg before **
    (if tmr_remain_get_calls p ty (tmr_remain_get_ints before) then
       (p + 37) # UChar |-> original.(timerImageState) ** tmr_remain_get_payload_fields p original
     else emp)
  else timer_raw_rep_without_type sg before.(TimerState) i original **
    interrupt_inv_no_int_nesting sg before.(IntrState) **
    UCOS2_raw_rep_missing_two sg before TimerModule InterruptModule.

Definition tmr_remain_get_globals_without_time (sg : StableGlobVars)
  (s : GlobTimerState) : Assertion :=
  sg.(g_OSTmrFreeList) # Ptr |-> timer_id_pointer sg s.(timerFree) **
  sg.(g_OSTmrFree) # UShort |-> s.(timerFreeCount) **
  sg.(g_OSTmrUsed) # UShort |-> s.(timerUsedCount) **
  sg.(g_OSTmrSem) # Ptr |-> s.(timerSem) **
  sg.(g_OSTmrSemSignal) # Ptr |-> s.(timerSignalSem).

Definition tmr_remain_get_timer_without_time (sg : StableGlobVars)
  (s : GlobTimerState) : Assertion :=
  match s.(timerInitPhase) with
  | TimerUninitialized =>
    UCharArray.undef_full sg.(g_OSTmrTbl)
      (timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) **
    UCharArray.undef_full sg.(g_OSTmrWheelTbl) (8 * sg.(osKernelConfig).(cfgTimerWheelSize)) **
    tmr_remain_get_globals_without_time sg timer_uninitialized
  | _ => timer_images_rep sg s ** timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) **
    tmr_remain_get_globals_without_time sg s
  end.

(** Every unread configured object byte remains in the actual residual. *)
Definition tmr_remain_get_object_rest (sg : StableGlobVars) (p : Z)
  (v : TimerImage) : Assertion :=
  p # UChar |-> v.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) ** (p + 8) # Ptr |-> v.(timerImageArg) **
  (p + 12) # Ptr |-> v.(timerImageNext) ** (p + 16) # Ptr |-> v.(timerImagePrev) **
  (if Z.eqb v.(timerImageState) 3 then emp else (p + 20) # UInt |-> v.(timerImageMatch)) **
  (if Z.eqb v.(timerImageState) 1 then emp else (p + 24) # UInt |-> v.(timerImageDelay)) **
  (if andb (Z.eqb v.(timerImageState) 1)
      (andb (Z.eqb v.(timerImageOption) 2) (Z.eqb v.(timerImageDelay) 0))
   then emp else (p + 28) # UInt |-> v.(timerImagePeriod)) **
  (p + 32) # Ptr |-> v.(timerImageName) **
  (if Z.eqb v.(timerImageState) 1 then emp else (p + 36) # UChar |-> v.(timerImageOption)) **
  store_optional_bytes (p + 38) (skipn 3 v.(timerImagePadding)).

Definition tmr_remain_get_payload (sg : StableGlobVars) (p : Z)
  (v : TimerImage) (locked : UCOS2_Verify_State) : Assertion :=
  tmr_remain_get_payload_fields p v **
  (if Z.eqb v.(timerImageState) 3
   then sg.(g_OSTmrTime) # UInt |-> tmr_remain_get_time locked else emp).

Definition tmr_remain_get_locked_rest (sg : StableGlobVars) (raw : bool)
  (p ty : Z) (i : TimerID) (v : TimerImage) (locked : UCOS2_Verify_State) : Assertion :=
  if raw then p # UChar |-> ty **
    (if Z.eqb v.(timerImageState) 3 then
       tmr_remain_get_timer_without_time sg locked.(TimerState) ** UCOS2_raw_rep_missing_timer sg locked
     else UCOS2_raw_rep sg locked)
  else tmr_remain_get_object_rest sg p v ** timer_images_without sg locked.(TimerState) i **
    timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) locked.(TimerState).(timerWheel) **
    tmr_remain_get_globals_without_time sg locked.(TimerState) **
    (if Z.eqb v.(timerImageState) 3 then emp
     else sg.(g_OSTmrTime) # UInt |-> tmr_remain_get_time locked) **
    UCOS2_raw_rep_missing_timer sg locked.

Lemma tmr_remain_get_timer_time_rep : forall sg s,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> valid_timer_configuration sg s ->
  timer_configured_rep sg s --||--
    (sg.(g_OSTmrTime) # UInt |-> s.(timerTime) ** tmr_remain_get_timer_without_time sg s).
Proof.
  intros sg s Henabled Hvalid.
  unfold timer_configured_rep, valid_timer_configuration in *; rewrite Henabled in *.
  unfold tmr_remain_get_timer_without_time.
  destruct s.(timerInitPhase) eqn:Hphase.
  - subst s; unfold timer_uninitialized_rep, timer_globals_rep,
      tmr_remain_get_globals_without_time; simpl; split; entailer!.
  - unfold timer_raw_rep, timer_globals_rep, tmr_remain_get_globals_without_time; split; entailer!.
  - unfold timer_raw_rep, timer_globals_rep, tmr_remain_get_globals_without_time; split; entailer!.
  - unfold timer_raw_rep, timer_globals_rep, tmr_remain_get_globals_without_time; split; entailer!.
  - unfold timer_raw_rep, timer_globals_rep, tmr_remain_get_globals_without_time; split; entailer!.
Qed.

Lemma tmr_remain_get_object_fields_rep : forall sg p current,
  sg.(osKernelConfig).(cfgTimerNames) = true ->
  timer_object_rep sg.(osKernelConfig) p current --||--
    ((p + 37) # UChar |-> current.(timerImageState) **
     tmr_remain_get_payload_fields p current ** tmr_remain_get_object_rest sg p current).
Proof.
  intros sg p current Hnames.
  unfold timer_object_rep, tmr_remain_get_payload_fields, tmr_remain_get_object_rest,
    timer_option_offset; rewrite Hnames; simpl.
  replace (p + 36 + 1) with (p + 37) by lia.
  replace (p + 36 + 2) with (p + 38) by lia.
  destruct (current.(timerImageState) =? 3) eqn:Hrunning;
    destruct (current.(timerImageState) =? 1) eqn:Hstopped; simpl.
  - apply Z.eqb_eq in Hrunning; apply Z.eqb_eq in Hstopped; lia.
  - split; entailer!.
  - destruct (andb (current.(timerImageOption) =? 2) (current.(timerImageDelay) =? 0));
      simpl; split; entailer!.
  - split; entailer!.
Qed.

Definition tmr_remain_get_image_ranges (v : TimerImage) (time : Z) : Prop :=
  0 <= v.(timerImageState) <= 255 /\
  (v.(timerImageState) = 3 -> 0 <= v.(timerImageMatch) < 4294967296 /\ 0 <= time < 4294967296) /\
  (v.(timerImageState) = 1 -> 0 <= v.(timerImageOption) <= 255 /\
    0 <= v.(timerImageDelay) < 4294967296 /\
    (v.(timerImageOption) = 2 -> v.(timerImageDelay) = 0 ->
     0 <= v.(timerImagePeriod) < 4294967296)).

Definition tmr_remain_get_locked_facts (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (raw : bool) (p ty : Z)
  (original : TimerImage) (i : TimerID) (before acquired locked : UCOS2_Verify_State)
  (current : TimerImage) : Prop :=
  tmr_remain_get_entry_facts external critical sg context raw p ty original i before /\
  p <> 0 /\ ty = 100 /\ tmr_remain_get_ints before = 0 /\
  os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before acquired locked /\
  UCOS2_state_inv sg locked /\ tmr_remain_get_image_binding raw original i locked current /\
  (raw = false -> timer_api_initialized locked.(TimerState)) /\
  tmr_remain_get_image_ranges current (tmr_remain_get_time locked).

Definition tmr_remain_get_return_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context returned : OsSchedCallContext) (mask : Z)
  (final : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  critical_region_outside critical sg context.(os_sched_call_invocation) final **
  os_sched_context_resources external returned ** unmap_table_rep sg.

Definition tmr_remain_get_observed (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (raw : bool)
  (p ty : Z) (original : TimerImage) (i : TimerID)
  (before locked : UCOS2_Verify_State) (count error : Z) : Prop :=
  tmr_remain_get_prefix critical sg context raw p ty original i before locked (count, error).

Definition tmr_remain_get_ready (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (raw : bool) (p ty : Z) (original : TimerImage) (i : TimerID)
  (before acquired locked : UCOS2_Verify_State) (current : TimerImage)
  (count error : Z) : Assertion :=
  coq_prop (tmr_remain_get_locked_facts external critical sg context raw p ty original i
      before acquired locked current /\
    tmr_remain_get_observe (tmr_remain_get_time locked) current = (count, error)) &&
  ((p + 37) # UChar |-> current.(timerImageState) **
   tmr_remain_get_payload sg p current locked **
   tmr_remain_get_locked_rest sg raw p ty i current locked **
   interrupt_platform_running platform context.(os_sched_call_invocation)
     context.(os_sched_call_origin) mask **
   os_sched_context_resources external context ** unmap_table_rep sg).

Definition tmr_remain_get_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (raw : bool) (p ty : Z) (original : TimerImage) (i : TimerID)
  (before : UCOS2_Verify_State) (perr ret : Z) (F : Assertion)
  (X : TmrRemainGetOutput -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX output returned final,
    coq_prop (ret = fst output /\
      tmr_remain_get_effect external critical sg context raw p ty original i before output returned final /\
      safeExec (tmr_remain_get_at_state final) (StateRelMonad.ret output) X) &&
    ((if tmr_remain_get_calls p ty (tmr_remain_get_ints before) then
        tmr_remain_get_return_frame external platform critical sg context returned mask final
      else UCOS2_raw_rep sg final) **
      tmr_remain_get_private raw p ty (tmr_remain_get_ints before) original **
      perr # UChar |-> snd output ** F).

Lemma tmr_remain_get_closed_rep : forall critical sg invocation s,
  critical_region_outside critical sg invocation s --||-- UCOS2_raw_rep sg s.
Proof.
  intros; unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep, UCOS2_raw_rep_split_running.
  split; reflexivity.
Qed.

Lemma tmr_remain_get_lock_has_current_image : forall critical sg invocation before acquired locked i original,
  timer_api_initialized before.(TimerState) ->
  before.(TimerState).(timerImages) i = Some original ->
  os_sched_lock_call_relation critical sg invocation before acquired locked ->
  timer_api_initialized locked.(TimerState) /\ exists current,
    locked.(TimerState).(timerImages) i = Some current.
Proof.
  intros critical sg invocation before acquired locked i original Hinit Himage Hcall.
  pose proof (timer_public_trace_public_storage_frame sg _ _
    (os_sched_lock_call_timer_public_trace critical sg invocation before acquired locked Hcall)) as Hframe.
  split.
  - eapply timer_public_storage_frame_initialized; eauto.
  - eapply timer_public_storage_frame_has_image; eauto.
Qed.

Lemma tmr_remain_get_unlock_post : forall external platform critical sg context mask locked,
  os_sched_unlock_post external platform critical sg context mask locked |--
  EX returned final,
    coq_prop (tmr_remain_get_unlock_return external critical sg context locked returned final) &&
    tmr_remain_get_return_frame external platform critical sg context returned mask final.
Proof.
  intros; unfold os_sched_unlock_post; apply derivable1_orp_elim.
  - Intros; Exists context locked.
    assert (Hreturn : tmr_remain_get_unlock_return external critical sg context locked context locked).
    { unfold tmr_remain_get_unlock_return; left; tauto. }
    unfold tmr_remain_get_return_frame, os_sched_unlock_observation_frame,
      critical_region_outside, os_sched_unlock_running in *; entailer!.
  - Intros entry; destruct (os_sched_unlock_requests entry) eqn:Hrequest.
    + unfold os_sched_post; Intros sched_entry final returned; Exists returned final.
      assert (Hreturn : tmr_remain_get_unlock_return external critical sg context locked returned final).
      { unfold tmr_remain_get_unlock_return; right; exists entry.
        split; [tauto|]. split; [tauto|]. split; [tauto|].
        left; split; [exact Hrequest|]. exists sched_entry; tauto. }
      unfold tmr_remain_get_return_frame; entailer!.
    + Exists context (os_sched_unlock_checkpoint true entry).
      assert (Hreturn : tmr_remain_get_unlock_return external critical sg context locked context
        (os_sched_unlock_checkpoint true entry)).
      { unfold tmr_remain_get_unlock_return; right; exists entry.
        split; [tauto|]. split; [tauto|]. split; [tauto|]. right; auto. }
      unfold tmr_remain_get_return_frame, os_sched_unlock_outside_frame; entailer!.
Qed.

Lemma tmr_remain_get_calls_passed : forall p ty nesting,
  p <> 0 -> ty = 100 -> nesting = 0 -> tmr_remain_get_calls p ty nesting = true.
Proof.
  intros p ty nesting Hp -> ->; unfold tmr_remain_get_calls.
  rewrite (proj2 (Z.eqb_neq p 0) Hp); reflexivity.
Qed.

Lemma tmr_remain_get_effect_after_unlock : forall external critical sg context raw p ty
  original i before locked output returned final,
  tmr_remain_get_prefix critical sg context raw p ty original i before locked output ->
  tmr_remain_get_unlock_return external critical sg context locked returned final ->
  tmr_remain_get_effect external critical sg context raw p ty original i before output returned final.
Proof.
  intros external critical sg context raw p ty original i before locked output returned final Hprefix Hreturn.
  pose proof Hprefix as (Hp & Hty & Hints & Hrest).
  subst ty.
  unfold tmr_remain_get_effect.
  rewrite (proj2 (Z.eqb_neq p 0) Hp), Hints; simpl.
  exists locked; split; assumption.
Qed.

(** Each actual post-Unlock return/STOPPED join consumes this same-X step.
    output, returned context and the heap share the same final witnesses. *)
Lemma tmr_remain_get_post_after_unlock : forall external platform critical sg context mask raw p ty
  original i before locked perr count error F X,
  tmr_remain_get_observed critical sg context raw p ty original i before locked count error ->
  tmr_remain_get_safe external critical sg context raw p ty original i before X ->
  os_sched_unlock_post external platform critical sg context mask locked **
    tmr_remain_get_private raw p ty (tmr_remain_get_ints before) original **
    perr # UChar |-> error ** F |--
  tmr_remain_get_post external platform critical sg context mask raw p ty original i before perr count F X.
Proof.
  intros external platform critical sg context mask raw p ty original i before locked perr count error F X
    Hprefix Hsafe.
  unfold tmr_remain_get_observed in Hprefix.
  sep_apply_l_atomic (tmr_remain_get_unlock_post external platform critical sg context mask locked).
  Intros returned final.
  assert (Heffect : tmr_remain_get_effect external critical sg context raw p ty original i
      before (count, error) returned final).
  { eapply tmr_remain_get_effect_after_unlock; eauto. }
  pose proof (tmr_remain_get_program_safe_return external critical sg context raw p ty original i
    before (count, error) returned final X Heffect Hsafe) as Hexec.
  pose proof Hprefix as (Hp & Hty & Hints & Hrest).
  pose proof (tmr_remain_get_calls_passed p ty (tmr_remain_get_ints before) Hp Hty Hints) as Hcalls.
  unfold tmr_remain_get_post; Exists (count, error) returned final; rewrite Hcalls; simpl.
  entailer!.
Qed.

Lemma tmr_remain_get_entry_rep_equiv__entry_refresh :
  forall external critical sg context raw p ty original i before,
  tmr_remain_get_entry_facts external critical sg context raw p ty original i before ->
  p <> 0 ->
  (UCOS2_raw_rep sg before **
   tmr_remain_get_private raw p ty (tmr_remain_get_ints before) original) --||--
  (p # UChar |-> ty **
   sg.(g_OSIntNesting) # UChar |-> tmr_remain_get_ints before **
   tmr_remain_get_observation_rest sg raw p ty original i before).
Proof.
  intros external critical sg context raw p ty original i before Hentry Hp.
  pose proof Hentry as (Hinv & Henabled & Hnames & Hconfigured & Hprotocol).
  destruct raw.
  - unfold tmr_remain_get_private, tmr_remain_get_observation_rest.
    rewrite (proj2 (Z.eqb_neq p 0) Hp).
    rewrite (UCOS2_raw_rep_split_module sg before InterruptModule).
    cbn [UCOS2_module_rep].
    unfold interrupt_inv, store_int_state, interrupt_inv_no_int_nesting,
      UCOS2_raw_rep_missing_interrupt, tmr_remain_get_ints.
    split; entailer!.
  - specialize (Hconfigured Hp eq_refl).
    destruct Hconfigured as (Hinit & Haddr & Himage & Htype).
    assert (Hview : timer_configured_rep sg before.(TimerState) --||--
      (timer_pool_addr sg i # UChar |-> original.(timerImageType) **
       timer_raw_rep_without_type sg before.(TimerState) i original)).
    { split.
      - apply timer_configured_rep_split_type; assumption.
      - apply timer_configured_rep_merge_type; assumption. }
    unfold tmr_remain_get_private, tmr_remain_get_observation_rest.
    rewrite (UCOS2_raw_rep_split_two sg before TimerModule InterruptModule ltac:(discriminate)).
    cbn [UCOS2_module_rep].
    rewrite Hview, Haddr, Htype.
    unfold interrupt_inv, store_int_state, interrupt_inv_no_int_nesting,
      tmr_remain_get_ints.
    split; entailer!.
Qed.
Lemma tmr_remain_get_payload_ranges__entry_refresh : forall sg p v locked,
  (p + 37) # UChar |-> v.(timerImageState) ** tmr_remain_get_payload sg p v locked |--
  coq_prop (tmr_remain_get_image_ranges v (tmr_remain_get_time locked)) &&
  ((p + 37) # UChar |-> v.(timerImageState) ** tmr_remain_get_payload sg p v locked).
Proof.
  intros sg p v locked; split_pure_spatial; [reflexivity|].
  assert (Hbyte_max : Byte.max_unsigned = 255) by reflexivity.
  assert (Huint_max : Int.max_unsigned = 4294967295) by reflexivity.
  unfold tmr_remain_get_payload, tmr_remain_get_payload_fields.
  prop_apply_p (store_uchar_range (p + 37) v.(timerImageState)); Intros.
  destruct (v.(timerImageState) =? 3) eqn:Hrunning; simpl.
  - prop_apply_p (store_uint_range (p + 20) v.(timerImageMatch)); Intros.
    prop_apply_p (store_uint_range sg.(g_OSTmrTime) (tmr_remain_get_time locked)); Intros.
    apply Z.eqb_eq in Hrunning.
    unfold tmr_remain_get_image_ranges; entailer!; lia.
  - apply Z.eqb_neq in Hrunning.
    destruct (v.(timerImageState) =? 1) eqn:Hstopped; simpl.
    + apply Z.eqb_eq in Hstopped.
      prop_apply_p (store_uchar_range (p + 36) v.(timerImageOption)); Intros.
      prop_apply_p (store_uint_range (p + 24) v.(timerImageDelay)); Intros.
      destruct (andb (v.(timerImageOption) =? 2) (v.(timerImageDelay) =? 0)) eqn:Hperiod.
      * prop_apply_p (store_uint_range (p + 28) v.(timerImagePeriod)); Intros.
        unfold tmr_remain_get_image_ranges; entailer!; lia.
      * apply andb_false_iff in Hperiod.
        destruct Hperiod as [Hperiod|Hperiod]; apply Z.eqb_neq in Hperiod;
          unfold tmr_remain_get_image_ranges; entailer!; lia.
    + apply Z.eqb_neq in Hstopped.
      unfold tmr_remain_get_image_ranges; entailer!; lia.
Qed.
Lemma tmr_remain_get_current_rep__entry_refresh : forall sg raw p ty nesting original i locked current,
  p <> 0 -> tmr_remain_get_calls p ty nesting = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  sg.(osKernelConfig).(cfgTimerNames) = true -> UCOS2_state_inv sg locked ->
  tmr_remain_get_image_binding raw original i locked current ->
  (raw = false -> timer_api_initialized locked.(TimerState) /\ p = timer_pool_addr sg i) ->
  UCOS2_raw_rep sg locked ** tmr_remain_get_private raw p ty nesting original |--
  (p + 37) # UChar |-> current.(timerImageState) **
  tmr_remain_get_payload sg p current locked **
  tmr_remain_get_locked_rest sg raw p ty i current locked.
Proof.
  intros sg raw p ty nesting original i locked current Hp Hcalls Henabled Hnames Hinv Himage Hpool.
  destruct raw.
  - unfold tmr_remain_get_image_binding in Himage; subst current.
    unfold tmr_remain_get_private; rewrite (proj2 (Z.eqb_neq p 0) Hp), Hcalls.
    unfold tmr_remain_get_payload, tmr_remain_get_locked_rest.
    destruct (original.(timerImageState) =? 3) eqn:Hrunning.
    + assert (Htimer : valid_timer_configuration sg locked.(TimerState)).
      { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv; tauto. }
      rewrite (UCOS2_raw_rep_split_module sg locked TimerModule).
      cbn [UCOS2_module_rep].
      rewrite (tmr_remain_get_timer_time_rep sg locked.(TimerState) Henabled Htimer).
      unfold UCOS2_raw_rep_missing_timer, tmr_remain_get_time; entailer!.
    + entailer!.
  - specialize (Hpool eq_refl); destruct Hpool as (Hinit & Haddr).
    unfold tmr_remain_get_image_binding in Himage.
    unfold tmr_remain_get_private; rewrite Haddr.
    rewrite (UCOS2_raw_rep_split_module sg locked TimerModule).
    cbn [UCOS2_module_rep].
    rewrite (timer_initialized_configured_rep_eq sg locked.(TimerState) Henabled Hinit).
    unfold timer_raw_rep.
    sep_apply_l_atomic (timer_images_split_object sg locked.(TimerState) i current Himage).
    rewrite (tmr_remain_get_object_fields_rep sg (timer_pool_addr sg i) current Hnames).
    unfold tmr_remain_get_payload, tmr_remain_get_locked_rest, timer_globals_rep,
      tmr_remain_get_globals_without_time, UCOS2_raw_rep_missing_timer, tmr_remain_get_time.
    destruct (current.(timerImageState) =? 3); entailer!.
Qed.
Lemma tmr_remain_get_ready_unlock_pre__unlock_return :
  forall external platform critical sg context mask raw p ty original i
    before acquired locked current count error,
  tmr_remain_get_ready external platform critical sg context mask raw p ty
    original i before acquired locked current count error |--
  coq_prop (tmr_remain_get_observed critical sg context raw p ty original i
    before locked count error) &&
  (os_sched_unlock_pre external platform critical sg context mask locked **
   tmr_remain_get_private raw p ty (tmr_remain_get_ints before) original).
Proof.
  intros.
  unfold tmr_remain_get_ready.
  Intros.
  destruct H as [Hfacts Hobserve].
  destruct Hfacts as (Hentry & Hp & Hty & Hints & Hlock & Hvalid & Hbinding & Hinit & Hranges).
  destruct Hentry as (Hbefore & Henabled & Hnames & Hlocation & Hacquire).
  pose proof (tmr_remain_get_calls_passed p ty (tmr_remain_get_ints before)
    Hp Hty Hints) as Hcalls.
  specialize (Hacquire Hcalls acquired locked Hlock).
  assert (Hobserved : tmr_remain_get_observed critical sg context raw p ty
    original i before locked count error).
  { unfold tmr_remain_get_observed, tmr_remain_get_prefix.
    split; [exact Hp|]. split; [exact Hty|]. split; [exact Hints|].
    exists acquired, current.
    split; [exact Hlock|]. split; [exact Hbinding|].
    symmetry; assumption. }
  assert (Htimer : valid_timer_configuration sg locked.(TimerState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  rewrite os_sched_unlock_pre_closed_equiv.
  unfold os_sched_unlock_outside_frame.
  rewrite tmr_remain_get_closed_rep.
  unfold tmr_remain_get_payload, tmr_remain_get_locked_rest, tmr_remain_get_private.
  destruct raw.
  - unfold tmr_remain_get_image_binding in Hbinding; subst current.
    rewrite (proj2 (Z.eqb_neq p 0) Hp), Hcalls.
    destruct (original.(timerImageState) =? 3) eqn:Hrunning.
    + rewrite (UCOS2_raw_rep_split_module sg locked TimerModule).
      cbn [UCOS2_module_rep].
      rewrite (tmr_remain_get_timer_time_rep sg locked.(TimerState) Henabled Htimer).
      entailer!.
    + entailer!.
  - unfold tmr_remain_get_image_binding in Hbinding.
    specialize (Hlocation Hp eq_refl).
    destruct Hlocation as (_ & Haddress & _).
    subst p.
    specialize (Hinit eq_refl).
    rewrite (UCOS2_raw_rep_split_module sg locked TimerModule).
    cbn [UCOS2_module_rep].
    rewrite (timer_initialized_configured_rep_eq sg locked.(TimerState) Henabled Hinit).
    unfold timer_raw_rep.
    entailer!.
    sep_apply_r_atomic (timer_images_merge_object sg locked.(TimerState) i current Hbinding).
    rewrite (tmr_remain_get_object_fields_rep sg (timer_pool_addr sg i) current Hnames).
    unfold timer_globals_rep, tmr_remain_get_globals_without_time,
      tmr_remain_get_time.
    destruct (current.(timerImageState) =? 3); entailer!.
Qed.
