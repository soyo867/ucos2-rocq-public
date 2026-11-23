Require Export Ucos2Verify.VC.code.timer.spec.tmr_link_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Export Ucos2Verify.lib.timer_execution.
Require Export Ucos2Verify.lib.error_codes.
Require Export MonadLib.StateRelMonad.safeexec_lib.
Require Export Coq.Strings.String.
Require Export Coq.Lists.List.
Require Export AUXLib.ListLib.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Export CNotation Mem SeparationLogic.
Require Export Logic.LogicGenerator.demo932.Interface.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The observation is the actual C Boolean and the byte written to *perr.
    Its state is the real normal-return endpoint, after OSSchedUnlock. *)
Definition tmr_start_result := (Z * Z)%type.
Definition tmr_start_bool (b : bool) : Z := if b then 1 else 0.
Definition tmr_start_here (before : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun current => current = before.

Definition tmr_start_layout (p type_addr state_addr : Z) : Prop :=
  type_addr = p /\ state_addr = p + 37.
Definition tmr_start_nonrunning_status (status : Z) : Prop := status = 1 \/ status = 2.

(** Raw callers only lend the bytes actually read.  In particular neither a
    NULL timer nor a bad-Type/ISR return requires a readable State byte. The
    disjoint caller frame retains any other bytes. A real Link/Unlink path
    needs the configured public pool object, wheel and neighbour ownership;
    a forged Type=100 byte is not an ownership certificate. *)
Definition tmr_start_raw_state_rep (p ty state : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  if Z.eq_dec ty 100 then
    if Z.eq_dec (os_sched_lock_ints before) 0 then (p + 37) # UChar |-> state else emp
  else emp.
Definition tmr_start_raw_rep (pooled : bool) (p ty state : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  if pooled then emp else
  if Z.eq_dec p 0 then emp else
  p # UChar |-> ty ** tmr_start_raw_state_rep p ty state before.

Definition tmr_start_client (sg : StableGlobVars) (pooled : bool)
  (p i ty state : Z) (before : UCOS2_Verify_State) : Prop :=
  if pooled then
    p = timer_pool_addr sg i /\ p <> 0 /\
    timer_api_initialized before.(TimerState) /\
    exists image, before.(TimerState).(timerImages) i = Some image /\
      ty = image.(timerImageType)
  else p <> 0 -> ty = 100 -> os_sched_lock_ints before = 0 ->
    state <> 1 /\ state <> 2 /\ state <> 3.

Definition tmr_start_current (sg : StableGlobVars) (pooled : bool)
  (p i raw_state status : Z) (current : UCOS2_Verify_State) : Prop :=
  if pooled then
    p = timer_pool_addr sg i /\ timer_api_initialized current.(TimerState) /\
    exists image, current.(TimerState).(timerImages) i = Some image /\
      status = image.(timerImageState)
  else status = raw_state.

Definition tmr_start_locked_step (sg : StableGlobVars) (pooled : bool)
  (i raw_state : Z) (before : UCOS2_Verify_State)
  (result : tmr_start_result) (after : UCOS2_Verify_State) : Prop :=
  if pooled then exists started error timers,
    timer_start_locked sg before.(TimerState) i = Some (started, error, timers) /\
    fst result = tmr_start_bool started /\ snd result = encode_os_err_code error /\
    after = replace_TimerS timers before
  else after = before /\ fst result = 0 /\
    ((raw_state = 0 /\ snd result = encode_os_err_code OS_ERR_TMR_INACTIVE) \/
     (raw_state <> 0 /\ raw_state <> 1 /\ raw_state <> 2 /\ raw_state <> 3 /\
      snd result = encode_os_err_code OS_ERR_TMR_INVALID_STATE)).

(** The scheduler checkpoint and its subsequent OS_Sched acquisition are
    distinct states. The returned continuation comes from this same call. *)
Definition tmr_start_unlock_return (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State)
  (returned : OsSchedCallContext) (final : UCOS2_Verify_State) : Prop :=
  (before.(SchedState).(isRunning) = false /\ returned = context /\ final = before) \/
  exists entry,
    before.(SchedState).(isRunning) = true /\
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
    if os_sched_unlock_requests entry then
      exists sched_entry,
        critical_region_interval critical sg context.(os_sched_call_invocation)
          (os_sched_unlock_checkpoint true entry) sched_entry /\
        os_sched_c_return external critical sg sched_entry context returned final
    else returned = context /\ final = os_sched_unlock_checkpoint true entry.

Definition tmr_start_lock_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) : program UCOS2_Verify_State unit :=
  update (fun before locked => exists entry,
    os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
      before entry locked).
Definition tmr_start_unlock_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) : program UCOS2_Verify_State OsSchedCallContext :=
  tmr_start_unlock_return external critical sg context.
Definition tmr_start_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pooled : bool) (p i ty raw_state : Z)
  : program UCOS2_Verify_State tmr_start_result :=
  if Z.eq_dec p 0 then ret (0, encode_os_err_code OS_ERR_TMR_INVALID) else
  if Z.eq_dec ty 100 then
    bind (get' os_sched_lock_ints) (fun ints =>
      if Z_gt_dec ints 0 then ret (0, encode_os_err_code OS_ERR_TMR_ISR) else
      bind (tmr_start_lock_program critical sg context) (fun _ =>
      bind (tmr_start_locked_step sg pooled i raw_state) (fun result =>
      bind (tmr_start_unlock_program external critical sg context) (fun _ => ret result))))
  else ret (0, encode_os_err_code OS_ERR_TMR_INVALID_TYPE).

Definition tmr_start_call_result (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pooled : bool) (p i ty raw_state : Z)
  (before : UCOS2_Verify_State) (returned : OsSchedCallContext)
  (result : tmr_start_result) (final : UCOS2_Verify_State) : Prop :=
  if Z.eq_dec p 0 then
    result = (0, encode_os_err_code OS_ERR_TMR_INVALID) /\ returned = context /\ final = before
  else if Z.eq_dec ty 100 then
    if Z_gt_dec (os_sched_lock_ints before) 0 then
      result = (0, encode_os_err_code OS_ERR_TMR_ISR) /\ returned = context /\ final = before
    else exists entry locked changed,
      os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
        before entry locked /\
      tmr_start_locked_step sg pooled i raw_state locked result changed /\
      tmr_start_unlock_return external critical sg context changed returned final
  else result = (0, encode_os_err_code OS_ERR_TMR_INVALID_TYPE) /\ returned = context /\ final = before.

(** This is the existing conditional OSSchedUnlock client protocol at its
    actual endpoint. It is not a no-scheduling or eventual-return premise. *)
Definition tmr_start_unlock_safety (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pooled : bool) (p i ty raw_state : Z)
  (before : UCOS2_Verify_State) : Prop :=
  p <> 0 -> ty = 100 -> os_sched_lock_ints before = 0 ->
  forall entry locked result changed,
    os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
      before entry locked ->
    tmr_start_locked_step sg pooled i raw_state locked result changed ->
    os_sched_unlock_acquire_safety external critical sg context changed.

Definition tmr_start_execution_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (context : OsSchedCallContext) (mask : Z) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask ** os_sched_context_resources external context.
Definition tmr_start_owned (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) (pooled : bool) (p ty raw_state : Z)
  (before current : UCOS2_Verify_State) : Assertion :=
  tmr_start_execution_frame external platform context mask ** unmap_table_rep sg **
  UCOS2_inv sg current ** tmr_start_raw_rep pooled p ty raw_state before.

Definition tmr_start_type_rest (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) (pooled : bool) (p i ty raw_state : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  tmr_start_execution_frame external platform context mask ** unmap_table_rep sg **
  (if pooled then
     EX image, coq_prop (UCOS2_state_inv sg before /\
       before.(TimerState).(timerImages) i = Some image /\ ty = image.(timerImageType)) &&
       (timer_raw_rep_without_type sg before.(TimerState) i image **
        UCOS2_raw_rep_missing_timer sg before)
   else UCOS2_inv sg before ** tmr_start_raw_state_rep p ty raw_state before).

Definition tmr_start_int_rest (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) (pooled : bool) (p ty raw_state : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  tmr_start_execution_frame external platform context mask ** unmap_table_rep sg **
  sg.(g_OSLockNesting) # UChar |-> before.(IntrState).(lockNesting) **
  UCOS2_raw_rep_missing_interrupt sg before **
  tmr_start_raw_rep pooled p ty raw_state before.

Definition tmr_start_state_rest (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) (pooled : bool) (p i ty raw_state status : Z)
  (before current : UCOS2_Verify_State) : Assertion :=
  tmr_start_execution_frame external platform context mask ** unmap_table_rep sg **
  (if pooled then
     EX image, coq_prop (UCOS2_state_inv sg current /\
       current.(TimerState).(timerImages) i = Some image /\ status = image.(timerImageState)) &&
       (timer_complete_rep_without_state sg current.(TimerState) i image **
        UCOS2_raw_rep_missing_timer sg current)
   else UCOS2_inv sg current ** p # UChar |-> ty).

Definition tmr_start_timer_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) (current : UCOS2_Verify_State) : Assertion :=
  tmr_start_execution_frame external platform context mask ** unmap_table_rep sg **
  UCOS2_raw_rep_missing_timer sg current.

Definition tmr_start_return_resources (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context returned : OsSchedCallContext) (mask : Z)
  (final : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  critical_region_outside critical sg context.(os_sched_call_invocation) final **
  os_sched_context_resources external returned ** unmap_table_rep sg.

Definition tmr_start_safe (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pooled : bool) (p i ty raw_state : Z)
  (before : UCOS2_Verify_State) (X : tmr_start_result -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (tmr_start_here before)
    (tmr_start_program external critical sg context pooled p i ty raw_state) X.
Definition tmr_start_safe_return (current : UCOS2_Verify_State) (retcode err : Z)
  (X : tmr_start_result -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (tmr_start_here current) (ret (retcode, err)) X.

Definition tmr_start_pre_facts (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pooled : bool) (p i ty raw_state : Z)
  (before : UCOS2_Verify_State) (X : tmr_start_result -> UCOS2_Verify_State -> Prop) : Prop :=
  tmr_link_layout /\ tmr_unlink_layout /\ tmr_link_profile sg /\
  tmr_start_client sg pooled p i ty raw_state before /\
  tmr_start_unlock_safety external critical sg context pooled p i ty raw_state before /\
  tmr_start_safe external critical sg context pooled p i ty raw_state before X.

Definition tmr_start_unlinked (sg : StableGlobVars) (before : GlobTimerState)
  (i : Z) (after : GlobTimerState) : Prop := timer_unlink sg before i = Some after.
Definition tmr_start_linked (sg : StableGlobVars) (before : GlobTimerState)
  (i : Z) (after : GlobTimerState) : Prop := timer_link sg before i false = Some after.
Definition tmr_start_prefix (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pooled : bool) (p i ty raw_state retcode err : Z)
  (before entry locked current : UCOS2_Verify_State) : Prop :=
  p <> 0 /\ ty = 100 /\ os_sched_lock_ints before = 0 /\
  os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked /\
  tmr_start_locked_step sg pooled i raw_state locked (retcode, err) current.

Definition tmr_start_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (pooled : bool) (p i ty raw_state perr retcode : Z)
  (before : UCOS2_Verify_State) (X : tmr_start_result -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX final, EX returned, EX err,
    coq_prop (tmr_start_call_result external critical sg context pooled p i ty raw_state
        before returned (retcode, err) final /\ tmr_start_safe_return final retcode err X) &&
    (tmr_start_return_resources external platform critical sg context returned mask final **
     tmr_start_raw_rep pooled p ty raw_state before ** perr # UChar |-> err).

Lemma tmr_start_safe_step : forall external critical sg context pooled p i ty raw_state
  before final retcode err X,
  tmr_start_safe external critical sg context pooled p i ty raw_state before X ->
  tmr_start_program external critical sg context pooled p i ty raw_state
    before (retcode, err) final ->
  tmr_start_safe_return final retcode err X.
Proof.
  intros external critical sg context pooled p i ty raw_state before final retcode err X Hsafe Hstep.
  unfold tmr_start_safe, tmr_start_safe_return in *.
  eapply highstependret_derive with
    (P' := fun _ => tmr_start_here final); [|exact Hsafe].
  intros current Hcurrent; unfold tmr_start_here in Hcurrent; subst current.
  exists final; split; [exact Hstep|reflexivity].
Qed.

Lemma tmr_start_call_result_program : forall external critical sg context pooled p i ty raw_state
  before returned result final,
  tmr_start_call_result external critical sg context pooled p i ty raw_state
    before returned result final ->
  tmr_start_program external critical sg context pooled p i ty raw_state before result final.
Proof.
  intros external critical sg context pooled p i ty raw_state before returned result final Hresult.
  unfold tmr_start_call_result, tmr_start_program in *.
  destruct (Z.eq_dec p 0).
  - destruct Hresult as [-> [_ ->]]; split; reflexivity.
  - destruct (Z.eq_dec ty 100).
    + change (exists ints observed,
        (ints = os_sched_lock_ints before /\ before = observed) /\
        (if Z_gt_dec ints 0 then ret (0, encode_os_err_code OS_ERR_TMR_ISR) else
         bind (tmr_start_lock_program critical sg context) (fun _ =>
         bind (tmr_start_locked_step sg pooled i raw_state) (fun answer =>
         bind (tmr_start_unlock_program external critical sg context) (fun _ => ret answer))))
          observed result final).
      exists (os_sched_lock_ints before), before; split; [auto|].
      destruct (Z_gt_dec (os_sched_lock_ints before) 0).
      * destruct Hresult as [-> [_ ->]]; split; reflexivity.
      * destruct Hresult as [entry [locked [changed [Hlock [Hstep Hunlock]]]]].
        exists tt, locked; split.
        -- exists entry; exact Hlock.
        -- exists result, changed; split; [exact Hstep|].
           exists returned, final; split; [exact Hunlock|split; reflexivity].
    + destruct Hresult as [-> [_ ->]]; split; reflexivity.
Qed.

Lemma tmr_start_prefix_call_result : forall external critical sg context pooled p i ty raw_state
  retcode err before entry locked changed returned final,
  tmr_start_prefix critical sg context pooled p i ty raw_state retcode err before entry locked changed ->
  tmr_start_unlock_return external critical sg context changed returned final ->
  tmr_start_call_result external critical sg context pooled p i ty raw_state
    before returned (retcode, err) final.
Proof.
  intros external critical sg context pooled p i ty raw_state retcode err before entry locked changed
    returned final [Hnonzero [Htype [Hints [Hlock Hstep]]]] Hunlock.
  unfold tmr_start_call_result.
  destruct (Z.eq_dec p 0); [contradiction|].
  destruct (Z.eq_dec ty 100); [|contradiction].
  rewrite Hints; destruct (Z_gt_dec 0 0); [lia|].
  exists entry, locked, changed; auto.
Qed.

Lemma tmr_start_closed_raw_equiv : forall critical sg invocation current,
  critical_region_outside critical sg invocation current --||-- UCOS2_raw_rep sg current.
Proof.
  intros; unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite UCOS2_raw_rep_split_running; split; reflexivity.
Qed.

Lemma tmr_start_lock_preserves_public_storage : forall critical sg context before entry locked,
  os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked ->
  timer_public_storage_frame before.(TimerState) locked.(TimerState).
Proof.
  intros; eapply timer_public_trace_public_storage_frame.
  eapply os_sched_lock_call_timer_public_trace; exact H.
Qed.

Lemma tmr_start_unlinked_eligible : forall sg before i stopped,
  tmr_unlink_running before i -> timer_unlink sg before i = Some stopped ->
  tmr_link_eligible stopped i.
Proof.
  intros sg before i stopped [node [Hlookup Hrunning]] Hstep.
  exists (timer_set_status node TimerStopped); split.
  - eapply timer_unlink_target_object_eq; eassumption.
  - discriminate.
Qed.

Lemma tmr_start_unlock_post_return : forall external platform critical sg context mask before,
  os_sched_unlock_post external platform critical sg context mask before |--
  EX returned, EX final,
    coq_prop (tmr_start_unlock_return external critical sg context before returned final) &&
    tmr_start_return_resources external platform critical sg context returned mask final.
Proof.
  intros; unfold os_sched_unlock_post; apply derivable1_orp_elim.
  - Intros; Exists context before; unfold tmr_start_unlock_return.
    unfold tmr_start_return_resources, os_sched_unlock_observation_frame,
      critical_region_outside, os_sched_unlock_running; entailer!; left; tauto.
  - Intros entry; destruct H as [Hrunning [Hinterval Hvalid]].
    destruct (os_sched_unlock_requests entry) eqn:Hschedule.
    + unfold os_sched_post; Intros sched_entry final returned.
      Exists returned final; unfold tmr_start_unlock_return, tmr_start_return_resources.
      entailer!; right; exists entry; split; [exact Hrunning|].
      split; [exact Hinterval|].
      rewrite Hschedule; exists sched_entry; tauto.
    + Exists context (os_sched_unlock_checkpoint true entry).
      unfold tmr_start_return_resources, os_sched_unlock_outside_frame.
      entailer!; right; exists entry; split; [exact Hrunning|].
      split; [exact Hinterval|].
      rewrite Hschedule; auto.
Qed.

Lemma tmr_start_post_after_unlock : forall external platform critical sg context mask pooled
  p i ty raw_state perr retcode err before entry locked changed returned final X,
  tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ->
  tmr_start_prefix critical sg context pooled p i ty raw_state retcode err before entry locked changed ->
  tmr_start_unlock_return external critical sg context changed returned final ->
  tmr_start_return_resources external platform critical sg context returned mask final **
    tmr_start_raw_rep pooled p ty raw_state before ** perr # UChar |-> err |--
  tmr_start_post external platform critical sg context mask pooled p i ty raw_state perr retcode before X.
Proof.
  intros external platform critical sg context mask pooled p i ty raw_state perr retcode err
    before entry locked changed returned final X Hfacts Hprefix Hreturn.
  pose proof (tmr_start_prefix_call_result external critical sg context pooled p i ty raw_state
    retcode err before entry locked changed returned final Hprefix Hreturn) as Hresult.
  pose proof (tmr_start_call_result_program external critical sg context pooled p i ty raw_state
    before returned (retcode, err) final Hresult) as Hprogram.
  assert (Hsafe : tmr_start_safe_return final retcode err X).
  { eapply (tmr_start_safe_step external critical sg context pooled p i ty raw_state
      before final retcode err X).
    - unfold tmr_start_pre_facts in Hfacts; tauto.
    - exact Hprogram. }
  unfold tmr_start_post; Exists final returned err; entailer!.
Qed.

Lemma tmr_start_post_early : forall external platform critical sg context mask pooled
  p i ty raw_state perr retcode err before X,
  tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ->
  tmr_start_call_result external critical sg context pooled p i ty raw_state
    before context (retcode, err) before ->
  tmr_start_owned external platform sg context mask pooled p ty raw_state before before **
    perr # UChar |-> err |--
  tmr_start_post external platform critical sg context mask pooled p i ty raw_state perr retcode before X.
Proof.
  intros external platform critical sg context mask pooled p i ty raw_state perr retcode err
    before X Hfacts Hresult.
  pose proof (tmr_start_call_result_program external critical sg context pooled p i ty raw_state
    before context (retcode, err) before Hresult) as Hprogram.
  assert (Hsafe : tmr_start_safe_return before retcode err X).
  { eapply (tmr_start_safe_step external critical sg context pooled p i ty raw_state
      before before retcode err X).
    - unfold tmr_start_pre_facts in Hfacts; tauto.
    - exact Hprogram. }
  unfold tmr_start_post; Exists before context err.
  unfold tmr_start_owned, tmr_start_execution_frame, tmr_start_return_resources, UCOS2_inv.
  rewrite tmr_start_closed_raw_equiv; entailer!.
Qed.

Lemma timer_complete_rep_merge_current_state__timer_updates : forall sg s i image,
  s.(timerImages) i = Some image ->
  (timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1) # UChar
    |-> image.(timerImageState) ** timer_complete_rep_without_state sg s i image
  |-- timer_raw_rep sg s.
Proof.
  intros sg s i image Himage.
  assert (Hobject : forall c p,
    (p + timer_option_offset c + 1) # UChar |-> image.(timerImageState) **
      timer_object_rep_without_state c p image |-- timer_object_rep c p image).
  { intros; unfold timer_object_rep_without_state, timer_object_rep; entailer!. }
  unfold timer_complete_rep_without_state.
  sep_apply_l_atomic (Hobject sg.(osKernelConfig) (timer_pool_addr sg i)).
  sep_apply_l_atomic (timer_images_merge_object sg s i image Himage).
  unfold timer_raw_rep; entailer!.
Qed.
Lemma timer_raw_rep_merge_same_state__unlock_returns : forall sg s i image,
  s.(timerImages) i = Some image ->
  (timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1) # UChar |->
    image.(timerImageState) ** timer_complete_rep_without_state sg s i image |--
  timer_raw_rep sg s.
Proof.
  intros sg s i image Hlookup.
  assert (Hobject :
    (timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1) # UChar |->
      image.(timerImageState) **
      timer_object_rep_without_state sg.(osKernelConfig) (timer_pool_addr sg i) image |--
    timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) image).
  { unfold timer_object_rep_without_state, timer_object_rep; entailer!. }
  unfold timer_complete_rep_without_state, timer_raw_rep.
  sep_apply Hobject.
  sep_apply (timer_images_merge_object sg s i image Hlookup); entailer!.
Qed.
Lemma tmr_start_state_rest_merge__unlock_returns :
  forall external platform sg context mask pooled p i ty raw_state status before current,
  p <> 0 -> ty = 100 -> os_sched_lock_ints before = 0 ->
  tmr_link_profile sg ->
  tmr_start_current sg pooled p i raw_state status current ->
  (p + 37) # UChar |-> status **
    tmr_start_state_rest external platform sg context mask pooled p i ty raw_state
      status before current |--
  tmr_start_owned external platform sg context mask pooled p ty raw_state before current.
Proof.
  intros external platform sg context mask pooled p i ty raw_state status before current
    Hnonzero Htype Hints Hprofile Hcurrent.
  unfold tmr_start_current in Hcurrent.
  unfold tmr_start_state_rest, tmr_start_owned, tmr_start_raw_rep.
  destruct pooled.
  - destruct Hcurrent as [Hp [Hinit Himage]].
    destruct Hprofile as [Henabled [Hnames Hprofile]].
    Intros image; destruct H as [Hvalid [Hlookup Hstatus]].
    rewrite Hp, Hstatus.
    assert (Hoffset : timer_pool_addr sg i + timer_option_offset sg.(osKernelConfig) + 1 =
      timer_pool_addr sg i + 37).
    { unfold timer_option_offset; rewrite Hnames; lia. }
    rewrite <- Hoffset.
    sep_apply (timer_raw_rep_merge_same_state__unlock_returns sg current.(TimerState) i image Hlookup).
    pose proof (proj2 (UCOS2_raw_rep_split_module sg current TimerModule)) as Hmerge.
    cbn [UCOS2_module_rep] in Hmerge.
    rewrite (timer_initialized_configured_rep_eq sg current.(TimerState) Henabled Hinit) in Hmerge.
    fold (UCOS2_raw_rep_missing_timer sg current) in Hmerge.
    sep_apply Hmerge; unfold UCOS2_inv; entailer!.
  - rewrite Hcurrent.
    destruct (Z.eq_dec p 0); [contradiction|].
    unfold tmr_start_raw_state_rep; rewrite Htype, Hints; simpl; entailer!.
Qed.
Lemma tmr_start_owned_unlock_pre__unlock_returns :
  forall external platform critical sg context mask pooled p i ty raw_state
    retcode err before entry locked changed X,
  tmr_start_pre_facts external critical sg context pooled p i ty raw_state before X ->
  tmr_start_prefix critical sg context pooled p i ty raw_state retcode err before entry locked changed ->
  tmr_start_owned external platform sg context mask pooled p ty raw_state before changed |--
  os_sched_unlock_pre external platform critical sg context mask changed **
    tmr_start_raw_rep pooled p ty raw_state before.
Proof.
  intros external platform critical sg context mask pooled p i ty raw_state retcode err
    before entry locked changed X Hfacts Hprefix.
  destruct Hfacts as [_ [_ [_ [_ [Hsafe _]]]]].
  destruct Hprefix as [Hnonzero [Htype [Hints [Hlock Hstep]]]].
  pose proof (Hsafe Hnonzero Htype Hints entry locked (retcode, err) changed Hlock Hstep) as Hunlock.
  unfold tmr_start_owned, tmr_start_execution_frame, UCOS2_inv.
  rewrite os_sched_unlock_pre_closed_equiv.
  unfold os_sched_unlock_outside_frame.
  rewrite tmr_start_closed_raw_equiv; entailer!.
Qed.
