Require Export Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Export Ucos2Verify.lib.ucos2_timer_region.
Require Export Ucos2Verify.lib.timer_execution.
Require Export Ucos2Verify.lib.timer.
Require Export MonadLib.StateRelMonad.safeexec_lib.
Require Export MonadLib.StateRelMonad.StateRelBasic.
Require Export MonadLib.StateRelMonad.StateRelHoare.
From SimpleC.SL Require Export Mem SeparationLogic.
Require Export Logic.LogicGenerator.demo932.Interface.

Import UCOS2_C_Rules ListNotations Monad.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Static ABI/configuration bindings consumed at the field cuts.  The
    arithmetic is on addresses in Z, never C OS_TMR pointer arithmetic. *)
Definition tmr_state_get_layout (sg : StableGlobVars)
  (p type_addr state_addr ints_addr : Z) : Prop :=
  cfgTimerEnabled sg.(osKernelConfig) = true /\
  timer_option_offset sg.(osKernelConfig) = 36 /\
  type_addr = p /\ state_addr = p + 37 /\ ints_addr = sg.(g_OSIntNesting).

(** [raw=true] denotes caller-owned bytes disjoint from the kernel.
    [raw=false] denotes an initialized, publicly present pool image.  Only
    the former can have a bad Type or State under the configured invariant.
    The raw state byte is needed only on the actual Lock/Unlock path. *)
Definition tmr_state_get_raw_storage (p : Z) (raw : bool)
  (ty state : Z) (before : UCOS2_Verify_State) : Assertion :=
  if Z.eqb p 0 then emp else
  if raw then
    p # UChar |-> ty **
    (if andb (Z.eqb ty 100) (Z.eqb (os_sched_ints before) 0)
     then (p + 37) # UChar |-> state else emp)
  else emp.

Definition tmr_state_get_input (sg : StableGlobVars)
  (before : UCOS2_Verify_State) (p : Z) (raw : bool) (i ty : Z) : Prop :=
  p = 0 \/
  (p <> 0 /\ if raw then True else
    cfgTimerEnabled sg.(osKernelConfig) = true /\
    timer_option_offset sg.(osKernelConfig) = 36 /\
    timer_api_initialized before.(TimerState) /\ p = timer_pool_addr sg i /\
    exists image, before.(TimerState).(timerImages) i = Some image /\
      image.(timerImageType) = ty).

(** This is exactly the conditional safety obligation of the existing
    Unlock caller.  It is required only after all three source guards pass
    and only at an endpoint supplied by the actual Lock relation.  It
    constrains the call environment, not the query result or termination. *)
Definition tmr_state_get_call_protocol (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State)
  (p ty : Z) : Prop :=
  p <> 0 -> ty = 100 -> os_sched_ints before = 0 ->
  forall entry locked,
    os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
      before entry locked ->
    os_sched_unlock_acquire_safety external critical sg context locked.

Definition tmr_state_get_state_error (state : Z) : Z :=
  if andb (0 <=? state) (state <=? 3) then 0 else 141.

Definition tmr_state_get_observation (raw : bool) (i raw_state : Z)
  (locked : UCOS2_Verify_State) (state : Z) : Prop :=
  if raw then state = raw_state else
  exists image, locked.(TimerState).(timerImages) i = Some image /\
    state = image.(timerImageState).

(** Ordinary return history projected from the EXISTING Unlock Ensure.
    A switch uses OS_Sched's real acquired state and returned context.
    No result is required to exist for a nonreturning continuation. *)
Definition tmr_state_get_unlock_return (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State)
  (returned : OsSchedCallContext) (final : UCOS2_Verify_State) : Prop :=
  if before.(SchedState).(isRunning) then
    exists entry,
      critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
      if os_sched_unlock_requests entry then
        exists acquired,
          critical_region_interval critical sg context.(os_sched_call_invocation)
            (os_sched_unlock_checkpoint true entry) acquired /\
          os_sched_c_return external critical sg acquired context returned final
      else returned = context /\ final = os_sched_unlock_checkpoint true entry
  else returned = context /\ final = before.

Definition tmr_state_get_result := ((Z * Z) * OsSchedCallContext)%type.

Lemma tmr_state_get_unlock_return_preserves_validity : forall external critical sg context
  before returned final,
  UCOS2_state_inv sg before ->
  os_sched_unlock_acquire_safety external critical sg context before ->
  tmr_state_get_unlock_return external critical sg context before returned final ->
  UCOS2_state_inv sg final.
Proof.
  intros external critical sg context before returned final Hvalid Hsafe Hreturn.
  unfold tmr_state_get_unlock_return in Hreturn.
  destruct before.(SchedState).(isRunning) eqn:Hrunning.
  - destruct Hreturn as [entry [Hinterval Hreturn]].
    pose proof (proj1 (critical_region_interval_transports_resources critical sg _ _ _
      Hinterval Hvalid)) as Hentry.
    pose proof (os_sched_unlock_checkpoint_preserves_validity sg true entry Hentry) as Hcheckpoint.
    destruct (os_sched_unlock_requests entry) eqn:Hrequest.
    + destruct Hreturn as [acquired [Hacquire Hreturn]].
      pose proof (proj1 (critical_region_interval_transports_resources critical sg _ _ _
        Hacquire Hcheckpoint)) as Hacquired.
      assert (Hsched : os_sched_acquire_safety external critical sg context
        (os_sched_unlock_checkpoint true entry)).
      { apply (Hsafe Hrunning entry Hinterval); exact Hrequest. }
      pose proof (Hsched acquired Hacquire) as [_ Hswitch].
      pose proof (os_sched_ready_checkpoint_preserves_validity sg acquired Hacquired) as Hprefix.
      unfold os_sched_c_return in Hreturn.
      destruct (os_sched_requests_switch acquired) eqn:Hrequested.
      * exact (os_sched_switch_outcome_preserves_validity external critical sg acquired context
          (OsSchedOriginalResumed returned final) Hprefix (Hswitch eq_refl) Hreturn).
      * destruct Hreturn as [_ ->]; exact Hprefix.
    + destruct Hreturn as [_ ->]; exact Hcheckpoint.
  - destruct Hreturn as [_ ->]; exact Hvalid.
Qed.

(** Source-ordered relational program. The pure object observation is
    between the two concrete callee relations; it never refers to final. *)
Definition tmr_state_get_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (p : Z) (raw : bool) (i ty raw_state : Z)
  : program UCOS2_Verify_State tmr_state_get_result :=
  fun before result final =>
    if Z.eqb p 0 then result = ((0,138),context) /\ final = before else
    if negb (Z.eqb ty 100) then result = ((0,137),context) /\ final = before else
    if Z.ltb 0 (os_sched_ints before) then result = ((0,139),context) /\ final = before else
    exists entry locked state returned,
      os_sched_lock_call_relation critical sg context.(os_sched_call_invocation)
        before entry locked /\
      tmr_state_get_observation raw i raw_state locked state /\
      tmr_state_get_unlock_return external critical sg context locked returned final /\
      result = ((state,tmr_state_get_state_error state),returned).

Definition tmr_state_get_at (before current : UCOS2_Verify_State) : Prop :=
  current = before.

Definition tmr_state_get_safe (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (p : Z) (raw : bool) (i ty raw_state : Z)
  (before : UCOS2_Verify_State)
  (X : tmr_state_get_result -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (tmr_state_get_at before)
    (tmr_state_get_program external critical sg context p raw i ty raw_state) X.

Definition tmr_state_get_safe_return (state error : Z)
  (returned : OsSchedCallContext) (final : UCOS2_Verify_State)
  (X : tmr_state_get_result -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (tmr_state_get_at final) (ret ((state,error),returned)) X.

Lemma tmr_state_get_program_safe_return : forall external critical sg context
  p raw i ty raw_state before state error returned final X,
  tmr_state_get_safe external critical sg context p raw i ty raw_state before X ->
  tmr_state_get_program external critical sg context p raw i ty raw_state
    before ((state,error),returned) final ->
  tmr_state_get_safe_return state error returned final X.
Proof.
  intros external critical sg context p raw i ty raw_state before state error returned final X
    Hsafe Hstep.
  unfold tmr_state_get_safe, tmr_state_get_safe_return in *.
  eapply (highstependret_derive _ _ ((state,error),returned)
    (fun _ => tmr_state_get_at final)); [|exact Hsafe].
  unfold hs_eval, tmr_state_get_at; intros current ->.
  exists final; auto.
Qed.

Definition tmr_state_get_resources (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context returned : OsSchedCallContext) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  critical_region_outside critical sg context.(os_sched_call_invocation) state **
  os_sched_context_resources external returned ** unmap_table_rep sg.

Definition tmr_state_get_context_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  os_sched_context_resources external context ** unmap_table_rep sg.

Definition tmr_state_get_calls (p ty : Z) (before : UCOS2_Verify_State) : bool :=
  andb (andb (negb (Z.eqb p 0)) (Z.eqb ty 100)) (Z.eqb (os_sched_ints before) 0).

Definition tmr_state_get_entry_context_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (p ty : Z) : Assertion :=
  if tmr_state_get_calls p ty before
  then tmr_state_get_context_frame external platform sg context mask else emp.

(** No task continuation, scheduler table or platform token is demanded
    by a NULL/type/ISR early return.  A successful guard prefix supplies
    exactly the resources required by the existing two callee contracts. *)
Definition tmr_state_get_public_resources (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context returned : OsSchedCallContext) (mask : Z)
  (before final : UCOS2_Verify_State) (p ty : Z) : Assertion :=
  UCOS2_raw_rep sg final **
  (if tmr_state_get_calls p ty before then
    interrupt_platform_running platform context.(os_sched_call_invocation)
      context.(os_sched_call_origin) mask **
    os_sched_context_resources external returned ** unmap_table_rep sg
   else emp).

Definition tmr_state_get_entry_facts (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State)
  (p : Z) (raw : bool) (i ty raw_state : Z)
  (X : tmr_state_get_result -> UCOS2_Verify_State -> Prop) : Prop :=
  UCOS2_state_inv sg before /\ tmr_state_get_input sg before p raw i ty /\
  tmr_state_get_call_protocol external critical sg context before p ty /\
  tmr_state_get_safe external critical sg context p raw i ty raw_state before X.

(** Complement of the two actual early observations.  For a pool object,
    the existential is tied to this snapshot's real map lookup. *)
Definition tmr_state_get_observation_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) (before : UCOS2_Verify_State)
  (p : Z) (raw : bool) (i ty raw_state : Z) : Assertion :=
  tmr_state_get_entry_context_frame external platform sg context mask before p ty **
  interrupt_inv_no_int_nesting sg before.(IntrState) **
  (if raw then
    (if andb (Z.eqb ty 100) (Z.eqb (os_sched_ints before) 0)
     then (p+37) # UChar |-> raw_state else emp) **
    UCOS2_raw_rep_missing_interrupt sg before
   else EX image,
     coq_prop (before.(TimerState).(timerImages) i = Some image /\
       image.(timerImageType) = ty) &&
     (timer_raw_rep_without_type sg before.(TimerState) i image **
      UCOS2_raw_rep_missing_two sg before TimerModule InterruptModule)).

(** Complement of the state byte read after Lock.  No old pool image is
    transported through Lock; the producer obtains a current lookup. *)
Definition tmr_state_get_state_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (locked : UCOS2_Verify_State) (p : Z) (raw : bool) (i ty observed : Z) : Assertion :=
  if raw then p # UChar |-> ty **
    tmr_state_get_resources external platform critical sg context context mask locked
  else tmr_state_get_context_frame external platform sg context mask **
    UCOS2_raw_rep_missing_timer sg locked **
    EX image,
      coq_prop (locked.(TimerState).(timerImages) i = Some image /\
        image.(timerImageState) = observed) &&
      (timer_pool_addr sg i # UChar |-> image.(timerImageType) **
        timer_raw_rep_without_type_state sg locked.(TimerState) i image).

Definition tmr_state_get_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (p : Z) (raw : bool) (i ty raw_state : Z)
  (X : tmr_state_get_result -> UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (tmr_state_get_entry_facts external critical sg context before p raw i ty raw_state X) &&
  (tmr_state_get_public_resources external platform sg context context mask before before p ty **
    tmr_state_get_raw_storage p raw ty raw_state before).

Definition tmr_state_get_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (p : Z) (raw : bool) (i ty raw_state error_addr result : Z)
  (X : tmr_state_get_result -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX final, EX returned, EX error,
    coq_prop (UCOS2_state_inv sg final /\
      tmr_state_get_program external critical sg context p raw i ty raw_state
      before ((result,error),returned) final /\
      tmr_state_get_safe_return result error returned final X) &&
    (tmr_state_get_public_resources external platform sg context returned mask before final p ty **
      tmr_state_get_raw_storage p raw ty raw_state before ** error_addr # UChar |-> error).

Lemma tmr_state_get_closed_rep : forall critical sg invocation state,
  critical_region_outside critical sg invocation state --||-- UCOS2_raw_rep sg state.
Proof.
  intros; unfold critical_region_outside.
  rewrite (critical_region_outside_without_running_rep critical), UCOS2_raw_rep_split_running.
  split; reflexivity.
Qed.

Lemma tmr_state_get_unlock_post : forall external platform critical sg context mask before,
  os_sched_unlock_post external platform critical sg context mask before |--
    EX final, EX returned,
      coq_prop (tmr_state_get_unlock_return external critical sg context before returned final) &&
      tmr_state_get_resources external platform critical sg context returned mask final.
Proof.
  intros; unfold os_sched_unlock_post; apply derivable1_orp_elim.
  - Intros; destruct H as [Hrunning Hvalid]; Exists before context.
    unfold tmr_state_get_unlock_return; rewrite Hrunning.
    unfold tmr_state_get_resources, os_sched_unlock_observation_frame,
      critical_region_outside, os_sched_unlock_running; entailer!.
  - Intros entry; destruct H as [Hrunning [Hinterval Hvalid]].
    destruct (os_sched_unlock_requests entry) eqn:Hrequest.
    + unfold os_sched_post; Intros acquired final returned.
      Exists final returned.
      unfold tmr_state_get_unlock_return; rewrite Hrunning.
      assert (Hreturn : exists e,
        critical_region_interval critical sg (os_sched_call_invocation context) before e /\
        (if os_sched_unlock_requests e then
          exists a, critical_region_interval critical sg (os_sched_call_invocation context)
            (os_sched_unlock_checkpoint true e) a /\
            os_sched_c_return external critical sg a context returned final
         else returned = context /\ final = os_sched_unlock_checkpoint true e)).
      { exists entry; split; [assumption|rewrite Hrequest; exists acquired; auto]. }
      unfold tmr_state_get_resources; entailer!.
    + Exists (os_sched_unlock_checkpoint true entry) context.
      unfold tmr_state_get_unlock_return; rewrite Hrunning.
      assert (Hreturn : exists e,
        critical_region_interval critical sg (os_sched_call_invocation context) before e /\
        (if os_sched_unlock_requests e then
          exists a, critical_region_interval critical sg (os_sched_call_invocation context)
            (os_sched_unlock_checkpoint true e) a /\
            os_sched_c_return external critical sg a context context
              (os_sched_unlock_checkpoint true entry)
         else context = context /\ os_sched_unlock_checkpoint true entry =
           os_sched_unlock_checkpoint true e)).
      { exists entry; split; [assumption|rewrite Hrequest; auto]. }
      unfold tmr_state_get_resources, os_sched_unlock_outside_frame; entailer!.
Qed.

Lemma tmr_state_get_lock_has_current_image : forall critical sg context before entry locked i old,
  os_sched_lock_call_relation critical sg context.(os_sched_call_invocation) before entry locked ->
  timer_api_initialized before.(TimerState) ->
  before.(TimerState).(timerImages) i = Some old ->
  timer_api_initialized locked.(TimerState) /\
    exists current, locked.(TimerState).(timerImages) i = Some current.
Proof.
  intros critical sg context before entry locked i old Hcall Hinit Himage.
  pose proof (timer_public_trace_public_storage_frame sg _ _
    (os_sched_lock_call_timer_public_trace critical sg _ _ _ _ Hcall)) as Hframe.
  split.
  - eapply timer_public_storage_frame_initialized; eauto.
  - eapply timer_public_storage_frame_has_image; eauto.
Qed.

Lemma tmr_state_get_observation_merge__branch_returns : forall external platform sg
  context mask before p raw i ty raw_state type_addr state_addr ints_addr,
  tmr_state_get_layout sg p type_addr state_addr ints_addr ->
  tmr_state_get_input sg before p raw i ty -> p <> 0 ->
  type_addr # UChar |-> ty ** ints_addr # UChar |-> os_sched_ints before **
    tmr_state_get_observation_frame external platform sg context mask before
      p raw i ty raw_state |--
  tmr_state_get_public_resources external platform sg context context mask
    before before p ty ** tmr_state_get_raw_storage p raw ty raw_state before.
Proof.
  intros external platform sg context mask before p raw i ty raw_state
    type_addr state_addr ints_addr Hlayout Hinput Hnonnull.
  destruct Hlayout as [Henabled [Hoffset [-> [_ ->]]]].
  assert (Hp : Z.eqb p 0 = false) by (apply Z.eqb_neq; exact Hnonnull).
  unfold tmr_state_get_observation_frame, tmr_state_get_public_resources,
    tmr_state_get_raw_storage, tmr_state_get_entry_context_frame,
    tmr_state_get_context_frame.
  rewrite Hp; destruct raw.
  - rewrite (UCOS2_raw_rep_split_module sg before InterruptModule).
    cbn [UCOS2_module_rep].
    unfold UCOS2_raw_rep_missing_interrupt, os_sched_ints, interrupt_inv,
      store_int_state, interrupt_inv_no_int_nesting.
    entailer!.
  - destruct Hinput as [Hzero|[_ [_ [_ [Hinit [Haddr Himage]]]]]];
      [contradiction|].
    Intros image; destruct H as [Hlookup Htype].
    rewrite Haddr, <- Htype.
    sep_apply (timer_configured_rep_merge_type sg before.(TimerState) i image
      Henabled Hinit Hlookup).
    rewrite (UCOS2_raw_rep_split_two sg before TimerModule InterruptModule
      ltac:(discriminate)).
    cbn [UCOS2_module_rep].
    unfold os_sched_ints, interrupt_inv, store_int_state, interrupt_inv_no_int_nesting.
    entailer!.
Qed.
