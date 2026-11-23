Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.borrowable_region.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The complement of the scheduler-protected Timer pool body.  In
    particular, type bytes and the service globals remain here: Timer APIs
    read the former before their ISR guard, and OSTmrSignal reads the latter.
    This is a physical partition of the existing heap, not an acquisition
    token or a new field of the abstract kernel state.  An outside-region
    handle does not entail either part of this partition. *)
Definition UCOS2_raw_rep_missing_timer_pool_body (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  timer_images_type_rep sg s.(TimerState) **
  timer_service_globals_rep sg s.(TimerState) **
  UCOS2_raw_rep_missing_timer sg s.

(** The pure state is the last stable snapshot.  While the borrowed body
    is being changed, this assertion alone does not represent a complete
    physical kernel at that snapshot. *)
Definition UCOS2_inv_missing_timer_pool_body (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) &&
  UCOS2_raw_rep_missing_timer_pool_body sg s.

Lemma UCOS2_raw_rep_split_timer_pool_body : forall sg s,
  cfgTimerEnabled sg.(osKernelConfig) = true ->
  timer_api_initialized s.(TimerState) ->
  UCOS2_raw_rep sg s --||--
    timer_pool_rep_without_types sg s.(TimerState) **
    UCOS2_raw_rep_missing_timer_pool_body sg s.
Proof.
  intros sg s Henabled Hinit.
  rewrite (UCOS2_raw_rep_split_module sg s TimerModule).
  cbn [UCOS2_module_rep].
  rewrite (timer_initialized_configured_rep_eq sg s.(TimerState) Henabled Hinit),
    timer_raw_rep_split_pool, timer_pool_rep_split_types.
  unfold UCOS2_raw_rep_missing_timer_pool_body, UCOS2_raw_rep_missing_timer.
  split; entailer!.
Qed.

Lemma UCOS2_inv_split_timer_pool_body : forall sg s,
  cfgTimerEnabled sg.(osKernelConfig) = true ->
  timer_api_initialized s.(TimerState) ->
  UCOS2_inv sg s --||--
    timer_pool_rep_without_types sg s.(TimerState) **
    UCOS2_inv_missing_timer_pool_body sg s.
Proof.
  intros sg s Henabled Hinit.
  unfold UCOS2_inv, UCOS2_inv_missing_timer_pool_body.
  rewrite (UCOS2_raw_rep_split_timer_pool_body sg s Henabled Hinit).
  split; entailer!.
Qed.

Lemma UCOS2_raw_rep_missing_timer_pool_body_replace_timer_eq : forall sg s timers,
  timer_image_types timers.(timerImages) = timer_image_types s.(TimerState).(timerImages) ->
  timer_service_globals_rep sg timers = timer_service_globals_rep sg s.(TimerState) ->
  UCOS2_raw_rep_missing_timer_pool_body sg (replace_TimerS timers s) =
    UCOS2_raw_rep_missing_timer_pool_body sg s.
Proof.
  intros sg s timers Htypes Hservice.
  unfold UCOS2_raw_rep_missing_timer_pool_body.
  cbn [replace_TimerS TimerState]; rewrite Hservice.
  unfold timer_images_type_rep; rewrite Htypes; reflexivity.
Qed.

Lemma UCOS2_inv_merge_updated_timer_pool_body : forall sg s timers,
  cfgTimerEnabled sg.(osKernelConfig) = true -> timer_api_initialized timers ->
  UCOS2_state_inv sg (replace_TimerS timers s) ->
  timer_image_types timers.(timerImages) = timer_image_types s.(TimerState).(timerImages) ->
  timer_service_globals_rep sg timers = timer_service_globals_rep sg s.(TimerState) ->
  timer_pool_rep_without_types sg timers ** UCOS2_raw_rep_missing_timer_pool_body sg s |--
    UCOS2_inv sg (replace_TimerS timers s).
Proof.
  intros sg s timers Henabled Hinit Hvalid Htypes Hservice.
  unfold UCOS2_inv.
  rewrite (UCOS2_raw_rep_split_timer_pool_body sg (replace_TimerS timers s) Henabled Hinit),
    (UCOS2_raw_rep_missing_timer_pool_body_replace_timer_eq sg s timers Htypes Hservice).
  cbn [replace_TimerS TimerState]; entailer!.
Qed.

(** OSIntEnter/OSIntExit may update the interrupt counters without taking
    the borrowed pool.  No Timer-body ownership is present in this frame. *)
Definition UCOS2_raw_rep_missing_timer_pool_body_interrupt (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  timer_images_type_rep sg s.(TimerState) **
  timer_service_globals_rep sg s.(TimerState) **
  UCOS2_raw_rep_missing_two sg s TimerModule InterruptModule.

Lemma UCOS2_raw_rep_missing_timer_pool_body_split_interrupt : forall sg s,
  UCOS2_raw_rep_missing_timer_pool_body sg s --||--
    interrupt_inv sg s.(IntrState) **
    UCOS2_raw_rep_missing_timer_pool_body_interrupt sg s.
Proof.
  intros; unfold UCOS2_raw_rep_missing_timer_pool_body,
    UCOS2_raw_rep_missing_timer_pool_body_interrupt, UCOS2_raw_rep_missing_timer.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg s TimerModule InterruptModule)
    by discriminate.
  cbn [UCOS2_module_rep]; split; entailer!.
Qed.

Lemma UCOS2_raw_rep_missing_timer_pool_body_interrupt_replace_interrupt_eq :
  forall sg s counters,
  UCOS2_raw_rep_missing_timer_pool_body_interrupt sg (replace_IntrS counters s) =
    UCOS2_raw_rep_missing_timer_pool_body_interrupt sg s.
Proof. reflexivity. Qed.

Lemma UCOS2_inv_missing_timer_pool_body_split_interrupt : forall sg s,
  UCOS2_inv_missing_timer_pool_body sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
    (interrupt_inv sg s.(IntrState) **
      UCOS2_raw_rep_missing_timer_pool_body_interrupt sg s).
Proof.
  intros; unfold UCOS2_inv_missing_timer_pool_body.
  rewrite UCOS2_raw_rep_missing_timer_pool_body_split_interrupt.
  split; reflexivity.
Qed.

Lemma UCOS2_inv_missing_timer_pool_body_merge_updated_interrupt : forall sg s counters,
  UCOS2_state_inv sg s ->
  interrupt_inv sg counters ** UCOS2_raw_rep_missing_timer_pool_body_interrupt sg s |--
    UCOS2_inv_missing_timer_pool_body sg (replace_IntrS counters s).
Proof.
  intros sg s counters Hvalid.
  rewrite UCOS2_inv_missing_timer_pool_body_split_interrupt,
    UCOS2_validity_replace_interrupt_eq,
    UCOS2_raw_rep_missing_timer_pool_body_interrupt_replace_interrupt_eq.
  cbn [replace_IntrS IntrState]; entailer!.
Qed.

(** A public Timer API's type and ISR tests can be performed against the
    complement.  The lookup is required: private allocations are absent
    from timerImages, so no type cell for them is manufactured here. *)
Definition UCOS2_timer_observation_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (i : TimerID) : Assertion :=
  store_map_missing_i (fun j ty => timer_pool_addr sg j # UChar |-> ty)
    (timer_image_types s.(TimerState).(timerImages)) i **
  timer_service_globals_rep sg s.(TimerState) **
  interrupt_inv_no_int_nesting sg s.(IntrState) **
  UCOS2_raw_rep_missing_two sg s TimerModule InterruptModule.

Lemma UCOS2_inv_missing_timer_pool_body_split_observation : forall sg s i v,
  s.(TimerState).(timerImages) i = Some v ->
  UCOS2_inv_missing_timer_pool_body sg s |--
    coq_prop (UCOS2_state_inv sg s) &&
    (timer_pool_addr sg i # UChar |-> v.(timerImageType) **
     sg.(g_OSIntNesting) # UChar |-> s.(IntrState).(intNesting) **
     UCOS2_timer_observation_residual sg s i).
Proof.
  intros sg s i v Hlookup.
  assert (Htype : timer_image_types s.(TimerState).(timerImages) i = Some v.(timerImageType)).
  { unfold timer_image_types; rewrite Hlookup; reflexivity. }
  rewrite UCOS2_inv_missing_timer_pool_body_split_interrupt.
  unfold UCOS2_raw_rep_missing_timer_pool_body_interrupt,
    timer_images_type_rep, UCOS2_timer_observation_residual,
    interrupt_inv, store_int_state, interrupt_inv_no_int_nesting.
  pureIntros.
  sep_apply_l_atomic (store_map_split
    (fun j ty => timer_pool_addr sg j # UChar |-> ty) i v.(timerImageType) _ Htype).
  entailer!.
Qed.

Lemma UCOS2_inv_missing_timer_pool_body_merge_observation : forall sg s i v,
  s.(TimerState).(timerImages) i = Some v -> UCOS2_state_inv sg s ->
  timer_pool_addr sg i # UChar |-> v.(timerImageType) **
    sg.(g_OSIntNesting) # UChar |-> s.(IntrState).(intNesting) **
    UCOS2_timer_observation_residual sg s i |--
  UCOS2_inv_missing_timer_pool_body sg s.
Proof.
  intros sg s i v Hlookup Hvalid.
  assert (Htype : timer_image_types s.(TimerState).(timerImages) i = Some v.(timerImageType)).
  { unfold timer_image_types; rewrite Hlookup; reflexivity. }
  rewrite UCOS2_inv_missing_timer_pool_body_split_interrupt.
  unfold UCOS2_raw_rep_missing_timer_pool_body_interrupt,
    timer_images_type_rep, UCOS2_timer_observation_residual,
    interrupt_inv, store_int_state, interrupt_inv_no_int_nesting.
  pureIntros.
  sep_apply_l_atomic (store_map_merge
    (fun j ty => timer_pool_addr sg j # UChar |-> ty) i v.(timerImageType) _ Htype).
  entailer!.
Qed.

(** Physical interpretation of the two-token ownership protocol.  These
    are real, disjoint pieces of the existing kernel representation.  A
    token/state value is NOT an Assertion granting either piece.  The
    conservation theorem below is the heap-transfer obligation for an
    embedding, not a stand-alone outside-to-heap entailment. *)
Definition timer_region_share_tokens (access pool : bool) : BorrowableRegion.Token -> Prop :=
  fun token => match token with
  | BorrowableRegion.Access => access = true
  | BorrowableRegion.Loan => pool = true
  end.

Definition timer_region_share_rep (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (access pool : bool) : Assertion :=
  (if access then UCOS2_inv_missing_timer_pool_body sg s else emp) **
  (if pool then timer_pool_rep_without_types sg s.(TimerState) else emp).

Definition timer_region_shared_access (region : BorrowableRegion.State) : bool :=
  match region with BorrowableRegion.Closed _ => true | BorrowableRegion.Open _ => false end.

Definition timer_region_shared_pool (region : BorrowableRegion.State) : bool :=
  match region with BorrowableRegion.Closed None => true | _ => false end.

Definition timer_region_shared_rep (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (region : BorrowableRegion.State) : Assertion :=
  timer_region_share_rep sg s (timer_region_shared_access region) (timer_region_shared_pool region).

Lemma timer_region_invariant_token_bits : forall region token,
  BorrowableRegion.invariant_tokens region token <->
  timer_region_share_tokens (timer_region_shared_access region) (timer_region_shared_pool region) token.
Proof.
  intros [[owner|]|[owner|]] []; unfold BorrowableRegion.invariant_tokens,
    BorrowableRegion.available_tokens, BorrowableRegion.access_tokens,
    BorrowableRegion.full_tokens, BorrowableRegion.empty_tokens,
    timer_region_share_tokens, timer_region_shared_access, timer_region_shared_pool;
    simpl; intuition discriminate.
Qed.

Lemma timer_region_full_share : forall sg s,
  cfgTimerEnabled sg.(osKernelConfig) = true -> timer_api_initialized s.(TimerState) ->
  timer_region_share_rep sg s true true --||-- UCOS2_inv sg s.
Proof.
  intros sg s Henabled Hinit.
  unfold timer_region_share_rep.
  rewrite (UCOS2_inv_split_timer_pool_body sg s Henabled Hinit).
  split; entailer!.
Qed.

Lemma timer_region_share_join : forall sg s access pool other_access other_pool,
  andb access other_access = false -> andb pool other_pool = false ->
  timer_region_share_rep sg s access pool ** timer_region_share_rep sg s other_access other_pool
    --||-- timer_region_share_rep sg s (orb access other_access) (orb pool other_pool).
Proof.
  intros sg s [] [] [] [] Haccess Hpool; simpl in Haccess, Hpool;
    try discriminate; unfold timer_region_share_rep; simpl; split; entailer!.
Qed.

(** At a transfer boundary both views refer to the same stable snapshot.
    In the middle of Del, the pool may be transient: rejoining its changed
    state additionally uses UCOS2_inv_merge_updated_timer_pool_body, not
    the same-snapshot theorem below.  In particular this theorem does not
    put the suspended task's pool in the interrupt's precondition. *)
Lemma timer_region_step_resources : forall sg s action before after
  access pool next_access next_pool,
  BorrowableRegion.step action before (timer_region_share_tokens access pool)
    after (timer_region_share_tokens next_access next_pool) ->
  timer_region_share_rep sg s access pool ** timer_region_shared_rep sg s before --||--
    timer_region_share_rep sg s next_access next_pool ** timer_region_shared_rep sg s after.
Proof.
  intros sg s action before after access pool next_access next_pool
    [_ [_ [Hbefore [Hafter Htotal]]]].
  pose proof (Hbefore BorrowableRegion.Access) as Hba.
  pose proof (Hbefore BorrowableRegion.Loan) as Hbp.
  pose proof (Hafter BorrowableRegion.Access) as Haa.
  pose proof (Hafter BorrowableRegion.Loan) as Hap.
  pose proof (Htotal BorrowableRegion.Access) as Hta.
  pose proof (Htotal BorrowableRegion.Loan) as Htp.
  rewrite !timer_region_invariant_token_bits in Hba, Hbp, Haa, Hap, Hta, Htp.
  rewrite (timer_region_invariant_token_bits after BorrowableRegion.Access) in Hta.
  rewrite (timer_region_invariant_token_bits after BorrowableRegion.Loan) in Htp.
  cbn [timer_region_share_tokens] in Hba, Hbp, Haa, Hap, Hta, Htp.
  assert (Hba' : andb access (timer_region_shared_access before) = false).
  { destruct access, (timer_region_shared_access before); simpl in *; tauto. }
  assert (Hbp' : andb pool (timer_region_shared_pool before) = false).
  { destruct pool, (timer_region_shared_pool before); simpl in *; tauto. }
  assert (Haa' : andb next_access (timer_region_shared_access after) = false).
  { destruct next_access, (timer_region_shared_access after); simpl in *; tauto. }
  assert (Hap' : andb next_pool (timer_region_shared_pool after) = false).
  { destruct next_pool, (timer_region_shared_pool after); simpl in *; tauto. }
  assert (Haccess : orb access (timer_region_shared_access before) =
    orb next_access (timer_region_shared_access after)).
  { apply Bool.eq_true_iff_eq; rewrite !Bool.orb_true_iff; exact Hta. }
  assert (Hpool : orb pool (timer_region_shared_pool before) =
    orb next_pool (timer_region_shared_pool after)).
  { apply Bool.eq_true_iff_eq; rewrite !Bool.orb_true_iff; exact Htp. }
  unfold timer_region_shared_rep.
  rewrite (timer_region_share_join _ _ _ _ _ _ Hba' Hbp'),
    (timer_region_share_join _ _ _ _ _ _ Haa' Hap'), Haccess, Hpool.
  split; reflexivity.
Qed.
