Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Export Ucos2Verify.VC.code.time.spec.time_get_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_reg_get_spec.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** V2.93.01 OSFlagPendGetFlagsRdy: Save, read the actual current TCB's
    UShort field, Restore, return the private snapshot. Task ONLY is the
    documented call protocol, not an executed ISR guard. The resource
    contract below states the exact additional memory-read responsibility;
    it neither turns TaskInvocationOrigin into ISR-execution evidence nor
    invents an error return or a live-current consequence of UCOS2_inv. *)
Definition flag_pend_get_flags_rdy_word_view (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (caller : Assertion)
  (pointer value : Z) (residual : Assertion) : Prop :=
  (task_public_storage sg entry.(TskState) ** caller |--
    (tcb_field_address pointer TCBFlagsRdy) # UShort |-> value ** residual) /\
  ((tcb_field_address pointer TCBFlagsRdy) # UShort |-> value ** residual |--
    task_public_storage sg entry.(TskState) ** caller).

Definition flag_pend_get_flags_rdy_observation (sg : StableGlobVars)
  (caller : Assertion) (entry : UCOS2_Verify_State) (value : Z) : Prop :=
  task_reg_get_current_pointer sg entry <> 0 /\
  exists residual, flag_pend_get_flags_rdy_word_view sg entry caller
    (task_reg_get_current_pointer sg entry) value residual.

(** Admission is an explicit caller/rely obligation at every actual Save
    endpoint. No future return is required and no new CPU guarantee is used.
    The view restores the very same public storage and caller-owned frame. *)
Definition flag_pend_get_flags_rdy_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (caller : Assertion) : Prop :=
  forall entry, critical_region_interval critical sg invocation before entry ->
    UCOS2_state_inv sg entry ->
    exists value, flag_pend_get_flags_rdy_observation sg caller entry value.

Definition flag_pend_get_flags_rdy_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (caller : Assertion)
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (get (flag_pend_get_flags_rdy_observation sg caller))
      (fun snapshot => StateRelMonad.bind
        (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret snapshot))).

Definition flag_pend_get_flags_rdy_safe critical sg invocation before caller
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (flag_pend_get_flags_rdy_program critical sg invocation caller) X.

Lemma flag_pend_get_flags_rdy_program_result_iff :
  forall critical sg invocation caller before snapshot current,
  flag_pend_get_flags_rdy_program critical sg invocation caller before snapshot current <->
  exists entry, critical_region_interval critical sg invocation before entry /\
    flag_pend_get_flags_rdy_observation sg caller entry snapshot /\
    critical_region_interval critical sg invocation entry current.
Proof.
  intros critical sg invocation caller before snapshot current.
  unfold flag_pend_get_flags_rdy_program, StateRelMonad.bind, update, get, StateRelMonad.ret.
  split.
  - intros [u [entry [Hentry [observed [read_state [[Hobserved Hread]
      [v [returned [Hreturn [Hresult Hcurrent]]]]]]]]]].
    subst read_state; subst returned; subst snapshot.
    exists entry; split; [exact Hentry|split; assumption].
  - intros [entry [Hentry [Hobserved Hreturn]]].
    exists tt, entry; split; [exact Hentry|].
    exists snapshot, entry; split; [split; [exact Hobserved|reflexivity]|].
    exists tt, current; split; [exact Hreturn|split; reflexivity].
Qed.

Lemma flag_pend_get_flags_rdy_program_has_result :
  forall critical sg invocation caller before,
  UCOS2_state_inv sg before ->
  flag_pend_get_flags_rdy_admission critical sg invocation before caller ->
  exists value, flag_pend_get_flags_rdy_program critical sg invocation caller before value before.
Proof.
  intros critical sg invocation caller before Hvalid Hadmit.
  destruct (Hadmit before ltac:(constructor) Hvalid) as [value Hread].
  exists value; apply flag_pend_get_flags_rdy_program_result_iff.
  exists before; split; [constructor|split; [exact Hread|constructor]].
Qed.

Lemma flag_pend_get_flags_rdy_safe_return :
  forall critical sg invocation before caller current snapshot X,
  flag_pend_get_flags_rdy_program critical sg invocation caller before snapshot current ->
  flag_pend_get_flags_rdy_safe critical sg invocation before caller X ->
  safeExec (eq current) (StateRelMonad.ret snapshot) X.
Proof.
  intros critical sg invocation before caller current snapshot X Hprogram Hsafe.
  eapply (highstependret_derive
    (flag_pend_get_flags_rdy_program critical sg invocation caller)
    (eq before) snapshot (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Definition flag_pend_get_flags_rdy_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (caller : Assertion) (snapshot : Z)
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX current, coq_prop
    (flag_pend_get_flags_rdy_program critical sg invocation caller before snapshot current /\
     safeExec (eq current) (StateRelMonad.ret snapshot) X) &&
    (mutex_query_closed platform critical sg invocation origin mask current ** caller).

Lemma flag_pend_get_flags_rdy_restore_api_post :
  forall platform critical sg invocation origin mask saved before entry caller snapshot X,
  time_get_acquire_facts critical sg invocation mask saved before entry ->
  flag_pend_get_flags_rdy_observation sg caller entry snapshot ->
  flag_pend_get_flags_rdy_safe critical sg invocation before caller X ->
  time_get_restore_post platform critical sg invocation origin saved entry ** caller |--
    flag_pend_get_flags_rdy_api_post platform critical sg invocation origin mask
      before caller snapshot X.
Proof.
  intros platform critical sg invocation origin mask saved before entry caller snapshot X
    [Hentry [Hvalid [Hsaved Hmask]]] Hread Hsafe.
  unfold time_get_restore_post, flag_pend_get_flags_rdy_api_post; Intros current.
  assert (Hprogram : flag_pend_get_flags_rdy_program critical sg invocation caller
    before snapshot current).
  { apply flag_pend_get_flags_rdy_program_result_iff; exists entry; auto. }
  pose proof (flag_pend_get_flags_rdy_safe_return critical sg invocation before caller
    current snapshot X Hprogram Hsafe) as Hreturn.
  rewrite Hmask; Exists current; entailer!.
Qed.

Definition flag_pend_get_flags_rdy_read_frame (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (residual : Assertion) : Assertion :=
  residual **
  task_reg_get_sched_without_current sg entry.(TskState) entry.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg entry.

Lemma flag_pend_get_flags_rdy_read_split : forall sg entry caller value residual,
  flag_pend_get_flags_rdy_word_view sg entry caller
    (task_reg_get_current_pointer sg entry) value residual ->
  UCOS2_inv sg entry ** caller |--
    coq_prop (UCOS2_state_inv sg entry) &&
    (sg.(g_OSTCBCur) # Ptr |-> task_reg_get_current_pointer sg entry **
     (tcb_field_address (task_reg_get_current_pointer sg entry) TCBFlagsRdy)
       # UShort |-> value ** flag_pend_get_flags_rdy_read_frame sg entry residual).
Proof.
  intros sg entry caller value residual [Hsplit Hmerge].
  unfold flag_pend_get_flags_rdy_read_frame, UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched,
    task_reg_get_sched_without_current, task_reg_get_current_pointer,
    sched_raw_rep, sched_physical_rep in *.
  Intros; sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma flag_pend_get_flags_rdy_read_merge : forall sg entry caller value residual,
  UCOS2_state_inv sg entry ->
  flag_pend_get_flags_rdy_word_view sg entry caller
    (task_reg_get_current_pointer sg entry) value residual ->
  sg.(g_OSTCBCur) # Ptr |-> task_reg_get_current_pointer sg entry **
  (tcb_field_address (task_reg_get_current_pointer sg entry) TCBFlagsRdy)
    # UShort |-> value ** flag_pend_get_flags_rdy_read_frame sg entry residual |--
  UCOS2_inv sg entry ** caller.
Proof.
  intros sg entry caller value residual Hvalid [Hsplit Hmerge].
  unfold flag_pend_get_flags_rdy_read_frame, UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched,
    task_reg_get_sched_without_current, task_reg_get_current_pointer,
    sched_raw_rep, sched_physical_rep in *.
  Intros; sep_apply_l_atomic Hmerge; entailer!.
Qed.

(** Live, initialized-free and private read sources all use the real UShort
    representation. The view is not restricted to the live-task map. *)
Lemma flag_pend_get_flags_rdy_live_word_view : forall sg entry caller tid t,
  entry.(TskState).(inUsedTaskStates) tid = Some t ->
  flag_pend_get_flags_rdy_word_view sg entry caller (task_slot_addr sg tid)
    t.(tcbFlagsRdy)
    (task_public_storage_without_field sg entry.(TskState) tid t
      (TCBCommonField TCBFlagsRdy) ** caller).
Proof.
  intros sg entry caller tid t Htask.
  pose proof (task_public_storage_split_field sg entry.(TskState) tid t
    (TCBCommonField TCBFlagsRdy) Htask
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)) as Hsplit.
  pose proof (task_public_storage_merge_field sg entry.(TskState) tid t
    (TCBCommonField TCBFlagsRdy) Htask
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image] in Hsplit, Hmerge.
  split; Intros; [sep_apply_l_atomic Hsplit|sep_apply_l_atomic Hmerge]; entailer!.
Qed.

Lemma flag_pend_get_flags_rdy_private_word_view : forall sg entry pointer value extra,
  flag_pend_get_flags_rdy_word_view sg entry
    ((tcb_field_address pointer TCBFlagsRdy) # UShort |-> value ** extra)
    pointer value (task_public_storage sg entry.(TskState) ** extra).
Proof. intros; split; entailer!. Qed.

(** A concrete normal-task source: the actual current slot is live. Pool
    membership and the pinned positive table base establish non-NULL;
    the UShort field is then supplied by the real live TCB representation. *)
Lemma flag_pend_get_flags_rdy_live_observation : forall sg entry caller tid t,
  UCOS2_state_inv sg entry ->
  entry.(SchedState).(curTaskID) = Some tid ->
  entry.(TskState).(inUsedTaskStates) tid = Some t ->
  flag_pend_get_flags_rdy_observation sg caller entry t.(tcbFlagsRdy).
Proof.
  intros sg entry caller tid t [Hprofile [Htasks Hrest]] Hcurrent Htask.
  assert (Hslot : task_slot_in_range sg tid).
  { destruct Htasks as [[Hpartition _] _].
    apply (proj2 (Hpartition tid)); left; eauto. }
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) (proj1 Hprofile)
    ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
  unfold flag_pend_get_flags_rdy_observation, task_reg_get_current_pointer.
  rewrite Hcurrent; cbn [encode_task_link]; split.
  - unfold task_slot_addr, tcb_configured_size, tcb_layout_size.
    unfold task_slot_in_range in Hslot.
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled),
      sg.(osKernelConfig).(cfgTaskProfile); lia.
  - eexists; apply flag_pend_get_flags_rdy_live_word_view; exact Htask.
Qed.

(** The admission proof is an induction over every registered actual Save
    interval, not merely its reflexive member. [source] is a caller-stage
    predicate with an explicit resource producer and client preservation. *)
Lemma flag_pend_get_flags_rdy_admission_from_source :
  forall critical sg invocation before caller (source : UCOS2_Verify_State -> Prop),
  UCOS2_state_inv sg before -> source before ->
  (forall entry, UCOS2_state_inv sg entry -> source entry ->
    exists value, flag_pend_get_flags_rdy_observation sg caller entry value) ->
  (forall action, critical_region_clients critical action ->
    forall a b, UCOS2_state_inv sg a -> kernel_client_step action sg a b ->
      source a -> source b) ->
  flag_pend_get_flags_rdy_admission critical sg invocation before caller.
Proof.
  intros critical sg invocation before caller source Hvalid Hinitial Hread Hclients
    entry Hinterval Hentry.
  apply Hread; [exact Hentry|].
  pose proof (critical_region_interval_raw_trace critical sg invocation before entry Hinterval)
    as Htrace.
  clear Hinterval Hentry.
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

Lemma flag_pend_get_flags_rdy_creation_client_preserves_current :
  forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID).
Proof.
  intros action sg before after [_ [_ ->]]; destruct action; reflexivity.
Qed.

(** One checked, nonempty client-family instance using the existing Task
    creation protocol. It does NOT assert that every kernel client preserves
    a live/nonempty current slot, or discharge the application's Task ONLY
    execution-context binding. Other callers prove their own source/rely
    instance (including the free/private views below) without changing the
    public admission or strengthening the CPU contract. *)
Lemma flag_pend_get_flags_rdy_admission_creation_clients :
  forall critical sg invocation before caller,
  UCOS2_state_inv sg before ->
  (exists tid, before.(SchedState).(curTaskID) = Some tid) ->
  task_reg_get_live_current before ->
  (forall client, critical_region_clients critical client -> task_creation_client_family client) ->
  flag_pend_get_flags_rdy_admission critical sg invocation before caller.
Proof.
  intros critical sg invocation before caller Hvalid Hcurrent Hlive Hclients.
  eapply flag_pend_get_flags_rdy_admission_from_source with
    (source := fun s => (exists tid, s.(SchedState).(curTaskID) = Some tid) /\
      task_reg_get_live_current s).
  - exact Hvalid.
  - split; assumption.
  - intros entry Hentry [[tid Htid] Hsource].
    destruct (Hsource tid Htid) as [t Htask].
    exists t.(tcbFlagsRdy); eapply flag_pend_get_flags_rdy_live_observation; eassumption.
  - intros client Hin a b Ha Hstep [[tid Htid] Hsource].
    destruct (Hclients client Hin) as [action ->]; split.
    + exists tid.
      rewrite (flag_pend_get_flags_rdy_creation_client_preserves_current
        action sg a b Hstep); exact Htid.
    + eapply task_reg_get_creation_client_preserves_live_current; eassumption.
Qed.

Definition flag_pend_get_flags_rdy_free_residual (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (caller : Assertion)
  (prefix suffix : list TaskID) (tid : TaskID) (image : TCBLayoutImage) : Assertion :=
  tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg tid) image
    (TCBCommonField TCBFlagsRdy) **
  task_free_storage_rep sg entry.(TskState).(taskLifecycle).(taskFreeStorage) prefix **
  task_free_storage_rep sg entry.(TskState).(taskLifecycle).(taskFreeStorage) suffix **
  store_used_task_map sg entry.(TskState).(inUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error entry.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg entry.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> entry.(TskState).(taskCount) **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** task_reg_allocator_rep sg entry.(TskState) ** caller.

Lemma flag_pend_get_flags_rdy_free_word_view : forall sg entry caller prefix tid suffix image value,
  entry.(TskState).(unUsedTaskStates) = prefix ++ tid :: suffix ->
  entry.(TskState).(taskLifecycle).(taskFreeStorage) tid = Some image ->
  image (TCBCommonField TCBFlagsRdy) = Some value ->
  flag_pend_get_flags_rdy_word_view sg entry caller (task_slot_addr sg tid) value
    (flag_pend_get_flags_rdy_free_residual sg entry caller prefix suffix tid image).
Proof.
  intros sg entry caller prefix tid suffix image value Hids Himage Hflags.
  pose proof (tcb_configured_storage_split_field
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image (TCBCommonField TCBFlagsRdy)
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)) as Hsplit.
  pose proof (tcb_configured_storage_merge_field
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image (TCBCommonField TCBFlagsRdy)
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)) as Hmerge.
  rewrite Hflags in Hsplit, Hmerge; cbn [tcb_layout_cell tcb_cell] in Hsplit, Hmerge.
  unfold flag_pend_get_flags_rdy_word_view, flag_pend_get_flags_rdy_free_residual,
    task_public_storage.
  rewrite Hids, (task_reg_get_free_storage_focus sg
    entry.(TskState).(taskLifecycle).(taskFreeStorage) prefix tid suffix image Himage).
  unfold task_slot_storage_rep.
  split; Intros; [sep_apply_l_atomic Hsplit|sep_apply_l_atomic Hmerge]; entailer!.
Qed.
