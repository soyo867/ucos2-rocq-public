Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.queue_core.
Require Export Ucos2Verify.lib.mbox Ucos2Verify.lib.mutex_query_spec.
Require Export Ucos2Verify.lib.ucos2_verify_inv.

Import ListNotations UCOS2_C_Rules Monad.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The selected original headers use the 20-byte unnamed OS_EVENT layout.
    These equalities bind the parser's actual field-address vocabulary to
    the registered ARM32 layout; they do not restrict runtime handles. *)
Definition mbox_accept_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgEventNames) = false /\
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false /\
  sg.(osKernelConfig).(cfgTaskProfile) = false /\
  (forall p, (&(p # "os_event" ->ₛ "OSEventType")) = p + OSEventType_off) /\
  (forall p, (&(p # "os_event" ->ₛ "OSEventPtr")) = p + OSEventPtr_off).

(** Public readable ECB storage includes both used and free slots. A private
    unpublished allocation is not an application's public handle. *)
Definition mbox_accept_public_slot (s : UCOS2_Verify_State) (eid : EventID) : Prop :=
  (exists e, s.(EventState).(inUsedEventStates) eid = Some e) \/
  (exists image, s.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image).

Definition mbox_accept_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  (before : UCOS2_Verify_State) (eid : EventID) : Prop :=
  pe = 0 \/
  (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
   mbox_accept_public_slot before eid /\
   (event_slot_type_value before.(EventState) eid = 1 ->
     mutex_query_handle_protocol critical sg invocation eid)).

Definition mbox_accept_type_frame (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  match s.(EventState).(inUsedEventStates) eid with
  | Some e => mutex_query_type_frame sg s eid e
  | None => EX image,
      coq_prop (s.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image /\
        image EventTypeField = Some 0) &&
      (event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
         (event_addr sg eid) image EventTypeField **
       store_map (used_event_rep sg s.(TskState)) s.(EventState).(inUsedEventStates) **
       event_free_storage_without_eid sg s.(EventState) eid **
       event_free_root_rep sg s.(EventState) **
       UCOS2_raw_rep_missing_module sg s EventModule)
  end.

Definition mbox_accept_update (s : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) (m : MboxFields) : UCOS2_Verify_State :=
  replace_EventS
    (update_event_field_raw s.(EventState) eid (mbox_set_message e (snd (mbox_take m)))) s.

(** The protected checkpoint records exactly the old message and NULL write.
    Both the already-empty and occupied mailbox execute the same operation. *)
Definition mbox_accept_taken (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  (before entry checkpoint : UCOS2_Verify_State) (message : addr) : Prop :=
  pe <> 0 /\ exists eid observed current m,
    pe = event_addr sg eid /\ valid_event_id sg eid /\
    mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_MBOX /\
    critical_region_interval critical sg invocation before entry /\
    mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_MBOX /\
    current.(eventGeneration) = observed.(eventGeneration) /\
    current.(mboxFields) = Some m /\
    message = fst (mbox_take m) /\ checkpoint = mbox_accept_update entry eid current m.

(** Source-ordered whole API: NULL and wrong Type return directly; only a
    MBOX executes acquisition, take, Restore and return of the saved pointer.
    The Restore interval may change the mailbox again. No application bytes
    are owned by this pointer-valued observation. *)
Definition mbox_accept_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  : program UCOS2_Verify_State addr :=
  fun before message after =>
    if Z.eqb pe 0 then message = 0 /\ after = before
    else
      (exists eid, pe = event_addr sg eid /\ valid_event_id sg eid /\
        event_slot_type_value before.(EventState) eid <> 1 /\
        message = 0 /\ after = before) \/
      (exists entry checkpoint,
        mbox_accept_taken critical sg invocation pe before entry checkpoint message /\
        critical_region_interval critical sg invocation checkpoint after).

Definition mbox_accept_safe critical sg invocation pe before X : Prop :=
  safeExec (fun state => state = before)
    (mbox_accept_program critical sg invocation pe) X.

Definition mbox_accept_return_safe after message
  (X : addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = after) (ret message) X.

Definition mbox_accept_post critical sg invocation pe before message after : Prop :=
  mbox_accept_program critical sg invocation pe before message after.

Lemma mbox_accept_safe_return : forall critical sg invocation pe before message after X,
  mbox_accept_safe critical sg invocation pe before X ->
  mbox_accept_post critical sg invocation pe before message after ->
  mbox_accept_return_safe after message X.
Proof.
  intros critical sg invocation pe before message after X Hsafe Hstep.
  unfold mbox_accept_safe in Hsafe; unfold mbox_accept_return_safe.
  eapply highstependret_derive with
    (c1 := mbox_accept_program critical sg invocation pe)
    (P := fun state => state = before)
    (P' := fun (_ : addr) state => state = after).
  - intros state ->; exists after; split; [exact Hstep|reflexivity].
  - exact Hsafe.
Qed.

Lemma mbox_accept_null_return : forall critical sg invocation before,
  mbox_accept_post critical sg invocation 0 before 0 before.
Proof. intros; unfold mbox_accept_post, mbox_accept_program; simpl; split; reflexivity. Qed.

Lemma mbox_accept_wrong_type_return : forall critical sg invocation pe before eid,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  event_slot_type_value before.(EventState) eid <> 1 ->
  mbox_accept_post critical sg invocation pe before 0 before.
Proof.
  intros critical sg invocation pe before eid Hpe Haddr Hid Htype.
  unfold mbox_accept_post, mbox_accept_program.
  destruct (Z.eqb pe 0) eqn:H; [apply Z.eqb_eq in H; contradiction|].
  left; exists eid; auto.
Qed.

Lemma mbox_accept_restored_return : forall critical sg invocation pe before entry checkpoint message after,
  mbox_accept_taken critical sg invocation pe before entry checkpoint message ->
  critical_region_interval critical sg invocation checkpoint after ->
  mbox_accept_post critical sg invocation pe before message after.
Proof.
  intros critical sg invocation pe before entry checkpoint message after Htake Hrestore.
  pose proof (proj1 Htake) as Hpe; unfold mbox_accept_post, mbox_accept_program.
  destruct (Z.eqb pe 0) eqn:H; [apply Z.eqb_eq in H; contradiction|].
  right; exists entry, checkpoint; auto.
Qed.

Lemma mbox_accept_encoded_type : forall e,
  encode_event_type e.(eventType) = 1 -> e.(eventType) = OS_EVENT_TYPE_MBOX.
Proof. intros e H; destruct e.(eventType); simpl in H; try lia; reflexivity. Qed.

Lemma mbox_accept_current_payload : forall sg s eid e,
  UCOS2_state_inv sg s -> mutex_query_lookup s eid e ->
  e.(eventType) = OS_EVENT_TYPE_MBOX -> exists m, e.(mboxFields) = Some m.
Proof.
  intros sg s eid e [_ [_ [_ [Hevents _]]]] Hget Htype.
  destruct Hevents as [_ [_ [_ [Hfields _]]]].
  specialize (Hfields eid e Hget); unfold event_fields_consistency in Hfields.
  rewrite Htype in Hfields.
  destruct e.(mboxFields) as [m|] eqn:Hm; [eauto|tauto].
Qed.

Lemma mbox_accept_update_preserves_validity : forall sg s eid e m,
  UCOS2_state_inv sg s -> mutex_query_lookup s eid e ->
  e.(eventType) = OS_EVENT_TYPE_MBOX -> UCOS2_state_inv sg (mbox_accept_update s eid e m).
Proof.
  intros sg s eid e m Hvalid Hget Htype.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  unfold mbox_accept_update; eapply UCOS2_event_payload_update_preserves_validity;
    try eassumption; try reflexivity.
  apply mbox_take_preserves_event_in_range with (e := e); assumption.
Qed.

(** No successful branch is hidden behind a post-invariant guard. From every
    admitted input the abstract program has a normal endpoint, using the
    reflexive environment intervals. This does not claim platform liveness. *)
Lemma mbox_accept_program_has_result : forall critical sg invocation pe before eid,
  UCOS2_state_inv sg before ->
  mbox_accept_call_input critical sg invocation pe before eid ->
  exists message after, mbox_accept_program critical sg invocation pe before message after.
Proof.
  intros critical sg invocation pe before eid Hvalid Hinput.
  destruct Hinput as [->|[Hpe [Haddr [Hid [Hslot Hprotocol]]]]].
  - exists 0, before; unfold mbox_accept_program; simpl; auto.
  - destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 1) as [Htype|Htype].
    + unfold event_slot_type_value in Htype.
      destruct (inUsedEventStates (EventState before) eid) as [e|] eqn:He; [|discriminate].
      apply mbox_accept_encoded_type in Htype.
      destruct (mbox_accept_current_payload sg before eid e Hvalid He Htype) as [m Hm].
      exists (mbox_message_ptr m), (mbox_accept_update before eid e m).
      apply mbox_accept_restored_return with (entry := before)
        (checkpoint := mbox_accept_update before eid e m).
      * split; [exact Hpe|]; exists eid, e, e, m.
        split; [exact Haddr|]. split; [exact Hid|].
        split; [exact He|]. split; [exact Htype|].
        split; [unfold critical_region_interval, kernel_resumption_trace; constructor|].
        repeat split; try assumption; try reflexivity.
      * unfold critical_region_interval, kernel_resumption_trace; constructor.
    + exists 0, before; apply mbox_accept_wrong_type_return with (eid := eid); assumption.
Qed.

Lemma mbox_accept_type_split_full : forall sg s eid,
  mbox_accept_public_slot s eid ->
  UCOS2_inv sg s |-- coq_prop (UCOS2_state_inv sg s) &&
    ((event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value s.(EventState) eid **
     mbox_accept_type_frame sg s eid).
Proof.
  intros sg s eid Hpublic.
  unfold mbox_accept_type_frame, event_slot_type_value.
  destruct (inUsedEventStates (EventState s) eid) as [e|] eqn:Hslot.
  - apply mutex_query_type_split_full; exact Hslot.
  - destruct Hpublic as [[e He]|[image Himage]]; [congruence|].
    rewrite (UCOS2_inv_split_module sg s EventModule); Intros.
    match goal with Hvalid : UCOS2_state_inv sg s |- _ =>
      pose proof Hvalid as [_ [_ [_ [Hevents _]]]] end.
    destruct Hevents as [_ [Hfree _]].
    assert (Htype : image EventTypeField = Some 0) by (apply (proj2 (proj2 Hfree) eid image Himage)).
    cbn [UCOS2_module_rep]; unfold event_raw_rep.
    sep_apply_l_atomic (event_free_storage_split_eid sg s.(EventState) eid image Himage).
    sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image EventTypeField ltac:(simpl; tauto)).
    rewrite Htype; cbn [event_cell event_field_offset].
    Exists image; unfold event_addr, OSEventType_off; entailer!.
Qed.

Lemma mbox_accept_type_merge_full : forall sg s eid,
  UCOS2_state_inv sg s ->
  (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value s.(EventState) eid **
    mbox_accept_type_frame sg s eid |-- UCOS2_inv sg s.
Proof.
  intros sg s eid Hvalid.
  unfold mbox_accept_type_frame, event_slot_type_value.
  destruct (inUsedEventStates (EventState s) eid) as [e|] eqn:Hslot.
  - apply mutex_query_type_merge_full; assumption.
  - Intros image.
    match goal with Hfacts : _ /\ _ |- _ => destruct Hfacts as [Himage Htype] end.
    pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image EventTypeField ltac:(simpl; tauto)) as Hmerge.
    rewrite Htype in Hmerge; cbn [event_cell event_field_offset] in Hmerge.
    unfold event_addr, OSEventType_off.
    sep_apply_l_atomic Hmerge.
    sep_apply_l_atomic (event_free_storage_merge_eid sg s.(EventState) eid image Himage).
    rewrite (UCOS2_inv_split_module sg s EventModule).
    cbn [UCOS2_module_rep]; unfold event_raw_rep; entailer!.
Qed.

Definition mbox_accept_success_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  (before : UCOS2_Verify_State) (eid : EventID) : Prop :=
  pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
  UCOS2_state_inv sg before /\
  mutex_query_handle_protocol critical sg invocation eid /\
  exists observed, mutex_query_lookup before eid observed /\
    observed.(eventType) = OS_EVENT_TYPE_MBOX.

Definition mbox_accept_acquired (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (eid : EventID)
  (observed current : OSEventAbstractState) (m : MboxFields) : Prop :=
  pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_MBOX /\
  critical_region_interval critical sg invocation before entry /\
  mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_MBOX /\
  current.(eventGeneration) = observed.(eventGeneration) /\ current.(mboxFields) = Some m.

Definition mbox_accept_message_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (pe : addr) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (eid : EventID)
  (observed current : OSEventAbstractState) (m : MboxFields) : Assertion :=
  coq_prop (mbox_accept_acquired critical sg invocation pe mask saved
    before entry eid observed current m) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   mbox_rep_no_message sg entry.(TskState) eid current **
   event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
   queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry).

(** Generic C modular Restore resource interface. The inside token remains
    indexed by the real acquisition; the restored heap starts at the actual
    written checkpoint. It supplies no no-interference or eventual-return axiom. *)
Definition mbox_accept_cpu_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask saved : Z)
  (entry checkpoint : UCOS2_Verify_State) : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\ UCOS2_state_inv sg checkpoint) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   UCOS2_inv sg checkpoint).

Lemma mbox_accept_message_merge_updated : forall sg entry eid current m,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_MBOX ->
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> 0 **
    mbox_rep_no_message sg entry.(TskState) eid current **
    event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
    queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry |--
  UCOS2_inv sg (mbox_accept_update entry eid current m).
Proof.
  intros sg entry eid current m Hvalid Hget Htype.
  pose proof (mbox_accept_update_preserves_validity sg entry eid current m Hvalid Hget Htype) as Hpost.
  pose proof (mbox_rep_merge_updated_message sg entry.(TskState) eid current
    (snd (mbox_take m)) Htype) as Hmerge.
  change (mbox_message_ptr (snd (mbox_take m))) with 0 in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold mbox_accept_update in *.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_event sg entry eid current
    (mbox_set_message current (snd (mbox_take m))) Hpost Hget eq_refl eq_refl).
  entailer!.
Qed.
