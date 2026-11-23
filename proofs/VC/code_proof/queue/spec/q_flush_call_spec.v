Require Export Ucos2Verify.VC.code.queue.spec.q_flush_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Coq.Lists.List Coq.Strings.String Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib MapLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** This is the source-call layer, not an equivalence claim for the older
    valid-ID-only input. A public live/free ECB supplies the actual type cell;
    a successful typed handle needs the established lifetime protocol.
    The protocol preserves identity, not queue contents. OSQFlush_sem remains
    unchanged as the operation performed on the freshly acquired entry. *)
Definition q_flush_public_slot := sem_query_public_slot.
Definition q_flush_type_frame := sem_query_type_frame.

Definition q_flush_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/
  (pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
   q_flush_public_slot before eid observed /\
   (event_slot_type_value before.(EventState) eid = 2 ->
    mutex_query_handle_protocol critical sg invocation eid)).

Definition q_flush_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  mutex_query_lookup before eid observed /\ mutex_query_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_Q /\ current.(eventType) = OS_EVENT_TYPE_Q /\
  current.(eventGeneration) = observed.(eventGeneration).

(** Source-call inference uses these exact resources, with pure facts on
    the same heap. Neither wrapper allocates a separate coq_prop heap tail. *)
Definition q_flush_save_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (eid : EventID) (observed : OSEventAbstractState) : Assertion :=
  coq_prop (mutex_query_handle_protocol critical sg invocation eid /\
    mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q) &&
  (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg before).

Definition q_flush_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed current : OSEventAbstractState) : Assertion :=
  coq_prop (q_flush_acquire_facts critical sg invocation eid mask saved before entry observed current) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   UCOS2_inv sg (q_flush_state entry eid current)).

Lemma q_flush_public_slot_is_queue : forall state eid observed,
  q_flush_public_slot state eid observed ->
  event_slot_type_value state.(EventState) eid = 2 ->
  mutex_query_lookup state eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q.
Proof.
  intros state eid observed [Hused|[Hnone Hfree]] Htype;
    unfold event_slot_type_value in Htype.
  - unfold mutex_query_lookup in Hused; rewrite Hused in Htype.
    split; [exact Hused|].
    destruct observed.(eventType); simpl in Htype; try lia; reflexivity.
  - rewrite Hnone in Htype; discriminate.
Qed.

Lemma q_flush_lookup_valid_id : forall sg state eid current,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid current -> valid_event_id sg eid.
Proof.
  intros sg state eid current Hvalid Hlookup.
  pose proof Hvalid as [_ [_ [_ [Hevent _]]]].
  destruct Hevent as [[[_ [_ Hpartition]] Hdisjoint] _].
  assert (Hprivate : state.(EventState).(eventLifecycle).(eventPrivate) eid = None).
  { destruct (state.(EventState).(eventLifecycle).(eventPrivate) eid) as [a|] eqn:E;
      [pose proof (Hdisjoint eid a E); unfold mutex_query_lookup in Hlookup; congruence|reflexivity]. }
  assert (Hallocated : exists v, event_allocated_slots state.(EventState) eid = Some v).
  { exists (inl current); unfold event_allocated_slots; rewrite Hprivate, Hlookup; reflexivity. }
  exact (proj1 (proj1 (Hpartition eid) Hallocated)).
Qed.

Lemma q_flush_type_layout : forall sg eid,
  q_flush_profile sg -> valid_event_id sg eid ->
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventType")) = event_addr sg eid + OSEventType_off.
Proof. intros sg eid [_ [Hlayout _]] Hid; exact (proj1 (proj1 (Hlayout eid Hid))). Qed.

Lemma q_flush_type_merge : forall sg state eid,
  q_flush_profile sg -> valid_event_id sg eid -> UCOS2_state_inv sg state ->
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventType")) # UChar |->
    event_slot_type_value state.(EventState) eid ** q_flush_type_frame sg state eid |-- UCOS2_inv sg state.
Proof.
  intros sg state eid Hprofile Hid Hvalid; rewrite (q_flush_type_layout sg eid Hprofile Hid).
  apply sem_query_type_merge_full; exact Hvalid.
Qed.

Lemma q_flush_save_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed,
  mutex_query_handle_protocol critical sg invocation eid ->
  UCOS2_state_inv sg before -> mutex_query_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_Q ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_raw_rep sg entry |--
  EX current, coq_prop (q_flush_acquire_facts critical sg invocation eid mask saved
    before entry observed current) &&
    (critical_region_masked platform critical sg invocation origin saved entry **
     UCOS2_inv sg entry).
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed
    Hprotocol Hvalid Hlookup Htype Hinterval Hsaved.
  destruct (mutex_query_handle_interval_preserves_identity critical sg invocation eid
    before entry observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgeneration HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : q_flush_acquire_facts critical sg invocation eid mask saved
    before entry observed current).
  { unfold q_flush_acquire_facts.
    split; [exact Hinterval|]; split; [exact Hentry|]; split; [exact Hsaved|].
    split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
    split; [congruence|exact Hgeneration]. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Lemma q_flush_restore_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed current,
  q_flush_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation (q_flush_state entry eid current) |--
  mutex_query_closed platform critical sg invocation origin mask (q_flush_state entry eid current).
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed current
    [Hinterval [Hentry [[Hsaved Hmask] [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  pose proof (q_flush_state_validity sg entry eid current Hentry Hlookup Hcurrent) as Hafter.
  rewrite Hmask; unfold mutex_query_closed; entailer!.
Qed.

Definition q_flush_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  : program UCOS2_Verify_State Z :=
  fun before ret after =>
    (pevent = 0 /\ ret = 4 /\ after = before) \/
    (pevent <> 0 /\ exists eid observed,
      pevent = event_addr sg eid /\ valid_event_id sg eid /\
      q_flush_public_slot before eid observed /\
      ((event_slot_type_value before.(EventState) eid <> 2 /\ ret = 1 /\ after = before) \/
       (mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q /\
        exists entry current,
          critical_region_interval critical sg invocation before entry /\
          mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_Q /\
          current.(eventGeneration) = observed.(eventGeneration) /\
          OSQFlush_sem pevent eid entry ret after))).

Lemma q_flush_call_null : forall critical sg invocation before,
  q_flush_call_program critical sg invocation 0 before 4 before.
Proof. intros; left; auto. Qed.

Lemma q_flush_call_wrong_type : forall critical sg invocation pevent before eid observed,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  q_flush_public_slot before eid observed -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_flush_call_program critical sg invocation pevent before 1 before.
Proof.
  intros critical sg invocation pevent before eid observed Hpe Haddr Hid Hslot Htype.
  right; split; [exact Hpe|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hslot|].
  left; auto.
Qed.

Lemma q_flush_queue_exists : forall sg state eid current,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid current ->
  current.(eventType) = OS_EVENT_TYPE_Q -> exists q, current.(queueFields) = Some q.
Proof.
  intros sg state eid current Hvalid Hlookup Htype.
  pose proof Hvalid as [_ [_ [_ [Hevent _]]]].
  destruct Hevent as [_ [_ [_ [Hfields _]]]].
  specialize (Hfields eid current Hlookup).
  unfold event_fields_consistency in Hfields; rewrite Htype in Hfields.
  destruct current.(queueFields) as [q|]; [exists q; reflexivity|tauto].
Qed.

Lemma q_flush_call_success :
  forall critical sg invocation pevent before eid observed mask saved entry current,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  q_flush_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  q_flush_call_program critical sg invocation pevent before 0 (q_flush_state entry eid current).
Proof.
  intros critical sg invocation pevent before eid observed mask saved entry current
    Hpe Haddr Hid [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  destruct (q_flush_queue_exists sg entry eid current Hvalid Hlookup Hcurrent) as [q Hq].
  right; split; [exact Hpe|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [left; exact Hbefore|].
  right; split; [exact Hbefore|]; split; [exact Htype|]; exists entry, current.
  split; [exact Hinterval|]; split; [exact Hlookup|]; split; [exact Hcurrent|].
  split; [exact Hgen|].
  unfold OSQFlush_sem; rewrite (proj2 (Z.eqb_neq pevent 0) Hpe), Hlookup, Hcurrent, Hq.
  repeat split; discriminate || reflexivity.
Qed.

Lemma q_flush_call_safe_endpoint : forall critical sg invocation pevent before ret after X,
  q_flush_call_program critical sg invocation pevent before ret after ->
  safeExec (LastSeen before) (atomic_cmd (q_flush_call_program critical sg invocation pevent)) X ->
  safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z ret) X.
Proof.
  intros critical sg invocation pevent before ret after X Hsem Hsafe.
  eapply (highstependret_derive
    (atomic_cmd (q_flush_call_program critical sg invocation pevent)) (LastSeen before) ret
    (fun _ => LastSeen after)); [|exact Hsafe].
  unfold hs_eval, atomic_cmd, LastSeen.
  intros B HB; exists (RTrans_Abs after); split.
  - exists before, after; split; [apply HB; exact I|].
    split; [exact Hsem|]; intro s; split; trivial.
  - intro s; split; trivial.
Qed.

(** The pointer cell is read and returned before splitting the Queue map.
    This frame includes the real Event and Queue residuals plus every other
    global module. It is never a logical label that manufactures memory. *)
Definition q_flush_pointer_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) current) EventPtrField **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Lemma q_flush_pointer_split : forall sg state eid current q,
  mutex_query_lookup state eid current -> current.(eventType) = OS_EVENT_TYPE_Q ->
  current.(queueFields) = Some q ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
      q_flush_pointer_frame sg state eid current).
Proof.
  intros sg state eid current q Hlookup Htype Hq.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState)
    eid current Hlookup).
  unfold used_event_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) current) EventPtrField
    ltac:(simpl; tauto)).
  cbn [event_cell event_field_offset event_image].
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value; rewrite Htype, Hq.
  unfold q_flush_pointer_frame, OSEventPtr_off; entailer!.
Qed.

Lemma q_flush_pointer_merge : forall sg state eid current q,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid current ->
  current.(eventType) = OS_EVENT_TYPE_Q -> current.(queueFields) = Some q ->
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> qcb_addr sg q.(qID) **
    q_flush_pointer_frame sg state eid current |-- UCOS2_inv sg state.
Proof.
  intros sg state eid current q Hvalid Hlookup Htype Hq.
  assert (Hptr : event_image sg state.(TskState) current EventPtrField =
    Some (qcb_addr sg q.(qID))).
  { unfold event_image, encode_event_ptr_value, verification_slice_encode_event_ptr_value.
    rewrite Htype, Hq; reflexivity. }
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) current) EventPtrField
    ltac:(simpl; tauto)) as Hmerge.
  rewrite Hptr in Hmerge; cbn [event_cell event_field_offset] in Hmerge.
  unfold q_flush_pointer_frame, OSEventPtr_off; sepcon_right_assoc.
  sep_apply_l_atomic Hmerge; fold (used_event_rep sg state.(TskState) eid current).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg state.(TskState) state.(EventState)
    eid current Hlookup).
  rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

Definition q_flush_pointer_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed current : OSEventAbstractState) (q : QueueFields) : Assertion :=
  coq_prop (q_flush_acquire_facts critical sg invocation eid mask saved before entry observed current /\
    current.(queueFields) = Some q /\ q_flush_profile sg /\ valid_event_id sg eid) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   q_flush_pointer_frame sg entry eid current).

Definition q_flush_store_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed current : OSEventAbstractState) (q : QueueFields)
  (free : list QueueID) (slots : list (option addr)) (base : addr) : Assertion :=
  coq_prop (q_flush_acquire_facts critical sg invocation eid mask saved before entry observed current /\
    q_flush_profile sg /\ valid_event_id sg eid /\ base = qcb_addr sg q.(qID)) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   q_flush_source_frame sg entry eid current q free slots (q_flush_readonly_storage sg q slots)).

Lemma q_flush_pointer_layout : forall sg eid,
  q_flush_profile sg -> valid_event_id sg eid ->
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventPtr")) = event_addr sg eid + OSEventPtr_off.
Proof.
  intros sg eid [_ [Hlayout _]] Hid.
  exact (proj1 (proj2 (proj1 (Hlayout eid Hid)))).
Qed.

Lemma q_flush_acquired_pointer_split :
  forall platform critical sg invocation origin mask saved before entry eid observed current,
  q_flush_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  q_flush_profile sg -> valid_event_id sg eid ->
  critical_region_masked platform critical sg invocation origin saved entry ** UCOS2_inv sg entry |--
  EX q, (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> qcb_addr sg q.(qID) **
    q_flush_pointer_context platform critical sg invocation origin mask saved before entry eid observed current q.
Proof.
  intros platform critical sg invocation origin mask saved before entry eid observed current
    Hfacts Hprofile Hid.
  pose proof Hfacts as [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  destruct (q_flush_queue_exists sg entry eid current Hvalid Hlookup Hcurrent) as [q Hq].
  sep_apply_l_atomic (q_flush_pointer_split sg entry eid current q Hlookup Hcurrent Hq).
  rewrite (q_flush_pointer_layout sg eid Hprofile Hid).
  Exists q; unfold q_flush_pointer_context; entailer!.
Qed.

Lemma q_flush_pointer_to_stores :
  forall platform critical sg invocation origin mask saved before entry eid observed current q,
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> qcb_addr sg q.(qID) **
    q_flush_pointer_context platform critical sg invocation origin mask saved before entry eid observed current q |--
  EX free, EX slots,
    q_flush_source_fields sg q (queue_in_addr q) (queue_out_addr q) (queue_entries q) **
    q_flush_store_context platform critical sg invocation origin mask saved before entry eid observed current q free slots
      (qcb_addr sg q.(qID)).
Proof.
  intros; unfold q_flush_pointer_context; Intros.
  destruct H as [Hfacts [Hq [Hprofile Hid]]].
  pose proof Hfacts as [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  rewrite (q_flush_pointer_layout sg eid Hprofile Hid).
  sep_apply_l_atomic (q_flush_pointer_merge sg entry eid current q Hvalid Hlookup Hcurrent Hq).
  sep_apply_l_atomic (q_flush_queue_split sg entry eid current q Hlookup Hcurrent Hq).
  Intros free slots.
  rewrite (q_flush_owned_stage_source_equiv sg entry eid current q free slots
    (queue_in_addr q) (queue_out_addr q) (queue_entries q) (q_flush_readonly_storage sg q slots) Hprofile).
  Exists free slots; unfold q_flush_store_context; entailer!.
Qed.

Lemma q_flush_stores_merge :
  forall platform critical sg invocation origin mask saved before entry eid observed current q free slots,
  q_flush_source_fields sg q q.(qStart) q.(qStart) 0 **
    q_flush_store_context platform critical sg invocation origin mask saved before entry eid observed current q free slots
      (qcb_addr sg q.(qID)) |--
  coq_prop (q_flush_acquire_facts critical sg invocation eid mask saved before entry observed current) &&
    (critical_region_masked platform critical sg invocation origin saved entry **
      UCOS2_inv sg (q_flush_state entry eid current)).
Proof.
  intros; unfold q_flush_store_context; Intros.
  destruct H as [Hfacts [Hprofile [Hid Hbase]]].
  sep_apply_l_atomic (q_flush_source_fields_merge_global sg entry eid current q free slots
    (q_flush_readonly_storage sg q slots) Hprofile); entailer!.
Qed.

Definition q_flush_call_post (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pevent : addr) (before : UCOS2_Verify_State) (ret : Z)
  (after : UCOS2_Verify_State) : Prop :=
  q_flush_call_program critical sg invocation pevent before ret after.

(** The protected operation above ends before Restore.  The public API keeps
    that exact checkpoint and the registered interval to the actual return
    world.  Null and wrong-type returns do not call Save or Restore. *)
Definition q_flush_api_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind (q_flush_call_program critical sg invocation pevent)
    (fun code => if Z.eqb code 0 then
      StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret code)
      else StateRelMonad.ret code).

Definition q_flush_api_safe critical sg invocation pevent before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (q_flush_api_program critical sg invocation pevent) X.

Definition q_flush_return_safe (current : UCOS2_Verify_State) (code : Z)
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret code) X.

Definition q_flush_api_post critical sg invocation pevent before code current : Prop :=
  q_flush_api_program critical sg invocation pevent before code current.

Lemma q_flush_api_program_iff : forall critical sg invocation pevent before code current,
  q_flush_api_program critical sg invocation pevent before code current <->
  exists released,
    q_flush_call_program critical sg invocation pevent before code released /\
    (if Z.eqb code 0 then critical_region_interval critical sg invocation released current
     else current = released).
Proof.
  intros; unfold q_flush_api_program, StateRelMonad.bind, update, StateRelMonad.ret.
  split.
  - intros [result [released [Hcall Hreturn]]].
    destruct (Z.eqb result 0) eqn:Hcode.
    + destruct Hreturn as [[] [after [Hinterval [Hresult Hafter]]]].
      subst; exists released; rewrite Hcode; auto.
    + destruct Hreturn as [Hresult Hafter]; subst code current.
      exists released; rewrite Hcode; auto.
  - intros [released [Hcall Hreturn]].
    exists code, released; split; [exact Hcall|].
    destruct (Z.eqb code 0).
    + exists tt, current; split; [exact Hreturn|split; reflexivity].
    + split; [reflexivity|symmetry; exact Hreturn].
Qed.

Lemma q_flush_api_error : forall critical sg invocation pevent before code current,
  code <> 0 ->
  q_flush_call_program critical sg invocation pevent before code current ->
  q_flush_api_program critical sg invocation pevent before code current.
Proof.
  intros; apply q_flush_api_program_iff; exists current; split; [assumption|].
  rewrite (proj2 (Z.eqb_neq code 0) H); reflexivity.
Qed.

Lemma q_flush_api_success : forall critical sg invocation pevent before released current,
  q_flush_call_program critical sg invocation pevent before 0 released ->
  critical_region_interval critical sg invocation released current ->
  q_flush_api_program critical sg invocation pevent before 0 current.
Proof. intros; apply q_flush_api_program_iff; exists released; auto. Qed.

(** A normal endpoint exists in every admitted input state (choose empty
    environment intervals). This is not a termination or fairness claim. *)
Lemma q_flush_api_program_has_result : forall critical sg invocation pevent before eid observed,
  UCOS2_state_inv sg before ->
  q_flush_call_input critical sg invocation pevent before eid observed ->
  exists code current, q_flush_api_program critical sg invocation pevent before code current.
Proof.
  intros critical sg invocation pevent before eid observed Hvalid Hinput.
  destruct Hinput as [Hzero|[Hnonzero [Haddr [Hid [Hslot Hprotocol]]]]].
  - subst pevent; exists 4, before.
    apply q_flush_api_error; [lia|apply q_flush_call_null].
  - destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 2) as [Htype|Htype].
    + destruct (q_flush_public_slot_is_queue before eid observed Hslot Htype)
        as [Hlookup Hqueue].
      assert (Hsaved : interrupt_saved_value 0 0).
      { unfold interrupt_saved_value, valid_os_cpu_sr, armv7a_irq_fiq_mask; cbn; lia. }
      assert (Hfacts : q_flush_acquire_facts critical sg invocation eid 0 0
        before before observed observed).
      { unfold q_flush_acquire_facts.
        split; [constructor|]; split; [exact Hvalid|]; split; [exact Hsaved|].
        repeat split; assumption || reflexivity. }
      exists 0, (q_flush_state before eid observed).
      eapply q_flush_api_success; [|constructor].
      exact (q_flush_call_success critical sg invocation pevent before eid observed 0 0
        before observed Hnonzero Haddr Hid Hfacts).
    + exists 1, before; apply q_flush_api_error; [lia|].
      exact (q_flush_call_wrong_type critical sg invocation pevent before eid observed
        Hnonzero Haddr Hid Hslot Htype).
Qed.

Lemma q_flush_api_safe_return : forall critical sg invocation pevent before code current X,
  q_flush_api_program critical sg invocation pevent before code current ->
  q_flush_api_safe critical sg invocation pevent before X ->
  q_flush_return_safe current code X.
Proof.
  intros critical sg invocation pevent before code current X Hprogram Hsafe.
  unfold q_flush_api_safe in Hsafe; unfold q_flush_return_safe.
  eapply (highstependret_derive
    (q_flush_api_program critical sg invocation pevent) (eq before) code
    (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; auto.
Qed.

(** The type observation is returned before Save.  Its original resource
    package is exactly a canonical closed region plus the caller's existing
    identity/lifetime facts; no duplicated field survives as a frame. *)
Lemma q_flush_save_pre_closed : forall platform critical sg invocation origin mask before eid observed,
  q_flush_save_pre platform critical sg invocation origin mask before eid observed --||--
  coq_prop (mutex_query_handle_protocol critical sg invocation eid /\
    mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q) &&
  mutex_query_closed platform critical sg invocation origin mask before.
Proof. intros; rewrite mutex_query_closed_equiv; reflexivity. Qed.

(** [current] indexes both the returned physical region and its source
    interval.  This is the normal-return observation of the approved CPU/CSL
    boundary, not a theorem manufacturing an after heap from a pure trace. *)
Definition q_flush_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed focused : OSEventAbstractState) : Assertion :=
  EX current,
    coq_prop (q_flush_acquire_facts critical sg invocation eid mask saved before entry observed focused /\
      critical_region_interval critical sg invocation (q_flush_state entry eid focused) current) &&
    mutex_query_closed platform critical sg invocation origin mask current.

Lemma q_flush_restore_return_consequence :
  forall platform critical sg invocation origin eid mask saved before entry current observed focused,
  q_flush_acquire_facts critical sg invocation eid mask saved before entry observed focused ->
  critical_region_interval critical sg invocation (q_flush_state entry eid focused) current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation current |--
  q_flush_restore_post platform critical sg invocation origin mask saved before entry eid observed focused.
Proof.
  intros platform critical sg invocation origin eid mask saved before entry current observed focused
    Hfacts Hinterval.
  pose proof Hfacts as [_ [Hentry [[Hsaved Hmask] [_ [Hlookup [_ [Htype _]]]]]]].
  pose proof (q_flush_state_validity sg entry eid focused Hentry Hlookup Htype) as Hreleased.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation (q_flush_state entry eid focused) current Hinterval Hreleased)) as Hcurrent.
  unfold q_flush_restore_post; Exists current; rewrite Hmask.
  unfold mutex_query_closed; entailer!.
Qed.

Lemma q_flush_restore_immediate_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed focused,
  q_flush_acquire_facts critical sg invocation eid mask saved before entry observed focused ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation (q_flush_state entry eid focused) |--
  q_flush_restore_post platform critical sg invocation origin mask saved before entry eid observed focused.
Proof.
  intros; eapply q_flush_restore_return_consequence; [exact H|constructor].
Qed.
