Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.

Import EventStateDef UCOS2_C_Rules.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Ordered guards shared by OSEventNameGet and OSEventNameSet.  The
    non-null [perr] condition belongs to this verified internal contract:
    OS_SAFETY_CRITICAL is not enabled in the selected full-features profile,
    so the upstream C body dereferences [perr] on every ordinary branch. *)
(** The type is the concrete byte read before Save, not necessarily a live
    abstract Event node. This preserves the default branch for every other
    byte and does not assume the object is unchanged across the call. *)
Definition event_name_type_allowed (ty : Z) : bool :=
  ((ty =? encode_event_type OS_EVENT_TYPE_SEM) ||
   (ty =? encode_event_type OS_EVENT_TYPE_MUTEX) ||
   (ty =? encode_event_type OS_EVENT_TYPE_MBOX) ||
   (ty =? encode_event_type OS_EVENT_TYPE_Q))%bool.

Definition event_name_get_error (pevent pname : addr) (nesting : Z)
  (ty : Z) : option OSErrCode :=
  if Z.eqb pevent 0 then Some OS_ERR_PEVENT_NULL else
  if Z.eqb pname 0 then Some OS_ERR_PNAME_NULL else
  if Z.ltb 0 nesting then Some OS_ERR_NAME_GET_ISR else
  if event_name_type_allowed ty then None else Some OS_ERR_EVENT_TYPE.

Definition event_name_set_error (pevent pname : addr) (nesting : Z)
  (ty : Z) : option OSErrCode :=
  if Z.eqb pevent 0 then Some OS_ERR_PEVENT_NULL else
  if Z.eqb pname 0 then Some OS_ERR_PNAME_NULL else
  if Z.ltb 0 nesting then Some OS_ERR_NAME_SET_ISR else
  if event_name_type_allowed ty then None else Some OS_ERR_EVENT_TYPE.

Lemma event_name_get_success_guard : forall pevent pname nesting ty,
  pevent <> 0 -> pname <> 0 -> nesting <= 0 ->
  event_name_type_allowed ty = true ->
  event_name_get_error pevent pname nesting ty = None.
Proof.
  intros pevent pname nesting ty Hevent Hname Hnest Htype.
  unfold event_name_get_error.
  assert (Hpevent : Z.eqb pevent 0 = false) by (apply Z.eqb_neq; exact Hevent).
  assert (Hpname : Z.eqb pname 0 = false) by (apply Z.eqb_neq; exact Hname).
  assert (Hnesting : Z.ltb 0 nesting = false) by (apply Z.ltb_ge; exact Hnest).
  rewrite Hpevent, Hpname, Hnesting, Htype; reflexivity.
Qed.

Lemma event_name_set_success_guard : forall pevent pname nesting ty,
  pevent <> 0 -> pname <> 0 -> nesting <= 0 ->
  event_name_type_allowed ty = true ->
  event_name_set_error pevent pname nesting ty = None.
Proof.
  intros pevent pname nesting ty Hevent Hname Hnest Htype.
  unfold event_name_set_error.
  assert (Hpevent : Z.eqb pevent 0 = false) by (apply Z.eqb_neq; exact Hevent).
  assert (Hpname : Z.eqb pname 0 = false) by (apply Z.eqb_neq; exact Hname).
  assert (Hnesting : Z.ltb 0 nesting = false) by (apply Z.ltb_ge; exact Hnest).
  rewrite Hpevent, Hpname, Hnesting, Htype; reflexivity.
Qed.

(** Pure result relation only, not a C callee contract. The callee still
    needs ownership of every byte through the NUL and a verified loop. This
    no-wrap relation does not assert that length is a termination measure:
    the C loop is controlled by the source byte, not by its INT8U counter. *)
Definition event_name_length_observation (names : NameResourceState) (p : addr)
  (chars : list Z) (len : Z) : Prop :=
  readable_name names p chars /\ os_strlen_length_valid chars /\
  len = name_length_result chars.

Lemma event_name_length_observation_exact : forall names p chars len,
  event_name_length_observation names p chars len ->
  len = Z.of_nat (List.length chars).
Proof.
  intros names p chars len [_ [Hlength Hlen]].
  rewrite Hlen; apply name_length_result_exact; exact Hlength.
Qed.

Definition event_name_set_post (s : UCOS2_Verify_State) (eid : EventID)
  (old : OSEventAbstractState) (name : addr) : UCOS2_Verify_State :=
  replace_EventS
    (update_event_field_raw s.(EventState) eid (event_set_name old name)) s.

Definition event_name_set_old (s : UCOS2_Verify_State) (eid : EventID)
  (old : OSEventAbstractState) (type_byte : Z) : Prop :=
  s.(EventState).(inUsedEventStates) eid = Some old /\
  type_byte = encode_event_type old.(eventType).

Definition event_name_set_entry (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (pevent type_byte : Z) : Prop :=
  pevent = event_addr sg eid /\
  exists old, event_name_set_old s eid old type_byte.

(** Canonical ordered operation used by the future C annotation.  The
    concrete type byte and the Event slot are explicit inputs because the
    source reads the type before entering the critical region; a successful
    critical write must still identify the same live slot at the operation
    boundary. *)
Definition event_name_set_sem (sg : StableGlobVars) (eid : EventID)
  (pevent pname : addr) (nesting type_byte : Z)
  : program UCOS2_Verify_State OSErrCode :=
  fun s error after =>
    match event_name_set_error pevent pname nesting type_byte with
    | Some expected => error = expected /\ after = s
    | None => exists old,
        s.(EventState).(inUsedEventStates) eid = Some old /\
        pevent = event_addr sg eid /\
        type_byte = encode_event_type old.(eventType) /\
        error = OS_ERR_NONE /\
        after = event_name_set_post s eid old pname
    end.

Definition event_name_set_observe_err (error : OSErrCode)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun post result after => result = encode_os_err_code error /\ post = after.

Lemma event_name_set_sem_deterministic : forall sg eid pevent pname nesting type_byte s r1 s1 r2 s2,
  event_name_set_sem sg eid pevent pname nesting type_byte s r1 s1 ->
  event_name_set_sem sg eid pevent pname nesting type_byte s r2 s2 ->
  r1 = r2 /\ s1 = s2.
Proof.
  intros sg eid pevent pname nesting type_byte s r1 s1 r2 s2 H1 H2.
  unfold event_name_set_sem in H1, H2.
  destruct (event_name_set_error pevent pname nesting type_byte) as [expected|].
  - destruct H1 as [-> ->], H2 as [-> ->]; auto.
  - destruct H1 as [old1 [Hold1 [Haddr1 [Htype1 [-> Hpost1]]]]].
    destruct H2 as [old2 [Hold2 [Haddr2 [Htype2 [-> Hpost2]]]]].
    assert (old1 = old2) by congruence; subst old2; split; [reflexivity|congruence].
Qed.

Lemma event_name_set_post_preserves_kernel_names : forall sg s eid old name chars,
  s.(EventState).(inUsedEventStates) eid = Some old ->
  kernel_names_valid sg s -> readable_name s.(NameState) name chars ->
  kernel_names_valid sg (event_name_set_post s eid old name).
Proof.
  intros sg s eid old name chars Hold Hvalid Hread.
  unfold event_name_set_post.
  exact (kernel_names_valid_event_set_name sg s eid old name chars Hvalid Hread).
Qed.

(** [OSEventNameSet] reads the type byte before it enters the critical
    region and writes the name pointer after Save.  The focused contract
    therefore exposes exactly those two concrete cells.  The residual is a
    real field-store over every other configured ECB field: all payload,
    wait-table and padding cells remain owned, rather than being replaced by
    an uninformative [emp] or [True] placeholder. *)
Definition event_name_set_type_name_residual
  (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (eid : EventID) (old : OSEventAbstractState) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec
    (event_cell (event_addr sg eid))
    (remove EventField_eq_dec EventNameField
      (remove EventField_eq_dec EventTypeField
        (event_fields sg.(osKernelConfig).(cfgEventNames))))
    (event_image sg tasks old).

Lemma event_name_set_remove_preserves_nodup : forall fields field,
  NoDup fields -> NoDup (remove EventField_eq_dec field fields).
Proof.
  intros fields field Hnd; induction Hnd as [|head rest Hnot Hrest IH].
  - simpl; constructor.
  - simpl; destruct (EventField_eq_dec field head) as [->|Hneq].
    + exact IH.
    + constructor.
      * intros Hin; apply Hnot; apply in_remove in Hin; tauto.
      * exact IH.
Qed.

Lemma event_name_set_type_name_split : forall sg tasks eid old,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  used_event_rep sg tasks eid old |--
    event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
    event_name_set_type_name_residual sg tasks eid old.
Proof.
  intros sg tasks eid old Hnamed.
  unfold used_event_rep, event_name_set_type_name_residual.
  sep_apply (event_storage_split_field
    sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg tasks old) EventTypeField
    ltac:(unfold event_fields; simpl; tauto)).
  unfold event_storage_without_field.
  sep_apply (EventFieldStorage.store_fields_split_field
    EventField (option Z) EventField_eq_dec (event_cell (event_addr sg eid))
    (remove EventField_eq_dec EventTypeField
      (event_fields sg.(osKernelConfig).(cfgEventNames)))
    (event_image sg tasks old) EventNameField
    ltac:(apply event_name_set_remove_preserves_nodup;
          apply event_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|apply event_name_field_in_fields;
      exact Hnamed])).
  cbn [event_image event_cell event_field_offset].
  entailer!.
Qed.

Lemma event_name_set_type_name_merge : forall sg tasks eid old,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
    event_name_set_type_name_residual sg tasks eid old |--
    used_event_rep sg tasks eid old.
Proof.
  intros sg tasks eid old Hnamed.
  unfold used_event_rep, event_name_set_type_name_residual.
  assert (Hname_image :
    event_image sg tasks old EventNameField = Some old.(eventName)) by reflexivity.
  rewrite <- Hname_image.
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_field
    EventField (option Z) EventField_eq_dec (event_cell (event_addr sg eid))
    (remove EventField_eq_dec EventTypeField
      (event_fields sg.(osKernelConfig).(cfgEventNames)))
    (event_image sg tasks old) EventNameField
    ltac:(apply event_name_set_remove_preserves_nodup;
          apply event_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|apply event_name_field_in_fields;
      exact Hnamed])).
  assert (Htype_image :
    event_image sg tasks old EventTypeField =
      Some (encode_event_type old.(eventType))) by reflexivity.
  rewrite <- Htype_image.
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_field
    EventField (option Z) EventField_eq_dec (event_cell (event_addr sg eid))
    (event_fields sg.(osKernelConfig).(cfgEventNames))
    (event_image sg tasks old) EventTypeField
    ltac:(apply event_fields_nodup)
    ltac:(unfold event_fields; simpl; tauto)).
  cbn [event_image event_cell event_field_offset].
  entailer!.
Qed.

Lemma event_name_set_type_name_merge_updated : forall sg tasks eid old name,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some name) **
    event_name_set_type_name_residual sg tasks eid old |--
    used_event_rep sg tasks eid (event_set_name old name).
Proof.
  intros sg tasks eid old name Hnamed.
  unfold used_event_rep, event_name_set_type_name_residual.
  rewrite event_set_name_image_eq.
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_updated_field
    EventField (option Z) EventField_eq_dec (event_cell (event_addr sg eid))
    (remove EventField_eq_dec EventTypeField
      (event_fields sg.(osKernelConfig).(cfgEventNames)))
    (event_image sg tasks old) EventNameField (Some name)
    ltac:(apply event_name_set_remove_preserves_nodup;
          apply event_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|apply event_name_field_in_fields;
      exact Hnamed])).
  assert (Htype_image_updated :
    event_write (event_image sg tasks old) EventNameField (Some name)
        EventTypeField = Some (encode_event_type old.(eventType))) by reflexivity.
  rewrite <- Htype_image_updated.
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_field
    EventField (option Z) EventField_eq_dec (event_cell (event_addr sg eid))
    (event_fields sg.(osKernelConfig).(cfgEventNames))
    (event_write (event_image sg tasks old) EventNameField (Some name))
    EventTypeField
    ltac:(apply event_fields_nodup)
    ltac:(unfold event_fields; simpl; tauto)).
  cbn [event_image event_cell event_field_offset].
  entailer!.
Qed.

(** Lift the field focus through the used-event map.  The second conjunct is
    the real map residual from [event_raw_rep_split_eid], so it can be
    reattached either to the old event or to the updated [event_set_name]
    event without manufacturing any global resource. *)
Definition event_name_set_raw_residual
  (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) (eid : EventID) (old : OSEventAbstractState)
  : Assertion :=
  event_name_set_type_name_residual sg tasks eid old **
  event_raw_rep_no_eid sg tasks events eid.

Lemma event_name_set_raw_split : forall sg tasks events eid old,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  events.(inUsedEventStates) eid = Some old ->
  event_raw_rep sg tasks events |--
    event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
    event_name_set_raw_residual sg tasks events eid old.
Proof.
  intros sg tasks events eid old Hnamed Hget.
  unfold event_name_set_raw_residual.
  sep_apply_l_atomic (event_raw_rep_split_eid sg tasks events eid old Hget).
  sep_apply_l_atomic (event_name_set_type_name_split sg tasks eid old Hnamed).
  entailer!.
Qed.

Lemma event_name_set_raw_merge : forall sg tasks events eid old,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  events.(inUsedEventStates) eid = Some old ->
  event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
    event_name_set_raw_residual sg tasks events eid old |--
    event_raw_rep sg tasks events.
Proof.
  intros sg tasks events eid old Hnamed Hget.
  unfold event_name_set_raw_residual.
  eapply derivable1_trans with
    ((event_cell (event_addr sg eid) EventTypeField
        (Some (encode_event_type old.(eventType))) **
      event_cell (event_addr sg eid) EventNameField (Some old.(eventName)) **
      event_name_set_type_name_residual sg tasks eid old) **
     event_raw_rep_no_eid sg tasks events eid).
  - entailer!.
  - eapply derivable1_trans.
    + apply derivable1_sepcon_mono.
      * apply event_name_set_type_name_merge; exact Hnamed.
      * reflexivity.
    + apply event_raw_rep_merge_eid; exact Hget.
Qed.

Lemma event_name_set_raw_merge_updated : forall sg tasks events eid old name,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  events.(inUsedEventStates) eid = Some old ->
  event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some name) **
    event_name_set_raw_residual sg tasks events eid old |--
    event_raw_rep sg tasks
      (update_event_field_raw events eid (event_set_name old name)).
Proof.
  intros sg tasks events eid old name Hnamed Hget.
  unfold event_name_set_raw_residual.
  eapply derivable1_trans with
    ((event_cell (event_addr sg eid) EventTypeField
        (Some (encode_event_type old.(eventType))) **
      event_cell (event_addr sg eid) EventNameField (Some name) **
      event_name_set_type_name_residual sg tasks eid old) **
     event_raw_rep_no_eid sg tasks events eid).
  - entailer!.
  - eapply derivable1_trans.
    + apply derivable1_sepcon_mono.
      * apply event_name_set_type_name_merge_updated; exact Hnamed.
      * reflexivity.
    + apply event_raw_rep_merge_updated_eid.
Qed.

(** The raw merge has a matching module-validity consequence.  This keeps
    the spatial reconstruction and the pure event-state preservation fact on
    separate, explicit sides of the entailment; neither side manufactures
    name-byte ownership or assumes the names-disabled global profile. *)
Lemma event_name_set_raw_merge_updated_preserves_range :
  forall sg tasks events eid old name,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  event_in_range sg tasks events ->
  events.(inUsedEventStates) eid = Some old ->
  event_cell (event_addr sg eid) EventTypeField
      (Some (encode_event_type old.(eventType))) **
    event_cell (event_addr sg eid) EventNameField (Some name) **
    event_name_set_raw_residual sg tasks events eid old |--
    coq_prop (event_in_range sg tasks
      (update_event_field_raw events eid (event_set_name old name))) &&
    event_raw_rep sg tasks
      (update_event_field_raw events eid (event_set_name old name)).
Proof.
  intros sg tasks events eid old name Hnamed Hvalid Hget.
  assert (Hpost : event_in_range sg tasks
      (update_event_field_raw events eid (event_set_name old name))).
  { apply event_set_name_preserves_in_range; assumption. }
  eapply derivable1_trans;
    [apply event_name_set_raw_merge_updated; assumption|].
  change (event_raw_rep sg tasks
    (update_event_field_raw events eid (event_set_name old name)) |--
    coq_prop (event_in_range sg tasks
      (update_event_field_raw events eid (event_set_name old name))) &&
    event_raw_rep sg tasks
      (update_event_field_raw events eid (event_set_name old name))).
  entailer!.
Qed.
