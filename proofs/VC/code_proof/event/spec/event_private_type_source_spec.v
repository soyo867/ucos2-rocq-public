Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Import UCOS2_C_Rules EventStateDef EventFieldStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A property of reachable source images, not a consequence of owning
    uninitialized bytes. Allocation reads a free ECB whose Type is zero;
    each source write stores Some value; publication removes its entry.
    No new state field or public API premise is introduced. *)
Definition event_private_types_defined (events : Glob_EventAbstractState) : Prop :=
  forall eid allocation, events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
    exists kind, allocation.(eventPrivateStorage) EventTypeField = Some kind.

Lemma event_pool_initial_private_types_defined : forall sg,
  event_private_types_defined (event_pool_initial sg).
Proof. intros sg eid allocation Hget; discriminate. Qed.

Lemma event_pool_initial_named_private_types_defined : forall sg name,
  event_private_types_defined (event_pool_initial_named sg name).
Proof. intros sg name eid allocation Hget; discriminate. Qed.

Lemma event_detach_head_preserves_private_types_defined : forall events eid rest image kind,
  event_private_types_defined events -> image EventTypeField = Some kind ->
  event_private_types_defined (event_detach_head events eid rest image).
Proof.
  intros events eid rest image kind Htypes Htype other allocation Hget.
  cbn [event_detach_head eventLifecycle eventPrivate] in Hget.
  destruct (Z.eq_dec other eid) as [->|Hneq].
  - rewrite kernel_map_set_same in Hget; injection Hget as <-; exists kind; exact Htype.
  - rewrite kernel_map_set_other in Hget by exact Hneq; eapply Htypes; exact Hget.
Qed.

Lemma event_private_write_preserves_private_types_defined : forall events eid allocation field value,
  event_private_types_defined events -> events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_private_types_defined (event_private_write events eid allocation field (Some value)).
Proof.
  intros events eid allocation field value Htypes Hget other updated Hupdated.
  cbn [event_private_write event_set_lifecycle eventLifecycle eventPrivate] in Hupdated.
  destruct (Z.eq_dec other eid) as [->|Hneq].
  - rewrite kernel_map_set_same in Hupdated; injection Hupdated as <-; cbn [eventPrivateStorage].
    destruct (EventField_eq_dec EventTypeField field) as [->|Hdifferent].
    + exists value; unfold event_write; apply field_update_same.
    + destruct (Htypes eid allocation Hget) as [kind Htype]; exists kind.
      unfold event_write; rewrite field_update_other by congruence; exact Htype.
  - rewrite kernel_map_set_other in Hupdated by exact Hneq; eapply Htypes; exact Hupdated.
Qed.

Lemma event_publish_preserves_private_types_defined : forall events eid node,
  event_private_types_defined events -> event_private_types_defined (event_publish events eid node).
Proof.
  intros events eid node Htypes other allocation Hget.
  cbn [event_publish eventLifecycle eventPrivate] in Hget.
  destruct (Z.eq_dec other eid) as [->|Hneq].
  - rewrite kernel_map_set_same in Hget; discriminate.
  - rewrite kernel_map_set_other in Hget by exact Hneq; eapply Htypes; exact Hget.
Qed.

Lemma event_create_allocate_preserves_private_types_defined : forall sg state result after,
  UCOS2_state_inv sg state -> event_private_types_defined state.(EventState) ->
  event_create_allocate_critical state result after -> event_private_types_defined after.(EventState).
Proof.
  intros sg state result after Hvalid Htypes Hstep.
  pose proof Hstep as Hactual; unfold event_create_allocate_critical in Hstep.
  destruct state.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  - destruct Hstep as [_ ->]; exact Htypes.
  - destruct Hstep as [image [Himage [-> ->]]]; cbn [replace_EventS EventState].
    eapply event_detach_head_preserves_private_types_defined; [exact Htypes|].
    eapply event_create_allocate_critical_image_type; eassumption.
Qed.

Lemma event_create_private_stores_preserves_private_types_defined : forall eid writes state result after,
  event_private_types_defined state.(EventState) ->
  event_create_private_stores eid writes state result after -> event_private_types_defined after.(EventState).
Proof.
  intros eid writes; induction writes as [|[field value] rest IH]; intros state result after Htypes Hstep.
  - destruct Hstep as [_ ->]; exact Htypes.
  - destruct Hstep as [allocation [Hget Htail]].
    eapply IH; [|exact Htail]; cbn [replace_EventS EventState].
    eapply event_private_write_preserves_private_types_defined; eassumption.
Qed.

(** A concrete consumer: the source fact chooses the current Type value,
    and the actual whole-pool owner supplies its byte. The matching field
    residual and missing pool retain every remaining byte exactly once. *)
Lemma event_private_pool_split_type : forall sg events eid allocation,
  event_private_types_defined events -> events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_private_pool_rep sg events |--
  EX kind, coq_prop (allocation.(eventPrivateStorage) EventTypeField = Some kind) &&
    ((event_pool_addr sg eid) # UChar |-> kind **
     event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
       allocation.(eventPrivateStorage) EventTypeField ** event_private_pool_missing_eid sg events eid).
Proof.
  intros sg events eid allocation Htypes Hget; destruct (Htypes eid allocation Hget) as [kind Htype].
  sep_apply_l_atomic (event_private_pool_split_eid sg events eid allocation Hget).
  unfold event_private_storage_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    allocation.(eventPrivateStorage) EventTypeField ltac:(unfold event_fields; destruct (cfgEventNames (osKernelConfig sg)); simpl; auto)).
  Exists kind; rewrite Htype; cbn [event_cell event_field_offset]; rewrite Z.add_0_r; entailer!.
Qed.
