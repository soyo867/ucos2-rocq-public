Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_checkpoint_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Reuses the source-level no-acquisition argument from the historical scan
    component, without importing its old full-invariant endpoints. *)
Lemma event_pend_multi_probe_unavailable_live : forall events eid kind,
  event_pend_multi_probe events eid = Some (EventPendMultiUnavailable kind) ->
  exists node, events.(inUsedEventStates) eid = Some node.
Proof.
  intros events eid kind Hprobe; unfold event_pend_multi_probe in Hprobe.
  destruct (inUsedEventStates events eid) as [node|] eqn:Hnode; try discriminate.
  eauto.
Qed.

Lemma event_pend_multi_scan_without_ready_preserves_events :
  forall sg ids events mask result,
  event_pend_multi_scan sg ids events mask = Some result ->
  result.(event_pend_multi_scan_ready) = [] ->
  result.(event_pend_multi_scan_type_error) = false ->
  result.(event_pend_multi_scan_events) = events /\
  Forall (fun eid => exists node, events.(inUsedEventStates) eid = Some node) ids.
Proof.
  intros sg ids; induction ids as [|eid rest IH];
    intros events mask result Hscan Hempty Herror.
  - cbn [event_pend_multi_scan] in Hscan; inversion Hscan; subst; split; auto.
  - cbn [event_pend_multi_scan] in Hscan.
    destruct (event_pend_multi_probe events eid)
      as [[|kind|message after]|] eqn:Hprobe; try discriminate.
    + inversion Hscan; subst; discriminate.
    + destruct (IH _ _ _ Hscan Hempty Herror) as [Heq Hrest].
      split; [exact Heq|constructor; [eapply event_pend_multi_probe_unavailable_live; eassumption|exact Hrest]].
    + destruct (event_pend_multi_scan sg rest after mask); inversion Hscan;
        subst; discriminate.
Qed.

(** Finite choice of the generations actually observed by this scan. The
    ordered input and duplicates are retained, with no extra Event ownership. *)
Lemma event_pend_multi_live_ids_array_binding : forall sg events ids,
  Forall (fun eid => exists node, events.(inUsedEventStates) eid = Some node) ids ->
  exists instances, map fst instances = ids /\
    event_multi_array_binding sg events (map (event_addr sg) ids) instances.
Proof.
  intros sg events ids Hlive; induction Hlive as [|eid ids [node Hnode] Hrest IH].
  - exists []; split; constructor.
  - destruct IH as [instances [Hids Hbinding]].
    exists ((eid, node.(eventGeneration)) :: instances); split.
    + cbn; rewrite Hids; reflexivity.
    + constructor; [split; [reflexivity|exists node; auto]|exact Hbinding].
Qed.

Lemma event_pend_multi_scan_wait_input :
  forall sg entry events ids pointers waiting tid task timeout,
  event_pend_multi_abi sg ->
  event_pend_multi_ids_valid sg pointers ids ->
  UCOS2_full_state_inv sg (replace_EventS events entry) ->
  event_pend_multi_task_selected sg (replace_EventS events entry) tid task ->
  event_pend_multi_scan sg ids entry.(EventState) event_pend_multi_empty_mask =
    Some {| event_pend_multi_scan_events := events; event_pend_multi_scan_ready := [];
      event_pend_multi_scan_messages := []; event_pend_multi_scan_mask := waiting;
      event_pend_multi_scan_type_error := false |} ->
  exists instances, event_pend_multi_wait_input sg (replace_EventS events entry)
    tid task (event_pend_multi_mask_value waiting) timeout pointers ids instances.
Proof.
  intros sg entry events ids pointers waiting tid task timeout [Hlayout _]
    [Hpointers Hids] Hvalid Hselected Hscan.
  destruct (event_pend_multi_scan_without_ready_preserves_events _ _ _ _ _
    Hscan eq_refl eq_refl) as [Hevents Hlive]; cbn in Hevents; subst events.
  destruct (event_pend_multi_live_ids_array_binding sg entry.(EventState) ids Hlive)
    as [instances [Hinstances Hbinding]].
  exists instances; split; [exact Hselected|]; split; [exact Hinstances|].
  destruct Hselected as [Hcurrent [Htask Hrow]].
  destruct Hvalid as [Hprofile _].
  unfold full_features_kernel_profile in Hprofile.
  unfold event_task_wait_multi_input; repeat split; try tauto.
  - cbn [event_pend_multi_prepared_tasks glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity.
  - rewrite Hpointers; exact Hbinding.
  - rewrite Forall_forall in *; intros [eid generation] Hin; cbn.
    apply Hlayout, Hids; rewrite <- Hinstances; apply in_map_iff.
    exists (eid, generation); auto.
Qed.

Lemma event_pend_multi_prepare_rest_unchanged : forall sg tid task mask timeout,
  event_pend_multi_tcb_rest sg tid task event_pend_multi_prepare_fields =
  event_pend_multi_tcb_rest sg tid (task_prepare_multi_wait task mask timeout)
    event_pend_multi_prepare_fields.
Proof.
  intros; unfold event_pend_multi_tcb_rest, TaskFieldStorage.store_fields.
  f_equal; apply functional_extensionality; intros [field| | | | | | |];
    try destruct field; reflexivity.
Qed.

(** Only the three cells written by the original prefix change. All 92-byte
    configured storage, including profile and Multi cells, is retained. *)
Lemma event_pend_multi_prepare_storage_merge : forall sg tid task mask timeout,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true ->
  sg.(osKernelConfig).(cfgTaskProfile) = true -> 0 <= mask < 8 ->
  let tcb := task_slot_addr sg tid in
  &(tcb # "os_tcb" ->ₛ "OSTCBStat") # UChar |->
    Z.lor (event_pend_multi_task_status task) (Z.lor mask 128) **
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBDly") # UInt |-> timeout **
  event_pend_multi_tcb_rest sg tid task event_pend_multi_prepare_fields |--
  used_task_rep sg tid (task_prepare_multi_wait task mask timeout).
Proof.
  intros sg tid task mask timeout Hmulti Hprofile Hmask; cbn zeta.
  rewrite (event_pend_multi_prepare_rest_unchanged sg tid task mask timeout).
  unfold used_task_rep, task_slot_storage_rep, tcb_configured_storage_rep.
  rewrite Hmulti, Hprofile.
  unfold event_pend_multi_tcb_rest, event_pend_multi_prepare_fields; cbn [fold_right].
  pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true (task_slot_addr sg tid))
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)))
    (task_layout_image sg (task_prepare_multi_wait task mask timeout)) (TCBCommonField TCBStat)
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; tauto)) as Hstat.
  pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true (task_slot_addr sg tid))
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true))
    (task_layout_image sg (task_prepare_multi_wait task mask timeout)) (TCBCommonField TCBStatPend)
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; tauto)) as Hpend.
  pose proof (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true (task_slot_addr sg tid)) (tcb_configured_fields true true)
    (task_layout_image sg (task_prepare_multi_wait task mask timeout)) (TCBCommonField TCBDly)
    (tcb_configured_fields_nodup true true) ltac:(simpl; tauto)) as Hdly.
  assert (Hstatus : encode_task_status (task_prepare_multi_wait task mask timeout).(stat) =
    Z.lor (event_pend_multi_task_status task) (Z.lor mask 128)).
  { unfold task_prepare_multi_wait; cbn [stat].
    rewrite encode_task_status_repr; [reflexivity|].
    apply task_status_set_multi_wait_in_range; [apply encode_task_status_in_range|exact Hmask]. }
  cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image]
    in Hstat, Hpend, Hdly.
  rewrite Hstatus in Hstat.
  change (encode_pend_status (statPend (task_prepare_multi_wait task mask timeout))) with 0 in Hpend.
  change (dly (task_prepare_multi_wait task mask timeout)) with timeout in Hdly.
  sepcon_right_assoc; sep_apply_l_atomic Hstat; sep_apply_l_atomic Hpend;
    sep_apply_l_atomic Hdly; entailer!.
Qed.

Lemma event_pend_multi_prepared_priority_observation :
  forall state tid task mask timeout slot,
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  option_map curPrio (state.(TskState).(inUsedTaskStates) slot) =
  option_map curPrio ((event_pend_multi_prepared_tasks state tid task mask timeout).(inUsedTaskStates) slot).
Proof.
  intros; symmetry; apply (glob_task_set_usedtask_observation _ curPrio _ tid task);
    [assumption|reflexivity].
Qed.

Lemma event_pend_multi_prepared_ready_encodings : forall state tid task mask timeout,
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  encode_ready_grp state.(SchedState).(readyList)
    (event_pend_multi_prepared_tasks state tid task mask timeout) =
    event_pend_multi_ready_group state /\
  encode_ready_tbl_at_or state.(SchedState).(readyList)
    (event_pend_multi_prepared_tasks state tid task mask timeout) (task.(curPrio) / 8) =
    event_pend_multi_ready_row state task.
Proof.
  intros state tid task mask timeout Htask.
  destruct (sched_encoding_priority_ext state.(SchedState).(readyList)
    state.(TskState) (event_pend_multi_prepared_tasks state tid task mask timeout)
    ltac:(intros; apply event_pend_multi_prepared_priority_observation; exact Htask)) as [Hgrp Hrow].
  split; symmetry; [exact Hgrp|apply Hrow].
Qed.

(** Compose the exact three prefix writes with the already proved C helper
    pre-split. The ready bitmap is indexed by priorities, which do not change.
    This is a transient raw heap, not a premature full-invariant assertion. *)
Lemma event_pend_multi_prepare_wait_split :
  forall sg state tid task mask timeout pointers ids instances base,
  0 <= mask < 8 ->
  event_pend_multi_wait_input sg state tid task mask timeout pointers ids instances ->
  let tcb := task_slot_addr sg tid in
  sg.(g_OSTCBCur) # Ptr |-> tcb **
  &(tcb # "os_tcb" ->ₛ "OSTCBStat") # UChar |->
    Z.lor (event_pend_multi_task_status task) (Z.lor mask 128) **
  &(tcb # "os_tcb" ->ₛ "OSTCBStatPend") # UChar |-> 0 **
  &(tcb # "os_tcb" ->ₛ "OSTCBDly") # UInt |-> timeout **
  event_pend_multi_task_frame sg state tid task event_pend_multi_prepare_fields **
  event_raw_rep sg state.(TskState) state.(EventState) **
  event_multi_array_rep base pointers |--
  event_task_wait_multi_pre sg (event_pend_multi_prepared_tasks state tid task mask timeout)
    state.(EventState) state.(SchedState) tid (task_prepare_multi_wait task mask timeout) base pointers **
  event_pend_multi_wait_frame sg state tid task mask timeout.
Proof.
  intros sg state tid task mask timeout pointers ids instances base Hmask Hinput; cbn zeta.
  destruct Hinput as [[Hcurrent [Htask Hrow]] [Hids Hinput]].
  pose proof Hinput as [Hmulti [Hprofile _]].
  assert (Hpriority : forall slot, option_map curPrio (state.(TskState).(inUsedTaskStates) slot) =
    option_map curPrio ((event_pend_multi_prepared_tasks state tid task mask timeout).(inUsedTaskStates) slot)).
  { intros; apply event_pend_multi_prepared_priority_observation; exact Htask. }
  assert (Hevent : event_raw_rep sg state.(TskState) state.(EventState) =
    event_raw_rep sg (event_pend_multi_prepared_tasks state tid task mask timeout) state.(EventState)).
  { apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes.
    intros eid node slot Hnode Hin; apply Hpriority. }
  assert (Hsched : sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched_raw_rep sg (event_pend_multi_prepared_tasks state tid task mask timeout) state.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot Hin; apply Hpriority. }
  assert (Hcurrent_merge : sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
      event_pend_multi_sched_without_current sg state |--
      sched_raw_rep sg state.(TskState) state.(SchedState)).
  { unfold event_pend_multi_sched_without_current, sched_raw_rep, sched_physical_rep.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!. }
  unfold event_pend_multi_task_frame, event_pend_multi_wait_frame.
  sepcon_right_assoc.
  pose proof (event_pend_multi_prepare_storage_merge sg tid task mask timeout Hmulti Hprofile Hmask) as Hprepare.
  cbn zeta in Hprepare; sep_apply_l_atomic Hprepare.
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg state.(TskState) tid
    (task_prepare_multi_wait task mask timeout)).
  sep_apply_l_atomic Hcurrent_merge.
  rewrite Hevent, Hsched.
  fold (event_pend_multi_prepared_tasks state tid task mask timeout).
  sepcon_right_assoc.
  sep_apply_l_atomic (event_task_wait_multi_pre_split sg
    (event_pend_multi_prepared_tasks state tid task mask timeout) state.(EventState)
    state.(SchedState) tid (task_prepare_multi_wait task mask timeout) base pointers instances Hinput Hcurrent).
  entailer!.
Qed.
