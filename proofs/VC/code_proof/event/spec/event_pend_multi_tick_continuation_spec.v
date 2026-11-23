Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_multi_tick_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_multi_source_transport_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_multi_continuation_phase_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_multi_resume_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_pend_multi_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def
  Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task
  Ucos2Verify.lib.task_status Ucos2Verify.lib.tick Ucos2Verify.lib.sched
  Ucos2Verify.lib.event Ucos2Verify.lib.event_registration.
Import ListNotations TaskStateDef EventStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A positive-delay continuation cannot already be the woken phase. Its
    nonempty original sequence and the full registration backlinks give
    an actual pending-kind bit, not a premise that assumes the timeout. *)
Lemma event_pend_multi_delayed_continuation_pending : forall sg state tid task base ids,
  UCOS2_full_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some task ->
  event_pend_multi_task_continuation base ids task -> ids <> [] -> task.(dly) <> 0 ->
  task.(tcbEventMultiPtr) <> 0 /\ task_status_has_pending (task.encode_task_status task.(stat)) = true.
Proof.
  intros sg state tid task base [|eid ids] Hvalid Htask
    [Hsingle [Hids Hphase]] Hnonempty Hdelay; [contradiction|].
  assert (Hlinked : task.(tcbEventMultiPtr) <> 0).
  { destruct Hphase as [[Hbase [Hptr _]]|[_ [selected [_ [_ [_ Hzero]]]]]]; congruence. }
  split; [exact Hlinked|].
  assert (Hregistration : event_registration_consistency sg state.(TskState) state.(EventState)).
  { destruct Hvalid as [_ [_ [_ [_ [[_ [_ [Hr _]]] _]]]]]; exact Hr. }
  destruct Hregistration as [Hentries [Hback Hclosed]].
  assert (Href : task_event_registered task eid).
  { right; split; [exact Hlinked|rewrite Hids; left; reflexivity]. }
  destruct (Hclosed tid task eid Htask Href) as [node Hnode].
  pose proof (Hback tid task eid node Htask Hnode Href) as Hin.
  destruct (Hentries eid node Hnode) as [_ Hwait].
  destruct (event_type_to_pend_type node.(eventType)) as [kind|] eqn:Hkind.
  - destruct (Hwait tid Hin) as [found [Hfound HphaseFound]].
    assert (found = task) by congruence; subst found.
    destruct HphaseFound as [[Hbad _]|[_ Hmulti]]; [congruence|].
    destruct Hmulti as [Hsupported [_ [_ [_ [mask [suspended [Hrange [Hbits Hpending]]]]]]]].
    destruct Hpending as [[Hmask _]|[_ [_ Hzero]]]; [|contradiction].
    assert (Hpositive : 0 < mask).
    { pose proof (task_pend_mask_in_range kind) as HkindRange.
      destruct (Z.eq_dec mask 0) as [->|Hne]; [cbn in Hmask; lia|lia]. }
    unfold task_status_has_pending; rewrite Hbits,
      (proj1 (encode_multi_wait_status_observations mask suspended Hrange)).
    apply Bool.negb_true_iff, Z.eqb_neq; lia.
  - rewrite Hwait in Hin; contradiction.
Qed.

Lemma event_pend_multi_tick_body_transports_continuation :
  forall sg state slot node tid generation base ids frame before after,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  event_pend_multi_state_continuation state tid generation base ids ->
  (UCOS2_full_inv sg state ** frame) before ->
  event_pend_multi_tick_body_fragment sg (task_slot_addr sg slot) before after ->
  event_pend_multi_state_continuation (tick_task_step sg slot node state) tid generation base ids /\
    (UCOS2_full_inv sg (tick_task_step sg slot node state) ** frame) after.
Proof.
  intros; split.
  - eapply event_pend_multi_tick_step_transports_continuation; eassumption.
  - eapply event_pend_multi_tick_body_preserves_full_inv; eassumption.
Qed.

Definition event_pend_multi_timeout_phase sg state tid task base ids : Prop :=
  task.(tcbEventMultiPtr) = base /\ base <> 0 /\
  task.(eventMultiWaitEvents) = ids /\ task.(eventPtr) = None /\ task.(eventMultiRdy) = None /\
  task.(statPend) = PendTimeout /\ task.(dly) = 0 /\
  event_pend_multi_remove_needed sg task = true /\
  Forall (fun eid => exists node, state.(EventState).(inUsedEventStates) eid = Some node) ids /\
  (task_is_suspended task.(stat) = false -> In tid state.(SchedState).(readyList)).

Lemma event_pend_multi_tick_expiration_establishes_timeout_phase : forall sg state tid task base ids,
  UCOS2_full_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some task ->
  event_pend_multi_task_continuation base ids task -> ids <> [] -> task.(dly) = 1 ->
  event_pend_multi_timeout_phase sg (tick_task_step sg tid task state) tid (tick_task_update task) base ids.
Proof.
  intros sg state tid task base ids Hvalid Htask Hphase Hnonempty Hdelay.
  destruct (event_pend_multi_delayed_continuation_pending sg state tid task base ids
    Hvalid Htask Hphase Hnonempty ltac:(lia)) as [Hlinked Hpending].
  destruct (event_pend_multi_tick_expiration_takes_remove sg task Hdelay Hpending)
    as [Hresult [Hzero Hremove]].
  destruct Hphase as [Hsingle [Hids [[Hbase [Hptr Hrdy]]|[_ [selected [_ [_ [_ Hbad]]]]]]]];
    [|lia].
  pose proof (event_pend_multi_tick_retains_registration task base ids Hptr Hids)
    as [HnewPtr [HnewIds [HnewRdy HnewSingle]]].
  assert (Hafter : UCOS2_full_state_inv sg (tick_task_step sg tid task state))
    by (eapply event_pend_multi_tick_step_preserves_full_state; eassumption).
  assert (HafterTask : (tick_task_step sg tid task state).(TskState).(inUsedTaskStates) tid =
      Some (tick_task_update task)).
  { rewrite tick_task_step_task_state_eq by exact Htask.
    cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity. }
  assert (Hlive : Forall (fun eid => exists node,
      (tick_task_step sg tid task state).(EventState).(inUsedEventStates) eid = Some node) ids).
  { eapply event_pend_multi_linked_ids_live; [exact Hafter|exact HafterTask|rewrite HnewPtr; exact Hbase|exact HnewIds]. }
  unfold event_pend_multi_timeout_phase.
  split; [exact HnewPtr|]. split; [exact Hbase|]. split; [exact HnewIds|].
  split; [congruence|]. split; [congruence|]. split; [exact Hresult|].
  split; [exact Hzero|]. split; [exact Hremove|]. split; [exact Hlive|].
  intro Hsuspended; unfold tick_task_step; rewrite Hdelay; cbn [Z.eqb].
  rewrite Hzero; cbn [Z.eqb replace_TskS replace_SchedS SchedState].
  apply sched_wake_by_status_membership; right; split; [reflexivity|exact Hsuspended].
Qed.

(** The full heap and the caller's private frame are obtained at the same
    actual endpoint. Readiness is still conditional on the real suspend
    bit; neither current selection nor return to the old call is claimed. *)
Lemma event_pend_multi_tick_body_timeout_post :
  forall sg state tid task base ids frame before after,
  state.(TskState).(inUsedTaskStates) tid = Some task ->
  event_pend_multi_task_continuation base ids task -> ids <> [] -> task.(dly) = 1 ->
  (UCOS2_full_inv sg state ** frame) before ->
  event_pend_multi_tick_body_fragment sg (task_slot_addr sg tid) before after ->
  event_pend_multi_timeout_phase sg (tick_task_step sg tid task state) tid (tick_task_update task) base ids /\
    (UCOS2_full_inv sg (tick_task_step sg tid task state) ** frame) after.
Proof.
  intros sg state tid task base ids frame before after Htask Hphase Hnonempty Hdelay Hbefore Hrun.
  assert (Hvalid : UCOS2_full_state_inv sg state).
  { destruct Hbefore as [owned [rest [_ [[Hvalid _] _]]]]; exact Hvalid. }
  split.
  - eapply event_pend_multi_tick_expiration_establishes_timeout_phase; eassumption.
  - eapply event_pend_multi_tick_body_preserves_full_inv; eassumption.
Qed.
