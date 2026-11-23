Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.event_multi Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.helpers.
Import ListNotations TaskStateDef EventStateDef.
Local Open Scope Z_scope.

Lemma event_multi_insert_waiters_lookup : forall sg tasks events tid ids eid after,
  (event_multi_insert_waiters sg tasks events tid ids).(inUsedEventStates) eid = Some after ->
  exists before, events.(inUsedEventStates) eid = Some before /\
    after.(eventType) = before.(eventType) /\
    (forall member, In member after.(waitList) <->
      (In eid ids /\ member = tid) \/ In member before.(waitList)).
Proof.
  intros sg tasks events tid ids eid after Hafter; cbn [event_multi_insert_waiters inUsedEventStates] in Hafter.
  destruct (events.(inUsedEventStates) eid) as [before|] eqn:Hbefore; [|discriminate].
  exists before; split; [reflexivity|].
  destruct (in_dec Z.eq_dec eid ids) as [Hin|Hnot]; injection Hafter as Hafter; subst after.
  - split; [reflexivity|]. intro member; rewrite event_insert_waiter_membership; tauto.
  - split; [reflexivity|]. intro member; tauto.
Qed.

(** The source prefix must supply the new TCB's actual phase facts, and
    the checked array must supply its live lookups. They are deliberately
    premises of this low-level composition rule, not new public API
    assumptions. Duplicate array entries are retained: no NoDup ids is
    required, and the bitmap/list operation is idempotent. *)
Lemma event_multi_register_preserves_registration :
  forall sg tasks events tid old written ids,
  tasks.(inUsedTaskStates) tid = Some old -> written.(curPrio) = old.(curPrio) ->
  task_priority_unique tasks -> valid_task_prio sg old.(curPrio) ->
  (forall eid, ~ task_event_registered old eid) ->
  (forall eid, task_event_registered written eid <-> In eid ids) ->
  (forall eid, In eid ids -> exists e, events.(inUsedEventStates) eid = Some e) ->
  (forall eid e, events.(inUsedEventStates) eid = Some e -> In eid ids ->
    match event_type_to_pend_type e.(eventType) with
    | Some kind => task_registered_wait_phase written eid kind
    | None => False
    end) ->
  event_registration_consistency sg tasks events ->
  event_registration_consistency sg (glob_task_set_usedtask tasks tid written)
    (event_multi_insert_waiters sg tasks events tid ids).
Proof.
  intros sg tasks events tid old written ids Hold Hprio Hunique Hrange
    Hnone Hnewrefs Hlive Hwritten Hvalid.
  destruct Hvalid as [Hentries [Hback Hclosed]].
  assert (Hnotlisted : forall eid e, events.(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)).
  { intros eid e He Hin; apply (Hnone eid).
    apply (event_registration_waiter_iff sg tasks events tid old eid e
      (conj Hentries (conj Hback Hclosed)) Hold He); exact Hin. }
  split.
  - intros eid after Hafter.
    destruct (event_multi_insert_waiters_lookup sg tasks events tid ids eid after Hafter)
      as [before [Hb [Htype Hmembers]]].
    split.
    + eapply event_waitList_canonical_update_task; [exact Hold|exact Hprio|].
      eapply event_multi_insert_waiters_preserves_canonical;
        [exact Hunique|exact Hold|exact Hrange| |exact Hafter].
      intros slot e He; exact (proj1 (Hentries slot e He)).
    + rewrite Htype; destruct (event_type_to_pend_type before.(eventType)) as [kind|] eqn:Hkind.
      * intros member Hin; apply Hmembers in Hin; destruct Hin as [[Hid ->]|Hin].
        -- exists written; split.
           ++ cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
           ++ specialize (Hwritten eid before Hb Hid); rewrite Hkind in Hwritten; exact Hwritten.
        -- destruct (Hentries eid before Hb) as [_ Hphase]; rewrite Hkind in Hphase.
           destruct (Hphase member Hin) as [t [Ht Hp]]; exists t; split; [|exact Hp].
           cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb member tid) eqn:E.
           ++ apply Z.eqb_eq in E; subst member; exfalso; exact (Hnotlisted eid before Hb Hin).
           ++ exact Ht.
      * destruct (Hentries eid before Hb) as [_ Hempty]; rewrite Hkind in Hempty.
        destruct after.(waitList) as [|member tail] eqn:Hlist; [reflexivity|exfalso].
        pose proof (proj1 (Hmembers member) (or_introl eq_refl)) as Hin.
        destruct Hin as [[Hid _]|Hin].
        -- specialize (Hwritten eid before Hb Hid); rewrite Hkind in Hwritten; exact Hwritten.
        -- rewrite Hempty in Hin; contradiction.
  - split.
    + intros member t eid after Ht Hafter Href.
      destruct (event_multi_insert_waiters_lookup sg tasks events tid ids eid after Hafter)
        as [before [Hb [_ Hmembers]]]; apply Hmembers.
      cbn [glob_task_set_usedtask inUsedTaskStates] in Ht; destruct (Z.eqb member tid) eqn:E.
      * apply Z.eqb_eq in E; subst member; injection Ht as Ht; subst t.
        left; split; [apply Hnewrefs; exact Href|reflexivity].
      * right; eapply Hback; eassumption.
    + intros member t eid Ht Href.
      assert (Hexists : exists before, events.(inUsedEventStates) eid = Some before).
      { cbn [glob_task_set_usedtask inUsedTaskStates] in Ht; destruct (Z.eqb member tid) eqn:E.
        - injection Ht as Ht; subst t; apply Hlive, Hnewrefs; exact Href.
        - eapply Hclosed; eassumption. }
      destruct Hexists as [before Hb].
      destruct (event_multi_insert_waiters_membership sg tasks events tid ids eid before Hb)
        as [after [Ha _]]; exists after; exact Ha.
Qed.

Lemma event_multi_remove_waiters_lookup : forall events tid ids eid after,
  (event_multi_remove_waiters events tid ids).(inUsedEventStates) eid = Some after ->
  exists before, events.(inUsedEventStates) eid = Some before /\
    after.(eventType) = before.(eventType) /\
    (forall member, In member after.(waitList) <->
      In member before.(waitList) /\ (member <> tid \/ ~ In eid ids)).
Proof.
  intros events tid ids eid after Ha; cbn [event_multi_remove_waiters inUsedEventStates] in Ha.
  destruct (events.(inUsedEventStates) eid) as [before|] eqn:Hb; [|discriminate].
  exists before; split; [reflexivity|].
  destruct (in_dec Z.eq_dec eid ids) as [Hin|Hnot]; injection Ha as Ha; subst after.
  - split; [reflexivity|]. intro member; cbn [event_set_wait_list waitList]; split.
    + intros H; split; [eapply remove_Z_eqb_in; exact H|]. left.
      intros ->; exact (remove_Z_eqb_notin tid before.(waitList) H).
    + intros [H [Hneq|Habsent]]; [apply remove_Z_eqb_in_neq; assumption|contradiction].
  - split; [reflexivity|]. intro member; tauto.
Qed.

(** EventTaskRdy, timeout cleanup and removal may clear a registration
    without erasing the caller's saved input sequence. Only the current
    registration set is removed. All other waiters keep their phase facts. *)
Lemma event_multi_remove_preserves_registration :
  forall sg tasks events tid old written ids,
  tasks.(inUsedTaskStates) tid = Some old -> written.(curPrio) = old.(curPrio) ->
  (forall eid, task_event_registered old eid <-> In eid ids) ->
  (forall eid, ~ task_event_registered written eid) ->
  event_registration_consistency sg tasks events ->
  event_registration_consistency sg (glob_task_set_usedtask tasks tid written)
    (event_multi_remove_waiters events tid ids).
Proof.
  intros sg tasks events tid old written ids Hold Hprio Hrefs Hnone Hvalid.
  destruct Hvalid as [Hentries [Hback Hclosed]].
  assert (Hnotlisted : forall eid after,
    (event_multi_remove_waiters events tid ids).(inUsedEventStates) eid = Some after ->
    ~ In tid after.(waitList)).
  { intros eid after Ha Hin.
    destruct (event_multi_remove_waiters_lookup events tid ids eid after Ha)
      as [before [Hb [_ Hmembers]]].
    apply Hmembers in Hin; destruct Hin as [Hin [Hne|Hnot]]; [congruence|].
    apply Hnot, Hrefs.
    apply (event_registration_waiter_iff sg tasks events tid old eid before
      (conj Hentries (conj Hback Hclosed)) Hold Hb); exact Hin. }
  split.
  - intros eid after Ha.
    destruct (event_multi_remove_waiters_lookup events tid ids eid after Ha)
      as [before [Hb [Htype Hmembers]]].
    destruct (Hentries eid before Hb) as [Horder Hphase].
    split.
    + eapply event_waitList_canonical_update_task; [exact Hold|exact Hprio|].
      eapply event_multi_remove_waiters_preserves_canonical; [|exact Ha].
      intros slot e He; exact (proj1 (Hentries slot e He)).
    + rewrite Htype; destruct (event_type_to_pend_type before.(eventType)) as [kind|] eqn:Hkind.
      * intros member Hin; destruct (Hphase member (proj1 (proj1 (Hmembers member) Hin))) as [t [Ht Hp]].
        exists t; split; [|exact Hp].
        cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb member tid) eqn:E.
        -- apply Z.eqb_eq in E; subst member; exfalso; exact (Hnotlisted eid after Ha Hin).
        -- exact Ht.
      * destruct after.(waitList) as [|member tail] eqn:Hlist; [reflexivity|exfalso].
        pose proof (proj1 (Hmembers member) (or_introl eq_refl)) as Hin.
        rewrite Hphase in Hin; tauto.
  - split.
    + intros member t eid after Ht Ha Href.
      destruct (event_multi_remove_waiters_lookup events tid ids eid after Ha)
        as [before [Hb [_ Hmembers]]]; apply Hmembers.
      cbn [glob_task_set_usedtask inUsedTaskStates] in Ht; destruct (Z.eqb member tid) eqn:E.
      * injection Ht as Ht; subst t; exfalso; exact (Hnone eid Href).
      * split; [eapply Hback; eassumption|]. left; apply Z.eqb_neq; exact E.
    + intros member t eid Ht Href.
      cbn [glob_task_set_usedtask inUsedTaskStates] in Ht; destruct (Z.eqb member tid) eqn:E.
      * injection Ht as Ht; subst t; exfalso; exact (Hnone eid Href).
      * destruct (Hclosed member t eid Ht Href) as [before Hb].
        cbn [event_multi_remove_waiters inUsedEventStates]; rewrite Hb.
        destruct (in_dec Z.eq_dec eid ids); eexists; reflexivity.
Qed.

Lemma event_multi_wake_preserves_registration : forall sg tasks events tid old selected kind message result,
  tasks.(inUsedTaskStates) tid = Some old -> old.(eventPtr) = None ->
  old.(tcbEventMultiPtr) <> 0 -> In selected old.(eventMultiWaitEvents) ->
  event_registration_consistency sg tasks events ->
  event_registration_consistency sg
    (glob_task_set_usedtask tasks tid (task_multi_wake old kind message result selected))
    (event_multi_remove_waiters events tid (selected :: old.(eventMultiWaitEvents))).
Proof.
  intros sg tasks events tid old selected kind message result Hold Hptr Harray Hselected Hvalid.
  eapply event_multi_remove_preserves_registration;
    [exact Hold|reflexivity| | |exact Hvalid].
  - intro eid; unfold task_event_registered; rewrite Hptr; simpl; split.
    + intros [H|[_ Hin]]; [discriminate|right; exact Hin].
    + intros [<-|Hin]; right; split; assumption.
  - intro eid; apply task_multi_wake_has_no_registration.
Qed.
