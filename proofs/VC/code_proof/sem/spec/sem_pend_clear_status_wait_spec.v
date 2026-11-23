Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass.
Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope sac_scope.

(** The literal event-pend update preserves suspension. It needs the
    same live caller to have no outstanding pending-status bits, rather than
    membership of that caller in the ready list. These lemmas generalize the
    three existing full-state/heap theorems without changing their models,
    physical owners, event update or other premises. A caller must still
    establish this exact status fact from its actual execution source;
    empty event/flag pointers alone do not imply it. *)
Lemma event_pend_preserves_validity_from_clear_status : forall sg s eid e tid old kind timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil -> old.(tcbFlagNode) = 0 ->
  task_non_suspension_bits old.(stat) = 0 ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  UCOS2_state_inv sg (event_pend_state sg s eid e tid old kind timeout).
Proof.
  intros sg s eid e tid old kind timeout
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]]
    He Hold Hprio Hnull Hmulti Hflagnull Hnone Hkind Hunavailable Hnotowner.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HpendingAfter : pending_mutex_consistency sg
    (event_pend_state sg s eid e tid old kind timeout).(TskState)
    (event_pend_state sg s eid e tid old kind timeout).(EventState)).
  { eapply pending_mutex_consistency_event_fields_update with (old := e);
      [exact He|reflexivity|reflexivity|exact Hpending]. }
  assert (HreferencesAfter : kernel_names_valid sg (event_pend_state sg s eid e tid old kind timeout)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - eapply event_update_preserves_name_references; [exact He|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (event_pend_state sg s eid e tid old kind timeout).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HbitsAfter : task_reserved_bits_clear sg
    (event_pend_state sg s eid e tid old kind timeout).(TskState)).
  { apply task_reserved_bits_clear_update_task; [exact Hstatus|].
    apply task_status_set_wait_preserves_reserved_bits; [exact (Hstatus tid old Hold)|].
    left; intro HmultiKind; subst kind; destruct e.(eventType); discriminate. }
  destruct (event_pend_preserves_task_sched sg s eid e tid old kind timeout
    Htasks Hsched Hold) as [HtasksAfter HschedAfter].
  split; [exact Hprofile|]; split; [exact HtasksAfter|]; split; [exact HschedAfter|]; split.
  - eapply event_pend_preserves_event_in_range; eauto.
  - split.
    + eapply event_pend_preserves_cross_module_consistency; eauto.
    + split.
      2: { split; [exact HbitsAfter|].
           repeat (split; [assumption|]); exact HpendingAfter. }
      intro Hrunning; eapply task_update_preserves_idle_tail;
        [exact Hold|reflexivity|apply Hidle; exact Hrunning].
Qed.

Lemma event_pend_merge_from_clear_status : forall sg s eid e tid old kind timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil -> old.(tcbFlagNode) = 0 ->
  task_non_suspension_bits old.(stat) = 0 ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  let post := event_pend_state sg s eid e tid old kind timeout in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  event_raw_rep sg s.(TskState) post.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s eid e tid old kind timeout Hvalid He Hold Hprio Hnull Hmulti Hflagnull
    Hnone Hkind Hunavailable Hnotowner post.
  pose proof (event_pend_preserves_validity_from_clear_status sg s eid e tid old kind timeout
    Hvalid He Hold Hprio Hnull Hmulti Hflagnull Hnone Hkind Hunavailable Hnotowner) as Hpost; fold post in Hpost.
  assert (Hindex : event_raw_rep sg s.(TskState) post.(EventState) =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (UCOS2_event_pend_preserves_residual
    sg s eid e tid old kind timeout He); fold post.
  unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event, task_shared_rep; entailer!.
Qed.

Lemma event_pend_merge_storage_from_clear_status : forall sg s eid e tid old kind timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil -> old.(tcbFlagNode) = 0 ->
  task_non_suspension_bits old.(stat) = 0 ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  let post := event_pend_state sg s eid e tid old kind timeout in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_mark_waiter (event_image sg s.(TskState) e)
      (old.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) s.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) s.(TskState))
      (Z.shiftl 1 (old.(curPrio) mod 8)) (Z.shiftl 1 (old.(curPrio) / 8))) **
    event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s eid e tid old kind timeout Hvalid He Hold Hprio Hnull Hmulti Hflagnull
    Hnone Hkind Hunavailable Hnotowner post.
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hvalid; tauto. }
  assert (Hrow : 0 <= old.(curPrio) / 8 < 8).
  { destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    unfold valid_task_prio in Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hevent : post.(EventState) =
    update_event_field_raw s.(EventState) eid (event_insert_waiter sg s.(TskState) e tid)).
  { unfold post, event_pend_state, event_wait_state; cbn zeta.
    change (update_event_field_raw s.(EventState) eid
      (event_insert_waiter sg (glob_task_set_usedtask s.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid))) e tid) =
      update_event_field_raw s.(EventState) eid (event_insert_waiter sg s.(TskState) e tid)).
    rewrite (event_insert_waiter_update_task_eq sg s.(TskState) tid old
      (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid)) e tid Hold eq_refl).
    reflexivity. }
  sep_apply_l_atomic (event_insert_waiter_reconstructs_raw_rep
    sg s.(TskState) s.(EventState) eid e tid old Hold Hrow).
  rewrite <- Hevent.
  pose proof (event_pend_merge_from_clear_status sg s eid e tid old kind timeout
    Hvalid He Hold Hprio Hnull Hmulti Hflagnull Hnone Hkind Hunavailable Hnotowner) as Hmerge.
  cbv zeta in Hmerge.
  fold post in Hmerge.
  sep_apply_l_atomic Hmerge.
  fold post; entailer!.
Qed.
