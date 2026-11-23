Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_creator_stack_spec.
Import UCOS2_C_Rules EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Spatial ownership of the CURRENT ECB images in the existing private
    map. No second lifecycle state or ghost field is added. This predicate
    is an optional resource parameter of the source-established program /
    stack world; it is NOT added to UCOS2_inv, which deliberately excludes
    the bytes locally owned by an active creator.

    At a local initialization/borrow cut the whole map is split into one
    actual ECB and the missing map below. A parked/returned whole owner
    consumes both pieces exactly once. A pure eventPrivate lookup alone
    never produces this predicate. Queue QCBs and message buffers, Mutex
    priority leases, and application-local data have independent owners. *)
Definition event_private_pool_rep sg events : Assertion :=
  store_map (event_private_storage_rep sg) events.(eventLifecycle).(eventPrivate).

Definition event_private_pool_missing_eid sg events eid : Assertion :=
  store_map_missing_i (event_private_storage_rep sg) events.(eventLifecycle).(eventPrivate) eid.

Lemma event_private_pool_empty : forall sg events,
  (forall eid, events.(eventLifecycle).(eventPrivate) eid = None) ->
  event_private_pool_rep sg events --||-- emp.
Proof.
  intros; unfold event_private_pool_rep; apply store_map_empty.
  - exists []; split.
    + intros eid; split; [intros Hin; contradiction|intros [allocation Hget]; rewrite H in Hget; discriminate].
    + constructor.
  - intros eid; left; apply H.
Qed.

Lemma event_private_pool_split_eid : forall sg events eid allocation,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_private_pool_rep sg events |--
    event_private_storage_rep sg eid allocation ** event_private_pool_missing_eid sg events eid.
Proof.
  intros; unfold event_private_pool_rep, event_private_pool_missing_eid.
  sep_apply_l_atomic (store_map_split (event_private_storage_rep sg) eid allocation _ H); entailer!.
Qed.

Lemma event_private_pool_merge_eid : forall sg events eid allocation,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_private_storage_rep sg eid allocation ** event_private_pool_missing_eid sg events eid |--
    event_private_pool_rep sg events.
Proof.
  intros; unfold event_private_pool_rep, event_private_pool_missing_eid.
  sep_apply_l_atomic (store_map_merge (event_private_storage_rep sg) eid allocation _ H); entailer!.
Qed.

Lemma event_private_pool_missing_eid_equiv : forall sg before after eid,
  (forall other, other <> eid -> before.(eventLifecycle).(eventPrivate) other =
    after.(eventLifecycle).(eventPrivate) other) ->
  event_private_pool_missing_eid sg before eid --||-- event_private_pool_missing_eid sg after eid.
Proof. intros; unfold event_private_pool_missing_eid; apply store_map_missing_i_equiv; exact H. Qed.

Lemma event_private_pool_merge_updated_eid : forall sg before after eid allocation,
  after.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  (forall other, other <> eid -> before.(eventLifecycle).(eventPrivate) other =
    after.(eventLifecycle).(eventPrivate) other) ->
  event_private_storage_rep sg eid allocation ** event_private_pool_missing_eid sg before eid |--
    event_private_pool_rep sg after.
Proof.
  intros; rewrite (event_private_pool_missing_eid_equiv sg before after eid H0).
  apply event_private_pool_merge_eid; exact H.
Qed.

Lemma event_private_pool_remove_eid_equiv : forall sg before after eid,
  after.(eventLifecycle).(eventPrivate) eid = None ->
  (forall other, other <> eid -> before.(eventLifecycle).(eventPrivate) other =
    after.(eventLifecycle).(eventPrivate) other) ->
  event_private_pool_missing_eid sg before eid --||-- event_private_pool_rep sg after.
Proof.
  intros; rewrite (event_private_pool_missing_eid_equiv sg before after eid H0).
  unfold event_private_pool_missing_eid, event_private_pool_rep; split.
  - apply store_map_missing_equiv_store_map; exact H.
  - apply store_map_equiv_store_map_missing; exact H.
Qed.

Lemma event_private_pool_merge_added_eid : forall sg before after eid allocation,
  before.(eventLifecycle).(eventPrivate) eid = None ->
  after.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  (forall other, other <> eid -> before.(eventLifecycle).(eventPrivate) other =
    after.(eventLifecycle).(eventPrivate) other) ->
  event_private_storage_rep sg eid allocation ** event_private_pool_rep sg before |--
    event_private_pool_rep sg after.
Proof.
  intros sg before after eid allocation Hnone Hget Hframe.
  unfold event_private_pool_rep at 1.
  sep_apply_l_atomic (store_map_equiv_store_map_missing (event_private_storage_rep sg)
    before.(eventLifecycle).(eventPrivate) eid Hnone).
  fold (event_private_pool_missing_eid sg before eid).
  sep_apply_l_atomic (event_private_pool_merge_updated_eid sg before after eid allocation Hget Hframe); entailer!.
Qed.

(** Publication transfers the detached ECB to the ordinary Event owner.
    This theorem returns its private bytes separately; a concrete publish
    producer consumes them into the matching initialized public object. *)
Lemma event_private_pool_split_publish : forall sg events eid allocation node,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_private_pool_rep sg events |--
    event_private_storage_rep sg eid allocation ** event_private_pool_rep sg (event_publish events eid node).
Proof.
  intros; sep_apply_l_atomic (event_private_pool_split_eid sg events eid allocation H).
  rewrite (event_private_pool_remove_eid_equiv sg events (event_publish events eid node) eid).
  - entailer!.
  - cbn [event_publish eventLifecycle eventPrivate]; apply kernel_map_set_same.
  - intros; cbn [event_publish eventLifecycle eventPrivate]; symmetry; apply kernel_map_set_other; assumption.
Qed.

Lemma event_private_pool_merge_detached : forall sg events eid rest image allocation,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  (event_detach_head events eid rest image).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_private_storage_rep sg eid allocation ** event_private_pool_rep sg events |--
    event_private_pool_rep sg (event_detach_head events eid rest image).
Proof.
  intros; eapply event_private_pool_merge_added_eid; [exact H|exact H0|].
  intros; cbn [event_detach_head eventLifecycle eventPrivate]; symmetry; apply kernel_map_set_other; assumption.
Qed.

Lemma event_private_pool_merge_written : forall sg events eid allocation field stored updated,
  (event_private_write events eid allocation field stored).(eventLifecycle).(eventPrivate) eid = Some updated ->
  event_private_storage_rep sg eid updated ** event_private_pool_missing_eid sg events eid |--
    event_private_pool_rep sg (event_private_write events eid allocation field stored).
Proof.
  intros; eapply event_private_pool_merge_updated_eid; [exact H|].
  intros; cbn [event_private_write event_set_lifecycle eventLifecycle eventPrivate].
  symmetry; apply kernel_map_set_other; assumption.
Qed.

(** Loan from the source-established whole owner at THIS heap/cut.
    Current creator invocation/generation come from the real map entry.
    Neither the missing pool nor the local ECB is duplicated. *)
Lemma event_private_pool_stack_split : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active state eid allocation,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  kernel_stack_inv abi
    (fun sg state => resources sg state ** event_private_pool_rep sg state.(EventState)) sg active state |--
  kernel_stack_inv abi
    (fun sg state => resources sg state ** event_private_pool_missing_eid sg state.(EventState) eid)
    sg active state ** event_creator_private_rep sg eid allocation.(eventPrivateInvocation)
      allocation.(eventPrivateGeneration) state.
Proof.
  intros; unfold kernel_stack_inv; Intros.
  sep_apply_l_atomic (event_private_pool_split_eid sg state.(EventState) eid allocation H).
  sep_apply_l_atomic (event_creator_private_rep_from_allocation sg eid allocation state H); entailer!.
Qed.

Lemma event_private_pool_stack_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active state eid invocation generation,
  kernel_stack_inv abi
    (fun sg state => resources sg state ** event_private_pool_missing_eid sg state.(EventState) eid)
    sg active state ** event_creator_private_rep sg eid invocation generation state |--
  kernel_stack_inv abi
    (fun sg state => resources sg state ** event_private_pool_rep sg state.(EventState)) sg active state.
Proof.
  intros; unfold event_creator_private_rep; Intros allocation.
  assert (Hlookup : state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) by tauto.
  unfold kernel_stack_inv; Intros.
  sep_apply_l_atomic (event_private_pool_merge_eid sg state.(EventState) eid allocation Hlookup); entailer!.
Qed.

(** The local source has already established resources/current Task map
    at [after] and produced its updated ECB bytes. Only the other private
    entries are reindexed; this is not a cross-client frame assertion. *)
Lemma event_private_pool_stack_merge_updated : forall external platform port
  (abi : Armv7aContinuationABI external platform port) resources sg active before after eid invocation generation,
  (forall other, other <> eid -> before.(EventState).(eventLifecycle).(eventPrivate) other =
    after.(EventState).(eventLifecycle).(eventPrivate) other) ->
  kernel_stack_inv abi
    (fun sg state => resources sg state ** event_private_pool_missing_eid sg before.(EventState) eid)
    sg active after ** event_creator_private_rep sg eid invocation generation after |--
  kernel_stack_inv abi
    (fun sg state => resources sg state ** event_private_pool_rep sg state.(EventState)) sg active after.
Proof.
  intros; unfold kernel_stack_inv.
  rewrite (event_private_pool_missing_eid_equiv sg before.(EventState) after.(EventState) eid H).
  fold (kernel_stack_inv abi
    (fun sg state => resources sg state ** event_private_pool_missing_eid sg state.(EventState) eid)
    sg active after).
  apply event_private_pool_stack_merge.
Qed.
