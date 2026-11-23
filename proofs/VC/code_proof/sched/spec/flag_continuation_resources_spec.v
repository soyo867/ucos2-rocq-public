Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From AUXLib Require Import ListLib.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.flag_stack Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.kernel_names Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Concrete Flag node resources shared by wake callers and Scheduler.
    This module imports the already verified internal helper contracts;
    it does not import the new Scheduler instance or Del/Post APIs. *)
Module FlagPendSchedulerResources.

Lemma flag_task_rdy_preserves_stack_metadata : forall sg s p bits result schedule post,
  flag_task_rdy sg s p bits result = Some (schedule, post) ->
  post.(TskState).(parkedTaskStacks) = s.(TskState).(parkedTaskStacks) /\
  (forall slot node, post.(TskState).(inUsedTaskStates) slot = Some node ->
    exists old, s.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)).
Proof.
  intros sg s p bits result schedule post Hstep.
  destruct (flag_task_rdy_result sg s p bits result schedule post Hstep)
    as [w [after [old [Hunlink [Hold [Hpost Hschedule]]]]]].
  subst post; split; [reflexivity|].
  intros slot node Hnode.
  change ((if Z.eqb slot w.(flagTask) then Some (task_flag_wake old bits result)
    else s.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
  destruct (Z.eqb slot w.(flagTask)) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
    exists old; split; [exact Hold|]; split; reflexivity.
  - exists node; split; [exact Hnode|]; split; reflexivity.
Qed.

Lemma flag_task_rdy_preserves_invocation_active : forall sg s p bits result schedule post invocation origin,
  flag_task_rdy sg s p bits result = Some (schedule, post) ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active post.(TskState) invocation origin.
Proof.
  intros sg s p bits result schedule post invocation origin Hstep Hactive.
  destruct (flag_task_rdy_result sg s p bits result schedule post Hstep)
    as [w [after [old [Hunlink [Hold [Hpost Hschedule]]]]]].
  subst post.
  eapply glob_task_set_usedtask_preserves_invocation_active;
    [exact Hold|reflexivity|exact Hactive].
Qed.

(** Timeout keeps the node linked until Pend executes Unlink. At the actual
    post-store cleanup cut, return the node owner separately from the stable
    global state. This C resource rule does not demand a physical-SP proof. *)
Lemma flag_timeout_returns_node_and_global_resources : forall sg s p w flags old,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg s -> flag_unlink_node s.(FlagState) p = Some (w, flags) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  task_non_suspension_bits old.(stat) = 0 ->
  let post := flag_timeout_cleanup_state s w flags old in
  task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
    flag_groups_rep sg flags ** flag_unlink_neighbors_rep sg s.(FlagState) w **
    sg.(g_OSFlagFreeList) # Ptr |->
      (match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s |--
  UCOS2_inv sg post ** flag_node_return_loan sg.(osKernelConfig) w.
Proof.
  intros sg s p w flags old Henabled Hvalid Hstep Hold Hpending post.
  assert (Hflags : valid_flag_state sg s.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_flag_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  sep_apply_l_atomic (flag_unlink_reconstructs_raw_rep sg s.(FlagState) p w flags Hflags Hstep).
  pose proof (UCOS2_inv_merge_flag_timeout_cleanup sg s p w flags old Hvalid Hstep Hold Hpending) as Hmerge.
  cbn zeta in Hmerge; fold post in Hmerge.
  assert (Hflag_rep : flag_configured_rep sg post.(FlagState) = flag_raw_rep sg flags).
  { unfold post, flag_timeout_cleanup_state; cbn [replace_TskS replace_FlagS FlagState].
    unfold flag_configured_rep; rewrite Henabled; reflexivity. }
  rewrite Hflag_rep in Hmerge; sep_apply_l_atomic Hmerge; entailer!.
Qed.


Definition kernel_sched_saved_local_resource_at platform critical sg tasks call saved acquired
  (receipt : Assertion) (other : Armv7aContinuation -> Assertion)
  (descriptor : Armv7aContinuation) : Assertion :=
  if task_stack_key_eq_dec (task_stack_key descriptor.(armv7a_continuation_stack))
      (task_stack_key call.(os_sched_call_stack))
  then kernel_sched_saved_local platform critical sg tasks call saved acquired descriptor ** receipt
  else other descriptor.

Lemma kernel_sched_saved_local_resource_at_selected :
  forall platform critical sg tasks call saved acquired receipt other descriptor,
  descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack) ->
  kernel_sched_saved_local_resource_at platform critical sg tasks call saved acquired
    receipt other descriptor =
  kernel_sched_saved_local platform critical sg tasks call saved acquired descriptor ** receipt.
Proof.
  intros; unfold kernel_sched_saved_local_resource_at; rewrite H.
  destruct task_stack_key_eq_dec; [reflexivity|contradiction].
Qed.

(** A wake producer transfers its returned bytes into the already present
    Scheduler entry. Only the selected key gains [receipt]; all other entries
    and the physical stack map are preserved. The receipt is consumed once. *)
Lemma kernel_saved_continuation_map_add_sched_resource : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg source_tasks tasks
  original saved acquired receipt other stacks fragments,
  stacks (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (kernel_sched_saved_local_at platform critical sg source_tasks original saved acquired other)) stacks **
  receipt |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (kernel_sched_saved_local_resource_at platform critical sg source_tasks original saved acquired
        receipt other)) stacks.
Proof.
  intros external platform port abi critical sg source_tasks tasks original saved acquired
    receipt other stacks fragments Hentry.
  set (old_local := kernel_sched_saved_local_at platform critical sg source_tasks
    original saved acquired other).
  set (new_local := kernel_sched_saved_local_resource_at platform critical sg source_tasks
    original saved acquired receipt other).
  set (old_resource := kernel_saved_continuation_entry abi tasks old_local).
  set (new_resource := kernel_saved_continuation_entry abi tasks new_local).
  change (store_parked_continuations old_resource stacks ** receipt |--
    store_parked_continuations new_resource stacks).
  assert (Hrest : store_parked_continuations old_resource
      (task_stack_take stacks original.(os_sched_call_stack)) |--
    store_parked_continuations new_resource
      (task_stack_take stacks original.(os_sched_call_stack))).
  { unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
    intros key payload Hlookup.
    unfold old_resource, new_resource, kernel_saved_continuation_entry; Intros descriptor.
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = key) by tauto.
    assert (Hne : task_stack_key descriptor.(armv7a_continuation_stack) <>
      task_stack_key original.(os_sched_call_stack)).
    { intro Heq; rewrite Hkey in Heq; rewrite Heq, task_stack_take_lookup in Hlookup; discriminate. }
    Exists descriptor; unfold old_local, new_local,
      kernel_sched_saved_local_at, kernel_sched_saved_local_resource_at.
    destruct task_stack_key_eq_dec; [contradiction|entailer!]. }
  assert (Hselected : old_resource (task_stack_key original.(os_sched_call_stack))
      (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ** receipt |--
    new_resource (task_stack_key original.(os_sched_call_stack))
      (original.(os_sched_call_stack).(stackLeaseRegion), fragments)).
  { unfold old_resource, new_resource, kernel_saved_continuation_entry; Intros descriptor.
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) =
      task_stack_key original.(os_sched_call_stack)) by tauto.
    Exists descriptor; unfold old_local, new_local,
      kernel_sched_saved_local_at, kernel_sched_saved_local_resource_at.
    destruct task_stack_key_eq_dec; [entailer!|contradiction]. }
  sep_apply_l_atomic (store_parked_continuations_take old_resource stacks
    original.(os_sched_call_stack) fragments Hentry).
  sep_apply_l_atomic Hrest.
  sep_apply_l_atomic Hselected.
  sep_apply_l_atomic (store_parked_continuations_park new_resource
    (task_stack_take stacks original.(os_sched_call_stack)) original.(os_sched_call_stack)
    fragments (task_stack_take_lookup stacks original.(os_sched_call_stack))).
  assert (Hmap : forall key,
    task_stack_park_fragments (task_stack_take stacks original.(os_sched_call_stack))
      original.(os_sched_call_stack) fragments key = stacks key).
  { intros key; unfold task_stack_park_fragments, task_stack_take, field_update.
    destruct (task_stack_key_eq_dec key (task_stack_key original.(os_sched_call_stack)))
      as [Heq|Hne]; [subst key; symmetry; exact Hentry|reflexivity]. }
  unfold store_parked_continuations; apply (proj1 (store_map_equiv new_resource _ _ Hmap)).
Qed.

Lemma kernel_saved_continuation_resource_map_unfocus_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  critical sg source_tasks tasks original saved acquired receipt other stacks,
  stacks (task_stack_key original.(os_sched_call_stack)) = None ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (kernel_sched_saved_local_resource_at platform critical sg source_tasks original saved acquired
        receipt other)) stacks |--
  store_parked_continuations (kernel_saved_continuation_entry abi tasks other) stacks.
Proof.
  intros external platform port abi critical sg source_tasks tasks original saved acquired receipt other stacks Hnone.
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
  assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = key) by tauto.
  assert (Hne : task_stack_key descriptor.(armv7a_continuation_stack) <>
    task_stack_key original.(os_sched_call_stack)).
  { intro Heq; rewrite Hkey in Heq; rewrite Heq, Hnone in Hlookup; discriminate. }
  Exists descriptor; unfold kernel_sched_saved_local_resource_at.
  destruct task_stack_key_eq_dec; [contradiction|entailer!].
Qed.

Lemma flag_pend_wake_saved_continuation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg source_tasks saved_tasks
  original saved acquired other stacks fragments s p w old bits result returned,
  UCOS2_state_inv sg s ->
  flag_task_rdy_domain sg s p w old bits ->
  task_stack_key original.(os_sched_call_stack) = (w.(flagTask), w.(flagTaskGeneration)) ->
  stacks (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_task_rdy_post sg s p w bits result returned **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg s **
  store_parked_continuations
    (kernel_saved_continuation_entry abi saved_tasks
      (kernel_sched_saved_local_at platform critical sg source_tasks original saved acquired other)) stacks |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg s p bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi saved_tasks
         (kernel_sched_saved_local_resource_at platform critical sg source_tasks original saved acquired
           (flag_node_return_loan sg.(osKernelConfig) w) other)) stacks).
Proof.
  intros external platform port abi critical sg source_tasks saved_tasks original saved acquired
    other stacks fragments s p w old bits result returned Hvalid Hdomain Hwaiter Hentry.
  sep_apply_l_atomic (flag_task_rdy_stable_merge sg s p w old bits result returned Hvalid Hdomain).
  Intros post schedule.
  sep_apply_l_atomic (kernel_saved_continuation_map_add_sched_resource external platform port abi
    critical sg source_tasks saved_tasks original saved acquired
    (flag_node_return_loan sg.(osKernelConfig) w) other stacks fragments Hentry).
  Exists post schedule; entailer!.
Qed.

(** Reindex the same owned entries after an actual wake. The frame's SP and
    generation come from the actual Task updater, and the saved invocation
    remains active by that updater's existing lifecycle rule. *)
Lemma flag_pend_wake_reindex_saved_continuations : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired receipt
  other stacks s p bits result schedule post,
  flag_task_rdy sg s p bits result = Some (schedule, post) ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi s.(TskState)
      (kernel_sched_saved_local_resource_at platform critical sg s.(TskState) original saved acquired
        receipt other)) stacks |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi post.(TskState)
      (kernel_sched_saved_local_resource_at platform critical sg post.(TskState) original saved acquired
        receipt other)) stacks.
Proof.
  intros external platform port abi critical sg original saved acquired receipt other stacks
    s p bits result schedule post Hstep.
  destruct (flag_task_rdy_preserves_stack_metadata sg s p bits result schedule post Hstep)
    as [Hstacks Hfields].
  assert (Hmetadata : forall key payload node, stacks key = Some payload ->
    post.(TskState).(inUsedTaskStates) (fst key) = Some node ->
    node.(taskGeneration) = snd key ->
    exists old, s.(TskState).(inUsedTaskStates) (fst key) = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros key payload node Hlookup Hnode Hgen; apply Hfields; exact Hnode. }
  sep_apply_l_atomic (kernel_saved_continuation_map_reindex external platform port abi
    s.(TskState) post.(TskState)
    (kernel_sched_saved_local_resource_at platform critical sg s.(TskState) original saved acquired
      receipt other) stacks Hmetadata).
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
  Exists descriptor; unfold kernel_sched_saved_local_resource_at.
  destruct task_stack_key_eq_dec.
  - unfold kernel_sched_saved_local; Intros.
    assert (Hactive : task_invocation_active post.(TskState)
      original.(os_sched_call_invocation) original.(os_sched_call_origin)).
    { eapply flag_task_rdy_preserves_invocation_active; [exact Hstep|tauto]. }
    entailer!; tauto.
  - entailer!.
Qed.

Lemma flag_pend_wake_current_continuation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired other
  fragments s p w old bits result returned,
  UCOS2_state_inv sg s ->
  flag_task_rdy_domain sg s p w old bits ->
  task_stack_key original.(os_sched_call_stack) = (w.(flagTask), w.(flagTaskGeneration)) ->
  s.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_task_rdy_post sg s p w bits result returned **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg s **
  store_parked_continuations
    (kernel_saved_continuation_entry abi s.(TskState)
      (kernel_sched_saved_local_at platform critical sg s.(TskState) original saved acquired other))
    s.(TskState).(parkedTaskStacks) |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg s p bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi post.(TskState)
         (kernel_sched_saved_local_resource_at platform critical sg post.(TskState) original saved acquired
           (flag_node_return_loan sg.(osKernelConfig) w) other)) post.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi critical sg original saved acquired other fragments s p w old
    bits result returned Hvalid Hdomain Hwaiter Hentry.
  sep_apply_l_atomic (flag_pend_wake_saved_continuation_resources external platform port abi critical
    sg s.(TskState) s.(TskState) original saved acquired other s.(TskState).(parkedTaskStacks)
    fragments s p w old bits result returned Hvalid Hdomain Hwaiter Hentry).
  Intros post schedule.
  assert (Hstep : flag_task_rdy sg s p bits result = Some (schedule, post)) by tauto.
  pose proof (proj1 (flag_task_rdy_preserves_stack_metadata sg s p bits result schedule post Hstep))
    as Hstacks.
  sep_apply_l_atomic (flag_pend_wake_reindex_saved_continuations external platform port abi critical
    sg original saved acquired (flag_node_return_loan sg.(osKernelConfig) w) other
    s.(TskState).(parkedTaskStacks) s p bits result schedule post Hstep).
  Exists post schedule; rewrite Hstacks; entailer!.
Qed.



End FlagPendSchedulerResources.

(** A linked node is already owned by the global Flag representation. Once
    unlinked, its complete image belongs to this invocation. The image is
    existential: intervening list insertions may have changed Next/Prev. *)
Definition flag_pend_sched_node_rep (sg : StableGlobVars) (node : addr)
  (state : UCOS2_Verify_State) : Assertion :=
  match state.(FlagState).(flagWaitNodes) node with
  | Some _ => emp
  | None => EX image, flag_node_rep sg.(osKernelConfig) node image
  end.

Definition flag_pend_sched_waiter_binding (call : OsSchedCallContext) (node : addr)
  (state : UCOS2_Verify_State) : Prop :=
  forall waiter, state.(FlagState).(flagWaitNodes) node = Some waiter ->
    waiter.(flagNodeAddr) = node /\
    task_stack_key call.(os_sched_call_stack) =
      (waiter.(flagTask), waiter.(flagTaskGeneration)).

Lemma flag_pend_sched_node_rep_linked : forall sg node state waiter,
  state.(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_pend_sched_node_rep sg node state = emp.
Proof. intros; unfold flag_pend_sched_node_rep; rewrite H; reflexivity. Qed.

Lemma flag_pend_sched_node_rep_from_loan : forall sg node state waiter,
  state.(FlagState).(flagWaitNodes) node = None -> waiter.(flagNodeAddr) = node ->
  flag_node_return_loan sg.(osKernelConfig) waiter |--
  flag_pend_sched_node_rep sg node state.
Proof.
  intros sg node state waiter Hnone Hnode.
  unfold flag_pend_sched_node_rep; rewrite Hnone.
  Exists waiter.(flagWaitImage); unfold flag_node_return_loan; rewrite Hnode; entailer!.
Qed.

Lemma flag_pend_sched_node_rep_prefix : forall sg node state,
  flag_pend_sched_node_rep sg node (os_sched_prefix_state state) =
  flag_pend_sched_node_rep sg node state.
Proof. reflexivity. Qed.

Lemma flag_pend_sched_waiter_binding_prefix : forall call node state,
  flag_pend_sched_waiter_binding call node (os_sched_prefix_state state) <->
  flag_pend_sched_waiter_binding call node state.
Proof. reflexivity. Qed.

Lemma flag_pend_sched_wake_unlinks_node : forall sg state node bits result schedule post,
  flag_task_rdy sg state node bits result = Some (schedule, post) ->
  post.(FlagState).(flagWaitNodes) node = None.
Proof.
  intros sg state node bits result schedule post Hstep.
  destruct (flag_task_rdy_result sg state node bits result schedule post Hstep)
    as [waiter [flags [old [Hunlink [Hold [Hpost Hschedule]]]]]].
  subst post; change (flags.(flagWaitNodes) node = None).
  exact (proj2 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)).
Qed.

(** This consequence consumes the real helper's post and its retained
    global residual. It neither infers a loan from absence nor assumes an
    eventual wake. Both source BOOLEAN results are covered. *)
Lemma flag_pend_sched_wake_returns_node : forall sg state node waiter old bits result returned,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  waiter.(flagNodeAddr) = node ->
  flag_task_rdy_post sg state node waiter bits result returned **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg state |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg state node bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_inv sg post ** flag_pend_sched_node_rep sg node post).
Proof.
  intros sg state node waiter old bits result returned Hvalid Hdomain Hnode.
  sep_apply_l_atomic (flag_task_rdy_stable_merge sg state node waiter old bits result returned
    Hvalid Hdomain).
  Intros post schedule.
  assert (Hnone : post.(FlagState).(flagWaitNodes) node = None).
  { apply (flag_pend_sched_wake_unlinks_node sg state node bits result schedule post); tauto. }
  sep_apply_l_atomic (flag_pend_sched_node_rep_from_loan sg node post waiter Hnone Hnode).
  Exists post schedule; entailer!.
Qed.


Definition flag_pend_sched_saved_map external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg
  original saved acquired node other state : Assertion :=
  store_parked_continuations
    (kernel_saved_continuation_entry abi state.(TskState)
      (FlagPendSchedulerResources.kernel_sched_saved_local_resource_at platform critical sg
        state.(TskState) original saved acquired (flag_pend_sched_node_rep sg node state) other))
    state.(TskState).(parkedTaskStacks).

Lemma flag_pend_sched_saved_map_receipt_mono : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg source_tasks tasks
  original saved acquired other stacks first second,
  first |-- second ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (FlagPendSchedulerResources.kernel_sched_saved_local_resource_at platform critical sg
        source_tasks original saved acquired first other)) stacks |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (FlagPendSchedulerResources.kernel_sched_saved_local_resource_at platform critical sg
        source_tasks original saved acquired second other)) stacks.
Proof.
  intros external platform port abi critical sg source_tasks tasks original saved acquired
    other stacks first second Hreceipt.
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
  Exists descriptor; unfold FlagPendSchedulerResources.kernel_sched_saved_local_resource_at.
  destruct task_stack_key_eq_dec; [sep_apply_l_atomic Hreceipt; entailer!|entailer!].
Qed.

Lemma flag_pend_sched_saved_map_linked : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired
  node other state waiter,
  state.(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other state |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi state.(TskState)
      (kernel_sched_saved_local_at platform critical sg state.(TskState)
        original saved acquired other)) state.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi critical sg original saved acquired node other state waiter Hlinked.
  unfold flag_pend_sched_saved_map; rewrite (flag_pend_sched_node_rep_linked sg node state waiter Hlinked).
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
  Exists descriptor; unfold FlagPendSchedulerResources.kernel_sched_saved_local_resource_at,
    kernel_sched_saved_local_at.
  destruct task_stack_key_eq_dec; entailer!.
Qed.

Lemma flag_pend_sched_wake_saved_map : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired
  node other fragments state waiter old bits result returned,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  task_stack_key original.(os_sched_call_stack) = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_task_rdy_post sg state node waiter bits result returned **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
    flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other state |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg state node bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_inv sg post **
     flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other post).
Proof.
  intros external platform port abi critical sg original saved acquired node other fragments state waiter
    old bits result returned Hvalid Hdomain Hkey Hentry.
  assert (Hlinked : state.(FlagState).(flagWaitNodes) node = Some waiter).
  { unfold flag_task_rdy_domain, flag_unlink_domain in Hdomain; tauto. }
  assert (Hnode : waiter.(flagNodeAddr) = node).
  { unfold flag_task_rdy_domain, flag_unlink_domain in Hdomain; tauto. }
  sep_apply_l_atomic (flag_pend_sched_saved_map_linked external platform port abi critical sg
    original saved acquired node other state waiter Hlinked).
  sep_apply_l_atomic (FlagPendSchedulerResources.flag_pend_wake_current_continuation_resources
    external platform port abi critical sg original saved acquired other fragments state node waiter old
    bits result returned Hvalid Hdomain Hkey Hentry).
  Intros post schedule.
  assert (Hnone : post.(FlagState).(flagWaitNodes) node = None).
  { apply (flag_pend_sched_wake_unlinks_node sg state node bits result schedule post); tauto. }
  assert (Hreceipt : flag_node_return_loan sg.(osKernelConfig) waiter |--
    flag_pend_sched_node_rep sg node post).
  { apply flag_pend_sched_node_rep_from_loan; assumption. }
  sep_apply_l_atomic (flag_pend_sched_saved_map_receipt_mono external platform port abi critical sg
    post.(TskState) post.(TskState) original saved acquired other post.(TskState).(parkedTaskStacks)
    _ _ Hreceipt).
  Exists post schedule; unfold flag_pend_sched_saved_map; entailer!.
Qed.

(** This relation is exactly the framed, already verified OS_FlagTaskRdy
    call contract. It is a modular C call boundary, not a new resource
    guarantee for Scheduler or a choice of a desired returned heap. The
    caller establishes its actual pre and receives the helper's actual post. *)
Definition flag_pend_sched_task_rdy_call sg node bits result returned (before after : model) : Prop :=
  forall state waiter old (frame : Assertion),
    (flag_task_rdy_pre sg state node waiter old bits ** frame) before ->
    (flag_task_rdy_post sg state node waiter bits result returned ** frame) after.

Lemma flag_pend_sched_task_rdy_call_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired
  node other fragments state waiter bits result returned before after (frame : Assertion),
  sg.(osKernelConfig) = selected_kernel_configuration -> flag_unlink_layout ->
  0 <= bits < 65536 -> state.(FlagState).(flagWaitNodes) node = Some waiter ->
  task_stack_key original.(os_sched_call_stack) = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_task_rdy_call sg node bits result returned before after ->
  (kernel_program_inv sg state **
    flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other state ** frame) before ->
  exists post schedule,
    flag_task_rdy sg state node bits result = Some (schedule, post) /\
    returned = (if schedule then 1 else 0) /\
    (kernel_program_inv sg post **
      flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other post ** frame) after.
Proof.
  intros external platform port abi critical sg original saved acquired node other fragments state waiter
    bits result returned before after frame Hcfg Hlayout Hbits Hlinked Hkey Hentry Hcall Hpre.
  assert (Hsplit : kernel_program_inv sg state **
      flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other state ** frame |--
    EX old, coq_prop (UCOS2_state_inv sg state /\ flag_task_rdy_domain sg state node waiter old bits) &&
      (flag_task_rdy_pre sg state node waiter old bits **
       (UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
        flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other state **
        unmap_table_rep sg ** frame))).
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (flag_task_rdy_stable_split sg state node waiter bits Hcfg Hlayout Hbits Hlinked).
    Intros old; Exists old; unfold flag_task_rdy_pre; entailer!. }
  destruct (Hsplit before Hpre) as [old [[Hvalid Hdomain] Howned]].
  pose proof (Hcall state waiter old _ Howned) as Hpost.
  assert (Hmerge : flag_task_rdy_post sg state node waiter bits result returned **
      (UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
       flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other state **
       unmap_table_rep sg ** frame) |--
    EX post, EX schedule,
      coq_prop (flag_task_rdy sg state node bits result = Some (schedule, post) /\
        returned = (if schedule then 1 else 0)) &&
      (kernel_program_inv sg post **
       flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other post ** frame)).
  { sep_apply_l_atomic (flag_pend_sched_wake_saved_map external platform port abi critical sg
      original saved acquired node other fragments state waiter old bits result returned Hvalid Hdomain Hkey Hentry).
    Intros post schedule; Exists post schedule; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hmerge after Hpost) as [post [schedule [[Hstep Hreturned] Howned_after]]].
  exists post, schedule; split; [exact Hstep|]; split; assumption.
Qed.


(** Attach only the concrete node owner to the source's existing local.
    Scheduler and IRQ descriptors keep their distinct original predicates.
    This construction imposes no PC, CPSR or Save-token condition. *)
Definition flag_continuation_local_node (original : TaskStackLease)
  (receipt : Assertion) (local : Armv7aContinuation -> Assertion)
  (descriptor : Armv7aContinuation) : Assertion :=
  if task_stack_key_eq_dec (task_stack_key descriptor.(armv7a_continuation_stack))
      (task_stack_key original)
  then local descriptor ** receipt
  else local descriptor.

Lemma flag_continuation_local_node_selected : forall original receipt local descriptor,
  descriptor.(armv7a_continuation_stack) = original ->
  flag_continuation_local_node original receipt local descriptor = local descriptor ** receipt.
Proof.
  intros; unfold flag_continuation_local_node; rewrite H.
  destruct task_stack_key_eq_dec; [reflexivity|contradiction].
Qed.

Lemma flag_continuation_map_node_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks original receipt local stacks,
  stacks (task_stack_key original) = None ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) stacks --||--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (flag_continuation_local_node original receipt local)) stacks.
Proof.
  intros external platform port abi tasks original receipt local stacks Hnone; split;
    unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono;
    intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor;
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = key) by tauto;
    assert (Hne : task_stack_key descriptor.(armv7a_continuation_stack) <> task_stack_key original)
      by (intro Heq; rewrite Hkey in Heq; rewrite Heq, Hnone in Hlookup; discriminate);
    Exists descriptor; unfold flag_continuation_local_node;
    destruct task_stack_key_eq_dec; try contradiction; entailer!.
Qed.

Lemma flag_continuation_map_publish_node : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks original receipt local stacks fragments,
  stacks (task_stack_key original) = Some (original.(stackLeaseRegion), fragments) ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) stacks ** receipt |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (flag_continuation_local_node original receipt local)) stacks.
Proof.
  intros external platform port abi tasks original receipt local stacks fragments Hentry.
  set (old_resource := kernel_saved_continuation_entry abi tasks local).
  set (new_resource := kernel_saved_continuation_entry abi tasks
    (flag_continuation_local_node original receipt local)).
  change (store_parked_continuations old_resource stacks ** receipt |--
    store_parked_continuations new_resource stacks).
  assert (Hrest : store_parked_continuations old_resource (task_stack_take stacks original) |--
    store_parked_continuations new_resource (task_stack_take stacks original)).
  { apply (proj1 (flag_continuation_map_node_absent external platform port abi tasks original
      receipt local (task_stack_take stacks original) (task_stack_take_lookup stacks original))). }
  assert (Hselected : old_resource (task_stack_key original) (original.(stackLeaseRegion), fragments) ** receipt |--
    new_resource (task_stack_key original) (original.(stackLeaseRegion), fragments)).
  { unfold old_resource, new_resource, kernel_saved_continuation_entry; Intros descriptor.
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = task_stack_key original) by tauto.
    Exists descriptor; unfold flag_continuation_local_node.
    destruct task_stack_key_eq_dec; [entailer!|contradiction]. }
  sep_apply_l_atomic (store_parked_continuations_take old_resource stacks original fragments Hentry).
  sep_apply_l_atomic Hrest; sep_apply_l_atomic Hselected.
  sep_apply_l_atomic (store_parked_continuations_park new_resource (task_stack_take stacks original)
    original fragments (task_stack_take_lookup stacks original)).
  assert (Hmap : forall key,
    task_stack_park_fragments (task_stack_take stacks original) original fragments key = stacks key).
  { intros key; unfold task_stack_park_fragments, task_stack_take, field_update.
    destruct (task_stack_key_eq_dec key (task_stack_key original)) as [Heq|Hne];
      [subst key; symmetry; exact Hentry|reflexivity]. }
  unfold store_parked_continuations; apply (proj1 (store_map_equiv new_resource _ _ Hmap)).
Qed.

(** OS_FlagTaskRdy has returned, but its Del/Post caller may still read
    Next. Keep the actual loan outside the capsule until that read ends.
    The source-established local itself is retained; only the live TCB
    indexing is transported through the concrete wake transformer. *)
Lemma flag_wake_returns_node_with_continuation_map : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state node waiter old bits result returned local,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  flag_task_rdy_post sg state node waiter bits result returned **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg state node bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_inv sg post ** flag_node_return_loan sg.(osKernelConfig) waiter **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg state node waiter old bits result returned local Hvalid Hdomain.
  sep_apply_l_atomic (flag_task_rdy_stable_merge sg state node waiter old bits result returned Hvalid Hdomain).
  Intros post schedule.
  assert (Hstep : flag_task_rdy sg state node bits result = Some (schedule, post)) by tauto.
  destruct (FlagPendSchedulerResources.flag_task_rdy_preserves_stack_metadata
    sg state node bits result schedule post Hstep) as [Hstacks Hfields].
  assert (Hmetadata : forall key payload task,
    state.(TskState).(parkedTaskStacks) key = Some payload ->
    post.(TskState).(inUsedTaskStates) (fst key) = Some task -> task.(taskGeneration) = snd key ->
    exists previous, state.(TskState).(inUsedTaskStates) (fst key) = Some previous /\
      previous.(taskGeneration) = task.(taskGeneration) /\ previous.(tcbStkPtr) = task.(tcbStkPtr)).
  { intros key payload task Hlookup Htask Hgen; apply Hfields; exact Htask. }
  sep_apply_l_atomic (kernel_saved_continuation_map_reindex external platform port abi state.(TskState)
    post.(TskState) local state.(TskState).(parkedTaskStacks) Hmetadata).
  Exists post schedule; rewrite Hstacks; entailer!.
Qed.

(** After the caller's actual Next read and image reassembly, the same
    loan is deposited into the already present originating entry. The
    extra resource may be attached to a Scheduler local or an IRQ local. *)
Lemma flag_wake_publish_returned_node : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg post node waiter original local fragments,
  waiter.(flagNodeAddr) = node -> post.(FlagState).(flagWaitNodes) node = None ->
  task_stack_key original = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  post.(TskState).(parkedTaskStacks) (task_stack_key original) = Some (original.(stackLeaseRegion), fragments) ->
  flag_node_return_loan sg.(osKernelConfig) waiter **
    store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
      post.(TskState).(parkedTaskStacks) |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi post.(TskState)
      (flag_continuation_local_node original (flag_pend_sched_node_rep sg node post) local))
    post.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg post node waiter original local fragments Hnode Hnone Hkey Hentry.
  sep_apply_l_atomic (flag_pend_sched_node_rep_from_loan sg node post waiter Hnone Hnode).
  sep_apply_l_atomic (flag_continuation_map_publish_node external platform port abi post.(TskState)
    original (flag_pend_sched_node_rep sg node post) local post.(TskState).(parkedTaskStacks) fragments Hentry).
  entailer!.
Qed.

Lemma flag_continuation_map_take_node : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks original receipt local stacks fragments,
  stacks (task_stack_key original) = Some (original.(stackLeaseRegion), fragments) ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (flag_continuation_local_node original receipt local)) stacks |--
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) stacks ** receipt.
Proof.
  intros external platform port abi tasks original receipt local stacks fragments Hentry.
  set (old_resource := kernel_saved_continuation_entry abi tasks local).
  set (new_resource := kernel_saved_continuation_entry abi tasks
    (flag_continuation_local_node original receipt local)).
  change (store_parked_continuations new_resource stacks |--
    store_parked_continuations old_resource stacks ** receipt).
  assert (Hrest : store_parked_continuations new_resource (task_stack_take stacks original) |--
    store_parked_continuations old_resource (task_stack_take stacks original)).
  { apply (proj2 (flag_continuation_map_node_absent external platform port abi tasks original
      receipt local (task_stack_take stacks original) (task_stack_take_lookup stacks original))). }
  assert (Hselected : new_resource (task_stack_key original) (original.(stackLeaseRegion), fragments) |--
    old_resource (task_stack_key original) (original.(stackLeaseRegion), fragments) ** receipt).
  { unfold old_resource, new_resource, kernel_saved_continuation_entry; Intros descriptor.
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = task_stack_key original) by tauto.
    unfold flag_continuation_local_node.
    destruct task_stack_key_eq_dec; [Exists descriptor; entailer!|contradiction]. }
  sep_apply_l_atomic (store_parked_continuations_take new_resource stacks original fragments Hentry).
  sep_apply_l_atomic Hrest; sep_apply_l_atomic Hselected.
  sep_apply_l_atomic (store_parked_continuations_park old_resource (task_stack_take stacks original)
    original fragments (task_stack_take_lookup stacks original)).
  assert (Hmap : forall key,
    task_stack_park_fragments (task_stack_take stacks original) original fragments key = stacks key).
  { intros key; unfold task_stack_park_fragments, task_stack_take, field_update.
    destruct (task_stack_key_eq_dec key (task_stack_key original)) as [Heq|Hne];
      [subst key; symmetry; exact Hentry|reflexivity]. }
  pose proof (proj1 (store_map_equiv old_resource _ _ Hmap)) as Hmap_owned.
  unfold store_parked_continuations in *; sep_apply_l_atomic Hmap_owned; entailer!.
Qed.

Lemma flag_node_return_loan_split_next : forall sg waiter,
  flag_node_return_loan sg.(osKernelConfig) waiter |--
  waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
    flag_node_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage).
Proof. intros; unfold flag_node_return_loan; apply flag_node_rep_split_next. Qed.

Lemma flag_node_return_loan_merge_next : forall sg waiter,
  waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
    flag_node_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage) |--
  flag_node_return_loan sg.(osKernelConfig) waiter.
Proof. intros; unfold flag_node_return_loan, flag_node_rep_without_next, flag_node_rep; entailer!. Qed.

(** A Del/Post scan may wake another waiter first. Link fields can change,
    while the originating node address and task generation remain the same.
    These facts come from the actual unlink transformer. *)
Lemma flag_pend_sched_waiter_binding_wake : forall sg state wake_node bits result schedule post call node,
  flag_task_rdy sg state wake_node bits result = Some (schedule, post) ->
  flag_pend_sched_waiter_binding call node state ->
  flag_pend_sched_waiter_binding call node post.
Proof.
  intros sg state wake_node bits result schedule post call node Hstep Hbinding waiter Hlookup.
  destruct (flag_task_rdy_result sg state wake_node bits result schedule post Hstep)
    as [removed [flags [old [Hunlink [Hold [Hpost Hschedule]]]]]].
  subst post; change (flags.(flagWaitNodes) node = Some waiter) in Hlookup.
  destruct (flag_unlink_surviving_node_origin state.(FlagState) wake_node removed flags
    node waiter Hunlink Hlookup) as [Hne [previous [Hprevious Hidentity]]].
  destruct (Hbinding previous Hprevious) as [Hnode Hkey].
  unfold flag_waiter_link_identity in Hidentity; inversion Hidentity; split; congruence.
Qed.

Lemma flag_pend_sched_node_rep_other_wake : forall sg state wake_node bits result schedule post node,
  flag_task_rdy sg state wake_node bits result = Some (schedule, post) -> node <> wake_node ->
  flag_pend_sched_node_rep sg node post = flag_pend_sched_node_rep sg node state.
Proof.
  intros sg state wake_node bits result schedule post node Hstep Hne.
  destruct (flag_task_rdy_result sg state wake_node bits result schedule post Hstep)
    as [removed [flags [old [Hunlink [Hold [Hpost Hschedule]]]]]].
  subst post.
  pose proof (flag_unlink_frames_waiter_identity state.(FlagState) wake_node removed flags
    node Hunlink Hne) as Hidentity.
  unfold flag_pend_sched_node_rep; change
    ((match flags.(flagWaitNodes) node with Some _ => emp | None => EX image,
        flag_node_rep sg.(osKernelConfig) node image end) =
     (match state.(FlagState).(flagWaitNodes) node with Some _ => emp | None => EX image,
        flag_node_rep sg.(osKernelConfig) node image end)).
  destruct (flags.(flagWaitNodes) node), (state.(FlagState).(flagWaitNodes) node);
    cbn in Hidentity; try discriminate; reflexivity.
Qed.

Lemma flag_pend_sched_other_wake_saved_map : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired node other
  state wake_node bits result schedule post,
  flag_task_rdy sg state wake_node bits result = Some (schedule, post) -> node <> wake_node ->
  flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other state |--
  flag_pend_sched_saved_map external platform port abi critical sg original saved acquired node other post.
Proof.
  intros external platform port abi critical sg original saved acquired node other state wake_node
    bits result schedule post Hstep Hne.
  destruct (FlagPendSchedulerResources.flag_task_rdy_preserves_stack_metadata
    sg state wake_node bits result schedule post Hstep) as [Hstacks Hfields].
  unfold flag_pend_sched_saved_map.
  rewrite (flag_pend_sched_node_rep_other_wake sg state wake_node bits result schedule post node Hstep Hne), Hstacks.
  apply (FlagPendSchedulerResources.flag_pend_wake_reindex_saved_continuations external platform port abi
    critical sg original saved acquired (flag_pend_sched_node_rep sg node state) other
    state.(TskState).(parkedTaskStacks) state wake_node bits result schedule post Hstep).
Qed.
