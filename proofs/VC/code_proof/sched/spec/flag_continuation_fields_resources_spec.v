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
Require Export Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_task_rdy_fields_spec.
Require Import Ucos2Verify.lib.flag_node_fields Ucos2Verify.lib.flag_fields_resources.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


(** Six-field continuation receipts for the actual protected Flag helper cuts.
    Existing pure transitions, task/stack metadata, key/entry protocols and
    generic arbitrary-receipt publication/take lemmas are reused unchanged.
    An unlinked receipt contains real field ownership; absence alone gives none.
    Supplemental padding remains separately owned by the caller's frame. *)

Definition flag_pend_sched_node_fields_rep (sg : StableGlobVars) (node : addr)
  (state : UCOS2_Verify_State) : Assertion :=
  match state.(FlagState).(flagWaitNodes) node with
  | Some _ => emp
  | None => EX image, flag_node_fields_rep sg.(osKernelConfig) node image
  end.

Lemma flag_pend_sched_node_fields_rep_linked : forall sg node state waiter,
  state.(FlagState).(flagWaitNodes) node = Some waiter ->
  flag_pend_sched_node_fields_rep sg node state = emp.
Proof. intros; unfold flag_pend_sched_node_fields_rep; rewrite H; reflexivity. Qed.

Lemma flag_pend_sched_node_fields_rep_from_loan : forall sg node state waiter,
  state.(FlagState).(flagWaitNodes) node = None -> waiter.(flagNodeAddr) = node ->
  flag_node_fields_return_loan sg.(osKernelConfig) waiter |--
  flag_pend_sched_node_fields_rep sg node state.
Proof.
  intros sg node state waiter Hnone Hnode.
  unfold flag_pend_sched_node_fields_rep; rewrite Hnone.
  Exists waiter.(flagWaitImage); unfold flag_node_fields_return_loan; rewrite Hnode; entailer!.
Qed.

Lemma flag_pend_sched_node_fields_rep_prefix : forall sg node state,
  flag_pend_sched_node_fields_rep sg node (os_sched_prefix_state state) =
  flag_pend_sched_node_fields_rep sg node state.
Proof. reflexivity. Qed.

(** The actual timeout Unlink stores return the six fields and restore the
    same pure global invariant. No physical-SP or local-allocation fact is added. *)

Lemma flag_timeout_fields_returns_node_and_global_resources : forall sg s p w flags old,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg s -> flag_unlink_node s.(FlagState) p = Some (w, flags) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  task_non_suspension_bits old.(stat) = 0 ->
  let post := flag_timeout_cleanup_state s w flags old in
  task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
    flag_groups_rep sg flags ** flag_unlink_fields_neighbors_rep sg s.(FlagState) w **
    sg.(g_OSFlagFreeList) # Ptr |->
      (match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s |--
  UCOS2_fields_inv sg post ** flag_node_fields_return_loan sg.(osKernelConfig) w.
Proof.
  intros sg s p w flags old Henabled Hvalid Hstep Hold Hpending post.
  assert (Hflags : valid_flag_state sg s.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_flag_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  sep_apply_l_atomic (flag_unlink_fields_reconstructs_raw_rep sg s.(FlagState) p w flags Hflags Hstep).
  pose proof (UCOS2_fields_inv_merge_flag_timeout_cleanup sg s p w flags old Hvalid Hstep Hold Hpending) as Hmerge.
  cbn zeta in Hmerge; fold post in Hmerge.
  assert (Hflag_rep : flag_fields_configured_rep sg post.(FlagState) = flag_fields_raw_rep sg flags).
  { unfold post, flag_timeout_cleanup_state; cbn [replace_TskS replace_FlagS FlagState].
    unfold flag_fields_configured_rep; rewrite Henabled; reflexivity. }
  rewrite Hflag_rep in Hmerge; sep_apply_l_atomic Hmerge; entailer!.
Qed.

(** Exactly the framed fields C helper pre/post relation. It preserves the
    original state, waiter, old-task and arbitrary-frame quantification. *)

Definition flag_pend_sched_fields_task_rdy_call sg node bits result returned (before after : model) : Prop :=
  forall state waiter old (frame : Assertion),
    (flag_task_rdy_fields_pre sg state node waiter old bits ** frame) before ->
    (flag_task_rdy_fields_post sg state node waiter bits result returned ** frame) after.

(** Keep the real returned loan outside the map until the source's Next read
    and assignment finish. Reindex only through the existing wake metadata rule. *)

Lemma flag_wake_fields_returns_node_with_continuation_map : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state node waiter old bits result returned local,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  flag_task_rdy_fields_post sg state node waiter bits result returned **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg state node bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_fields_inv sg post ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg state node waiter old bits result returned local Hvalid Hdomain.
  sep_apply_l_atomic (flag_task_rdy_fields_stable_merge sg state node waiter old bits result returned Hvalid Hdomain).
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

Lemma flag_node_fields_return_loan_split_next : forall sg waiter,
  flag_node_fields_return_loan sg.(osKernelConfig) waiter |--
  waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
    flag_node_fields_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage).
Proof. intros; unfold flag_node_fields_return_loan; apply flag_node_fields_rep_split_next. Qed.

Lemma flag_node_fields_return_loan_merge_next : forall sg waiter,
  waiter.(flagNodeAddr) # Ptr |-> waiter.(flagWaitImage).(flagNodeNext) **
    flag_node_fields_rep_without_next sg.(osKernelConfig) waiter.(flagNodeAddr) waiter.(flagWaitImage) |--
  flag_node_fields_return_loan sg.(osKernelConfig) waiter.
Proof. intros; unfold flag_node_fields_return_loan, flag_node_fields_rep_without_next, flag_node_fields_rep; entailer!. Qed.

(** Deposit the reassembled fields into the already present originating entry.
    Scheduler/IRQ locals and original key/entry hypotheses are unchanged. *)

Lemma flag_wake_fields_publish_returned_node : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg post node waiter original local fragments,
  waiter.(flagNodeAddr) = node -> post.(FlagState).(flagWaitNodes) node = None ->
  task_stack_key original = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  post.(TskState).(parkedTaskStacks) (task_stack_key original) = Some (original.(stackLeaseRegion), fragments) ->
  flag_node_fields_return_loan sg.(osKernelConfig) waiter **
    store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
      post.(TskState).(parkedTaskStacks) |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi post.(TskState)
      (flag_continuation_local_node original (flag_pend_sched_node_fields_rep sg node post) local))
    post.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg post node waiter original local fragments Hnode Hnone Hkey Hentry.
  sep_apply_l_atomic (flag_pend_sched_node_fields_rep_from_loan sg node post waiter Hnone Hnode).
  sep_apply_l_atomic (flag_continuation_map_publish_node external platform port abi post.(TskState)
    original (flag_pend_sched_node_fields_rep sg node post) local post.(TskState).(parkedTaskStacks) fragments Hentry).
  entailer!.
Qed.

(** This component supplies internal spatial consequences only. It does not
    strengthen public entry domains, supply stack ABI bindings, or establish
    registered-client, scheduler/IRQ, closed-world or public same-X refinement. *)
