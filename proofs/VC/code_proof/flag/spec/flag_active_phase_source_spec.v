Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.flag Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.lib.flag_node_fields Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This active resource is indexed by the original C invocation and the actual
    local node address. Task/Sched control facts remain in the caller source
    interface: a blocked caller is not required to be ready or current here. *)
Definition flag_active_event_clear (task : TaskAbstractState) : Prop :=
  task.(eventPtr) = None /\ task.(eventMultiWaitEvents) = [] /\
  task.(tcbEventMultiPtr) = 0.

Definition flag_active_task_fields (original call : OsSchedCallContext)
  (state : UCOS2_Verify_State) (task : TaskAbstractState) : Prop :=
  task_tcb_init_stack_same_call call original /\
  original.(os_sched_call_origin) =
    RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration) /\
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some task /\
  task.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) /\
  flag_active_event_clear task.

Definition flag_active_fresh_registration original call state : Prop :=
  exists task, flag_active_task_fields original call state task /\ task.(tcbFlagNode) = 0.

Definition flag_active_waiting_registration original node call state : Prop :=
  exists task, flag_active_task_fields original call state task /\
    match state.(FlagState).(flagWaitNodes) node with
    | Some waiter =>
        waiter.(flagNodeAddr) = node /\
        task_stack_key original.(os_sched_call_stack) =
          (waiter.(flagTask), waiter.(flagTaskGeneration)) /\
        task.(tcbFlagNode) = node
    | None => task.(tcbFlagNode) = 0
    end.

Definition flag_active_fresh (sg : StableGlobVars) (original : OsSchedCallContext)
  (node : addr) (call : OsSchedCallContext) (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (flag_active_fresh_registration original call state) &&
    flag_node_fields_uninit_rep sg.(osKernelConfig) node.

Definition flag_active_waiting (sg : StableGlobVars) (original : OsSchedCallContext)
  (node : addr) (call : OsSchedCallContext) (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (flag_active_waiting_registration original node call state) &&
    flag_pend_sched_node_fields_rep sg node state.

Lemma flag_active_fresh_state_equiv : forall sg original node call before after,
  before.(TskState) = after.(TskState) -> before.(FlagState) = after.(FlagState) ->
  flag_active_fresh sg original node call before --||--
  flag_active_fresh sg original node call after.
Proof.
  intros sg original node call before after Htasks Hflags.
  unfold flag_active_fresh, flag_active_fresh_registration, flag_active_task_fields.
  rewrite Htasks; split; reflexivity.
Qed.

Lemma flag_active_waiting_state_equiv : forall sg original node call before after,
  before.(TskState) = after.(TskState) -> before.(FlagState) = after.(FlagState) ->
  flag_active_waiting sg original node call before --||--
  flag_active_waiting sg original node call after.
Proof.
  intros sg original node call before after Htasks Hflags.
  unfold flag_active_waiting, flag_active_waiting_registration, flag_active_task_fields,
    flag_pend_sched_node_fields_rep.
  rewrite Htasks, Hflags; split; reflexivity.
Qed.

Lemma flag_active_fresh_sched_prefix : forall sg original node call state,
  flag_active_fresh sg original node call (os_sched_prefix_state state) --||--
  flag_active_fresh sg original node call state.
Proof. intros; apply flag_active_fresh_state_equiv; reflexivity. Qed.

Lemma flag_active_waiting_sched_prefix : forall sg original node call state,
  flag_active_waiting sg original node call (os_sched_prefix_state state) --||--
  flag_active_waiting sg original node call state.
Proof. intros; apply flag_active_waiting_state_equiv; reflexivity. Qed.

Lemma flag_active_fresh_same_call : forall sg original node call state,
  flag_active_fresh sg original node call state |--
  coq_prop (task_tcb_init_stack_same_call call original) &&
    flag_active_fresh sg original node call state.
Proof.
  unfold flag_active_fresh, flag_active_fresh_registration, flag_active_task_fields.
  intros sg original node call state heap [[task [Htask Hnode]] Hfields].
  split; [tauto|]. split; [exists task; tauto|exact Hfields].
Qed.

Lemma flag_active_waiting_same_call : forall sg original node call state,
  flag_active_waiting sg original node call state |--
  coq_prop (task_tcb_init_stack_same_call call original) &&
    flag_active_waiting sg original node call state.
Proof.
  unfold flag_active_waiting, flag_active_waiting_registration, flag_active_task_fields.
  intros sg original node call state heap [[task [Htask Hnode]] Hfields].
  split; [tauto|]. split; [exists task; tauto|exact Hfields].
Qed.

(** Initialization supplies clean fields. Selection alone, an execution token,
    a zero lookup, or the global closed world supplies no such fact. *)
Lemma flag_active_initialized_task_clear : forall args acquired slot image next prev,
  let task := task_set_links (task_tcb_init_commit_node args acquired slot image) next prev in
  flag_active_event_clear task /\ task.(tcbFlagNode) = 0.
Proof. intros; repeat split; reflexivity. Qed.

Lemma flag_active_fresh_register : forall call state task,
  call.(os_sched_call_origin) =
    RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
      call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some task ->
  task.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  flag_active_event_clear task -> task.(tcbFlagNode) = 0 ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  flag_active_fresh_registration call call
    (replace_TskS (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state).
Proof.
  intros call state task Horigin Htask Hgeneration Hevent Hnode Hinv.
  exists task; split; [|exact Hnode].
  unfold flag_active_task_fields; cbn [replace_TskS TskState].
  split; [unfold task_tcb_init_stack_same_call; repeat split|].
  split; [exact Horigin|]. split; [exact Htask|]. split; [exact Hgeneration|].
  split; [|exact Hevent].
  rewrite Hinv; apply task_begin_invocation_active.
  rewrite Horigin; exists task; auto.
Qed.

Lemma flag_active_fresh_initial_fields : forall sg selected state task args acquired image next prev node,
  state.(TskState).(inUsedTaskStates) selected.(armv7a_continuation_stack).(stackLeaseSlot) = Some task ->
  task.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  task = task_set_links (task_tcb_init_commit_node args acquired
    selected.(armv7a_continuation_stack).(stackLeaseSlot) image) next prev ->
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  flag_node_fields_uninit_rep sg.(osKernelConfig) node |--
  flag_active_fresh sg call node call (armv7a_initial_call_registered selected state).
Proof.
  intros sg selected state task args acquired image next prev node Htask Hgeneration Hinitial call.
  assert (Hclear : flag_active_event_clear task /\ task.(tcbFlagNode) = 0).
  { rewrite Hinitial; apply flag_active_initialized_task_clear. }
  assert (Hregistered : flag_active_fresh_registration call call
    (armv7a_initial_call_registered selected state)).
  { apply (flag_active_fresh_register call state task); try tauto; try reflexivity. }
  unfold flag_active_fresh; entailer!.
Qed.

(** A preceding completed C return must supply the clean registration.
    This pure registration step does not create the sequential ABI event. *)
Lemma flag_active_fresh_sequential_registration : forall previous state,
  flag_active_fresh_registration previous previous state ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  flag_active_fresh_registration call call
    (replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state).
Proof.
  intros previous state [task [[Hsame [Horigin [Htask [Hgen [Hactive Hevent]]]]] Hnode]] call.
  apply (flag_active_fresh_register call state task); assumption || reflexivity.
Qed.

Lemma flag_active_waiting_detached_fresh : forall sg original node call state,
  state.(FlagState).(flagWaitNodes) node = None ->
  flag_active_waiting sg original node call state |--
  flag_active_fresh sg original node call state.
Proof.
  intros sg original node call state Hnone.
  unfold flag_active_waiting, flag_active_waiting_registration, flag_pend_sched_node_fields_rep,
    flag_active_fresh, flag_active_fresh_registration.
  rewrite Hnone.
  intros heap [[task [Htask Hflag]] [image Hfields]].
  split; [exists task; auto|].
  exact (flag_node_fields_rep_to_uninit sg.(osKernelConfig) node image heap Hfields).
Qed.

Lemma flag_active_task_fields_update : forall original call state task replacement,
  flag_active_task_fields original call state task ->
  replacement.(taskGeneration) = task.(taskGeneration) ->
  flag_active_event_clear replacement ->
  flag_active_task_fields original call
    (replace_TskS (glob_task_set_usedtask state.(TskState)
      original.(os_sched_call_stack).(stackLeaseSlot) replacement) state) replacement.
Proof.
  intros original call state task replacement [Hsame [Horigin [Htask [Hgen [Hactive Hevent]]]]]
    Hreplacement Hclear.
  unfold flag_active_task_fields; cbn [replace_TskS TskState].
  split; [exact Hsame|]. split; [exact Horigin|].
  split; [cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity|].
  split; [congruence|]. split; [|exact Hclear].
  eapply glob_task_set_usedtask_preserves_invocation_active; eassumption.
Qed.

(** OS_FlagBlock publishes the actual local node and removes the caller from
    ready. The phase fact observes only the resulting Task/Flag fields. *)
Lemma flag_active_block_waiting_registration :
  forall sg state original call waiter old group image timeout flags,
  flag_active_fresh_registration original call state ->
  task_stack_key original.(os_sched_call_stack) =
    (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  valid_flag_state sg state.(FlagState) ->
  flag_block_call_protocol sg state waiter old group image timeout ->
  flag_block_node sg state.(FlagState) waiter (flag_block_call_tcb sg waiter) = Some flags ->
  flag_active_waiting_registration original waiter.(flagNodeAddr) call
    (flag_block_state state waiter flags old timeout).
Proof.
  intros sg state original call waiter old group image timeout flags
    [task [Htask Hzero]] Hkey Hvalid Hprotocol Hblock.
  pose proof Htask as [Hsame [Horigin [Hlookup [Hgen [Hactive Hevent]]]]].
  destruct Hprotocol as [Hcur [Hprio [Hold [Hready [Hnull [Hptr [Hmulti
    [Hwgen [Hnode [Hfresh [Hgroup [Hgroupgen [Himage Hrest]]]]]]]]]]]]].
  assert (Hslot : original.(os_sched_call_stack).(stackLeaseSlot) = waiter.(flagTask)).
  { exact (f_equal fst Hkey). }
  assert (Htask_eq : task = old) by (rewrite Hslot in Hlookup; congruence).
  subst task.
  pose proof (flag_block_installs_node sg state.(FlagState) waiter
    (flag_block_call_tcb sg waiter) flags group image Hvalid Hgroup Himage Hfresh Hblock) as Hlinked.
  exists (task_prepare_flag_wait old waiter.(flagNodeAddr) timeout); split.
  - unfold flag_block_state.
    change (flag_active_task_fields original call
      (replace_TskS (glob_task_set_usedtask state.(TskState) waiter.(flagTask)
        (task_prepare_flag_wait old waiter.(flagNodeAddr) timeout)) state)
      (task_prepare_flag_wait old waiter.(flagNodeAddr) timeout)).
    rewrite <- Hslot; apply flag_active_task_fields_update with (task := old);
      [exact Htask|reflexivity|exact Hevent].
  - cbn [flag_block_state replace_TskS replace_FlagS replace_SchedS FlagState].
    rewrite Hlinked; cbn [flag_waiter_set_image flagNodeAddr flagTask flagTaskGeneration].
    split; [reflexivity|]. split; [exact Hkey|reflexivity].
Qed.

Lemma flag_active_block_fields_post :
  forall sg state original call waiter old group image timeout,
  flag_active_fresh_registration original call state ->
  task_stack_key original.(os_sched_call_stack) =
    (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  valid_flag_state sg state.(FlagState) ->
  flag_block_call_protocol sg state waiter old group image timeout ->
  flag_block_call_fields_post sg state waiter old timeout |--
  EX flags,
    coq_prop (flag_block_node sg state.(FlagState) waiter (flag_block_call_tcb sg waiter) = Some flags /\
      flag_block_spec.flag_block sg state waiter timeout = Some (flag_block_state state waiter flags old timeout)) &&
    (UCOS2_fields_inv sg (flag_block_state state waiter flags old timeout) **
      flag_active_waiting sg original waiter.(flagNodeAddr) call
        (flag_block_state state waiter flags old timeout)).
Proof.
  intros sg state original call waiter old group image timeout Hfresh Hkey Hvalid Hprotocol.
  unfold flag_block_call_fields_post; Intros flags.
  assert (Hblock : flag_block_node sg state.(FlagState) waiter (flag_block_call_tcb sg waiter) = Some flags)
    by tauto.
  pose proof (flag_active_block_waiting_registration sg state original call waiter old group image timeout
    flags Hfresh Hkey Hvalid Hprotocol Hblock) as Hwaiting.
  destruct Hprotocol as [Hcur [Hprio [Hold [Hready [Hnull [Hptr [Hmulti
    [Hwgen [Hnode [Habsent [Hgroup [Hgroupgen [Himage Hrest]]]]]]]]]]]]].
  pose proof (flag_block_installs_node sg state.(FlagState) waiter (flag_block_call_tcb sg waiter)
    flags group image Hvalid Hgroup Himage Habsent Hblock) as Hlinked.
  Exists flags.
  unfold flag_active_waiting, flag_pend_sched_node_fields_rep.
  cbn [flag_block_state replace_TskS replace_FlagS replace_SchedS FlagState].
  rewrite Hlinked; entailer!; tauto.
Qed.

(** The source result is retained, including false schedule/abort outcomes.
    Its actual unlink gives None; the next resource lemma separately consumes
    the returned loan. No PendOK-to-detached inference is used. *)
Lemma flag_active_task_rdy_waiting_registration :
  forall sg state original call node bits result schedule post,
  flag_active_waiting_registration original node call state ->
  flag_task_rdy sg state node bits result = Some (schedule, post) ->
  flag_active_waiting_registration original node call post /\
    post.(FlagState).(flagWaitNodes) node = None.
Proof.
  intros sg state original call node bits result schedule post [task [Htask Hbinding]] Hstep.
  unfold flag_task_rdy in Hstep.
  destruct (flag_unlink_node state.(FlagState) node) as [[waiter flags]|] eqn:Hunlink;
    [|discriminate].
  destruct (state.(TskState).(inUsedTaskStates) waiter.(flagTask)) as [old|] eqn:Hold;
    [|discriminate].
  inversion Hstep; subst post schedule.
  destruct (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink) as [Hlinked Hnone].
  rewrite Hlinked in Hbinding; destruct Hbinding as [Haddr [Hkey Hflag]].
  pose proof Htask as [Hsame [Horigin [Hlookup [Hgen [Hactive Hevent]]]]].
  assert (Hslot : original.(os_sched_call_stack).(stackLeaseSlot) = waiter.(flagTask)).
  { exact (f_equal fst Hkey). }
  assert (Htask_eq : task = old) by (rewrite Hslot in Hlookup; congruence).
  subst task; split; [|exact Hnone].
  exists (task_flag_wake old bits result); split.
  - unfold flag_wake_state.
    change (flag_active_task_fields original call
      (replace_TskS (glob_task_set_usedtask state.(TskState) waiter.(flagTask)
        (task_flag_wake old bits result)) state) (task_flag_wake old bits result)).
    rewrite <- Hslot; apply flag_active_task_fields_update with (task := old);
      [exact Htask|reflexivity|exact Hevent].
  - cbn [flag_wake_state replace_TskS replace_FlagS replace_SchedS FlagState].
    rewrite Hnone; reflexivity.
Qed.

Lemma flag_active_timeout_waiting_registration :
  forall state original call node waiter flags old,
  flag_active_waiting_registration original node call state ->
  flag_unlink_node state.(FlagState) node = Some (waiter, flags) ->
  state.(TskState).(inUsedTaskStates) waiter.(flagTask) = Some old ->
  flag_active_waiting_registration original node call (flag_timeout_cleanup_state state waiter flags old) /\
    (flag_timeout_cleanup_state state waiter flags old).(FlagState).(flagWaitNodes) node = None.
Proof.
  intros state original call node waiter flags old [task [Htask Hbinding]] Hunlink Hold.
  destruct (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink) as [Hlinked Hnone].
  rewrite Hlinked in Hbinding; destruct Hbinding as [Haddr [Hkey Hflag]].
  pose proof Htask as [Hsame [Horigin [Hlookup [Hgen [Hactive Hevent]]]]].
  assert (Hslot : original.(os_sched_call_stack).(stackLeaseSlot) = waiter.(flagTask)).
  { exact (f_equal fst Hkey). }
  assert (Htask_eq : task = old) by (rewrite Hslot in Hlookup; congruence).
  subst task; split; [|exact Hnone].
  exists (task_set_flag_node old 0); split.
  - unfold flag_timeout_cleanup_state.
    change (flag_active_task_fields original call
      (replace_TskS (glob_task_set_usedtask state.(TskState) waiter.(flagTask)
        (task_set_flag_node old 0)) state) (task_set_flag_node old 0)).
    rewrite <- Hslot; apply flag_active_task_fields_update with (task := old);
      [exact Htask|reflexivity|exact Hevent].
  - cbn [flag_timeout_cleanup_state replace_TskS replace_FlagS FlagState].
    rewrite Hnone; reflexivity.
Qed.

Lemma flag_active_waiting_from_return_loan : forall sg original call node state waiter,
  flag_active_waiting_registration original node call state ->
  state.(FlagState).(flagWaitNodes) node = None -> waiter.(flagNodeAddr) = node ->
  flag_node_fields_return_loan sg.(osKernelConfig) waiter |--
    flag_active_waiting sg original node call state.
Proof.
  intros sg original call node state waiter Hregistration Hnone Hnode.
  unfold flag_active_waiting.
  sep_apply_l_atomic (flag_pend_sched_node_fields_rep_from_loan sg node state waiter Hnone Hnode).
  entailer!.
Qed.

Lemma flag_active_task_rdy_fields_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg state original call node waiter old bits result returned local,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  flag_active_waiting_registration original node call state -> waiter.(flagNodeAddr) = node ->
  flag_task_rdy_fields_post sg state node waiter bits result returned **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) |--
  EX post schedule,
    coq_prop (flag_task_rdy sg state node bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0) /\ post.(FlagState).(flagWaitNodes) node = None) &&
    (UCOS2_fields_inv sg post ** flag_active_waiting sg original node call post **
      store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
        post.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg state original call node waiter old bits result returned local
    Hvalid Hdomain Hregistration Hnode.
  sep_apply_l_atomic (flag_wake_fields_returns_node_with_continuation_map external platform port abi
    sg state node waiter old bits result returned local Hvalid Hdomain).
  Intros post schedule.
  assert (Hstep : flag_task_rdy sg state node bits result = Some (schedule, post)) by tauto.
  destruct (flag_active_task_rdy_waiting_registration sg state original call node bits result schedule post
    Hregistration Hstep) as [Hafter Hnone].
  sep_apply_l_atomic (flag_active_waiting_from_return_loan sg original call node post waiter Hafter Hnone Hnode).
  Exists post schedule; entailer!; tauto.
Qed.


(** Save/Restore can change fragment partitions while keeping the same C
    invocation, origin and lease. The phase does not freeze those partitions. *)
Lemma flag_active_fresh_call_equiv : forall sg original node call next state,
  task_tcb_init_stack_same_call next call ->
  flag_active_fresh sg original node call state --||--
  flag_active_fresh sg original node next state.
Proof.
  intros sg original node call next state [Hinv [Horigin Hstack]].
  unfold flag_active_fresh, flag_active_fresh_registration, flag_active_task_fields,
    task_tcb_init_stack_same_call.
  rewrite Hinv, Horigin, Hstack; split; reflexivity.
Qed.

Lemma flag_active_waiting_call_equiv : forall sg original node call next state,
  task_tcb_init_stack_same_call next call ->
  flag_active_waiting sg original node call state --||--
  flag_active_waiting sg original node next state.
Proof.
  intros sg original node call next state [Hinv [Horigin Hstack]].
  unfold flag_active_waiting, flag_active_waiting_registration, flag_active_task_fields,
    task_tcb_init_stack_same_call.
  rewrite Hinv, Horigin, Hstack; split; reflexivity.
Qed.

Lemma flag_active_timeout_fields_resources : forall sg state original call node waiter flags old,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg state ->
  flag_active_waiting_registration original node call state ->
  flag_unlink_node state.(FlagState) node = Some (waiter, flags) ->
  state.(TskState).(inUsedTaskStates) waiter.(flagTask) = Some old ->
  task_non_suspension_bits old.(stat) = 0 -> waiter.(flagNodeAddr) = node ->
  let post := flag_timeout_cleanup_state state waiter flags old in
  task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
    flag_groups_rep sg flags ** flag_unlink_fields_neighbors_rep sg state.(FlagState) waiter **
    sg.(g_OSFlagFreeList) # Ptr |->
      (match state.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg state |--
  UCOS2_fields_inv sg post ** flag_active_waiting sg original node call post.
Proof.
  intros sg state original call node waiter flags old Henabled Hvalid Hregistration Hunlink Hold
    Hpending Hnode post.
  destruct (flag_active_timeout_waiting_registration state original call node waiter flags old
    Hregistration Hunlink Hold) as [Hafter Hnone].
  pose proof (flag_timeout_fields_returns_node_and_global_resources sg state node waiter flags old
    Henabled Hvalid Hunlink Hold Hpending) as Hresources.
  cbn zeta in Hresources; fold post in Hresources.
  sep_apply_l_atomic Hresources.
  sep_apply_l_atomic (flag_active_waiting_from_return_loan sg original call node post waiter
    Hafter Hnone Hnode).
  entailer!.
Qed.

(** The actual source caller retains the returned node loan through its Next
    read and pnode write. Only after that execution is the full Waiting
    assertion transferred into the original parked continuation. *)
Lemma flag_active_waiting_next_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg post original call node waiter local fragments pnode
  (frame : Assertion) before after observed,
  flag_active_waiting_registration original node call post ->
  waiter.(flagNodeAddr) = node -> post.(FlagState).(flagWaitNodes) node = None ->
  post.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  (pnode # Ptr |-> node ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
    (UCOS2_fields_inv sg post **
     store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
       post.(TskState).(parkedTaskStacks) ** frame)) before ->
  flag_source_next_assignment pnode node observed before after ->
  observed = waiter.(flagWaitImage).(flagNodeNext) /\
  (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
   store_parked_continuations
     (kernel_saved_continuation_entry abi post.(TskState)
       (flag_continuation_local_node original.(os_sched_call_stack)
         (flag_active_waiting sg original node call post) local))
     post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg post original call node waiter local fragments pnode frame
    before after observed Hregistration Hnode Hnone Hentry Hpre Hrun.
  rewrite <- Hnode in Hpre, Hrun.
  destruct (flag_source_fields_next_assignment_resources sg waiter pnode _ before after observed Hpre Hrun)
    as [Hobserved Hafter].
  split; [exact Hobserved|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (flag_active_waiting_from_return_loan sg original call node post waiter
      Hregistration Hnone Hnode).
    sep_apply_l_atomic (flag_continuation_map_publish_node external platform port abi post.(TskState)
      original.(os_sched_call_stack) (flag_active_waiting sg original node call post) local
      post.(TskState).(parkedTaskStacks) fragments Hentry).
    entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma flag_active_task_rdy_next_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state original call node waiter old bits result returned
  local fragments pnode (frame : Assertion) before middle after observed,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  flag_active_waiting_registration original node call state -> waiter.(flagNodeAddr) = node ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_fields_task_rdy_call sg node bits result returned before middle ->
  flag_source_next_assignment pnode node observed middle after ->
  (flag_task_rdy_fields_pre sg state node waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
     store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> node ** frame))) before ->
  exists post schedule,
    flag_task_rdy sg state node bits result = Some (schedule, post) /\
    returned = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    post.(FlagState).(flagWaitNodes) node = None /\
    (pnode # Ptr |-> observed ** UCOS2_fields_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi post.(TskState)
         (flag_continuation_local_node original.(os_sched_call_stack)
           (flag_active_waiting sg original node call post) local))
       post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg state original call node waiter old bits result returned local fragments
    pnode frame before middle after observed Hvalid Hdomain Hregistration Hnode Hentry Hcall Hnext Hpre.
  destruct (flag_source_fields_task_rdy_call_loan external platform port abi sg state node waiter old bits result
    returned local (pnode # Ptr |-> node ** frame) before middle Hvalid Hdomain Hcall Hpre)
    as [post [schedule [[Hstep Hreturned] Hmiddle]]].
  destruct (flag_active_task_rdy_waiting_registration sg state original call node bits result schedule post
    Hregistration Hstep) as [Hafter Hnone].
  pose proof (proj1 (FlagPendSchedulerResources.flag_task_rdy_preserves_stack_metadata
    sg state node bits result schedule post Hstep)) as Hstacks.
  assert (Hparked : post.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments)) by (rewrite Hstacks; exact Hentry).
  match type of Hmiddle with ?P middle => assert (Horder : P |--
    pnode # Ptr |-> node ** flag_node_fields_return_loan sg.(osKernelConfig) waiter **
      (UCOS2_fields_inv sg post **
       store_parked_continuations (kernel_saved_continuation_entry abi post.(TskState) local)
         post.(TskState).(parkedTaskStacks) ** frame)) by entailer! end.
  destruct (flag_active_waiting_next_publish external platform port abi sg post original call node waiter
    local fragments pnode frame middle after observed Hafter Hnode Hnone Hparked
    (Horder middle Hmiddle) Hnext) as [Hobserved Hresources].
  exists post, schedule; auto.
Qed.


Lemma flag_active_fresh_registration_state_iff : forall original call before after,
  before.(TskState) = after.(TskState) ->
  (flag_active_fresh_registration original call before <->
   flag_active_fresh_registration original call after).
Proof.
  intros original call before after Htasks.
  unfold flag_active_fresh_registration, flag_active_task_fields.
  rewrite Htasks; reflexivity.
Qed.

Lemma flag_active_waiting_registration_state_iff : forall original node call before after,
  before.(TskState) = after.(TskState) -> before.(FlagState) = after.(FlagState) ->
  (flag_active_waiting_registration original node call before <->
   flag_active_waiting_registration original node call after).
Proof.
  intros original node call before after Htasks Hflags.
  unfold flag_active_waiting_registration, flag_active_task_fields.
  rewrite Htasks, Hflags; reflexivity.
Qed.

(** The private typed Next cell cannot also belong to a registered waiter.
    This is the ownership-to-absence direction, never absence-to-ownership. *)
Lemma flag_active_fresh_node_absent : forall sg original call node state nodes,
  flag_wait_nodes_fields_rep sg nodes ** flag_active_fresh sg original node call state |--
  coq_prop (nodes node = None) &&
    (flag_wait_nodes_fields_rep sg nodes ** flag_active_fresh sg original node call state).
Proof.
  intros sg original call node state nodes; destruct (nodes node) as [waiter|] eqn:Hnode.
  - assert (Hfalse :
      flag_wait_nodes_fields_rep sg nodes ** flag_active_fresh sg original node call state |--
      coq_prop False).
    { sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_next sg nodes node waiter Hnode).
      unfold flag_active_fresh, flag_node_fields_uninit_rep.
      Intros.
      sep_apply_l_atomic (store_ptr_undef_store_ptr node waiter.(flagWaitImage).(flagNodeNext)).
      sep_apply_l_atomic (dup_undef_store_ptr node); entailer!. }
    intros heap Hheap; exfalso; exact (Hfalse heap Hheap).
  - entailer!.
Qed.
