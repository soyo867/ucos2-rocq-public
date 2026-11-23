Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.micromega.Lia.
From compcert.lib Require Import Integers.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTaskDel, V2.93.01 Source/os_task.c:450--566.
    These are source phases, not a single atomic whole-call specification.
    Prefix observations precede Save; SELF/table reads follow Save.  Event/
    Flag unlink, the Restore/Dummy/Save window, Delete/TLS hooks and the
    final Restore/OS_Sched continuation still require their own composition.
    No state equality or ownership is inferred across those boundaries. *)

(** The safety branch invokes OS_SAFETY_CRITICAL_EXCEPTION before returning
    the indicated error, if that hook returns.  This discriminator records
    ordered branches only; it does not erase the hook or claim no writes.
    [started] is the observed flag, not a new global state field. *)
Definition task_delete_prefix_error (sg : StableGlobVars) (started : bool)
  (int_nesting : Z) (priority : Priority) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool
  then Some OS_ERR_ILLEGAL_DEL_RUN_TIME else
  if Z.ltb 0 int_nesting then Some OS_ERR_TASK_DEL_ISR else
  if Z.eqb priority sg.(osTaskIdlePrio) then Some OS_ERR_TASK_DEL_IDLE else
  if (sg.(osKernelConfig).(cfgArgumentChecks) && Z.leb sg.(osLowestPrio) priority &&
      negb (Z.eqb priority sg.(osPrioSelf)))%bool
  then Some OS_ERR_PRIO_INVALID else None.

Lemma task_delete_prefix_error_safety : forall sg int_nesting priority,
  sg.(osKernelConfig).(cfgSafetyCriticalIEC) = true ->
  task_delete_prefix_error sg true int_nesting priority = Some OS_ERR_ILLEGAL_DEL_RUN_TIME.
Proof. intros; unfold task_delete_prefix_error; rewrite H; reflexivity. Qed.

Lemma task_delete_prefix_error_isr : forall sg started int_nesting priority,
  (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool = false ->
  0 < int_nesting ->
  task_delete_prefix_error sg started int_nesting priority = Some OS_ERR_TASK_DEL_ISR.
Proof.
  intros; unfold task_delete_prefix_error; rewrite H, (proj2 (Z.ltb_lt _ _) H0); reflexivity.
Qed.

(** The literal idle argument is rejected even when argument checks are off.
    It is not a second idle check after SELF or priority-alias resolution. *)
Lemma task_delete_prefix_error_idle : forall sg started,
  (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool = false ->
  task_delete_prefix_error sg started 0 sg.(osTaskIdlePrio) = Some OS_ERR_TASK_DEL_IDLE.
Proof. intros; unfold task_delete_prefix_error; rewrite H, Z.eqb_refl; reflexivity. Qed.

Lemma task_delete_prefix_allows_priority_index : forall sg started int_nesting priority,
  sg.(osKernelConfig).(cfgArgumentChecks) = true -> 0 <= priority ->
  task_delete_prefix_error sg started int_nesting priority = None ->
  priority = sg.(osPrioSelf) \/ task_priority_in_range sg priority.
Proof.
  intros sg started int_nesting priority Hchecks Hnonnegative Hallowed.
  unfold task_delete_prefix_error in Hallowed.
  destruct (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool; [discriminate|].
  destruct (Z.ltb 0 int_nesting); [discriminate|].
  destruct (Z.eqb priority sg.(osTaskIdlePrio)); [discriminate|].
  rewrite Hchecks in Hallowed; simpl in Hallowed.
  destruct (Z.eqb priority sg.(osPrioSelf)) eqn:Hself;
    [left; apply Z.eqb_eq; exact Hself|right].
  rewrite Bool.andb_true_r in Hallowed.
  destruct (Z.leb sg.(osLowestPrio) priority) eqn:Hrange; [discriminate|].
  apply Z.leb_gt in Hrange; unfold task_priority_in_range; lia.
Qed.

(** Only SELF reads OSTCBCur->OSTCBPrio.  An explicit priority request does
    not require a live current TCB merely to select its table entry. *)
Definition task_delete_selection (sg : StableGlobVars) (requested : Priority)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) (selected : Priority) : Prop :=
  if Z.eqb requested sg.(osPrioSelf) then
    exists cid current, s.(curTaskID) = Some cid /\
      tasks.(inUsedTaskStates) cid = Some current /\ selected = current.(curPrio)
  else selected = requested.

Lemma task_delete_selection_explicit : forall sg requested tasks s selected,
  requested <> sg.(osPrioSelf) ->
  (task_delete_selection sg requested tasks s selected <-> selected = requested).
Proof.
  intros; unfold task_delete_selection; rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
Qed.

Lemma task_delete_selection_self : forall sg tasks s cid current,
  s.(curTaskID) = Some cid -> tasks.(inUsedTaskStates) cid = Some current ->
  task_delete_selection sg sg.(osPrioSelf) tasks s current.(curPrio).
Proof.
  intros; unfold task_delete_selection; rewrite Z.eqb_refl; exists cid, current; auto.
Qed.

(** A read-only lookup phase.  The selected index's bounds and the physical
    pointer/table permissions are caller obligations, not invented branches.
    PTReserved is rejected; PTTask denotes the actual live TCB read next. *)
Definition task_delete_table_lookup (tasks : Glob_TaskAbstractState) (selected : Priority)
  (result : OSErrCode + (TaskID * TaskAbstractState)) : Prop :=
  match tasks.(prioTbl) selected with
  | PTFree => result = inl OS_ERR_TASK_NOT_EXIST
  | PTReserved => result = inl OS_ERR_TASK_DEL
  | PTTask tid => exists node,
      tasks.(inUsedTaskStates) tid = Some node /\ result = inr (tid, node)
  end.

Lemma task_delete_table_lookup_live : forall tasks selected tid node,
  task_delete_table_lookup tasks selected (inr (tid, node)) ->
  tasks.(prioTbl) selected = PTTask tid /\ tasks.(inUsedTaskStates) tid = Some node.
Proof.
  intros tasks selected tid node Hlookup; unfold task_delete_table_lookup in Hlookup.
  destruct (tasks.(prioTbl) selected) as [| |slot] eqn:Htable;
    try discriminate.
  destruct Hlookup as [t [Ht E]]; injection E as Eslot Enode; subst slot; subst t; auto.
Qed.

(** Source-local counter arithmetic: OSTaskDel increments the lock without
    OSSchedLock's running/ISR tests.  Reuse the existing interrupt scheduling
    decision below rather than inventing a second interrupt transition. *)
Lemma task_delete_window_lock_in_range : forall lock,
  0 <= lock <= 255 ->
  0 < (if lock <? 255 then lock + 1 else lock) <= 255.
Proof.
  intros lock Hrange; destruct (lock <? 255) eqn:E;
    [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; lia.
Qed.

Lemma task_delete_window_blocks_interrupt_schedule : forall running nesting lock,
  0 <= lock <= 255 ->
  interrupt_exit_requests_schedule running
    {| intNesting := nesting; lockNesting := if lock <? 255 then lock + 1 else lock |} = false.
Proof.
  intros running nesting lock Hrange.
  pose proof (task_delete_window_lock_in_range lock Hrange) as Hpositive.
  destruct (interrupt_exit_requests_schedule running
    {| intNesting := nesting; lockNesting := if lock <? 255 then lock + 1 else lock |}) eqn:E;
    [|reflexivity].
  apply interrupt_exit_requests_schedule_iff in E.
  destruct E as [_ [_ Hlock]].
  unfold interrupt_exit_state in Hlock; destruct running; simpl in Hlock;
    try destruct (0 <? nesting); simpl in Hlock; lia.
Qed.

(** A source-facing phase indexed by the selected slot's existing generation,
    not a stored deletion flag.  It supplies neither Event/Flag unlink facts
    nor stability across Restore. *)
Definition task_delete_prepared (sg : StableGlobVars) (tid : TaskID) (generation : nat)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  sched_ready_except sg [tid] tasks s /\
  exists t, tasks.(inUsedTaskStates) tid = Some t /\ t.(taskGeneration) = generation /\
    t.(dly) = 0 /\ t.(stat) = Byte.zero /\ t.(statPend) = PendOK.

Lemma task_prepare_delete_establishes_prepared : forall sg tasks s tid old,
  tasks.(inUsedTaskStates) tid = Some old -> sched_ready_in_range sg tasks s ->
  task_delete_prepared sg tid old.(taskGeneration)
    (glob_task_set_usedtask tasks tid (task_prepare_delete old)) (sched_remove_ready_task s tid).
Proof.
  intros; split; [eapply task_prepare_delete_ready_phase; eassumption|].
  exists (task_prepare_delete old); split; [simpl; rewrite Z.eqb_refl; reflexivity|].
  repeat split; reflexivity.
Qed.

(** An actual Tick iteration preserves the saved deletion instance, while
    allowing another cursor task to decrement/expire and change ready bits.
    These are existing configuration/status facts, not an ISR no-write
    assumption.  The whole Restore window still has to compose the other
    permitted ISR actions, hooks and saved interrupt token. *)
Lemma tick_task_step_preserves_delete_prepared : forall sg s tid generation cursor node,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_in_range sg s.(TskState) -> task_reserved_bits_clear sg s.(TskState) ->
  task_delete_prepared sg tid generation s.(TskState) s.(SchedState) ->
  s.(TskState).(inUsedTaskStates) cursor = Some node ->
  let post := tick_task_step sg cursor node s in
  task_in_range sg post.(TskState) /\ task_reserved_bits_clear sg post.(TskState) /\
  task_delete_prepared sg tid generation post.(TskState) post.(SchedState).
Proof.
  intros sg s tid generation cursor node Hmulti Htasks Hbits Hphase Hnode post.
  split; [apply tick_task_step_preserves_task_in_range; assumption|].
  split.
  - unfold post; rewrite tick_task_step_task_state_eq by exact Hnode.
    apply task_reserved_bits_clear_update_task; [exact Hbits|].
    apply tick_task_preserves_reserved_bits_clear; exact (Hbits cursor node Hnode).
  - destruct Hphase as [Hready [retiring [Hretiring [Hgen [Hdly [Hstat Hpend]]]]]].
    split.
    + apply tick_task_step_preserves_ready_except; try assumption.
      * pose proof (Hbits cursor node Hnode) as Hclear; rewrite Hmulti in Hclear; exact Hclear.
      * intros slot t [Heq|Hin] Ht; [subst slot|contradiction].
        rewrite Hretiring in Ht; injection Ht as Ht; subst t; exact Hdly.
    + exists retiring; split; [|split; [exact Hgen|split; [exact Hdly|split; assumption]]].
      unfold post; destruct (Z.eq_dec tid cursor) as [Heq|Hne].
      * subst cursor; rewrite Hretiring in Hnode; injection Hnode as Hnode; subst node.
        rewrite tick_task_step_zero_delay_eq by exact Hdly; exact Hretiring.
      * rewrite tick_task_step_other_task_eq by exact Hne; exact Hretiring.
Qed.

Lemma tick_task_step_preserves_delete_relations : forall sg s tid generation cursor node,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_in_range sg s.(TskState) -> task_reserved_bits_clear sg s.(TskState) ->
  task_delete_prepared sg tid generation s.(TskState) s.(SchedState) ->
  event_in_range sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  s.(TskState).(inUsedTaskStates) cursor = Some node ->
  let post := tick_task_step sg cursor node s in
  task_in_range sg post.(TskState) /\ task_reserved_bits_clear sg post.(TskState) /\
  task_delete_prepared sg tid generation post.(TskState) post.(SchedState) /\
  event_in_range sg post.(TskState) post.(EventState) /\ cross_module_consistency sg post.
Proof.
  intros sg s tid generation cursor node Hmulti Htasks Hbits Hphase Hevents Hcross Hnode post.
  destruct (tick_task_step_preserves_delete_prepared sg s tid generation cursor node
    Hmulti Htasks Hbits Hphase Hnode) as [Htasks' [Hbits' Hphase']].
  split; [exact Htasks'|]; split; [exact Hbits'|]; split; [exact Hphase'|]; split.
  - apply tick_task_step_preserves_event_in_range; assumption.
  - apply tick_task_step_preserves_cross_module_consistency; assumption.
Qed.

(** The ordinary stable ready relation is false at this real source point. *)
Lemma task_prepare_delete_not_stable_ready : forall sg tasks s tid old,
  ~ sched_ready_in_range sg (glob_task_set_usedtask tasks tid (task_prepare_delete old))
    (sched_remove_ready_task s tid).
Proof.
  intros sg tasks s tid old [_ [_ [Hcomplete _]]].
  apply (remove_Z_eqb_notin tid s.(readyList)).
  apply (Hcomplete tid (task_prepare_delete old)); [simpl; rewrite Z.eqb_refl; reflexivity|reflexivity].
Qed.

Lemma task_prepare_delete_not_suspended : forall t,
  task_is_suspended (task_prepare_delete t).(stat) = false.
Proof. reflexivity. Qed.

(** Operation-level counterexample to stability under ALL clients.  The API
    Reference marks Suspend/Resume Task-only although their C bodies have no
    ISR rejection.  This trace is not a permitted ISR step under that calling
    protocol; its exclusion also needs the deletion window's scheduler-lock
    argument.  Neither fact follows merely from a retirement phase name. *)
Lemma task_prepare_delete_suspend_resume_ready : forall sg tasks s tid old,
  task_is_suspended (task_suspend (task_prepare_delete old)).(stat) = true /\
  In tid (sched_resume_task sg tasks (sched_remove_ready_task s tid)
    tid (task_suspend (task_prepare_delete old))).(readyList).
Proof.
  intros; split; [reflexivity|].
  apply sched_resume_task_ready_membership; right; split; [reflexivity|].
  split; reflexivity.
Qed.

(** Once the deletion phase has actually survived the window and hooks,
    its exact source suffix restores Task and ordinary ready consistency.
    This does not discharge the window, global object/alias relations, stack
    lifetime or platform stopping/return obligations.  The UChar bound is a
    fact of the counter's storage, not an additional public API restriction. *)
Lemma task_delete_recycle_restores_task_sched : forall sg tasks s tid generation priority node name,
  task_in_range sg tasks -> task_delete_prepared sg tid generation tasks s ->
  tasks.(inUsedTaskStates) tid = Some node -> tasks.(prioTbl) priority = PTTask tid ->
  tasks.(taskCount) <= 255 ->
  task_in_range sg (task_recycle sg tasks tid priority node name) /\
  sched_ready_in_range sg (task_recycle sg tasks tid priority node name) s.
Proof.
  intros sg tasks s tid generation priority node name Htasks [Hphase _] Hnode Hselected Hbound.
  split; [apply task_recycle_preserves_in_range; assumption|].
  apply task_recycle_restores_ready; assumption.
Qed.

(** Endpoint through the three preparation stores, using the TCB AFTER
    the unlink callees.  Ready removal occurs before those calls in C;
    this combined masked endpoint does not assert stable intermediate
    states, increment the scheduler lock or cross Restore. *)
Definition task_delete_prepare_after_unlink (s : UCOS2_Verify_State)
  (tid : TaskID) (node : TaskAbstractState) : UCOS2_Verify_State :=
  replace_SchedS (sched_remove_ready_task s.(SchedState) tid)
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_prepare_delete node)) s).

Lemma task_delete_prepare_after_unlink_preserves_task_sched : forall sg s tid old node,
  task_in_range sg s.(TskState) -> sched_ready_in_range sg s.(TskState) s.(SchedState) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  node.(taskID) = old.(taskID) -> node.(taskGeneration) = old.(taskGeneration) ->
  node.(curPrio) = old.(curPrio) -> node.(nextTCB) = old.(nextTCB) ->
  node.(prevTCB) = old.(prevTCB) ->
  let post := task_delete_prepare_after_unlink s tid node in
  task_delete_prepared sg tid old.(taskGeneration) post.(TskState) post.(SchedState) /\
  task_in_range sg post.(TskState).
Proof.
  intros sg s tid old node Htasks Hready Hold Hid Hg Hp Hnext Hprev; split.
  - split.
    + eapply sched_ready_except_remove_updated_task;
        [exact Hold|exact Hp|apply sched_ready_except_nil_iff; exact Hready].
    + exists (task_prepare_delete node); split; [simpl; rewrite Z.eqb_refl; reflexivity|].
      split; [exact Hg|repeat split; reflexivity].
  - eapply task_update_preserves_in_range; eassumption.
Qed.

(** Source endpoint in the single-Event native profile.  None denotes an
    unresolved required object/node lookup, NOT a C error or an added guard.
    The optional returned waiter records the actual unlinked stack-node
    loan; its bytes are not freed or discarded by this pure transformer.
    Multi-enabled removal has a separate array/callee phase and is not
    silently represented by this single-wait endpoint. *)
Definition task_delete_prepare_single_wait (s : UCOS2_Verify_State)
  (tid : TaskID) (old : TaskAbstractState)
  : option (UCOS2_Verify_State * option FlagWaiterState) :=
  let unlink_flag := fun events node =>
    if Z.eqb node.(tcbFlagNode) 0 then
      Some (task_delete_prepare_after_unlink (replace_EventS events s) tid node, None)
    else match flag_unlink_node s.(FlagState) node.(tcbFlagNode) with
      | Some (w, flags) =>
          Some (task_delete_prepare_after_unlink
            (replace_FlagS flags (replace_EventS events s)) tid (task_set_flag_node node 0), Some w)
      | None => None
      end in
  match old.(eventPtr) with
  | None => unlink_flag s.(EventState) old
  | Some eid => match s.(EventState).(inUsedEventStates) eid with
    | None => None
    | Some e => unlink_flag
        (update_event_field_raw s.(EventState) eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList))))
        (task_set_event_ptr old None)
    end
  end.

Lemma task_delete_prepare_single_wait_preserves_relations : forall sg s tid old,
  selected_kernel_profile sg ->
  task_in_range sg s.(TskState) -> sched_ready_in_range sg s.(TskState) s.(SchedState) ->
  event_in_range sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  valid_flag_configuration sg s.(FlagState) -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  exists post loan, task_delete_prepare_single_wait s tid old = Some (post, loan) /\
    task_delete_prepared sg tid old.(taskGeneration) post.(TskState) post.(SchedState) /\
    task_in_range sg post.(TskState) /\
    event_in_range sg post.(TskState) post.(EventState) /\
    cross_module_consistency sg post /\ valid_flag_configuration sg post.(FlagState).
Proof.
  intros sg s tid old Hprofile Htasks Hready Hevents Hcross Hflags Hold.
  pose proof Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  pose proof Hwait as [Hentries [Hback Hclosed]].
  assert (Hmulti : old.(eventMultiWaitEvents) = []).
  { destruct old.(eventMultiWaitEvents) as [|eid rest] eqn:E; [reflexivity|].
    destruct (proj2 (Hclosed tid old Hold) eid ltac:(rewrite E; left; reflexivity)) as [e He].
    assert (Hin : In tid e.(waitList)).
    { eapply Hback; [exact Hold|exact He|right; rewrite E; left; reflexivity]. }
    destruct (event_waiter_task_fields sg s.(TskState) eid e tid (Hentries eid e He) Hin)
      as [found [kind [Hfound [_ [_ [Hempty _]]]]]].
    assert (found = old) by congruence; subst found; congruence. }
  destruct old.(eventPtr) as [eid|] eqn:Hptr.
  - destruct (proj1 (Hclosed tid old Hold) eid Hptr) as [e He].
    assert (Hin : In tid e.(waitList)) by (eapply Hback; [exact Hold|exact He|left; exact Hptr]).
    pose proof (proj1 (task_with_event_ptr_has_no_flag_registration
      sg s.(TskState) s.(FlagState) tid old eid Hflag Hold Hptr)) as Hnull.
    set (events := update_event_field_raw s.(EventState) eid
      (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))).
    set (post := task_delete_prepare_after_unlink (replace_EventS events s) tid (task_set_event_ptr old None)).
    exists post, None; split.
    + unfold task_delete_prepare_single_wait; rewrite Hptr, He; simpl.
      rewrite Hnull; reflexivity.
    + destruct (task_delete_prepare_after_unlink_preserves_task_sched sg
        (replace_EventS events s) tid old (task_set_event_ptr old None)
        Htasks Hready Hold eq_refl eq_refl eq_refl eq_refl eq_refl) as [Hphase Htask].
      split; [exact Hphase|]. split; [exact Htask|]. split.
      * eapply event_remove_waiter_update_task_preserves_in_range; eassumption.
      * split; [|exact Hflags].
        exact (event_remove_waiter_update_task_preserves_cross_module_consistency
          sg s eid e tid old (task_prepare_delete (task_set_event_ptr old None))
          Hcross He Hin Hold eq_refl eq_refl Hmulti Hnull ltac:(discriminate)).
  - destruct (Z.eqb old.(tcbFlagNode) 0) eqn:Hnode.
    + apply Z.eqb_eq in Hnode.
      assert (Habsent : forall eid e, s.(EventState).(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)).
      { intros eid e He Hin.
        destruct (event_waiter_task_fields sg s.(TskState) eid e tid (Hentries eid e He) Hin)
          as [found [kind [Hfound [_ [Href _]]]]].
        assert (found = old) by congruence; subst found; congruence. }
      set (post := task_delete_prepare_after_unlink (replace_EventS s.(EventState) s) tid old).
      exists post, None; split.
      * unfold task_delete_prepare_single_wait; rewrite Hptr, Hnode; reflexivity.
      * destruct (task_delete_prepare_after_unlink_preserves_task_sched sg
          (replace_EventS s.(EventState) s) tid old old
          Htasks Hready Hold eq_refl eq_refl eq_refl eq_refl eq_refl) as [Hphase Htask].
        split; [exact Hphase|]. split; [exact Htask|]. split.
        -- eapply event_update_unlisted_task_preserves_in_range; eassumption.
        -- split; [|exact Hflags]. split.
           ++ eapply task_mutex_priotbl_consistency_update_task; [exact Hold|reflexivity|exact Htable].
           ++ split.
              ** eapply mutex_owner_snapshot_update_task; eassumption.
              ** split.
                 --- eapply event_wait_object_update_unlisted_task;
                       [exact Hold|reflexivity|reflexivity|exact Habsent|exact Hwait].
                 --- split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Htimer].
                     eapply task_flag_waiter_consistency_update_unregistered_task;
                       [exact Hold|exact Hnode|exact Hnode|discriminate|exact Hflag].
    + assert (Hnonzero : old.(tcbFlagNode) <> 0) by (apply Z.eqb_neq; exact Hnode).
      destruct (proj2 Hflag tid old Hold (or_introl Hnonzero)) as [w [Hw Htid]].
      assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true).
      { destruct Hprofile as [_ [_ [_ [_ [Hlayout _]]]]]; exact (proj1 Hlayout). }
      assert (Hflagvalid : valid_flag_state sg s.(FlagState)).
      { unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags. }
      destruct (flag_linked_node_unlink_exists sg s.(FlagState)
        old.(tcbFlagNode) w Hflagvalid Hw) as [flags Hstep].
      set (post := task_delete_prepare_after_unlink
        (replace_FlagS flags (replace_EventS s.(EventState) s)) tid (task_set_flag_node old 0)).
      exists post, (Some w); split.
      * unfold task_delete_prepare_single_wait; rewrite Hptr, Hnode, Hstep; reflexivity.
      * destruct (task_delete_prepare_after_unlink_preserves_task_sched sg
          (replace_FlagS flags (replace_EventS s.(EventState) s)) tid old (task_set_flag_node old 0)
          Htasks Hready Hold eq_refl eq_refl eq_refl eq_refl eq_refl) as [Hphase Htask].
        split; [exact Hphase|]. split; [exact Htask|]. split.
        -- eapply event_update_unlisted_task_preserves_in_range; [|exact Hevents].
           intros eid e He; rewrite <- Htid; eapply task_flag_waiter_not_in_event_wait_list; eauto.
        -- split.
           ++ pose proof (flag_unlink_update_task_preserves_cross_module_consistency
                sg s old.(tcbFlagNode) w flags old
                (task_prepare_delete (task_set_flag_node old 0)) Hcross Hevents Hstep
                ltac:(rewrite Htid; exact Hold) eq_refl eq_refl eq_refl eq_refl ltac:(discriminate)) as Hpost.
              rewrite Htid in Hpost; exact Hpost.
           ++ unfold valid_flag_configuration; rewrite Henabled.
              eapply flag_unlink_preserves_state_validity; [|exact Hstep].
              unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags; exact Hflags.
Qed.

(** These are resource cutpoints, not heap synthesis from the pure theorem
    above.  Task/Scheduler cells must already reflect their actual stores;
    Event/Flag reassembly consumes the existing owners' written cells and
    genuine residuals.  Other kernel resources are carried by the ordinary
    separation-logic frame rule, not a new abstract "other invariant". *)
Lemma task_delete_prepare_event_reconstructs_wait_resources : forall sg s eid e tid old,
  valid_stable_glob_vars sg -> task_priority_unique s.(TskState) ->
  event_waitList_canonical sg s.(TskState) e.(waitList) ->
  valid_task_prio sg old.(curPrio) -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  let events := update_event_field_raw s.(EventState) eid
    (event_set_wait_list e (remove_Z_eqb tid e.(waitList))) in
  let post := task_delete_prepare_after_unlink (replace_EventS events s) tid (task_set_event_ptr old None) in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  (event_storage_rep false (event_addr sg eid)
    (event_clear_waiter (event_image sg s.(TskState) e)
      (old.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) s.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) s.(TskState))
      (Z.shiftl 1 (old.(curPrio) mod 8)) (Z.shiftl 1 (old.(curPrio) / 8))) **
    event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid) |--
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  event_raw_rep sg post.(TskState) post.(EventState).
Proof.
  intros sg s eid e tid old Hsg Hunique Hcanonical Hprio Hold events post.
  assert (Hindex : event_raw_rep sg s.(TskState) events =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  sep_apply_l_atomic (event_remove_waiter_reconstructs_raw_rep
    sg s.(TskState) s.(EventState) eid e tid old Hsg Hunique Hcanonical Hprio Hold).
  fold events; rewrite Hindex; entailer!.
Qed.

Lemma task_delete_prepare_flag_reconstructs_wait_resources : forall sg s tid old p w flags,
  valid_flag_state sg s.(FlagState) -> flag_unlink_node s.(FlagState) p = Some (w, flags) ->
  let post := task_delete_prepare_after_unlink
    (replace_FlagS flags s) tid (task_set_flag_node old 0) in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  flag_groups_rep sg flags ** flag_unlink_neighbors_rep sg s.(FlagState) w **
  sg.(g_OSFlagFreeList) # Ptr |->
    (match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) |--
  flag_node_return_loan sg.(osKernelConfig) w **
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) ** flag_raw_rep sg post.(FlagState).
Proof.
  intros sg s tid old p w flags Hvalid Hstep post.
  sep_apply_l_atomic (flag_unlink_reconstructs_raw_rep sg s.(FlagState) p w flags Hvalid Hstep).
  entailer!.
Qed.

(** At the post-unlink preparation boundary, RDY/OK is incompatible with
    both an active wait and a still-linked timeout.  Thus cleanup facts
    come from the proved phase and cross relations, not extra annotation
    assumptions.  Preservation of this boundary through Restore/hooks is
    still a separate source/protocol obligation. *)
Lemma task_delete_prepared_has_no_wait_registration : forall sg s tid generation node,
  task_delete_prepared sg tid generation s.(TskState) s.(SchedState) ->
  cross_module_consistency sg s -> s.(TskState).(inUsedTaskStates) tid = Some node ->
  node.(eventPtr) = None /\ node.(tcbFlagNode) = 0 /\
  (forall eid e, s.(EventState).(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)).
Proof.
  intros sg s tid generation node [_ [prepared [Ht [_ [Hdly [Hstat Hpend]]]]]]
    [_ [_ [Hwait [_ [_ [Hflags _]]]]]] Hnode.
  rewrite Hnode in Ht; injection Ht as Ht; subst prepared.
  destruct Hwait as [Hentries [Hback Hclosed]].
  assert (Habsent : forall eid e, s.(EventState).(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)).
  { intros eid e He Hin.
    destruct (event_waiter_task_fields sg s.(TskState) eid e tid (Hentries eid e He) Hin)
      as [old [kind [Hold [Hkind [_ [_ Hphase]]]]]].
    rewrite Hnode in Hold; injection Hold as Hold; subst old.
    unfold task_linked_wait_phase in Hphase; rewrite Hstat, Hpend in Hphase.
    destruct e.(eventType); simpl in Hkind; try discriminate;
      injection Hkind as Hkind; subst kind; simpl in Hphase; intuition discriminate. }
  split.
  - destruct node.(eventPtr) as [eid|] eqn:Hptr; [|reflexivity].
    destruct (proj1 (Hclosed tid node Hnode) eid Hptr) as [e He].
    exfalso; apply (Habsent eid e He); eapply Hback; [exact Hnode|exact He|left; exact Hptr].
  - split; [|exact Habsent].
    destruct (Z.eq_dec node.(tcbFlagNode) 0) as [Hnull|Hnonzero]; [exact Hnull|].
    destruct (proj2 Hflags tid node Hnode (or_introl Hnonzero)) as [w [Hw Htid]].
    destruct (proj1 Hflags _ w Hw) as [_ [old [Hold [_ [_ [_ [Hphase _]]]]]]].
    rewrite Htid, Hnode in Hold; injection Hold as Hold; subst old.
    unfold task_linked_wait_phase in Hphase; rewrite Hstat, Hpend in Hphase.
    simpl in Hphase; intuition discriminate.
Qed.

(** Only the selected, different TCB is overwritten.  The ready relation
    is supplied by the actual updater's preservation proof below, not by
    assuming the complete post-phase or freezing the entire shared state. *)
Lemma task_delete_prepared_update_other : forall sg tid generation tasks sched selected new sched',
  tid <> selected -> task_delete_prepared sg tid generation tasks sched ->
  sched_ready_except sg [tid] (glob_task_set_usedtask tasks selected new) sched' ->
  task_delete_prepared sg tid generation (glob_task_set_usedtask tasks selected new) sched'.
Proof.
  intros sg tid generation tasks sched selected new sched' Hne
    [_ [retiring [Ht Hfields]]] Hready.
  split; [exact Hready|]; exists retiring; split; [|exact Hfields].
  simpl; rewrite (proj2 (Z.eqb_neq _ _) Hne); exact Ht.
Qed.

Lemma event_wake_preserves_delete_relations :
  forall sg s deleting generation eid e selected old kind message result,
  task_in_range sg s.(TskState) -> task_reserved_bits_clear sg s.(TskState) ->
  task_delete_prepared sg deleting generation s.(TskState) s.(SchedState) ->
  event_in_range sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In selected e.(waitList) ->
  s.(TskState).(inUsedTaskStates) selected = Some old ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  let post := event_wake_state sg s eid e selected old kind message result in
  task_in_range sg post.(TskState) /\ task_reserved_bits_clear sg post.(TskState) /\
  task_delete_prepared sg deleting generation post.(TskState) post.(SchedState) /\
  event_in_range sg post.(TskState) post.(EventState) /\ cross_module_consistency sg post.
Proof.
  intros sg s deleting generation eid e selected old kind message result
    Htasks Hbits Hphase Hevents Hcross He Hin Hold Hkind post.
  pose proof Hphase as [Hready [retiring [Hretiring Hfields]]].
  destruct (task_delete_prepared_has_no_wait_registration sg s deleting generation retiring
    Hphase Hcross Hretiring) as [_ [_ Habsent]].
  assert (Hdifferent : deleting <> selected).
  { intro E; subst selected; exact (Habsent eid e He Hin). }
  pose proof Hcross as [_ [_ [Hwait _]]].
  destruct (event_waiter_task_fields sg s.(TskState) eid e selected
    (proj1 Hwait eid e He) Hin) as [found [actual [Hfound [Hactual [Hptr [Hmulti Hlinked]]]]]].
  assert (found = old) by congruence; subst found.
  assert (actual = kind) by congruence; subst actual.
  split; [eapply task_event_wake_single_preserves_in_range; eassumption|].
  split.
  - apply task_reserved_bits_clear_update_task; [exact Hbits|].
    apply task_status_clear_wait_preserves_reserved_bits; exact (Hbits selected old Hold).
  - split.
    + eapply task_delete_prepared_update_other; [exact Hdifferent|exact Hphase|].
      eapply sched_wake_by_status_preserves_ready_except;
        [exact Htasks|exact Hold|reflexivity| | | |exact Hready].
      * intros [E|HinDelete]; [congruence|contradiction].
      * rewrite task_event_wake_single_ready_iff_not_suspended by exact Hlinked.
        change (negb (task_is_suspended old.(stat)) =
          negb (task_is_suspended (task_clear_pending_status old.(stat) kind))).
        rewrite task_clear_pending_status_preserves_suspension; reflexivity.
      * apply task_event_wake_single_keeps_ready_task_ready.
    + split.
      * apply event_wake_preserves_event_in_range; assumption.
      * apply event_wake_preserves_cross_module_consistency; assumption.
Qed.

(** The Event bitmap and the actual priority-table lookup select the same
    surviving waiter.  Its identity is derived, not an annotation premise
    saying that the ISR happened to choose a different task. *)
Lemma event_task_rdy_preserves_delete_relations :
  forall sg s deleting generation eid e head tail kind message result,
  valid_stable_glob_vars sg -> task_in_range sg s.(TskState) ->
  task_reserved_bits_clear sg s.(TskState) ->
  task_delete_prepared sg deleting generation s.(TskState) s.(SchedState) ->
  event_in_range sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(waitList) = head :: tail ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  exists old post, s.(TskState).(inUsedTaskStates) head = Some old /\
    event_task_rdy sg s eid kind message result = Some (old.(curPrio), post) /\
    task_in_range sg post.(TskState) /\ task_reserved_bits_clear sg post.(TskState) /\
    task_delete_prepared sg deleting generation post.(TskState) post.(SchedState) /\
    event_in_range sg post.(TskState) post.(EventState) /\ cross_module_consistency sg post.
Proof.
  intros sg s deleting generation eid e head tail kind message result
    Hsg Htasks Hbits Hphase Hevents Hcross He Hlist Hkind.
  pose proof Hcross as [_ [_ [Hwait _]]].
  pose proof (proj1 Hwait eid e He) as Hentry.
  assert (Hin : In head e.(waitList)) by (rewrite Hlist; left; reflexivity).
  destruct (event_waiter_task_fields sg s.(TskState) eid e head Hentry Hin)
    as [old [actual [Hold Hfields]]].
  exists old, (event_wake_state sg s eid e head old kind message result).
  split; [exact Hold|]; split.
  - apply event_task_rdy_selects_waiter with (tail := tail); assumption.
  - apply event_wake_preserves_delete_relations; assumption.
Qed.

Lemma flag_wake_preserves_delete_relations :
  forall sg s deleting generation p w after old bits result,
  task_in_range sg s.(TskState) -> task_reserved_bits_clear sg s.(TskState) ->
  task_delete_prepared sg deleting generation s.(TskState) s.(SchedState) ->
  event_in_range sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  valid_flag_configuration sg s.(FlagState) ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  let post := flag_wake_state sg s w after old bits result in
  task_in_range sg post.(TskState) /\ task_reserved_bits_clear sg post.(TskState) /\
  task_delete_prepared sg deleting generation post.(TskState) post.(SchedState) /\
  event_in_range sg post.(TskState) post.(EventState) /\ cross_module_consistency sg post /\
  valid_flag_configuration sg post.(FlagState).
Proof.
  intros sg s deleting generation p w after old bits result Htasks Hbits Hphase Hevents Hcross Hflags Hstep Hold post.
  pose proof Hphase as [Hready [retiring [Hretiring Hfields]]].
  pose proof Hcross as [_ [_ [_ [_ [_ [Hflag _]]]]]].
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (task_delete_prepared_has_no_wait_registration sg s deleting generation retiring
    Hphase Hcross Hretiring) as [_ [Hnull _]].
  assert (Hdifferent : deleting <> w.(flagTask)).
  { intro E; apply (task_flag_null_pointer_has_no_waiter sg s.(TskState) s.(FlagState)
      deleting retiring Hflag Hretiring Hnull).
    exists p, w; split; [exact Hw|symmetry; exact E]. }
  pose proof (proj1 Hflag p w Hw) as [_ [found [Hfound [_ [_ [_ [Hlinked _]]]]]]].
  assert (found = old) by congruence; subst found.
  assert (HreadyGuard : is_effectively_ready (task_flag_wake old bits result).(stat)
    (task_flag_wake old bits result).(dly) =
    negb (task_status_is_suspended (encode_task_status (task_flag_wake old bits result).(stat)))).
  { rewrite task_flag_wake_ready_iff_not_suspended by exact Hlinked.
    change (negb (task_is_suspended old.(stat)) =
      negb (task_is_suspended (task_clear_pending_status old.(stat) PendFlag))).
    rewrite task_clear_pending_status_preserves_suspension; reflexivity. }
  split; [eapply task_flag_wake_preserves_in_range; eassumption|].
  split.
  - apply task_reserved_bits_clear_update_task; [exact Hbits|].
    apply task_status_clear_wait_preserves_reserved_bits; exact (Hbits _ old Hold).
  - split.
    + eapply task_delete_prepared_update_other; [exact Hdifferent|exact Hphase|].
      change (sched_ready_except sg [deleting]
        (glob_task_set_usedtask s.(TskState) w.(flagTask) (task_flag_wake old bits result))
        (sched_wake_task sg s.(TskState) s.(SchedState) w.(flagTask)
          (task_flag_wake old bits result))).
      rewrite <- sched_wake_by_status_eq_wake_task with
        (bits := encode_task_status (task_flag_wake old bits result).(stat)) by exact HreadyGuard.
      eapply sched_wake_by_status_preserves_ready_except;
        [exact Htasks|exact Hold|reflexivity| |exact HreadyGuard| |exact Hready].
      * intros [E|HinDelete]; [congruence|contradiction].
      * apply task_flag_wake_keeps_ready_task_ready.
    + split.
      * eapply event_update_unlisted_task_preserves_in_range; [|exact Hevents].
        intros eid e He; eapply task_flag_waiter_not_in_event_wait_list; eassumption.
      * split; [apply flag_wake_preserves_cross_module_consistency with (p := p); assumption|].
        unfold valid_flag_configuration in *.
        destruct sg.(osKernelConfig).(cfgFlagEnabled).
        -- eapply flag_unlink_preserves_state_validity; eassumption.
        -- rewrite Hflags in Hstep; discriminate.
Qed.

Lemma flag_task_rdy_preserves_delete_relations :
  forall sg s deleting generation p w bits result,
  task_in_range sg s.(TskState) -> task_reserved_bits_clear sg s.(TskState) ->
  task_delete_prepared sg deleting generation s.(TskState) s.(SchedState) ->
  event_in_range sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  valid_flag_configuration sg s.(FlagState) ->
  s.(FlagState).(flagWaitNodes) p = Some w ->
  exists schedule post, flag_task_rdy sg s p bits result = Some (schedule, post) /\
    task_in_range sg post.(TskState) /\ task_reserved_bits_clear sg post.(TskState) /\
    task_delete_prepared sg deleting generation post.(TskState) post.(SchedState) /\
    event_in_range sg post.(TskState) post.(EventState) /\ cross_module_consistency sg post /\
    valid_flag_configuration sg post.(FlagState).
Proof.
  intros sg s deleting generation p w bits result Htasks Hbits Hphase Hevents Hcross Hflags Hw.
  pose proof Hcross as [_ [_ [_ [_ [_ [Hflag _]]]]]].
  destruct (flag_task_rdy_selects_waiter sg s p w bits result Hflags Hflag Hw)
    as [old [after [Hold [Haddr [Hunlink Hstep]]]]].
  eexists; eexists; split; [exact Hstep|].
  eapply flag_wake_preserves_delete_relations; eassumption.
Qed.

Lemma task_delete_recycle_preserves_relations : forall sg s tid generation priority node name,
  task_in_range sg s.(TskState) ->
  task_delete_prepared sg tid generation s.(TskState) s.(SchedState) ->
  event_in_range sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  s.(TskState).(inUsedTaskStates) tid = Some node -> task_priority_in_range sg priority ->
  s.(TskState).(prioTbl) priority = PTTask tid -> s.(TskState).(taskCount) <= 255 ->
  (forall mid e m, s.(EventState).(inUsedEventStates) mid = Some e ->
     e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  let post := replace_TskS (task_recycle sg s.(TskState) tid priority node name) s in
  task_in_range sg post.(TskState) /\
  sched_ready_in_range sg post.(TskState) post.(SchedState) /\
  event_in_range sg post.(TskState) post.(EventState) /\ cross_module_consistency sg post.
Proof.
  intros sg s tid generation priority node name Htasks Hphase Hevents Hcross
    Hnode Hrange Hselected Hcount Hnotowner post.
  destruct (task_delete_prepared_has_no_wait_registration sg s tid generation node Hphase Hcross Hnode)
    as [Hptr [Hflag Habsent]].
  destruct (task_delete_recycle_restores_task_sched sg s.(TskState) s.(SchedState)
    tid generation priority node name Htasks Hphase Hnode Hselected Hcount) as [Htask Hready].
  split; [exact Htask|]. split; [exact Hready|]. split.
  - apply task_recycle_preserves_event_in_range; assumption.
  - eapply task_recycle_preserves_cross_module_consistency; eassumption.
Qed.

(** ECB bits are unchanged by TCB list recycling.  Their old Task index
    must nevertheless be transported because the deleted map entry is
    now absent.  This equality uses actual waiter exclusion and the shared
    encoding/representation interface; it does not duplicate bitmap cells. *)
Lemma task_delete_recycle_event_rep_eq : forall sg s tid generation priority node name,
  task_delete_prepared sg tid generation s.(TskState) s.(SchedState) ->
  cross_module_consistency sg s -> s.(TskState).(inUsedTaskStates) tid = Some node ->
  event_raw_rep sg s.(TskState) s.(EventState) =
  event_raw_rep sg (task_recycle sg s.(TskState) tid priority node name) s.(EventState).
Proof.
  intros sg s tid generation priority node name Hphase Hcross Hnode.
  destruct (task_delete_prepared_has_no_wait_registration sg s tid generation node Hphase Hcross Hnode)
    as [_ [_ Habsent]].
  apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
  apply task_recycle_preserves_event_priority_agreement; exact Habsent.
Qed.

(** The same shared heap as the ordinary global invariant, with the real
    deletion-ready phase in place of quiescent ready membership.  This is
    not private TCB ownership, an additional OS field, or a certificate for
    arbitrary ISR interference.  Lock/token and source-action obligations
    remain separate from this phase's state validity. *)
Definition task_delete_shared_validity (sg : StableGlobVars) (tid : TaskID)
  (generation : nat) (s : UCOS2_Verify_State) : Prop :=
  UCOS2_state_inv_with_ready sg s
    (task_delete_prepared sg tid generation s.(TskState) s.(SchedState)).

Definition task_delete_shared_inv (sg : StableGlobVars) (tid : TaskID)
  (generation : nat) (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (task_delete_shared_validity sg tid generation s) && UCOS2_raw_rep sg s.

(** The unlink callees may change Event and Flag, but no other owner.
    The selected TCB's priority is preserved and its status is cleared.
    The complete read/write semantics stays in the existing transformer. *)
Lemma task_delete_prepare_single_wait_frame : forall s tid old post loan,
  task_delete_prepare_single_wait s tid old = Some (post, loan) ->
  exists node,
    post = replace_FlagS post.(FlagState)
      (replace_EventS post.(EventState)
        (replace_SchedS (sched_remove_ready_task s.(SchedState) tid)
          (replace_TskS (glob_task_set_usedtask s.(TskState) tid node) s))) /\
    node.(curPrio) = old.(curPrio) /\ node.(stat) = Byte.zero /\
    node.(taskID) = old.(taskID) /\
    node.(taskGeneration) = old.(taskGeneration) /\
    node.(tcbStkPtr) = old.(tcbStkPtr).
Proof.
  intros s tid old post loan Hstep.
  unfold task_delete_prepare_single_wait in Hstep.
  destruct old.(eventPtr) as [eid|];
    [destruct (s.(EventState).(inUsedEventStates) eid) as [e|]; [|discriminate]|];
    cbn [task_set_event_ptr tcbFlagNode] in Hstep;
    destruct (Z.eqb old.(tcbFlagNode) 0);
    try (destruct (flag_unlink_node s.(FlagState) old.(tcbFlagNode))
      as [[w flags]|]; [|discriminate]);
    injection Hstep as Hpost Hloan; subst post;
    (eexists; split; [reflexivity|]; repeat split; reflexivity).
Qed.

Lemma task_delete_prepare_single_wait_establishes_shared_validity : forall sg s tid old,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  exists post loan, task_delete_prepare_single_wait s tid old = Some (post, loan) /\
    task_delete_shared_validity sg tid old.(taskGeneration) post.
Proof.
  intros sg s tid old [Hprofile [Htasks [[Hready Hmeta]
    [Hevents [Hcross [Hidle [Hbits [Hflags Hmodules]]]]]]]] Hold.
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames Hstacks]]]]].
  destruct (task_delete_prepare_single_wait_preserves_relations sg s tid old Hprofile
    Htasks Hready Hevents Hcross Hflags Hold)
    as [post [loan [Hstep [Hphase [Htasks' [Hevents' [Hcross' Hflags']]]]]]].
  destruct (task_delete_prepare_single_wait_frame s tid old post loan Hstep)
    as [node [Hpost [Hprio [Hstat [Hid [Hgen Hsp]]]]]].
  assert (HstacksAfter : parked_stacks_consistent
    post.(TskState) post.(TskState).(parkedTaskStacks)).
  { rewrite Hpost; eapply parked_stacks_consistent_update_task;
      [exact Hold|exact Hid|exact Hgen|exact Hsp|exact Hstacks]. }
  exists post, loan; split; [exact Hstep|].
  unfold task_delete_shared_validity, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]; split; [exact Htasks'|]; split.
  - split; [exact Hphase|]; rewrite Hpost; exact Hmeta.
  - split; [exact Hevents'|]; split; [exact Hcross'|]; split.
    + rewrite Hpost; intro Hrunning.
      eapply task_update_preserves_idle_tail; [exact Hold|exact Hprio|apply Hidle; exact Hrunning].
    + split.
      * rewrite Hpost; apply task_reserved_bits_clear_update_task; [exact Hbits|].
        rewrite Hstat; apply task_status_no_pending_reserved_bits_clear; reflexivity.
      * split; [exact Hflags'|].
        rewrite Hpost in HstacksAfter |- *.
        repeat (split; [assumption|]); exact HstacksAfter.
Qed.

Lemma event_wake_preserves_delete_shared_validity :
  forall sg s tid generation eid e selected old kind message result,
  task_delete_shared_validity sg tid generation s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In selected e.(waitList) ->
  s.(TskState).(inUsedTaskStates) selected = Some old ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  task_delete_shared_validity sg tid generation
    (event_wake_state sg s eid e selected old kind message result).
Proof.
  intros sg s tid generation eid e selected old kind message result
    [Hprofile [Htasks [[Hphase Hmeta] [Hevents [Hcross [Hidle [Hbits Hmodules]]]]]]]
    He Hin Hold Hkind.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames Hstacks]]]]]].
  assert (HstacksAfter : parked_stacks_consistent
    (event_wake_state sg s eid e selected old kind message result).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  destruct (event_wake_preserves_delete_relations sg s tid generation
    eid e selected old kind message result Htasks Hbits Hphase Hevents Hcross He Hin Hold Hkind)
    as [Htasks' [Hbits' [Hphase' [Hevents' Hcross']]]].
  unfold task_delete_shared_validity, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]; split; [exact Htasks'|]; split.
  - split; [exact Hphase'|].
    change (sched_metadata_in_range sg
      (sched_wake_by_status sg s.(TskState) s.(SchedState) selected
        (encode_task_status (task_event_wake_single old kind message result).(stat)))).
    unfold sched_wake_by_status; destruct task_status_is_suspended; exact Hmeta.
  - split; [exact Hevents'|]; split; [exact Hcross'|]; split.
    + intro Hrunning; eapply task_update_preserves_idle_tail;
        [exact Hold|reflexivity|apply Hidle].
      change ((sched_wake_by_status sg s.(TskState) s.(SchedState) selected
        (encode_task_status (task_event_wake_single old kind message result).(stat))).(isRunning) = true)
        in Hrunning.
      rewrite sched_wake_by_status_running_eq in Hrunning; exact Hrunning.
    + split; [exact Hbits'|].
      repeat (split; [assumption|]); exact HstacksAfter.
Qed.

Lemma flag_wake_preserves_delete_shared_validity :
  forall sg s tid generation p w flags old bits result,
  task_delete_shared_validity sg tid generation s ->
  flag_unlink_node s.(FlagState) p = Some (w, flags) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  task_delete_shared_validity sg tid generation (flag_wake_state sg s w flags old bits result).
Proof.
  intros sg s tid generation p w flags old bits result
    [Hprofile [Htasks [[Hphase Hmeta] [Hevents [Hcross [Hidle [Hbits [Hflags Hmodules]]]]]]]]
    Hstep Hold.
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames Hstacks]]]]].
  assert (HstacksAfter : parked_stacks_consistent
    (flag_wake_state sg s w flags old bits result).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  destruct (flag_wake_preserves_delete_relations sg s tid generation p w flags old bits result
    Htasks Hbits Hphase Hevents Hcross Hflags Hstep Hold)
    as [Htasks' [Hbits' [Hphase' [Hevents' [Hcross' Hflags']]]]].
  unfold task_delete_shared_validity, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]; split; [exact Htasks'|]; split.
  - split; [exact Hphase'|exact Hmeta].
  - split; [exact Hevents'|]; split; [exact Hcross'|]; split.
    + intro Hrunning; eapply task_update_preserves_idle_tail;
        [exact Hold|reflexivity|apply Hidle; exact Hrunning].
    + split; [exact Hbits'|]. split; [exact Hflags'|].
      repeat (split; [assumption|]); exact HstacksAfter.
Qed.

Lemma tick_task_step_preserves_delete_shared_validity : forall sg s tid generation cursor old,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_delete_shared_validity sg tid generation s ->
  s.(TskState).(inUsedTaskStates) cursor = Some old ->
  task_delete_shared_validity sg tid generation (tick_task_step sg cursor old s).
Proof.
  intros sg s tid generation cursor old Hmulti
    [Hprofile [Htasks [[Hphase Hmeta] [Hevents [Hcross [Hidle [Hbits Hmodules]]]]]]] Hold.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames Hstacks]]]]]].
  assert (HstacksAfter : parked_stacks_consistent
    (tick_task_step sg cursor old s).(TskState) s.(TskState).(parkedTaskStacks)).
  { rewrite tick_task_step_task_state_eq by exact Hold.
    destruct (tick_task_preserves_non_timeout_fields old) as [Hid [Hgen [_ [Hsp _]]]].
    eapply parked_stacks_consistent_update_task;
      [exact Hold|exact Hid|exact Hgen|exact Hsp|exact Hstacks]. }
  destruct (tick_task_step_preserves_delete_relations sg s tid generation cursor old
    Hmulti Htasks Hbits Hphase Hevents Hcross Hold)
    as [Htasks' [Hbits' [Hphase' [Hevents' Hcross']]]].
  assert (Hmetadata : sched_metadata_in_range sg
    (tick_task_step sg cursor old s).(SchedState) /\
    (tick_task_step sg cursor old s).(SchedState).(isRunning) = s.(SchedState).(isRunning)).
  { unfold tick_task_step.
    destruct (Z.eqb old.(dly) 0); [auto|].
    destruct (Z.eqb (tick_task_update old).(dly) 0); [|auto].
    unfold sched_wake_by_status; destruct task_status_is_suspended; auto. }
  unfold task_delete_shared_validity, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]; split; [exact Htasks'|]; split.
  - split; [exact Hphase'|exact (proj1 Hmetadata)].
  - split; [exact Hevents'|]; split; [exact Hcross'|]; split.
    + rewrite (proj2 Hmetadata); intro Hrunning.
      rewrite tick_task_step_task_state_eq by exact Hold.
      eapply task_update_preserves_idle_tail; [exact Hold| |apply Hidle; exact Hrunning].
      unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
    + split; [exact Hbits'|].
      unfold tick_task_step in HstacksAfter |- *.
      destruct (Z.eqb old.(dly) 0).
      * repeat (split; [assumption|]); exact HstacksAfter.
      * destruct (Z.eqb (tick_task_update old).(dly) 0);
          repeat (split; [assumption|]); exact HstacksAfter.
Qed.

(** Already modeled masked kernels, not an exhaustive ISR API family or
    a new machine transition system.  Event selection uses its canonical
    wait-list head; event_task_rdy_selects_waiter connects it to the
    actual bitmap/table reads.  Flag unlink retains the caller's removed
    node image, and either Boolean return is represented.  The observed
    running value for interrupt counters belongs to their source prefix.
    Save/Restore tokens, outer Tick traversal, caller stores and hooks are
    not erased by this relation. *)
Inductive task_delete_window_kernel_step (sg : StableGlobVars)
  : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| TaskDeleteWindowTick : forall s cursor node,
    s.(TskState).(inUsedTaskStates) cursor = Some node ->
    task_delete_window_kernel_step sg s (tick_task_step sg cursor node s)
| TaskDeleteWindowEventWake : forall s eid e head tail old kind message result,
    s.(EventState).(inUsedEventStates) eid = Some e -> e.(waitList) = head :: tail ->
    s.(TskState).(inUsedTaskStates) head = Some old ->
    event_type_to_pend_type e.(eventType) = Some kind ->
    task_delete_window_kernel_step sg s (event_wake_state sg s eid e head old kind message result)
| TaskDeleteWindowFlagWake : forall s p w flags old bits result,
    flag_unlink_node s.(FlagState) p = Some (w, flags) ->
    s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
    task_delete_window_kernel_step sg s (flag_wake_state sg s w flags old bits result)
| TaskDeleteWindowInterruptEnter : forall s observed_running,
    task_delete_window_kernel_step sg s
      (replace_IntrS (interrupt_enter_state observed_running s.(IntrState)) s)
| TaskDeleteWindowInterruptExit : forall s observed_running,
    task_delete_window_kernel_step sg s
      (replace_IntrS (interrupt_exit_state observed_running s.(IntrState)) s).

Lemma task_delete_window_kernel_step_preserves_shared_validity :
  forall sg tid generation before after,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_delete_window_kernel_step sg before after ->
  task_delete_shared_validity sg tid generation before ->
  task_delete_shared_validity sg tid generation after /\
  after.(IntrState).(lockNesting) = before.(IntrState).(lockNesting).
Proof.
  intros sg tid generation before after Hmulti Hstep Hvalid.
  destruct Hstep as
    [s cursor node Hnode
    |s eid e head tail old kind message result He Hlist Hold Hkind
    |s p w flags old bits result Hunlink Hold
    |s observed_running
    |s observed_running]; split.
  - eapply tick_task_step_preserves_delete_shared_validity; eassumption.
  - unfold tick_task_step; destruct (Z.eqb node.(dly) 0); [reflexivity|].
    destruct (Z.eqb (tick_task_update node).(dly) 0); reflexivity.
  - eapply event_wake_preserves_delete_shared_validity; try eassumption.
    rewrite Hlist; left; reflexivity.
  - reflexivity.
  - eapply flag_wake_preserves_delete_shared_validity; eassumption.
  - reflexivity.
  - exact Hvalid.
  - unfold interrupt_enter_state; destruct observed_running; [|reflexivity].
    destruct (s.(IntrState).(intNesting) <? 255); reflexivity.
  - exact Hvalid.
  - unfold interrupt_exit_state; destruct observed_running; [|reflexivity].
    destruct (0 <? s.(IntrState).(intNesting)); reflexivity.
Qed.

(** Reuse Rocq's standard finite reflexive-transitive closure.  A source
    execution still has to supply its kernel steps; this theorem neither
    postulates all-ISR stability nor proves that an interrupt returns. *)
Lemma task_delete_window_kernel_trace_preserves_shared_validity :
  forall sg tid generation before after,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) before after ->
  task_delete_shared_validity sg tid generation before ->
  task_delete_shared_validity sg tid generation after /\
  after.(IntrState).(lockNesting) = before.(IntrState).(lockNesting).
Proof.
  intros sg tid generation before after Hmulti Htrace.
  induction Htrace as [s|before middle after Hstep Htail IH]; intro Hvalid.
  - split; [exact Hvalid|reflexivity].
  - destruct (task_delete_window_kernel_step_preserves_shared_validity
      sg tid generation before middle Hmulti Hstep Hvalid) as [Hmiddle Hlock].
    destruct (IH Hmiddle) as [Hafter HlockAfter].
    split; [exact Hafter|rewrite HlockAfter; exact Hlock].
Qed.

Lemma task_delete_window_kernel_trace_blocks_interrupt_schedule :
  forall sg tid generation before after observed_running,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_delete_shared_validity sg tid generation before ->
  0 < before.(IntrState).(lockNesting) ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) before after ->
  interrupt_exit_requests_schedule observed_running after.(IntrState) = false.
Proof.
  intros sg tid generation before after observed_running Hmulti Hvalid Hpositive Htrace.
  pose proof (proj2 (task_delete_window_kernel_trace_preserves_shared_validity
    sg tid generation before after Hmulti Htrace Hvalid)) as Hlock.
  unfold interrupt_exit_requests_schedule; rewrite Hlock.
  assert (Hnonzero : before.(IntrState).(lockNesting) <> 0) by lia.
  rewrite (proj2 (Z.eqb_neq before.(IntrState).(lockNesting) 0) Hnonzero).
  apply Bool.andb_false_r.
Qed.

(** Actual post-store ownership is an input, not a consequence of the pure
    trace.  This reconnects the same complete global resource inventory. *)
Lemma task_delete_window_kernel_trace_reconstructs_shared_inv :
  forall sg tid generation before after,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_delete_shared_validity sg tid generation before ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) before after ->
  UCOS2_raw_rep sg after |-- task_delete_shared_inv sg tid generation after.
Proof.
  intros sg tid generation before after Hmulti Hvalid Htrace.
  pose proof (proj1 (task_delete_window_kernel_trace_preserves_shared_validity
    sg tid generation before after Hmulti Htrace Hvalid)) as Hafter.
  unfold task_delete_shared_inv; entailer!.
Qed.

(** Rejoin ordinary global validity after actual recycling.  The selected
    task is non-idle and owns no Mutex at this point; these are source/
    caller obligations, not extra guards in task_recycle.  Cache
    bytes stay unchanged until the later contracted scheduling operation. *)
Lemma task_delete_recycle_restores_global_validity :
  forall sg s tid generation priority node name,
  task_delete_shared_validity sg tid generation s ->
  s.(TskState).(inUsedTaskStates) tid = Some node -> task_priority_in_range sg priority ->
  s.(TskState).(prioTbl) priority = PTTask tid -> s.(TskState).(taskCount) <= 255 ->
  node.(curPrio) <> sg.(osLowestPrio) ->
  (forall mid e m, s.(EventState).(inUsedEventStates) mid = Some e ->
     e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  UCOS2_state_inv sg
    (replace_TskS (task_recycle sg s.(TskState) tid priority node name) s).
Proof.
  intros sg s tid generation priority node name
    [Hprofile [Htasks [[Hphase Hmeta] [Hevents [Hcross [Hidle [Hbits Hmodules]]]]]]]
    Hnode Hpriority Htable Hcount Hnonidle Hnotowner.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames Hstacks]]]]]].
  assert (HstacksAfter : parked_stacks_consistent
    (task_recycle sg s.(TskState) tid priority node name) s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_transport with (before := s.(TskState)).
    - intros observer slot gen Hhistory; exact Hhistory.
    - intros slot updated Hupdated.
      change (task_unlink_used_map s.(TskState).(inUsedTaskStates) tid node slot = Some updated)
        in Hupdated.
      unfold task_unlink_used_map in Hupdated.
      destruct (Z.eq_dec slot tid); [discriminate|].
      destruct (s.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
      injection Hupdated as Hupdated; subst updated.
      exists old; split; [assumption || reflexivity|]; repeat split; reflexivity.
    - exact Hstacks. }
  destruct (task_delete_recycle_preserves_relations sg s tid generation priority node name
    Htasks Hphase Hevents Hcross Hnode Hpriority Htable Hcount Hnotowner)
    as [Htasks' [Hready' [Hevents' Hcross']]].
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]; split; [exact Htasks'|]; split.
  - exact (conj Hready' Hmeta).
  - split; [exact Hevents'|]; split; [exact Hcross'|]; split.
    + intro Hrunning; apply task_recycle_preserves_idle_tail;
        [apply Hidle; exact Hrunning|exact Hnode|exact Hnonidle].
    + split.
      2: { repeat (split; [assumption|]); exact HstacksAfter. }
      intros slot t Ht.
      change (task_unlink_used_map s.(TskState).(inUsedTaskStates) tid node slot = Some t) in Ht.
      unfold task_unlink_used_map in Ht.
      destruct (Z.eq_dec slot tid); [discriminate|].
      destruct (s.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
      injection Ht as Ht; subst t; exact (Hbits slot old Hold).
Qed.

(** These kernels change live status/delay/message fields, not the task
    pool ledger or the captured priority table.  Every saved invocation
    remains the same live instance; this is not a scheduling/return claim. *)
Lemma task_delete_window_kernel_step_task_frame : forall sg before after,
  task_delete_window_kernel_step sg before after ->
  after.(TskState).(prioTbl) = before.(TskState).(prioTbl) /\
  after.(TskState).(taskCount) = before.(TskState).(taskCount) /\
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  (forall observer origin,
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin).
Proof.
  intros sg before after Hstep; destruct Hstep as
    [s cursor node Hnode
    |s eid e head tail old kind message result He Hlist Hold Hkind
    |s p w flags old bits result Hunlink Hold
    |s observed_running
    |s observed_running].
  - rewrite tick_task_step_task_state_eq by exact Hnode.
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    intros observer origin Hactive.
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode| |exact Hactive].
    unfold tick_task_update; destruct (Z.eqb node.(dly) 0); reflexivity.
  - split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    intros observer origin Hactive.
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive].
  - split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    intros observer origin Hactive.
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive].
  - split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|auto].
  - split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|auto].
Qed.

Lemma task_delete_window_kernel_trace_task_frame : forall sg before after,
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) before after ->
  after.(TskState).(prioTbl) = before.(TskState).(prioTbl) /\
  after.(TskState).(taskCount) = before.(TskState).(taskCount) /\
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  (forall observer origin,
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin).
Proof.
  intros sg before after Htrace.
  induction Htrace as [s|before middle after Hstep Htail IH].
  - split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|auto].
  - destruct (task_delete_window_kernel_step_task_frame sg before middle Hstep)
      as [Htable [Hcount [Hlife Hactive]]].
    destruct IH as [HtableAfter [HcountAfter [HlifeAfter HactiveAfter]]].
    split; [rewrite HtableAfter; exact Htable|]; split; [rewrite HcountAfter; exact Hcount|].
    split; [rewrite HlifeAfter; exact Hlife|].
    intros observer origin Hsaved; apply HactiveAfter, Hactive; exact Hsaved.
Qed.

(** Reuse the saved-token and creation-resource interfaces.  The equality
    transports an already owned private assertion; it does not allocate
    storage or manufacture a CPU token.  The second Save in OSTaskDel still
    produces its own CPSR value and overwrites the local cpu_sr variable. *)
Lemma task_delete_window_kernel_trace_preserves_caller_resources : forall sg before after token,
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) before after ->
  interrupt_token_for_invocation before token ->
  task_invocation_active before.(TskState)
    token.(savedInvocation) token.(savedOrigin) ->
  interrupt_token_for_invocation after token /\
  task_invocation_active after.(TskState)
    token.(savedInvocation) token.(savedOrigin) /\
  task_private_storage sg after.(TskState) token.(savedInvocation) =
    task_private_storage sg before.(TskState) token.(savedInvocation).
Proof.
  intros sg before after token Htrace Htoken Hsaved.
  destruct (task_delete_window_kernel_trace_task_frame sg before after Htrace)
    as [_ [_ [Hlife Hactive]]].
  split.
  - unfold interrupt_token_for_invocation; rewrite Hlife; exact Htoken.
  - split; [apply Hactive; exact Hsaved|].
    apply task_creation_frame_private_storage.
    unfold task_creation_frame, task_creation_view; rewrite Hlife; reflexivity.
Qed.

(** The whole captured TCB, including its physical neighbour links, stays
    unchanged in this window.  Other TCBs need not stay unchanged.  Tick's
    zero-delay test and the actual Event/Flag unlink relations establish
    this fact; it is not an environment no-write premise. *)
Lemma task_delete_window_kernel_step_preserves_selected_task :
  forall sg tid generation before after node,
  task_delete_shared_validity sg tid generation before ->
  before.(TskState).(inUsedTaskStates) tid = Some node ->
  task_delete_window_kernel_step sg before after ->
  after.(TskState).(inUsedTaskStates) tid = Some node.
Proof.
  intros sg tid generation before after node Hvalid Hnode Hstep.
  pose proof Hvalid as [_ [_ [[Hphase _] [_ [Hcross _]]]]].
  destruct (task_delete_prepared_has_no_wait_registration sg before tid generation node
    Hphase Hcross Hnode) as [_ [Hnull Habsent]].
  destruct Hstep as
    [s cursor old Hold
    |s eid e head tail old kind message result He Hlist Hold Hkind
    |s p w flags old bits result Hunlink Hold
    |s observed_running
    |s observed_running].
  - destruct (Z.eq_dec tid cursor) as [E|Hdifferent].
    + subst cursor; rewrite Hnode in Hold; injection Hold as Hold; subst old.
      destruct Hphase as [_ [prepared [Hprepared [_ [Hdly _]]]]].
      rewrite Hnode in Hprepared; injection Hprepared as Hprepared; subst prepared.
      rewrite tick_task_step_zero_delay_eq by exact Hdly; exact Hnode.
    + rewrite tick_task_step_other_task_eq by exact Hdifferent; exact Hnode.
  - assert (Hdifferent : tid <> head).
    { intro E; subst head; apply (Habsent eid e He); rewrite Hlist; left; reflexivity. }
    cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq _ _) Hdifferent); exact Hnode.
  - pose proof Hcross as [_ [_ [_ [_ [_ [Hflag _]]]]]].
    pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hw.
    assert (Hdifferent : tid <> w.(flagTask)).
    { intro E; apply (task_flag_null_pointer_has_no_waiter sg s.(TskState) s.(FlagState)
        tid node Hflag Hnode Hnull).
      exists p, w; split; [exact Hw|symmetry; exact E]. }
    cbn [flag_wake_state replace_FlagS replace_SchedS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq _ _) Hdifferent); exact Hnode.
  - exact Hnode.
  - exact Hnode.
Qed.

(** A wake only removes wait-list entries.  It cannot create ownership of
    a Mutex that the retiring task did not own before the window.  Actual
    Mutex Post/Accept/Pend caller actions are not silently included here. *)
Lemma task_delete_window_kernel_step_preserves_mutex_owner_exclusion : forall sg tid before after,
  task_delete_window_kernel_step sg before after ->
  (forall mid e m, before.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  (forall mid e m, after.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid).
Proof.
  intros sg tid before after Hstep Howner; destruct Hstep as
    [s cursor node Hnode
    |s eid e head tail old kind message result He Hlist Hold Hkind
    |s p w flags old bits result Hunlink Hold
    |s observed_running
    |s observed_running].
  - unfold tick_task_step; destruct (Z.eqb node.(dly) 0); [exact Howner|].
    destruct (Z.eqb (tick_task_update node).(dly) 0); exact Howner.
  - intros mid new m Hnew Htype Hfields.
    cbn [event_wake_state replace_SchedS replace_EventS EventState
      update_event_field_raw inUsedEventStates] in Hnew.
    destruct (Z.eqb mid eid) eqn:E.
    + injection Hnew as Hnew; subst new.
      eapply Howner; [exact He|exact Htype|exact Hfields].
    + eapply Howner; [exact Hnew|exact Htype|exact Hfields].
  - exact Howner.
  - exact Howner.
  - exact Howner.
Qed.

Lemma task_delete_window_kernel_trace_frame : forall sg tid generation before after node,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) before after ->
  task_delete_shared_validity sg tid generation before ->
  before.(TskState).(inUsedTaskStates) tid = Some node ->
  (forall mid e m, before.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  after.(TskState).(inUsedTaskStates) tid = Some node /\
  after.(TskState).(prioTbl) = before.(TskState).(prioTbl) /\
  after.(TskState).(taskCount) = before.(TskState).(taskCount) /\
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  (forall observer origin, task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin) /\
  (forall mid e m, after.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid).
Proof.
  intros sg tid generation before after node Hmulti Htrace.
  induction Htrace as [s|before middle after Hstep Htail IH]; intros Hvalid Hnode Howner.
  - split; [exact Hnode|]; split; [reflexivity|]; split; [reflexivity|];
      split; [reflexivity|]; split; [auto|exact Howner].
  - pose proof (proj1 (task_delete_window_kernel_step_preserves_shared_validity
      sg tid generation before middle Hmulti Hstep Hvalid)) as Hmiddle.
    pose proof (task_delete_window_kernel_step_preserves_selected_task
      sg tid generation before middle node Hvalid Hnode Hstep) as HnodeMiddle.
    pose proof (task_delete_window_kernel_step_preserves_mutex_owner_exclusion
      sg tid before middle Hstep Howner) as HownerMiddle.
    destruct (task_delete_window_kernel_step_task_frame sg before middle Hstep)
      as [Htable [Hcount [Hlife Hactive]]].
    destruct (IH Hmiddle HnodeMiddle HownerMiddle)
      as [HnodeAfter [HtableAfter [HcountAfter [HlifeAfter [HactiveAfter HownerAfter]]]]].
    split; [exact HnodeAfter|]; split; [rewrite HtableAfter; exact Htable|].
    split; [rewrite HcountAfter; exact Hcount|]; split; [rewrite HlifeAfter; exact Hlife|].
    split; [intros observer origin Hsaved; apply HactiveAfter, Hactive; exact Hsaved|exact HownerAfter].
Qed.

(** Entry obligations now travel through the proved kernels instead of
    being re-assumed at the recycle point.  The count bound comes from the
    selected pool invariant.  Hooks and additional ISR families still need
    their own source contracts before they can instantiate this trace. *)
Lemma task_delete_window_kernel_trace_recycle_restores_global_validity :
  forall sg tid generation before after priority node name,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg) before after ->
  task_delete_shared_validity sg tid generation before ->
  before.(TskState).(inUsedTaskStates) tid = Some node -> task_priority_in_range sg priority ->
  before.(TskState).(prioTbl) priority = PTTask tid -> node.(curPrio) <> sg.(osLowestPrio) ->
  (forall mid e m, before.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  UCOS2_state_inv sg
    (replace_TskS (task_recycle sg after.(TskState) tid priority node name) after).
Proof.
  intros sg tid generation before after priority node name Hmulti Htrace Hvalid
    Hnode Hpriority Htable Hnonidle Howner.
  pose proof (proj1 (task_delete_window_kernel_trace_preserves_shared_validity
    sg tid generation before after Hmulti Htrace Hvalid)) as Hafter.
  destruct (task_delete_window_kernel_trace_frame sg tid generation before after node
    Hmulti Htrace Hvalid Hnode Howner) as [HnodeAfter [HtableAfter [_ [_ [_ HownerAfter]]]]].
  pose proof Hafter as [Hprofile [Htasks _]].
  pose proof (task_count_in_pool_range sg after.(TskState) Hprofile Htasks) as Hcount.
  eapply task_delete_recycle_restores_global_validity;
    [exact Hafter|exact HnodeAfter|exact Hpriority|rewrite HtableAfter; exact Htable|
     lia|exact Hnonidle|exact HownerAfter].
Qed.

(** These two source-local writes deliberately have no running/ISR guard,
    unlike the public OSSchedLock/OSSchedUnlock APIs.  They affect only the
    physical counter, not the CPU's masking state. *)
Definition task_delete_lock_state (s : InterruptAbstractState) : InterruptAbstractState :=
  {| intNesting := s.(intNesting);
     lockNesting := if s.(lockNesting) <? 255 then s.(lockNesting) + 1 else s.(lockNesting) |}.

Definition task_delete_unlock_state (s : InterruptAbstractState) : InterruptAbstractState :=
  {| intNesting := s.(intNesting);
     lockNesting := if 0 <? s.(lockNesting) then s.(lockNesting) - 1 else s.(lockNesting) |}.

Lemma task_delete_lock_preserves_counters_in_range : forall s,
  interrupt_counters_in_range s -> interrupt_counters_in_range (task_delete_lock_state s).
Proof.
  intros [nesting lock] [Hint Hlock]; split; [exact Hint|].
  pose proof (task_delete_window_lock_in_range lock Hlock); cbn; lia.
Qed.

Lemma task_delete_unlock_preserves_counters_in_range : forall s,
  interrupt_counters_in_range s -> interrupt_counters_in_range (task_delete_unlock_state s).
Proof.
  intros [nesting lock] [Hint Hlock]; split; [exact Hint|].
  change (0 <= lock <= 255) in Hlock.
  change (0 <= (if 0 <? lock then lock - 1 else lock) <= 255).
  destruct (0 <? lock) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; lia.
Qed.

(** At saturation the source produces 254, not the old value 255.  In the
    unsaturated case this restores only lockNesting; interrupt nesting can
    change during the represented window and is not equated to its entry. *)
Lemma task_delete_unlock_after_lock_count_eq : forall before resumed,
  0 <= before.(lockNesting) <= 255 ->
  resumed.(lockNesting) = (task_delete_lock_state before).(lockNesting) ->
  (task_delete_unlock_state resumed).(lockNesting) =
    if before.(lockNesting) <? 255 then before.(lockNesting) else 254.
Proof.
  intros before resumed Hrange Hlock.
  set (lock := before.(lockNesting)) in *.
  change (resumed.(lockNesting) = if lock <? 255 then lock + 1 else lock) in Hlock.
  change ((if 0 <? resumed.(lockNesting) then resumed.(lockNesting) - 1 else resumed.(lockNesting)) =
    if lock <? 255 then lock else 254).
  rewrite Hlock; destruct (lock <? 255) eqn:E.
  - apply Z.ltb_lt in E; destruct (0 <? lock + 1) eqn:Htest;
      [apply Z.ltb_lt in Htest|apply Z.ltb_ge in Htest]; lia.
  - apply Z.ltb_ge in E; destruct (0 <? lock) eqn:Htest;
      [apply Z.ltb_lt in Htest|apply Z.ltb_ge in Htest]; lia.
Qed.

Lemma task_delete_kernel_window_lock_count_eq : forall sg tid generation before resumed,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_delete_shared_validity sg tid generation before ->
  0 <= before.(IntrState).(lockNesting) <= 255 ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg)
    (replace_IntrS (task_delete_lock_state before.(IntrState)) before) resumed ->
  (task_delete_unlock_state resumed.(IntrState)).(lockNesting) =
    if before.(IntrState).(lockNesting) <? 255 then before.(IntrState).(lockNesting) else 254.
Proof.
  intros sg tid generation before resumed Hmulti Hvalid Hrange Htrace.
  apply task_delete_unlock_after_lock_count_eq; [exact Hrange|].
  exact (proj2 (task_delete_window_kernel_trace_preserves_shared_validity sg tid generation
    (replace_IntrS (task_delete_lock_state before.(IntrState)) before) resumed Hmulti Htrace Hvalid)).
Qed.

(** Compose the actual lock writes with the modeled interference and the
    source recycle suffix.  This ends before the final Restore/OS_Sched,
    and does not insert an unverified Delete/TLS hook into the trace. *)
Lemma task_delete_kernel_window_recycle_restores_global_validity :
  forall sg tid generation before resumed priority node name,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_delete_shared_validity sg tid generation before ->
  before.(TskState).(inUsedTaskStates) tid = Some node -> task_priority_in_range sg priority ->
  before.(TskState).(prioTbl) priority = PTTask tid -> node.(curPrio) <> sg.(osLowestPrio) ->
  (forall mid e m, before.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg)
    (replace_IntrS (task_delete_lock_state before.(IntrState)) before) resumed ->
  UCOS2_state_inv sg
    (replace_TskS (task_recycle sg resumed.(TskState) tid priority node name)
      (replace_IntrS (task_delete_unlock_state resumed.(IntrState)) resumed)).
Proof.
  intros sg tid generation before resumed priority node name Hmulti Hvalid
    Hnode Hpriority Htable Hnonidle Howner Htrace.
  exact (task_delete_window_kernel_trace_recycle_restores_global_validity sg tid generation
    (replace_IntrS (task_delete_lock_state before.(IntrState)) before) resumed priority node name
    Hmulti Htrace Hvalid Hnode Hpriority Htable Hnonidle Howner).
Qed.
