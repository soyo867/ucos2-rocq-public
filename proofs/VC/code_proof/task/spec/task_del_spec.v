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
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Export Ucos2Verify.VC.code.core.spec.os_dummy_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_del_hook_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.

(** Intake seed, not an accepted OSTaskDel proof.  The original unconsumed
    task_delete_spec.v is preserved; this active case owns the adaptation of
    its source-phase helpers to the current invariant and lock_added patch.
    Old 255 -> 254 lemmas describe the original release rule only; the
    repaired implementation needs a separate flag-aware release rule. *)

Import ListNotations UCOS2_C_Rules KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Static facts of this compiled program, carried with the same [sg].
    The TCB initializer requires the pool alignment; the names-disabled
    Event initializer requires and preserves the native-field ABI premise.
    Initialization does not derive arbitrary opaque C field addresses. *)
Definition task_delete_static_profile (sg : StableGlobVars) : Prop :=
  selected_kernel_profile sg /\
  sg.(osKernelConfig) = selected_kernel_configuration /\
  sg.(g_OSTCBTbl) mod 4 = 0 /\ event_table_layout_prop sg.

Lemma task_delete_static_profile_from_initialization : forall sg,
  selected_kernel_profile sg -> init_tcb_list_profile sg ->
  init_tcb_list_layout sg -> event_table_layout_prop sg ->
  task_delete_static_profile sg.
Proof.
  intros sg Hprofile [_ [_ [_ Hconfig]]] [_ [_ [_ [Halign _]]]] Hevent.
  unfold task_delete_static_profile; auto.
Qed.

Lemma task_delete_static_profile_argument_checks : forall sg,
  task_delete_static_profile sg -> sg.(osKernelConfig).(cfgArgumentChecks) = true.
Proof. intros sg [_ [Hconfig _]]; rewrite Hconfig; reflexivity. Qed.

Lemma task_delete_static_profile_slot_not_reserved : forall sg tid,
  task_delete_static_profile sg -> task_slot_addr sg tid <> 1.
Proof.
  intros sg tid [_ [Hconfig [Halign _]]].
  unfold task_slot_addr; rewrite Hconfig.
  change (sg.(g_OSTCBTbl) + tid * 64 <> 1).
  pose proof (Z.div_mod sg.(g_OSTCBTbl) 4 ltac:(lia)) as Hdivide.
  rewrite Halign in Hdivide; lia.
Qed.

Lemma task_delete_static_profile_event_layout : forall sg eid,
  task_delete_static_profile sg -> valid_event_id sg eid ->
  event_object_layout_prop sg eid.
Proof.
  intros sg eid [_ [_ [_ Hlayout]]] Hvalid.
  exact (event_table_layout_select sg eid Hlayout Hvalid).
Qed.

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
  (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
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

Lemma task_delete_prepared_excludes_stable_ready : forall sg tid generation tasks sched,
  task_delete_prepared sg tid generation tasks sched ->
  ~ sched_ready_in_range sg tasks sched.
Proof.
  intros sg tid generation tasks sched
    [[Hstructure Hmembership] [node [Hnode [Hgeneration [Hdelay [Hstatus Hpend]]]]]]
    [_ [_ [Hcomplete _]]].
  assert (Hready : is_effectively_ready node.(stat) node.(dly) = true).
  { rewrite Hdelay, Hstatus; reflexivity. }
  destruct (proj1 (Hmembership tid node Hnode) (Hcomplete tid node Hnode Hready))
    as [_ Hnot].
  apply Hnot; left; reflexivity.
Qed.

Lemma task_delete_shared_validity_excludes_stable_inv : forall sg tid generation state,
  task_delete_shared_validity sg tid generation state -> ~ UCOS2_state_inv sg state.
Proof.
  intros sg tid generation state [_ [_ [[Hphase _] _]]] [_ [_ [[Hready _] _]]].
  exact (task_delete_prepared_excludes_stable_ready sg tid generation
    state.(TskState) state.(SchedState) Hphase Hready).
Qed.

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
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  destruct (task_delete_prepare_single_wait_preserves_relations sg s tid old Hprofile
    Htasks Hready Hevents Hcross Hflags Hold)
    as [post [loan [Hstep [Hphase [Htasks' [Hevents' [Hcross' Hflags']]]]]]].
  destruct (task_delete_prepare_single_wait_frame s tid old post loan Hstep)
    as [node [Hpost [Hprio [Hstat [Hid [Hgen Hsp]]]]]].
  assert (HstacksAfter : parked_stacks_consistent
    post.(TskState) post.(TskState).(parkedTaskStacks)).
  { rewrite Hpost; eapply parked_stacks_consistent_update_task;
      [exact Hold|exact Hid|exact Hgen|exact Hsp|exact Hstacks]. }
  assert (HreferencesAfter : kernel_names_valid sg post).
  { clear Hpost HstacksAfter.
    unfold task_delete_prepare_single_wait in Hstep.
    destruct old.(eventPtr) as [eid|] eqn:Hptr.
    - destruct (s.(EventState).(inUsedEventStates) eid) as [e|] eqn:He; [|discriminate].
      pose proof Hcross as [_ [_ [_ [_ [_ [Hflag _]]]]]].
      pose proof (proj1 (task_with_event_ptr_has_no_flag_registration
        sg s.(TskState) s.(FlagState) tid old eid Hflag Hold Hptr)) as Hnull.
      cbn [task_set_event_ptr tcbFlagNode] in Hstep; rewrite Hnull, Z.eqb_refl in Hstep.
      injection Hstep as Hpost Hloan; subst post.
      eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
      + eapply task_update_name_references; [exact Hold|reflexivity].
      + eapply event_update_preserves_name_references; [exact He|reflexivity].
      + intros; assumption.
      + intros; assumption.
      + intros; assumption.
    - destruct (Z.eqb old.(tcbFlagNode) 0) eqn:Hnull.
      + injection Hstep as Hpost Hloan; subst post.
        eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
        * eapply task_update_name_references; [exact Hold|reflexivity].
        * intros; assumption.
        * intros; assumption.
        * intros; assumption.
        * intros; assumption.
      + destruct (flag_unlink_node s.(FlagState) old.(tcbFlagNode)) as [[w flags]|] eqn:Hflag;
          [|discriminate].
        injection Hstep as Hpost Hloan; subst post.
        eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
        * eapply task_update_name_references; [exact Hold|reflexivity].
        * intros; assumption.
        * eapply flag_unlink_name_references; exact Hflag.
        * intros; assumption.
        * intros; assumption. }
  assert (HpendingAfter : pending_mutex_consistency sg post.(TskState) post.(EventState)).
  { clear Hpost HstacksAfter.
    unfold task_delete_prepare_single_wait in Hstep.
    destruct old.(eventPtr) as [eid|] eqn:Hptr.
    - destruct (s.(EventState).(inUsedEventStates) eid) as [e|] eqn:He; [|discriminate].
      pose proof Hcross as [_ [_ [_ [_ [_ [Hflag _]]]]]].
      pose proof (proj1 (task_with_event_ptr_has_no_flag_registration
        sg s.(TskState) s.(FlagState) tid old eid Hflag Hold Hptr)) as Hnull.
      cbn [task_set_event_ptr tcbFlagNode] in Hstep; rewrite Hnull, Z.eqb_refl in Hstep.
      injection Hstep as Hpost Hloan; subst post.
      eapply pending_mutex_consistency_event_fields_update;
        [exact He|reflexivity|reflexivity|exact Hpending].
    - destruct (Z.eqb old.(tcbFlagNode) 0);
        try (destruct (flag_unlink_node s.(FlagState) old.(tcbFlagNode)) as [[w flags]|];
          [|discriminate]);
        injection Hstep as Hpost Hloan; subst post; exact Hpending. }
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
        rewrite Hpost in HreferencesAfter, HpendingAfter, HstacksAfter |- *.
        repeat (split; [assumption|]); exact HpendingAfter.
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
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HpendingAfter : pending_mutex_consistency sg
    (event_wake_state sg s eid e selected old kind message result).(TskState)
    (event_wake_state sg s eid e selected old kind message result).(EventState)).
  { eapply pending_mutex_consistency_event_fields_update;
      [exact He|reflexivity|reflexivity|exact Hpending]. }
  assert (HreferencesAfter : kernel_names_valid sg
    (event_wake_state sg s eid e selected old kind message result)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - eapply event_update_preserves_name_references; [exact He|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
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
      repeat (split; [assumption|]); exact HpendingAfter.
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
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  assert (HreferencesAfter : kernel_names_valid sg (flag_wake_state sg s w flags old bits result)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - intros; assumption.
    - eapply flag_unlink_name_references; exact Hstep.
    - intros; assumption.
    - intros; assumption. }
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
      repeat (split; [assumption|]); exact Hpending.
Qed.

Lemma tick_task_step_preserves_delete_shared_validity : forall sg s tid generation cursor old,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_delete_shared_validity sg tid generation s ->
  s.(TskState).(inUsedTaskStates) cursor = Some old ->
  task_delete_shared_validity sg tid generation (tick_task_step sg cursor old s).
Proof.
  intros sg s tid generation cursor old Hmulti
    [Hprofile [Htasks [[Hphase Hmeta] [Hevents [Hcross [Hidle [Hbits Hmodules]]]]]]] Hold.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HreferencesAfter : kernel_names_valid sg (tick_task_step sg cursor old s)).
  { eapply kernel_names_valid_frame; [exact Hreferences| | | | | |].
    - unfold tick_task_step; destruct (Z.eqb old.(dly) 0);
        [|destruct (Z.eqb (tick_task_update old).(dly) 0)]; reflexivity.
    - rewrite tick_task_step_task_state_eq by exact Hold.
      eapply task_update_name_references; [exact Hold|].
      unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
    - unfold tick_task_step; destruct (Z.eqb old.(dly) 0);
        [|destruct (Z.eqb (tick_task_update old).(dly) 0)]; intros; assumption.
    - unfold tick_task_step; destruct (Z.eqb old.(dly) 0);
        [|destruct (Z.eqb (tick_task_update old).(dly) 0)]; intros; assumption.
    - unfold tick_task_step; destruct (Z.eqb old.(dly) 0);
        [|destruct (Z.eqb (tick_task_update old).(dly) 0)]; intros; assumption.
    - unfold tick_task_step; destruct (Z.eqb old.(dly) 0);
        [|destruct (Z.eqb (tick_task_update old).(dly) 0)]; intros; assumption. }
  assert (HpendingAfter : pending_mutex_consistency sg
    (tick_task_step sg cursor old s).(TskState) (tick_task_step sg cursor old s).(EventState)).
  { unfold tick_task_step; destruct (Z.eqb old.(dly) 0);
      [|destruct (Z.eqb (tick_task_update old).(dly) 0)]; exact Hpending. }
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
      unfold tick_task_step in HreferencesAfter, HpendingAfter, HstacksAfter |- *.
      destruct (Z.eqb old.(dly) 0) eqn:Hdelay.
      * repeat (split; [assumption|]); exact HpendingAfter.
      * destruct (Z.eqb (tick_task_update old).(dly) 0);
          repeat (split; [assumption|]); exact HpendingAfter.
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
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HreferencesAfter : kernel_names_valid sg
    (replace_TskS (task_recycle sg s.(TskState) tid priority node name) s)).
  { apply kernel_names_valid_replace_task; [exact Hreferences|].
    intros p [slot [found [Hget Hname]]].
    change (task_unlink_used_map s.(TskState).(inUsedTaskStates) tid node slot = Some found) in Hget.
    unfold task_unlink_used_map in Hget; destruct (Z.eq_dec slot tid); [discriminate|].
    destruct (s.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    injection Hget as Hfound; subst found.
    exists slot, old; split; [exact Hold|exact Hname]. }
  assert (HpendingAfter : pending_mutex_consistency sg
    (task_recycle sg s.(TskState) tid priority node name) s.(EventState)).
  { eapply pending_mutex_consistency_table_transport; [| |exact Hpending].
    - intros p Hclaim; simpl; destruct (Z.eq_dec p priority); [|reflexivity].
      subst p; exfalso; eapply pending_mutex_consistency_task_slot_excludes_claim; eassumption.
    - intros; reflexivity. }
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
      2: { repeat (split; [assumption|]); exact HpendingAfter. }
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

(** Historical unflagged writes, retained with their original mathematical
    meaning.  The current lock_added implementation uses the release rule
    below; the old saturated 255 -> 254 theorem is not its specification. *)
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

(** The real local Boolean is set exactly when this invocation increments
    the counter. It is not a stored kernel flag or an environmental guard. *)
Definition task_delete_lock_added (before : InterruptAbstractState) : bool :=
  before.(lockNesting) <? 255.

Definition task_delete_release_state (lock_added : bool)
  (state : InterruptAbstractState) : InterruptAbstractState :=
  {| intNesting := state.(intNesting);
     lockNesting :=
       if (lock_added && (0 <? state.(lockNesting)))%bool
       then state.(lockNesting) - 1 else state.(lockNesting) |}.

Lemma task_delete_release_preserves_counters_in_range : forall added state,
  interrupt_counters_in_range state ->
  interrupt_counters_in_range (task_delete_release_state added state).
Proof.
  intros added [nesting lock] [Hint Hlock]; split; [exact Hint|].
  change (0 <= lock <= 255) in Hlock.
  change (0 <= (if (added && (0 <? lock))%bool then lock - 1 else lock) <= 255).
  destruct added.
  - change (0 <= (if 0 <? lock then lock - 1 else lock) <= 255).
    destruct (0 <? lock) eqn:E;
      [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; lia.
  - exact Hlock.
Qed.

(** Exact endpoint under a lock-preserving completed window. Interrupt
    nesting is intentionally not equated to its entry value. *)
Lemma task_delete_release_after_lock_count_eq : forall before resumed,
  0 <= before.(lockNesting) <= 255 ->
  resumed.(lockNesting) = (task_delete_lock_state before).(lockNesting) ->
  (task_delete_release_state (task_delete_lock_added before) resumed).(lockNesting) =
    before.(lockNesting).
Proof.
  intros before resumed Hrange Hlock.
  unfold task_delete_lock_added, task_delete_release_state; cbn.
  change (resumed.(lockNesting) =
    if before.(lockNesting) <? 255 then before.(lockNesting) + 1 else before.(lockNesting)) in Hlock.
  rewrite Hlock; destruct (before.(lockNesting) <? 255) eqn:E; simpl.
  - apply Z.ltb_lt in E; destruct (0 <? before.(lockNesting) + 1) eqn:Hpositive;
      [apply Z.ltb_lt in Hpositive|apply Z.ltb_ge in Hpositive]; lia.
  - reflexivity.
Qed.

Lemma task_delete_release_keeps_interrupt_nesting : forall added state,
  (task_delete_release_state added state).(intNesting) = state.(intNesting).
Proof. reflexivity. Qed.

Lemma task_delete_kernel_window_release_count_eq :
  forall sg tid generation before resumed,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  task_delete_shared_validity sg tid generation before ->
  0 <= before.(IntrState).(lockNesting) <= 255 ->
  clos_refl_trans_1n _ (task_delete_window_kernel_step sg)
    (replace_IntrS (task_delete_lock_state before.(IntrState)) before) resumed ->
  (task_delete_release_state (task_delete_lock_added before.(IntrState))
    resumed.(IntrState)).(lockNesting) = before.(IntrState).(lockNesting).
Proof.
  intros sg tid generation before resumed Hmulti Hvalid Hrange Htrace.
  apply task_delete_release_after_lock_count_eq; [exact Hrange|].
  exact (proj2 (task_delete_window_kernel_trace_preserves_shared_validity sg tid generation
    (replace_IntrS (task_delete_lock_state before.(IntrState)) before) resumed Hmulti Htrace Hvalid)).
Qed.

Lemma task_delete_kernel_window_flagged_recycle_restores_global_validity :
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
      (replace_IntrS (task_delete_release_state (task_delete_lock_added before.(IntrState))
        resumed.(IntrState)) resumed)).
Proof.
  intros sg tid generation before resumed priority node name Hmulti Hvalid
    Hnode Hpriority Htable Hnonidle Howner Htrace.
  exact (task_delete_window_kernel_trace_recycle_restores_global_validity sg tid generation
    (replace_IntrS (task_delete_lock_state before.(IntrState)) before) resumed priority node name
    Hmulti Htrace Hvalid Hnode Hpriority Htable Hnonidle Howner).
Qed.

(** The option is accompanied by the real typed node owner.  The removed
    node is absent from Flag raw, so no part of this predicate is supplied
    by a second Flag representation or a second full-stack assertion. *)
Definition task_delete_return_loan (sg : StableGlobVars)
  (loan : option FlagWaiterState) : Assertion :=
  match loan with
  | None => emp
  | Some waiter => flag_node_return_loan sg.(osKernelConfig) waiter
  end.

Definition task_delete_window_resources (tid : TaskID) (generation : nat)
  (loan : option FlagWaiterState) (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  task_delete_shared_inv sg tid generation state ** unmap_table_rep sg **
  task_delete_return_loan sg loan.

(** The node's Event/Flag/status stores keep its generation and saved SP.
    This transports the existing descriptors and locals, not stack bytes. *)
Lemma task_delete_update_preserves_continuation_capsules :
  forall environment saved_local state tid old updated,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  updated.(tcbStkPtr) = old.(tcbStkPtr) ->
  task_tcb_init_continuation_capsules environment saved_local state |--
  task_tcb_init_continuation_capsules environment saved_local
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid updated) state).
Proof.
  intros environment saved_local state tid old updated Hold Hgeneration Hsp.
  unfold task_tcb_init_continuation_capsules.
  apply kernel_saved_continuation_map_reindex.
  intros [slot generation] payload node Hstack Hnode Hgen.
  change ((if Z.eqb slot tid then Some updated
    else state.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
  destruct (Z.eqb slot tid) eqn:E.
  - apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node.
    exists old; split; [exact Hold|]. split; symmetry; assumption.
  - exists node; split; [exact Hnode|]. split; reflexivity.
Qed.

Lemma task_delete_recycle_preserves_continuation_capsules :
  forall environment saved_local sg state tid priority node name,
  task_tcb_init_continuation_capsules environment saved_local state |--
  task_tcb_init_continuation_capsules environment saved_local
    (replace_TskS (task_recycle sg state.(TskState) tid priority node name) state).
Proof.
  intros environment saved_local sg state tid priority node name.
  unfold task_tcb_init_continuation_capsules.
  apply kernel_saved_continuation_map_reindex.
  intros [slot generation] payload updated Hstack Hupdated Hgen.
  change (task_unlink_used_map state.(TskState).(inUsedTaskStates) tid node slot = Some updated)
    in Hupdated.
  unfold task_unlink_used_map in Hupdated.
  destruct (Z.eq_dec slot tid); [discriminate|].
  destruct (state.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  injection Hupdated as Hupdated; subst updated.
  exists old; split; [exact Hold|]. split; reflexivity.
Qed.

(** These two C counter fragments already have raw heap producers.  They
    therefore need no stable-ready assumption when called in this phase.
    The arbitrary disjoint frame can contain the typed node and parked map. *)
Lemma task_delete_int_enter_heap_writes : forall sg tid generation state
  (frame : Assertion) before after,
  (task_delete_shared_inv sg tid generation state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  kernel_heap_execution (os_int_enter_heap_writes sg state) before after.
Proof.
  intros sg tid generation state frame before after
    [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]] Hsource.
  pose proof (uchar_load_frame _ _ _ _ _
    (os_int_exit_raw_running_load sg state owned Hraw) Hjoin) as Hr.
  pose proof (uchar_load_frame _ _ _ _ _
    (os_int_exit_raw_nesting_load sg state owned Hraw) Hjoin) as Hn.
  unfold os_int_enter_heap_writes.
  destruct Hsource as
    [heap Hread|heap nesting Hread Hnest Hsat|heap nesting final Hread Hnest Hlt Hwrite].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    destruct state.(SchedState).(isRunning); [discriminate|].
    split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
    destruct state.(SchedState).(isRunning); [|discriminate].
    assert ((state.(IntrState).(intNesting) <? 255) = false) as ->
      by (apply Z.ltb_ge; exact Hsat).
    split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
    destruct state.(SchedState).(isRunning); [|discriminate].
    assert ((state.(IntrState).(intNesting) <? 255) = true) as ->
      by (apply Z.ltb_lt; exact Hlt).
    exact Hwrite.
Qed.

Lemma task_delete_int_enter_preserves_resources : forall sg tid generation state
  (frame : Assertion) before after,
  (task_delete_shared_inv sg tid generation state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  (task_delete_shared_inv sg tid generation (os_int_enter_state state) ** frame) after.
Proof.
  intros sg tid generation state frame before after Hpre Hsource.
  pose proof (task_delete_int_enter_heap_writes sg tid generation state frame
    before after Hpre Hsource) as Hactual.
  destruct Hpre as [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]].
  destruct (os_int_enter_source_heap_raw_post sg state owned Hraw)
    as [updated [Hrun Hupdated]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin)
    as [produced [Hwhole Hjoined]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  exists updated, rest; split; [exact Hjoined|]. split; [|exact Hrest].
  split; [exact Hvalid|exact Hupdated].
Qed.

Lemma task_delete_int_exit_preserves_resources : forall sg tid generation state
  (frame : Assertion) before after,
  (task_delete_shared_inv sg tid generation state ** frame) before ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (task_delete_shared_inv sg tid generation
     (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros sg tid generation state frame before after
    [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]] Hsource.
  destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw)
    as [updated [Hcounter Hupdated]].
  destruct (os_int_exit_masked_counter_fragment_frame sg owned _ updated rest before
    Hcounter Hjoin) as [produced [Hwhole Hjoined]].
  assert (produced = after).
  { destruct Hsource; eapply os_int_exit_masked_counter_final_eq; eassumption. }
  subst produced.
  exists updated, rest; split; [exact Hjoined|]. split; [|exact Hrest].
  split; [exact Hvalid|exact Hupdated].
Qed.

(** Diagnostic of the flat interface, not a returning IRQ execution.
    A real OSIntEnter source cut alone is admitted with the same origin;
    no matching OSIntExit is required by this relation's constructors. *)
Lemma task_delete_flat_source_admits_unpaired_enter :
  forall external port clients sg observer origin state,
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  kernel_resumption_task_source_trace external port clients sg observer None
    origin state false origin (os_int_enter_state state).
Proof.
  intros external port clients sg observer origin state Hin.
  change (kernel_resumption_task_source_trace external port clients sg observer None
    origin state (kernel_client_stops
      (kernel_full_profile_cut_client KernelFullIntEnter) observer)
    origin (os_int_enter_state state)).
  eapply kernel_client_framed_step_resumption_source.
  - exact Hin.
  - discriminate.
  - intros invocation Hnone; discriminate.
  - split; [exact I|reflexivity].
  - reflexivity.
  - reflexivity.
Qed.

Lemma task_delete_unpaired_enter_changes_zero_nesting : forall state,
  state.(SchedState).(isRunning) = true -> state.(IntrState).(intNesting) = 0 ->
  (os_int_enter_state state).(IntrState).(intNesting) = 1.
Proof.
  intros state Hrunning Hnesting.
  unfold os_int_enter_state, interrupt_enter_state; rewrite Hrunning, Hnesting; reflexivity.
Qed.

(** This is only the actual uninterrupted Restore branch.  The existing
    source theorem frames the SAME resource and parked-map interpretation.
    Interrupt execution needs a source/heap producer for these resources;
    the result below does not make that producer a CPU postcondition. *)
Lemma task_delete_window_uninterrupted_restore :
  forall environment critical saved_local arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg tid generation loan call saved acquired state cursor before written middle
    final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (kernel_continuation_call_masked environment.(task_stack_call_continuations)
     (task_delete_window_resources tid generation loan)
     (task_create_continuation_local saved_local) critical sg
     (task_stack_call_active_key call) call saved acquired state ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (kernel_continuation_call_closed environment.(task_stack_call_continuations)
     (task_delete_window_resources tid generation loan)
     (task_create_continuation_local saved_local) sg
     (task_stack_call_active_key call) call (armv7a_irq_fiq_mask saved) state ** frame) after.
Proof.
  intros environment critical saved_local arch restore sg tid generation loan call saved
    acquired state cursor before written middle final_cursor after frame
    Hr0 Hmask Hpre Hprefix Hsuffix.
  eapply kernel_continuation_call_uninterrupted_restore; eassumption.
Qed.

(** The matching uninterrupted Save retains the same typed node owner.
    No equality across an interrupted Restore/Dummy/Save window is used. *)
Lemma task_delete_window_uninterrupted_save :
  forall environment critical saved_local arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg tid generation loan call state mask registers before final_registers acquired
    after (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_continuation_call_closed environment.(task_stack_call_continuations)
     (task_delete_window_resources tid generation loan)
     (task_create_continuation_local saved_local) sg
     (task_stack_call_active_key call) call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  acquired = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (kernel_continuation_call_masked environment.(task_stack_call_continuations)
     (task_delete_window_resources tid generation loan)
     (task_create_continuation_local saved_local) critical sg
     (task_stack_call_active_key call) call final_registers.(kernel_save_r0) state state ** frame) after.
Proof.
  intros environment critical saved_local arch save sg tid generation loan call state mask
    registers before final_registers acquired after frame Hreturn Hvalid Hmask Hpre Hsuffix.
  eapply kernel_continuation_call_uninterrupted_save; eassumption.
Qed.

(** The public result records the deletion cut.  Environment execution
    after that cut may allocate the same slot again, so absence at the
    eventual C return is deliberately not substituted for this effect. *)
Definition task_delete_mutex_owner_exclusion (state : UCOS2_Verify_State)
  (tid : TaskID) : Prop :=
  forall eid event mutex,
    state.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) = OS_EVENT_TYPE_MUTEX ->
    event.(mutexFields) = Some mutex -> mutex.(mfOwner) <> Some tid.

Definition task_delete_success_domain (sg : StableGlobVars)
  (requested : Priority) (state : UCOS2_Verify_State) : Prop :=
  (requested = sg.(osPrioSelf) ->
    exists cid current, state.(SchedState).(curTaskID) = Some cid /\
      state.(TskState).(inUsedTaskStates) cid = Some current) /\
  forall selected tid node,
    task_delete_selection sg requested state.(TskState) state.(SchedState) selected ->
    task_delete_table_lookup state.(TskState) selected (inr (tid, node)) ->
    node.(taskID) = tid /\ node.(curPrio) <> sg.(osLowestPrio) /\
    (state.(SchedState).(isRunning) = false -> node.(nextTCB) <> None) /\
    task_delete_mutex_owner_exclusion state tid.

(** The native unlink always dereferences Next. Running callers obtain a
    successor from the existing Idle-tail invariant. A successful stopped
    caller must retain this one initialized-chain fact explicitly; the
    global boot invariant also admits intermediate initialization states.
    This condition is below the actual live lookup, so no error path gains
    a current-task, ready-list, or successor requirement. *)
Lemma task_delete_success_domain_successor : forall sg requested state selected tid node,
  UCOS2_state_inv sg state ->
  task_delete_success_domain sg requested state ->
  task_delete_selection sg requested state.(TskState) state.(SchedState) selected ->
  task_delete_table_lookup state.(TskState) selected (inr (tid, node)) ->
  node.(nextTCB) <> None.
Proof.
  intros sg requested state selected tid node Hvalid [_ Hdomain] Hselection Hlookup.
  destruct (Hdomain selected tid node Hselection Hlookup)
    as [Hid [Hnonidle [Hstopped Howner]]].
  destruct state.(SchedState).(isRunning) eqn:Hrunning.
  - unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid.
    destruct Hvalid as [Hprofile [Htasks [Hready [Hevents [Hcross [Hidle Hrest]]]]]].
    destruct Htasks as [Hpool [Hactive Htaskrest]].
    destruct (task_delete_table_lookup_live _ _ _ _ Hlookup) as [_ Hnode].
    destruct (task_idle_tail_successor sg state.(TskState) tid node
      Hactive (Hidle Hrunning) Hnode Hnonidle) as [next [successor [Hnext Hsuccessor]]].
    rewrite Hnext; discriminate.
  - exact (Hstopped eq_refl).
Qed.

Definition task_delete_prefix_passed sg requested (initial : UCOS2_Verify_State) : Prop :=
  task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = None.

Definition task_delete_idle_ready (sg : StableGlobVars) (state : UCOS2_Verify_State) : Prop :=
  exists tid node, state.(TskState).(inUsedTaskStates) tid = Some node /\
    node.(curPrio) = sg.(osLowestPrio) /\ In tid state.(SchedState).(readyList).

(** The ordinary running-call protocol is needed only beyond the ordered
    pre-Save errors. It gives current storage, not caller readiness: the
    ready witness is the distinct Idle task. The storage predicate already
    includes the recycled-current free-image alternative used by SELF. *)
Definition task_delete_running_protocol sg call (state : UCOS2_Verify_State) : Prop :=
  state.(SchedState).(isRunning) = true ->
  task_delete_idle_ready sg state /\
  os_sched_current_storage_binding sg call state /\
  kernel_call_stack_available call state.

Definition task_delete_success_protocol sg requested call (state : UCOS2_Verify_State) : Prop :=
  forall selected tid node,
    task_delete_selection sg requested state.(TskState) state.(SchedState) selected ->
    task_delete_table_lookup state.(TskState) selected (inr (tid, node)) ->
    task_delete_running_protocol sg call state.

Definition task_delete_protocol_transport sg requested original before returned after : Prop :=
  (task_delete_running_protocol sg original before ->
    task_delete_running_protocol sg returned after) /\
  (task_delete_success_protocol sg requested original before ->
    task_delete_success_protocol sg requested returned after).

Inductive TaskDeletePhase : Type :=
| TaskDeleteStable
| TaskDeleteLookup (requested : Priority)
| TaskDeletePrepared (tid : TaskID) (generation : nat).

Definition task_delete_phase_valid (phase : TaskDeletePhase)
  (sg : StableGlobVars) (state : UCOS2_Verify_State) : Prop :=
  match phase with
  | TaskDeleteStable => UCOS2_state_inv sg state
  | TaskDeleteLookup requested =>
      UCOS2_state_inv sg state /\ task_delete_success_domain sg requested state
  | TaskDeletePrepared tid generation => task_delete_shared_validity sg tid generation state
  end.

Definition task_delete_phase_resources (phase : TaskDeletePhase)
  (loan : option FlagWaiterState) (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (task_delete_phase_valid phase sg state) &&
  (UCOS2_raw_rep sg state ** unmap_table_rep sg ** task_delete_return_loan sg loan).

(** This is an endpoint condition on completed C-environment intervals.
    It is not claimed for individual interrupt-entry steps.  In the
    prepared phase the selected incarnation, table index and its complete
    TCB image are retained, together with the no-Mutex-owner protocol.
    Other tasks and all unrelated kernel state may change. *)
Definition task_delete_phase_rely (requested : Priority) (phase : TaskDeletePhase)
  (sg : StableGlobVars) (before after : UCOS2_Verify_State) : Prop :=
  after.(IntrState) = before.(IntrState) /\
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  task_delete_phase_valid phase sg after /\
  match phase with
  | TaskDeleteStable => True
  | TaskDeleteLookup priority => task_delete_success_domain sg priority after
  | TaskDeletePrepared tid generation =>
      after.(TskState).(prioTbl) = before.(TskState).(prioTbl) /\
      (forall node, before.(TskState).(inUsedTaskStates) tid = Some node ->
        after.(TskState).(inUsedTaskStates) tid = Some node) /\
      (task_delete_mutex_owner_exclusion before tid ->
        task_delete_mutex_owner_exclusion after tid)
  end.

Definition task_delete_call_closed environment saved_local phase loan sg call mask state : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
    sg (task_stack_call_active_key call) call mask state.

Definition task_delete_call_masked environment critical saved_local phase loan
  sg call saved acquired state : Assertion :=
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
    critical sg (task_stack_call_active_key call) call saved acquired state.

Definition task_delete_same_return original before returned after : Prop :=
  task_tcb_init_stack_same_call returned original /\
  (kernel_call_stack_available original before -> kernel_call_stack_available returned after).

Definition task_delete_save_post environment critical saved_local requested phase loan
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg original returned mask saved before acquired /\
      task_delete_same_return original before returned acquired /\
      task_delete_phase_rely requested phase sg before acquired /\
      task_delete_protocol_transport sg requested original before returned acquired) &&
    task_delete_call_masked environment critical saved_local phase loan
      sg returned saved acquired acquired.

Definition task_delete_restore_post environment critical saved_local requested phase loan
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin) released false
      returned.(os_sched_call_origin) current /\
      task_delete_same_return original released returned current /\
      task_delete_phase_rely requested phase sg released current /\
      task_delete_protocol_transport sg requested original released returned current) &&
    task_delete_call_closed environment saved_local phase loan sg returned mask current.

Lemma task_delete_same_return_refl : forall call state,
  task_delete_same_return call state call state.
Proof. intros; unfold task_delete_same_return, task_tcb_init_stack_same_call; auto. Qed.

Lemma task_delete_phase_resources_stable : forall loan sg state,
  task_delete_phase_resources TaskDeleteStable loan sg state --||--
  kernel_program_inv sg state ** task_delete_return_loan sg loan.
Proof.
  intros; unfold task_delete_phase_resources, task_delete_phase_valid,
    kernel_program_inv, kernel_program_rep; split; entailer!.
Qed.

Lemma task_delete_phase_resources_prepared : forall tid generation loan sg state,
  task_delete_phase_resources (TaskDeletePrepared tid generation) loan sg state --||--
  task_delete_window_resources tid generation loan sg state.
Proof.
  intros; unfold task_delete_phase_resources, task_delete_phase_valid,
    task_delete_window_resources, task_delete_shared_inv; split; entailer!.
Qed.

(** [completed] denotes the actual completed C-environment intervals of
    the selected linked program.  It is kept separate from the flat
    registered trace: the latter also admits an unmatched IntEnter prefix.
    This public conditional R/G premise constrains the actual two heaps
    of each such interval.  It grants no law to the ARM/BSP records and
    does not assume TaskDel's own stores or its public postcondition. *)
Record TaskDeleteCompletedEnvironment : Type := {
  task_delete_environment_execution :
    TaskDeletePhase -> OsSchedCallContext -> UCOS2_Verify_State ->
      OsSchedCallContext -> UCOS2_Verify_State -> model -> model -> Prop;
  task_delete_completed_interval :
    TaskDeletePhase -> OsSchedCallContext -> UCOS2_Verify_State ->
      OsSchedCallContext -> UCOS2_Verify_State -> model -> model -> Prop
}.

(** The first relation is the selected linked C environment's actual
    interval, at the caller's instruction cuts. Applicability is an
    explicit obligation on that relation, not on every prefix of the
    registered trace. It preserves all six endpoint indices. The record
    supplies no law and no existence or eventual-return assertion. *)
Definition task_delete_environment_applicable
  (completed : TaskDeleteCompletedEnvironment) : Prop :=
  forall phase original before returned after initial_heap final_heap,
    completed.(task_delete_environment_execution)
      phase original before returned after initial_heap final_heap ->
    completed.(task_delete_completed_interval)
      phase original before returned after initial_heap final_heap.

Definition task_delete_environment_rely environment critical saved_local requested sg
  (completed : TaskDeleteCompletedEnvironment) : Prop :=
  forall phase loan original before returned after mask initial_heap final_heap (frame : Assertion),
    completed.(task_delete_completed_interval)
      phase original before returned after initial_heap final_heap ->
    (task_delete_call_closed environment saved_local phase loan
      sg original mask before ** frame) initial_heap ->
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before false returned.(os_sched_call_origin) after /\
    task_delete_same_return original before returned after /\
    task_delete_phase_rely requested phase sg before after /\
    task_delete_protocol_transport sg requested original before returned after /\
    (task_delete_call_closed environment saved_local phase loan
      sg returned mask after ** frame) final_heap.

Definition task_delete_c_environment environment critical saved_local requested sg completed : Prop :=
  task_delete_environment_applicable completed /\
  task_delete_environment_rely environment critical saved_local requested sg completed.

(** This rule consumes an actual interval, rather than an unproved
    membership antecedent. Both premises remain visible in public Require.
    Own C writes and direct callee effects are absent from this R. *)
Lemma task_delete_actual_environment_return :
  forall environment critical saved_local requested sg completed
    phase loan original before returned after mask initial_heap final_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  completed.(task_delete_environment_execution)
    phase original before returned after initial_heap final_heap ->
  (task_delete_call_closed environment saved_local phase loan
    sg original mask before ** frame) initial_heap ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after /\
  task_delete_same_return original before returned after /\
  task_delete_phase_rely requested phase sg before after /\
  task_delete_protocol_transport sg requested original before returned after /\
  (task_delete_call_closed environment saved_local phase loan
    sg returned mask after ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed phase loan
    original before returned after mask initial_heap final_heap frame [Happ HR] Hactual Hpre.
  apply (HR phase loan original before returned after mask initial_heap final_heap frame).
  - exact (Happ phase original before returned after initial_heap final_heap Hactual).
  - exact Hpre.
Qed.

(** Save's completed environment interval ends on the very heap consumed
    by the existing MRS/CPSID/DSB/BX suffix rule. This is conditional C
    composition; it does not strengthen that primitive rule. *)
Lemma task_delete_save_completed_boundary :
  forall environment critical saved_local requested sg completed arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan original before returned current mask registers initial_heap
    environment_heap final_registers acquired final_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  completed.(task_delete_environment_execution)
    phase original before returned current initial_heap environment_heap ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (task_delete_call_closed environment saved_local phase loan
    sg original mask before ** frame) initial_heap ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current environment_heap
    final_registers acquired final_heap ->
  acquired = current /\
  (task_delete_save_post environment critical saved_local requested phase loan
    sg original mask final_registers.(kernel_save_r0) before ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed arch save phase loan
    original before returned current mask registers initial_heap environment_heap
    final_registers acquired final_heap frame Henv Hactual Hreturn Hvalid Hmask Hpre Hsuffix.
  destruct (task_delete_actual_environment_return environment critical saved_local requested sg
    completed phase loan original before returned current mask initial_heap environment_heap
    frame Henv Hactual Hpre) as [Htrace [Hnormal [HR [Hprotocol Hclosed]]]].
  destruct (kernel_continuation_call_uninterrupted_save
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) critical arch environment.(task_stack_call_continuations)
    save (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
    sg (task_stack_call_active_key returned) returned current mask registers environment_heap
    final_registers acquired final_heap frame Hreturn Hvalid Hmask Hclosed Hsuffix)
    as [Hstate [Hr0 [Hsource Hmasked]]].
  split; [exact Hstate|]; subst acquired.
  assert (Hsaved : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { rewrite Hr0; split; [exact Hvalid|exact Hmask]. }
  assert (Hcall : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask
      final_registers.(kernel_save_r0) before current).
  { unfold kernel_call_save_source; destruct Hnormal as [[Hi [Ho Hs]] Havailable]; auto. }
  match type of Hmasked with ?P final_heap =>
    assert (Hclose : P |-- task_delete_save_post environment critical saved_local requested
      phase loan sg original mask final_registers.(kernel_save_r0) before ** frame)
  end.
  { unfold task_delete_save_post; Exists returned current; entailer!. }
  exact (Hclose final_heap Hmasked).
Qed.

(** Restore uses the real prefix, the same completed C interval, then
    the real suffix. The inside/saved token is consumed once by the prefix;
    the suffix only transports the returned execution and world. *)
Lemma task_delete_restore_completed_boundary :
  forall environment critical saved_local requested sg completed arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    phase loan original saved acquired released cursor initial_heap written prefix_heap
    returned current environment_heap final_cursor final_heap frame,
  task_delete_c_environment environment critical saved_local requested sg completed ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_delete_call_masked environment critical saved_local phase loan
    sg original saved acquired released ** frame) initial_heap ->
  armv7a_restore_prefix_transition restore cursor initial_heap written prefix_heap ->
  completed.(task_delete_environment_execution)
    phase original released returned current prefix_heap environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor final_heap ->
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (task_delete_restore_post environment critical saved_local requested phase loan
    sg original (armv7a_irq_fiq_mask saved) released ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed arch restore phase loan
    original saved acquired released cursor initial_heap written prefix_heap returned current
    environment_heap final_cursor final_heap frame Henv Hr0 Hmask Hpre Hprefix Hactual Hsuffix.
  unfold task_delete_call_masked, kernel_continuation_call_masked in Hpre.
  assert (Hopen :
    critical_region_masked environment.(task_stack_call_platform) critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) original **
    kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key original) released ** frame |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) original **
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key original) released ** frame)) by entailer!.
  destruct (armv7a_restore_prefix_releases_critical_region
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch
    restore sg original saved acquired cursor initial_heap written prefix_heap _ Hr0 Hmask
    (Hopen initial_heap Hpre) Hprefix) as [Hwritten [Hmemory Howned]].
  assert (Hclosed : (task_delete_call_closed environment saved_local phase loan sg original
    (armv7a_irq_fiq_mask saved) released ** frame) prefix_heap).
  { match type of Howned with ?P prefix_heap => match goal with |- ?Q prefix_heap =>
      assert (Hclose : P |-- Q) end end.
    { unfold task_delete_call_closed, kernel_continuation_call_closed; entailer!. }
    exact (Hclose prefix_heap Howned). }
  destruct (task_delete_actual_environment_return environment critical saved_local requested sg
    completed phase loan original released returned current (armv7a_irq_fiq_mask saved)
    prefix_heap environment_heap frame Henv Hactual Hclosed)
    as [Htrace [Hnormal [HR [Hprotocol Hreturned]]]].
  assert (Hword : written.(kernel_restore_msr_word) = Some
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))).
  { rewrite Hwritten; reflexivity. }
  unfold task_delete_call_closed, kernel_continuation_call_closed in Hreturned.
  assert (Horder : kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) returned (armv7a_irq_fiq_mask saved) **
    kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key returned) current ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) returned (armv7a_irq_fiq_mask saved) **
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      (task_delete_phase_resources phase loan) (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key returned) current ** frame)) by entailer!.
  pose proof (Horder environment_heap Hreturned) as Hsuffix_pre.
  rewrite <- Hr0, <- (armv7a_cpsr_restore_mask_eq cursor.(kernel_restore_current_cpsr)
    cursor.(kernel_restore_r0)) in Hsuffix_pre.
  destruct (armv7a_restore_suffix_transports_owned_execution
    environment.(task_stack_call_external) environment.(task_stack_call_platform) critical arch
    restore returned _ written environment_heap final_cursor final_heap _ Hword Hsuffix_pre Hsuffix)
    as [Hfinal [Hmemory' Hafter]].
  split.
  - rewrite Hfinal, Hwritten; reflexivity.
  - rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hafter.
    match type of Hafter with ?P final_heap =>
      assert (Hclose : P |-- task_delete_restore_post environment critical saved_local requested
        phase loan sg original (armv7a_irq_fiq_mask saved) released ** frame)
    end.
    { unfold task_delete_restore_post; Exists returned current.
      unfold task_delete_call_closed, kernel_continuation_call_closed; entailer!. }
    exact (Hclose final_heap Hafter).
Qed.

(** Caller protocol is guarded by the actually selected live entry.  It
    imposes no live-current, non-Idle or owner condition on any error arm. *)
Definition task_delete_entry environment critical saved_local completed sg requested call mask initial : Assertion :=
  coq_prop (task_delete_static_profile sg /\
    task_delete_c_environment environment critical saved_local requested sg completed /\
    0 <= requested <= 255 /\ flag_unlink_layout /\
    (task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = None ->
      task_delete_success_domain sg requested initial /\
      task_delete_success_protocol sg requested call initial)) &&
  task_delete_call_closed environment saved_local TaskDeleteStable None sg call mask initial.

Definition task_delete_recycled (sg : StableGlobVars) tid priority
  (node : TaskAbstractState) name (resumed : UCOS2_Verify_State) added : UCOS2_Verify_State :=
  replace_TskS (task_recycle sg resumed.(TskState) tid priority node name)
    (replace_IntrS (task_delete_release_state added resumed.(IntrState)) resumed).

Inductive task_delete_effect (sg : StableGlobVars) (requested name : Z)
  : UCOS2_Verify_State -> Z -> UCOS2_Verify_State -> Prop :=
| TaskDeletePrefixError : forall initial error,
    task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = Some error ->
    task_delete_effect sg requested name initial (encode_os_err_code error) initial
| TaskDeleteLookupError : forall initial acquired selected error,
    task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = None ->
    task_delete_phase_rely requested (TaskDeleteLookup requested) sg initial acquired ->
    task_delete_selection sg requested acquired.(TskState) acquired.(SchedState) selected ->
    task_delete_table_lookup acquired.(TskState) selected (inl error) ->
    task_delete_effect sg requested name initial (encode_os_err_code error) acquired
| TaskDeleteSuccess : forall initial acquired selected tid node prepared loan resumed,
    task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = None ->
    task_delete_phase_rely requested (TaskDeleteLookup requested) sg initial acquired ->
    task_delete_selection sg requested acquired.(TskState) acquired.(SchedState) selected ->
    task_delete_table_lookup acquired.(TskState) selected (inr (tid, node)) ->
    task_delete_prepare_single_wait acquired tid node = Some (prepared, loan) ->
    task_delete_phase_rely requested (TaskDeletePrepared tid node.(taskGeneration)) sg
      (replace_IntrS (task_delete_lock_state prepared.(IntrState)) prepared) resumed ->
    task_delete_effect sg requested name initial 0
      (task_delete_recycled sg tid selected (task_prepare_delete
        (task_set_flag_node (task_set_event_ptr node None) 0)) name resumed
        (task_delete_lock_added prepared.(IntrState))).

(** These are exactly the endpoint observations provided by the final
    Restore and the accepted Scheduler contract. No absence claim at the
    eventual return replaces the earlier deletion cut. *)
Inductive task_delete_return_relation environment critical requested sg
  : OsSchedCallContext -> UCOS2_Verify_State ->
    OsSchedCallContext -> UCOS2_Verify_State -> Prop :=
| TaskDeleteReturnImmediate : forall call state,
    task_delete_return_relation environment critical requested sg call state call state
| TaskDeleteReturnRestored : forall original cut returned final,
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin) cut false
      returned.(os_sched_call_origin) final ->
    task_delete_same_return original cut returned final ->
    task_delete_phase_rely requested TaskDeleteStable sg cut final ->
    task_delete_return_relation environment critical requested sg original cut returned final
| TaskDeleteReturnScheduled : forall original cut middle current returned final,
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin) cut false
      middle.(os_sched_call_origin) current ->
    task_delete_same_return original cut middle current ->
    task_delete_phase_rely requested TaskDeleteStable sg cut current ->
    current.(SchedState).(isRunning) = true ->
    task_tcb_init_stack_same_call returned middle ->
    (kernel_call_task_source middle current -> kernel_call_task_source returned final) ->
    task_delete_return_relation environment critical requested sg original cut returned final.

Definition task_delete_post environment critical saved_local sg requested name original mask initial result : Assertion :=
  EX cut_call returned final deletion_cut loan,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_same_call cut_call original /\
      task_delete_effect sg requested name initial result deletion_cut /\
      task_delete_return_relation environment critical requested sg cut_call deletion_cut returned final) &&
    task_delete_call_closed environment saved_local TaskDeleteStable loan sg returned mask final.

(** The following views expose actual cells for the C obligations.  Their
    reconstruction wands are goals generated from the incoming owner, not
    assumptions in the public Require.  Every local C store therefore has
    its own independent spatial preservation obligation. *)
Definition task_delete_uchar_cell (p value : Z) : Assertion := p # UChar |-> value.
Definition task_delete_ptr_cell (p value : Z) : Assertion := p # Ptr |-> value.
Definition task_delete_uint_cell (p value : Z) : Assertion := p # UInt |-> value.
Definition task_delete_tcb_value sg node field : Z :=
  match task_tcb64_image sg node field with Some stored => stored | None => 0 end.
Definition task_delete_ints (s : UCOS2_Verify_State) := s.(IntrState).(intNesting).
Definition task_delete_locks (s : UCOS2_Verify_State) := s.(IntrState).(lockNesting).
Definition task_delete_current sg (s : UCOS2_Verify_State) :=
  encode_task_link sg s.(SchedState).(curTaskID).
Definition task_delete_table sg (s : UCOS2_Verify_State) p :=
  prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) p).
Definition task_delete_ready_state (s : UCOS2_Verify_State) tid :=
  replace_SchedS (sched_remove_ready_task s.(SchedState) tid) s.

Definition task_delete_masked_raw environment critical saved_local loan sg call saved acquired state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  UCOS2_raw_rep sg state ** unmap_table_rep sg ** task_delete_return_loan sg loan **
   task_tcb_init_continuation_capsules environment saved_local state).

Definition task_delete_ready_cells sg (s : UCOS2_Verify_State) tid node (cleared : bool) : Assertion :=
  let base := task_slot_addr sg tid in
  let row := tcb_y_of_prio node.(curPrio) in
  let bit_x := tcb_bit_x_of_prio node.(curPrio) in
  let bit_y := tcb_bit_y_of_prio node.(curPrio) in
  let row_value := encode_ready_tbl_at_or s.(SchedState).(readyList) s.(TskState) row in
  let group_value := encode_ready_grp s.(SchedState).(readyList) s.(TskState) in
  tcb_field_address base TCBY # UChar |-> row **
  tcb_field_address base TCBBitX # UChar |-> bit_x **
  tcb_field_address base TCBBitY # UChar |-> bit_y **
  (sg.(g_OSRdyTbl) + row) # UChar |->
    (if cleared then event_task_remove_cleared row_value bit_x else row_value) **
  sg.(g_OSRdyGrp) # UChar |->
    (if cleared then event_task_remove_group row_value group_value bit_x bit_y else group_value).

Definition task_delete_event_state (s : UCOS2_Verify_State) tid node eid event :=
  replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_set_event_ptr node None))
    (replace_EventS (update_event_field_raw s.(EventState) eid
      (event_set_wait_list event (remove_Z_eqb tid event.(waitList)))) s).

Definition task_delete_flag_state (s : UCOS2_Verify_State) tid node flags :=
  replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_set_flag_node node 0))
    (replace_FlagS flags s).

Definition task_delete_prepare_cells sg (s : UCOS2_Verify_State) tid node (prepared : bool) : Assertion :=
  let base := task_slot_addr sg tid in
  tcb_field_address base TCBDly # UInt |-> (if prepared then 0 else node.(dly)) **
  tcb_field_address base TCBStat # UChar |->
    (if prepared then 0 else Byte.unsigned node.(stat)) **
  tcb_field_address base TCBStatPend # UChar |->
    (if prepared then 0 else encode_pend_status node.(statPend)) **
  sg.(g_OSLockNesting) # UChar |->
    (if prepared then (task_delete_lock_state s.(IntrState)).(lockNesting) else s.(IntrState).(lockNesting)).

Definition task_delete_prepare_state (s : UCOS2_Verify_State) tid node :=
  replace_IntrS (task_delete_lock_state s.(IntrState))
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_prepare_delete node)) s).

Definition task_delete_added_value (s : UCOS2_Verify_State) : Z :=
  if task_delete_lock_added s.(IntrState) then 1 else 0.

Lemma task_delete_added_value_below_saturation : forall s,
  task_delete_locks s < 255 -> task_delete_added_value s = 1.
Proof.
  intros s Hlock; unfold task_delete_locks in Hlock.
  unfold task_delete_added_value, task_delete_lock_added.
  rewrite (proj2 (Z.ltb_lt _ _) Hlock); reflexivity.
Qed.

Lemma task_delete_added_value_at_saturation : forall s,
  255 <= task_delete_locks s -> task_delete_added_value s = 0.
Proof.
  intros s Hlock; unfold task_delete_locks in Hlock.
  unfold task_delete_added_value, task_delete_lock_added.
  rewrite (proj2 (Z.ltb_ge _ _) Hlock); reflexivity.
Qed.

Definition task_delete_running (s : UCOS2_Verify_State) : Z :=
  if s.(SchedState).(isRunning) then 1 else 0.

Definition task_delete_next sg (node : TaskAbstractState) := encode_task_link sg node.(nextTCB).
Definition task_delete_prev sg (node : TaskAbstractState) := encode_task_link sg node.(prevTCB).
Definition task_delete_count (s : UCOS2_Verify_State) := s.(TskState).(taskCount).
Definition task_delete_free_head sg (s : UCOS2_Verify_State) :=
  encode_task_link sg (hd_error s.(TskState).(unUsedTaskStates)).
Definition task_delete_list_head sg (s : UCOS2_Verify_State) :=
  encode_task_link sg s.(TskState).(tcbListHead).

Definition task_delete_neighbor_cells sg tid node (recycled : bool) : Assertion :=
  tcb_field_address (encode_task_link sg node.(nextTCB)) TCBPrev # Ptr |->
    (if recycled then encode_task_link sg node.(prevTCB) else task_slot_addr sg tid) **
  match node.(prevTCB) with
  | None => emp
  | Some previous =>
      tcb_field_address (task_slot_addr sg previous) TCBNext # Ptr |->
        (if recycled then encode_task_link sg node.(nextTCB) else task_slot_addr sg tid)
  end.

Definition task_delete_recycle_cells sg (s : UCOS2_Verify_State) tid priority node name
  (recycled : bool) : Assertion :=
  let base := task_slot_addr sg tid in
  sg.(g_OSTaskCtr) # UChar |->
    (if recycled then (s.(TskState).(taskCount) - 1) mod 256 else s.(TskState).(taskCount)) **
  (sg.(g_OSTCBPrioTbl) + priority * 4) # Ptr |-> (if recycled then 0 else base) **
  sg.(g_OSTCBFreeList) # Ptr |->
    (if recycled then base else encode_task_link sg (hd_error s.(TskState).(unUsedTaskStates))) **
  sg.(g_OSTCBList) # Ptr |->
    encode_task_link sg (if recycled then
      match node.(prevTCB) with None => node.(nextTCB) | Some _ => s.(TskState).(tcbListHead) end
      else s.(TskState).(tcbListHead)) **
  tcb_field_address base TCBNext # Ptr |->
    (if recycled then encode_task_link sg (hd_error s.(TskState).(unUsedTaskStates))
     else encode_task_link sg node.(nextTCB)) **
  tcb_field_address base TCBPrev # Ptr |-> encode_task_link sg node.(prevTCB) **
  tcb_field_address base TCBTaskName # Ptr |->
    (if recycled then name else task_delete_tcb_value sg node TCBTaskName) **
  task_delete_neighbor_cells sg tid node recycled.

Definition task_delete_global_addresses (sg : StableGlobVars)
  nesting locks current free_list active_list count table group rows running : Prop :=
  sg.(g_OSIntNesting) = nesting /\ sg.(g_OSLockNesting) = locks /\
  sg.(g_OSTCBCur) = current /\ sg.(g_OSTCBFreeList) = free_list /\
  sg.(g_OSTCBList) = active_list /\ sg.(g_OSTaskCtr) = count /\
  sg.(g_OSTCBPrioTbl) = table /\ sg.(g_OSRdyGrp) = group /\
  sg.(g_OSRdyTbl) = rows /\ sg.(g_OSRunning) = running.

Lemma task_delete_focus_reassemble : forall part whole,
  part ** wand part whole |-- whole.
Proof. intros; apply derivable1_wand_elim2. Qed.

Definition task_delete_lookup_history sg requested original initial current acquired : Prop :=
  task_delete_static_profile sg /\ 0 <= requested <= 255 /\
  task_tcb_init_stack_same_call current original /\
  task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = None /\
  task_delete_phase_rely requested (TaskDeleteLookup requested) sg initial acquired /\
  task_delete_success_protocol sg requested current acquired.

Lemma task_delete_lookup_selected_in_range :
  forall sg requested original initial current acquired selected,
  task_delete_lookup_history sg requested original initial current acquired ->
  task_delete_selection sg requested acquired.(TskState) acquired.(SchedState) selected ->
  0 <= selected <= 63.
Proof.
  intros sg requested original initial current acquired selected
    [Hstatic [Hrequested [Hsame [Hprefix [Hrely Hprotocol]]]]] Hselection.
  pose proof Hstatic as [Hprofile [Hconfig _]].
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
  destruct Hrely as [_ [_ [Hvalid _]]].
  destruct Hvalid as [Hvalid Hdomain].
  unfold task_delete_selection in Hselection.
  destruct (Z.eqb requested sg.(osPrioSelf)) eqn:Hself.
  - destruct Hselection as [cid [node [Hcurrent [Hnode Hselected]]]].
    subst selected.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid.
    destruct Hvalid as [_ [Htasks _]].
    assert (Hpriority : task_priority_in_range sg node.(curPrio)).
    { unfold task_in_range in Htasks.
      destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriorities _]]]]]]]].
      exact (Hpriorities cid node Hnode). }
    unfold task_priority_in_range in Hpriority; lia.
  - subst selected.
    pose proof (task_delete_static_profile_argument_checks sg Hstatic) as Hchecks.
    destruct (task_delete_prefix_allows_priority_index sg false
      initial.(IntrState).(intNesting) requested Hchecks (proj1 Hrequested) Hprefix)
      as [Heq | Hrange].
    + apply Z.eqb_neq in Hself; contradiction.
    + unfold task_priority_in_range in Hrange; lia.
Qed.

Definition task_delete_selected sg requested (acquired : UCOS2_Verify_State) selected pointer : Prop :=
  task_delete_selection sg requested acquired.(TskState) acquired.(SchedState) selected /\
  pointer = task_delete_table sg acquired selected.

Definition task_delete_live sg (acquired : UCOS2_Verify_State) selected pointer tid node : Prop :=
  task_delete_table_lookup acquired.(TskState) selected (inr (tid, node)) /\
  pointer = task_slot_addr sg tid.

Definition task_delete_event_unlinked (before : UCOS2_Verify_State) tid node after new : Prop :=
  match node.(eventPtr) with
  | None => after = before /\ new = node
  | Some eid => exists event, before.(EventState).(inUsedEventStates) eid = Some event /\
      after = task_delete_event_state before tid node eid event /\ new = task_set_event_ptr node None
  end.

Definition task_delete_flag_unlinked (before : UCOS2_Verify_State) tid node after new loan : Prop :=
  if Z.eqb node.(tcbFlagNode) 0 then after = before /\ new = node /\ loan = None
  else exists w flags, flag_unlink_node before.(FlagState) node.(tcbFlagNode) = Some (w, flags) /\
    after = task_delete_flag_state before tid node flags /\ new = task_set_flag_node node 0 /\ loan = Some w.

Definition task_delete_event_handle (sg : StableGlobVars) (node : TaskAbstractState) :=
  encode_event_link sg node.(eventPtr).
Definition task_delete_flag_handle (node : TaskAbstractState) := node.(tcbFlagNode).
Definition task_delete_ready_row (s : UCOS2_Verify_State) (node : TaskAbstractState) :=
  encode_ready_tbl_at_or s.(SchedState).(readyList) s.(TskState) (tcb_y_of_prio node.(curPrio)).
Definition task_delete_ready_group (s : UCOS2_Verify_State) :=
  encode_ready_grp s.(SchedState).(readyList) s.(TskState).

Definition task_delete_self_binding (sg : StableGlobVars) (s : UCOS2_Verify_State) tid node : Prop :=
  s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some node.
Definition task_delete_self_cells sg (s : UCOS2_Verify_State) node : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> task_delete_current sg s **
  tcb_field_address (task_delete_current sg s) TCBPrio # UChar |-> node.(curPrio).

Definition task_delete_acquired environment critical saved_local sg requested original initial
  current saved acquired : Assertion :=
  coq_prop (task_delete_lookup_history sg requested original initial current acquired) &&
  task_delete_masked_raw environment critical saved_local None sg current saved acquired acquired.

Definition task_delete_live_history sg requested original initial current acquired priority pointer tid node : Prop :=
  task_delete_lookup_history sg requested original initial current acquired /\
  task_delete_selected sg requested acquired priority pointer /\
  task_delete_live sg acquired priority pointer tid node.

Definition task_delete_live_body environment critical saved_local sg requested original initial
  current saved acquired priority pointer tid node : Assertion :=
  coq_prop (task_delete_live_history sg requested original initial current acquired priority pointer tid node) &&
  task_delete_masked_raw environment critical saved_local None sg current saved acquired acquired.

Definition task_delete_ready_body environment critical saved_local sg requested original initial
  current saved acquired priority pointer tid node : Assertion :=
  coq_prop (task_delete_live_history sg requested original initial current acquired priority pointer tid node) &&
  task_delete_masked_raw environment critical saved_local None sg current saved acquired
    (task_delete_ready_state acquired tid).

Definition task_delete_event_body environment critical saved_local sg requested original initial
  current saved acquired priority pointer tid node : Assertion :=
  EX evented event_node,
    coq_prop (task_delete_live_history sg requested original initial current acquired priority pointer tid node /\
      task_delete_event_unlinked (task_delete_ready_state acquired tid) tid node evented event_node) &&
    task_delete_masked_raw environment critical saved_local None sg current saved acquired evented.

Definition task_delete_flag_body environment critical saved_local sg requested original initial
  current saved acquired priority pointer tid node : Assertion :=
  EX evented event_node flagged flag_node loan,
    coq_prop (task_delete_live_history sg requested original initial current acquired priority pointer tid node /\
      task_delete_event_unlinked (task_delete_ready_state acquired tid) tid node evented event_node /\
      task_delete_flag_unlinked evented tid event_node flagged flag_node loan) &&
    task_delete_masked_raw environment critical saved_local loan sg current saved acquired flagged.

Definition task_delete_prepared_body environment critical saved_local sg requested original initial
  current saved acquired priority pointer tid node added : Assertion :=
  EX prepared loan,
    coq_prop (task_delete_live_history sg requested original initial current acquired priority pointer tid node /\
      task_delete_prepare_single_wait acquired tid node = Some (prepared, loan) /\
      added = (if task_delete_lock_added prepared.(IntrState) then 1 else 0) /\
      task_delete_running_protocol sg current
        (replace_IntrS (task_delete_lock_state prepared.(IntrState)) prepared)) &&
    task_delete_call_masked environment critical saved_local (TaskDeletePrepared tid node.(taskGeneration)) loan
      sg current saved acquired (replace_IntrS (task_delete_lock_state prepared.(IntrState)) prepared).

Definition task_delete_locked (prepared : UCOS2_Verify_State) :=
  replace_IntrS (task_delete_lock_state prepared.(IntrState)) prepared.

Definition task_delete_prepared_node node :=
  task_prepare_delete (task_set_flag_node (task_set_event_ptr node None) 0).

Definition task_delete_preparation_history sg requested original initial current acquired
  priority tid node prepared loan : Prop :=
  task_delete_live_history sg requested original initial current acquired priority
    (task_slot_addr sg tid) tid node /\
  task_delete_prepare_single_wait acquired tid node = Some (prepared, loan) /\
  task_delete_running_protocol sg current (task_delete_locked prepared).

Definition task_delete_restore_history environment critical requested phase sg
  original released returned current : Prop :=
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin) released false
    returned.(os_sched_call_origin) current /\
  task_delete_same_return original released returned current /\
  task_delete_phase_rely requested phase sg released current /\
  task_delete_protocol_transport sg requested original released returned current.

Definition task_delete_window_history sg requested original initial first acquired
  priority tid node prepared loan returned resumed : Prop :=
  task_delete_preparation_history sg requested original initial first acquired
    priority tid node prepared loan /\
  task_tcb_init_stack_same_call returned original /\
  task_delete_phase_rely requested (TaskDeletePrepared tid node.(taskGeneration)) sg
    (task_delete_locked prepared) resumed /\
  task_delete_running_protocol sg returned resumed.

Definition task_delete_released (prepared resumed : UCOS2_Verify_State) :=
  replace_IntrS (task_delete_release_state
    (task_delete_lock_added prepared.(IntrState)) resumed.(IntrState)) resumed.

Definition task_delete_released_body environment critical saved_local sg requested original initial
  first acquired priority tid node prepared loan returned saved resumed : Assertion :=
  coq_prop (task_delete_window_history sg requested original initial first acquired
    priority tid node prepared loan returned resumed) &&
  task_delete_masked_raw environment critical saved_local loan sg returned saved resumed
    (task_delete_released prepared resumed).

Definition task_delete_cut sg prepared resumed tid priority node name :=
  task_delete_recycled sg tid priority (task_delete_prepared_node node) name resumed
    (task_delete_lock_added prepared.(IntrState)).

Definition task_delete_recycled_body environment critical saved_local sg requested original initial
  returned saved acquired cut loan name : Assertion :=
  coq_prop (task_tcb_init_stack_same_call returned original /\
    task_delete_effect sg requested name initial 0 cut /\
    task_delete_running_protocol sg returned cut) &&
  task_delete_call_masked environment critical saved_local TaskDeleteStable loan
    sg returned saved acquired cut.

Definition task_delete_result_history sg requested name original initial returned cut : Prop :=
  task_tcb_init_stack_same_call returned original /\
  task_delete_effect sg requested name initial 0 cut /\
  task_delete_running_protocol sg returned cut.

Definition task_delete_final_body environment critical saved_local sg requested name original mask initial
  returned final cut loan : Assertion :=
  coq_prop ((exists cut_call,
    task_delete_result_history sg requested name original initial cut_call cut /\
    task_delete_restore_history environment critical requested TaskDeleteStable sg cut_call cut returned final) /\
    task_delete_running_protocol sg returned final) &&
  task_delete_call_closed environment saved_local TaskDeleteStable loan sg returned mask final.

Definition task_delete_sched_return_with_loan environment saved_local sg original mask before loan : Assertion :=
  os_sched_continuation_return_post environment saved_local kernel_program_inv
    sg original mask before ** task_delete_return_loan sg loan.

Lemma task_delete_running_protocol_sched_cut : forall sg call state,
  task_delete_running_protocol sg call state ->
  state.(SchedState).(isRunning) = true -> os_sched_call_cut sg call state.
Proof.
  intros sg call state Hprotocol Hrunning.
  destruct (Hprotocol Hrunning) as [[idle [node [Hnode [Hprio Hready]]]] [Hstorage Havailable]].
  split.
  - intros _ Hempty; rewrite Hempty in Hready; contradiction.
  - intros _; split; [exact Hstorage|].
    unfold kernel_call_stack_available in Havailable.
    rewrite (proj1 Hstorage) in Havailable; exact Havailable.
Qed.

Lemma task_delete_call_closed_stable_split_loan :
  forall environment saved_local loan sg call mask state,
  task_delete_call_closed environment saved_local TaskDeleteStable loan sg call mask state --||--
  os_sched_continuation_pre environment saved_local kernel_program_inv sg call mask state **
    task_delete_return_loan sg loan.
Proof.
  intros; unfold task_delete_call_closed, os_sched_continuation_pre,
    kernel_continuation_call_closed, kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid, kernel_program_inv, kernel_program_rep.
  split; entailer!.
Qed.

Lemma task_delete_final_restore_body :
  forall environment critical saved_local sg requested name original mask initial cut_call cut loan,
  task_delete_result_history sg requested name original initial cut_call cut ->
  task_delete_restore_post environment critical saved_local requested TaskDeleteStable loan
    sg cut_call mask cut |--
  EX returned final, task_delete_final_body environment critical saved_local sg requested name
    original mask initial returned final cut loan.
Proof.
  intros environment critical saved_local sg requested name original mask initial cut_call cut loan Hhistory.
  unfold task_delete_restore_post; Intros returned final.
  assert (Hprotocol : task_delete_running_protocol sg returned final).
  { assert (Htransport : task_delete_protocol_transport sg requested cut_call cut returned final) by tauto.
    apply (proj1 Htransport); exact (proj2 (proj2 Hhistory)). }
  Exists returned final; unfold task_delete_final_body.
  assert (Hreturn : task_delete_restore_history environment critical requested TaskDeleteStable
    sg cut_call cut returned final).
  { unfold task_delete_restore_history; tauto. }
  entailer!; exists cut_call; auto.
Qed.

Lemma task_delete_final_body_post :
  forall environment critical saved_local sg requested name original mask initial returned final cut loan,
  task_delete_final_body environment critical saved_local sg requested name original mask initial
    returned final cut loan |--
  task_delete_post environment critical saved_local sg requested name original mask initial 0.
Proof.
  intros; unfold task_delete_final_body; Intros.
  assert (Hhistory : exists cut_call,
    task_delete_result_history sg requested name original initial cut_call cut /\
    task_delete_restore_history environment critical requested TaskDeleteStable sg
      cut_call cut returned final) by tauto.
  destruct Hhistory as [cut_call [[Hcut_same [Heffect Hcut_protocol]]
    [Htrace [Hnormal [HR Htransport]]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { destruct Hnormal as [[Hi [Ho Hs]] Havailable], Hcut_same as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Htail : task_delete_return_relation environment critical requested sg cut_call cut returned final).
  { apply TaskDeleteReturnRestored; assumption. }
  unfold task_delete_post; Exists cut_call returned final cut loan; entailer!.
Qed.

Lemma task_delete_scheduled_return_post :
  forall environment critical saved_local sg requested name original mask initial
    cut_call cut middle current loan,
  task_delete_result_history sg requested name original initial cut_call cut ->
  task_delete_restore_history environment critical requested TaskDeleteStable sg cut_call cut middle current ->
  current.(SchedState).(isRunning) = true ->
  task_delete_sched_return_with_loan environment saved_local sg middle mask current loan |--
  task_delete_post environment critical saved_local sg requested name original mask initial 0.
Proof.
  intros environment critical saved_local sg requested name original mask initial
    cut_call cut middle current loan [Hcut_same [Heffect Hprotocol]]
    [Htrace [Hnormal [HR Htransport]]] Hrunning.
  unfold task_delete_sched_return_with_loan, os_sched_continuation_return_post; Intros returned final.
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { assert (Hlast : task_tcb_init_stack_same_call returned middle) by tauto.
    destruct Hlast as [Hi [Ho Hs]], Hnormal as [[Hi' [Ho' Hs']] Havailable],
      Hcut_same as [Hi'' [Ho'' Hs'']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Htail : task_delete_return_relation environment critical requested sg cut_call cut returned final).
  { eapply TaskDeleteReturnScheduled; eassumption || tauto. }
  unfold task_delete_post; Exists cut_call returned final cut loan.
  rewrite task_delete_call_closed_stable_split_loan.
  unfold os_sched_continuation_pre; entailer!.
Qed.

Lemma task_delete_same_return_trans : forall first initial middle current last final,
  task_delete_same_return first initial middle current ->
  task_delete_same_return middle current last final ->
  task_delete_same_return first initial last final.
Proof.
  intros first initial middle current last final [[Hi [Ho Hs]] Hfirst]
    [[Hi' [Ho' Hs']] Hlast].
  split; [unfold task_tcb_init_stack_same_call; repeat split; congruence|auto].
Qed.

Lemma task_delete_phase_rely_trans : forall requested phase sg before middle after,
  task_delete_phase_rely requested phase sg before middle ->
  task_delete_phase_rely requested phase sg middle after ->
  task_delete_phase_rely requested phase sg before after.
Proof.
  intros requested phase sg before middle after
    [Hi [Hr [Hv Hphase]]] [Hi' [Hr' [Hv' Hphase']]].
  unfold task_delete_phase_rely; repeat split; try congruence; try assumption.
  destruct phase; simpl in *; try exact I; try assumption.
  destruct Hphase as [Hp [Ht Ho]], Hphase' as [Hp' [Ht' Ho']].
  repeat split; [congruence|intros; auto|auto].
Qed.

(** The exact EventPtr remains exposed while C evaluates the second actual
    argument.  The other cells are the accepted helper's unchanged footprint.
    Its precondition consequence forgets only the old pointer value. *)
Definition task_delete_event_remove_fields
  (tcb group table row bit_x bit_y row_value group_value : Z) : Assertion :=
  coq_prop (0 <= row < 8) &&
  (tcb_field_address tcb TCBY # UChar |-> row **
   tcb_field_address tcb TCBBitX # UChar |-> bit_x **
   tcb_field_address tcb TCBBitY # UChar |-> bit_y **
   group # UChar |-> group_value ** (table + row) # UChar |-> row_value).

Lemma task_delete_event_remove_pre_refines :
  forall tcb event group table row bit_x bit_y row_value group_value,
  tcb_field_address tcb TCBEventPtr # Ptr |-> event **
    task_delete_event_remove_fields tcb group table row bit_x bit_y row_value group_value |--
  event_task_remove_pre tcb group table row bit_x bit_y row_value group_value.
Proof.
  intros; unfold task_delete_event_remove_fields, event_task_remove_pre.
  sep_apply_l_atomic (store_ptr_undef_store_ptr
    (tcb_field_address tcb TCBEventPtr) event); entailer!.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma task_delete_prefix_error_selected_profile__prefix_and_error_returns :
  forall sg nesting priority,
  task_delete_static_profile sg ->
  task_delete_prefix_error sg false nesting priority =
    (if 0 <? nesting then Some OS_ERR_TASK_DEL_ISR else
     if priority =? 63 then Some OS_ERR_TASK_DEL_IDLE else
     if ((63 <=? priority) && negb (priority =? 255))%bool
     then Some OS_ERR_PRIO_INVALID else None).
Proof.
  intros sg nesting priority [[Hstable Hprofile] [Hconfig Hrest]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold valid_stable_glob_vars in Hstable; tauto).
  assert (Hidle : sg.(osTaskIdlePrio) = 63)
    by (unfold valid_stable_glob_vars in Hstable; lia).
  assert (Hself : sg.(osPrioSelf) = 255)
    by (unfold valid_stable_glob_vars in Hstable; tauto).
  unfold task_delete_prefix_error.
  rewrite Hconfig, Hlowest, Hidle, Hself; reflexivity.
Qed.
Lemma task_delete_table_reserved_lookup__prefix_and_error_returns :
  forall sg state selected,
  task_delete_static_profile sg -> task_delete_table sg state selected = 1 ->
  task_delete_table_lookup state.(TskState) selected (inl OS_ERR_TASK_DEL).
Proof.
  intros sg state selected Hprofile Hpointer.
  unfold task_delete_table, task_delete_table_lookup in *.
  destruct (state.(TskState).(prioTbl) selected) as [| |tid];
    simpl in *; try congruence.
  exfalso; exact (task_delete_static_profile_slot_not_reserved sg tid Hprofile Hpointer).
Qed.
Lemma task_delete_table_null_lookup__prefix_and_error_returns :
  forall sg state selected,
  task_delete_static_profile sg -> UCOS2_state_inv sg state ->
  task_priority_in_range sg selected -> task_delete_table sg state selected = 0 ->
  task_delete_table_lookup state.(TskState) selected (inl OS_ERR_TASK_NOT_EXIST).
Proof.
  intros sg state selected Hstatic Hvalid Hrange Hpointer.
  unfold task_delete_table, task_delete_table_lookup in *.
  destruct (state.(TskState).(prioTbl) selected) as [| |tid] eqn:Hentry;
    simpl in *; try congruence.
  destruct Hstatic as [[Hstable Hprofile] [Hconfig Hlayout]].
  destruct Hvalid as [_ [Htasks [_ [_ [Hcross Hrest]]]]].
  destruct Hcross as [[Hcreator [Hslots Halias]] Hcross].
  specialize (Hslots selected Hrange); rewrite Hentry in Hslots.
  destruct Hslots as [node Hnode].
  destruct Htasks as [[Hpartition Hpool] Htasks].
  assert (Hslot : task_slot_in_range sg tid).
  { apply (proj2 (Hpartition tid)); left; eauto. }
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable) as Hbase.
  assert (Hin : In sg.(g_OSTCBTbl) (stable_global_addresses sg)).
  { unfold stable_global_addresses; simpl; tauto. }
  specialize (Hbase Hin).
  unfold task_slot_addr in Hpointer; rewrite Hconfig in Hpointer.
  change (sg.(g_OSTCBTbl) + tid * 64 = 0) in Hpointer.
  unfold task_slot_in_range in Hslot; lia.
Qed.
Lemma task_delete_lookup_error_post__prefix_and_error_returns :
  forall environment critical saved_local sg requested name original mask initial
    current acquired selected error,
  task_delete_lookup_history sg requested original initial current acquired ->
  task_delete_selection sg requested acquired.(TskState) acquired.(SchedState) selected ->
  task_delete_table_lookup acquired.(TskState) selected (inl error) ->
  task_delete_restore_post environment critical saved_local requested TaskDeleteStable None
    sg current mask acquired |--
  task_delete_post environment critical saved_local sg requested name original mask initial
    (encode_os_err_code error).
Proof.
  intros environment critical saved_local sg requested name original mask initial
    current acquired selected error
    [Hstatic [Hbound [Hsame [Hprefix [Hrely Hprotocol]]]]] Hselection Hlookup.
  unfold task_delete_restore_post; Intros returned final.
  assert (Hrestored : task_delete_same_return current acquired returned final) by tauto.
  assert (Hsame_return : task_tcb_init_stack_same_call returned original).
  { destruct Hrestored as [[Hi [Ho Hs]] Havailable], Hsame as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Heffect : task_delete_effect sg requested name initial
    (encode_os_err_code error) acquired).
  { eapply TaskDeleteLookupError; eassumption. }
  assert (Hreturn : task_delete_return_relation environment critical requested sg
    current acquired returned final).
  { apply TaskDeleteReturnRestored; tauto. }
  unfold task_delete_post; Exists current returned final acquired (@None FlagWaiterState).
  entailer!.
Qed.
Lemma task_delete_prefix_error_post__prefix_and_error_returns :
  forall environment critical saved_local completed sg requested name call mask initial error,
  task_delete_prefix_error sg false initial.(IntrState).(intNesting) requested = Some error ->
  task_delete_entry environment critical saved_local completed sg requested call mask initial |--
  task_delete_post environment critical saved_local sg requested name call mask initial
    (encode_os_err_code error).
Proof.
  intros; unfold task_delete_entry, task_delete_post; Intros.
  Exists call call initial initial (@None FlagWaiterState).
  assert (Hsame : task_tcb_init_stack_same_call call call)
    by (unfold task_tcb_init_stack_same_call; auto).
  assert (Heffect : task_delete_effect sg requested name initial
    (encode_os_err_code error) initial) by (apply TaskDeletePrefixError; assumption).
  assert (Hreturn : task_delete_return_relation environment critical requested sg
    call initial call initial) by constructor.
  entailer!.
Qed.
Lemma task_delete_entry_profile_and_priority__prefix_and_error_returns :
  forall environment critical saved_local completed sg requested call mask initial,
  task_delete_entry environment critical saved_local completed sg requested call mask initial |--
  coq_prop (task_delete_static_profile sg /\ 0 <= requested <= 255).
Proof. intros; unfold task_delete_entry; entailer!. Qed.
Lemma task_delete_entry_split_int_nesting__prefix_and_error_returns :
  forall environment critical saved_local completed sg requested call mask initial,
  task_delete_entry environment critical saved_local completed sg requested call mask initial |--
  coq_prop flag_unlink_layout &&
  (task_delete_uchar_cell sg.(g_OSIntNesting) (task_delete_ints initial) **
   wand (task_delete_uchar_cell sg.(g_OSIntNesting) (task_delete_ints initial))
     (task_delete_entry environment critical saved_local completed sg requested call mask initial)).
Proof.
  intros; unfold task_delete_entry, task_delete_call_closed,
    kernel_continuation_call_closed, kernel_continuation_inv,
    task_delete_phase_resources, task_delete_phase_valid.
  rewrite (UCOS2_raw_rep_split_module sg initial InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, store_int_state, task_delete_uchar_cell, task_delete_ints.
  Intros; entailer!.
  apply_sepcon_adjoint; entailer!.
Qed.
Lemma task_public_storage_field_focus__ready_bitmap : forall sg tasks tid node field,
  tasks.(TaskStateDef.inUsedTaskStates) tid = Some node ->
  In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  task_public_storage sg tasks |--
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field (task_layout_image sg node field) **
  wand (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field (task_layout_image sg node field))
    (task_public_storage sg tasks).
Proof.
  intros sg tasks tid node field Hnode Hin.
  match goal with |- _ |-- ?post => set (focused_post := post) end.
  sep_apply (task_public_storage_split_field sg tasks tid node field Hnode Hin).
  unfold focused_post.
  entailer!; apply_sepcon_adjoint.
  sep_apply (task_public_storage_merge_field sg tasks tid node field Hnode Hin).
  entailer!.
Qed.
Lemma used_task_rep_ready_fields_focus__ready_bitmap : forall sg tid node,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  used_task_rep sg tid node |--
  (tcb_field_address (task_slot_addr sg tid) TCBY # UChar |->
      tcb_y_of_prio node.(TaskStateDef.curPrio) **
   tcb_field_address (task_slot_addr sg tid) TCBBitX # UChar |->
      tcb_bit_x_of_prio node.(TaskStateDef.curPrio) **
   tcb_field_address (task_slot_addr sg tid) TCBBitY # UChar |->
      tcb_bit_y_of_prio node.(TaskStateDef.curPrio)) **
  wand (tcb_field_address (task_slot_addr sg tid) TCBY # UChar |->
      tcb_y_of_prio node.(TaskStateDef.curPrio) **
   tcb_field_address (task_slot_addr sg tid) TCBBitX # UChar |->
      tcb_bit_x_of_prio node.(TaskStateDef.curPrio) **
   tcb_field_address (task_slot_addr sg tid) TCBBitY # UChar |->
      tcb_bit_y_of_prio node.(TaskStateDef.curPrio))
    (used_task_rep sg tid node).
Proof.
  intros sg tid node Hmulti Hprofile.
  rewrite (used_task_rep_tcb64 sg tid node Hmulti Hprofile).
  rewrite (task_slot_addr_tcb64 sg tid Hmulti Hprofile).
  match goal with |- _ |-- ?post => set (focused_post := post) end.
  set (fields_y := remove TCBField_eq_dec TCBY tcb_fields).
  set (fields_x := remove TCBField_eq_dec TCBBitX fields_y).
  assert (Hnd_y : NoDup fields_y).
  { unfold fields_y, tcb_fields; vm_compute; repeat constructor; simpl; intuition discriminate. }
  assert (Hnd_x : NoDup fields_x).
  { unfold fields_x, fields_y, tcb_fields; vm_compute; repeat constructor; simpl; intuition discriminate. }
  assert (Hx : In TCBBitX fields_y).
  { unfold fields_y, tcb_fields; vm_compute; intuition congruence. }
  assert (Hy : In TCBBitY fields_x).
  { unfold fields_x, fields_y, tcb_fields; vm_compute; intuition congruence. }
  sep_apply (tcb64_storage_split (tcb64_addr sg tid) (task_tcb64_image sg node) TCBY).
  unfold tcb64_storage_without; fold fields_y.
  sep_apply (tcb64_fields_rep_split fields_y (tcb64_addr sg tid)
    (task_tcb64_image sg node) TCBBitX Hnd_y Hx).
  fold fields_x.
  sep_apply (tcb64_fields_rep_split fields_x (tcb64_addr sg tid)
    (task_tcb64_image sg node) TCBBitY Hnd_x Hy).
  unfold focused_post.
  cbn [task_tcb64_image tcb_cell].
  entailer!; apply_sepcon_adjoint.
  pose proof (tcb64_fields_rep_merge fields_x (tcb64_addr sg tid)
    (task_tcb64_image sg node) TCBBitY Hnd_x Hy) as Hmerge_y.
  pose proof (tcb64_fields_rep_merge fields_y (tcb64_addr sg tid)
    (task_tcb64_image sg node) TCBBitX Hnd_y Hx) as Hmerge_x.
  pose proof (tcb64_storage_merge (tcb64_addr sg tid)
    (task_tcb64_image sg node) TCBY) as Hmerge_row.
  cbn [task_tcb64_image tcb_cell] in Hmerge_y, Hmerge_x, Hmerge_row.
  sep_apply Hmerge_y.
  unfold fields_x; sep_apply Hmerge_x.
  unfold fields_y; sep_apply Hmerge_row.
  entailer!.
Qed.
Lemma sched_remove_ready_row_values__ready_bitmap : forall sg tasks sched tid node,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(TaskStateDef.inUsedTaskStates) tid = Some node ->
  task_priority_in_range sg node.(TaskStateDef.curPrio) ->
  sched_ready_structure sg tasks sched ->
  0 <= tcb_y_of_prio node.(TaskStateDef.curPrio) < 8 ->
  sched_row_values tasks (sched_remove_ready_task sched tid).(SchedStateDef.readyList) =
  replace_Znth (tcb_y_of_prio node.(TaskStateDef.curPrio))
    (event_task_remove_cleared
      (encode_ready_tbl_at_or sched.(SchedStateDef.readyList) tasks
        (tcb_y_of_prio node.(TaskStateDef.curPrio)))
      (tcb_bit_x_of_prio node.(TaskStateDef.curPrio)))
    (sched_row_values tasks sched.(SchedStateDef.readyList)).
Proof.
  intros sg tasks sched tid node Hsg Hu Hnode Hp Hr Hy.
  destruct (sched_remove_ready_encoding sg tasks sched tid node Hsg Hu Hnode Hp Hr)
    as [_ Hrows].
  unfold sched_row_values; cbn [map].
  rewrite (Hrows 0), (Hrows 1), (Hrows 2), (Hrows 3),
    (Hrows 4), (Hrows 5), (Hrows 6), (Hrows 7).
  unfold tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio,
    event_task_remove_cleared in *.
  set (row := TaskStateDef.curPrio node / 8) in *.
  assert (Hcases : row = 0 \/ row = 1 \/ row = 2 \/ row = 3 \/
    row = 4 \/ row = 5 \/ row = 6 \/ row = 7) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
Qed.
Lemma sched_raw_rep_remove_ready_focus__ready_bitmap : forall sg tasks sched tid node,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(TaskStateDef.inUsedTaskStates) tid = Some node ->
  task_priority_in_range sg node.(TaskStateDef.curPrio) ->
  sched_ready_structure sg tasks sched ->
  0 <= tcb_y_of_prio node.(TaskStateDef.curPrio) < 8 ->
  sched_raw_rep sg tasks sched |--
  ((sg.(g_OSRdyTbl) + tcb_y_of_prio node.(TaskStateDef.curPrio)) # UChar |->
      encode_ready_tbl_at_or sched.(SchedStateDef.readyList) tasks
        (tcb_y_of_prio node.(TaskStateDef.curPrio)) **
   sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp sched.(SchedStateDef.readyList) tasks) **
  wand ((sg.(g_OSRdyTbl) + tcb_y_of_prio node.(TaskStateDef.curPrio)) # UChar |->
      event_task_remove_cleared
        (encode_ready_tbl_at_or sched.(SchedStateDef.readyList) tasks
          (tcb_y_of_prio node.(TaskStateDef.curPrio)))
        (tcb_bit_x_of_prio node.(TaskStateDef.curPrio)) **
   sg.(g_OSRdyGrp) # UChar |->
      event_task_remove_group
        (encode_ready_tbl_at_or sched.(SchedStateDef.readyList) tasks
          (tcb_y_of_prio node.(TaskStateDef.curPrio)))
        (encode_ready_grp sched.(SchedStateDef.readyList) tasks)
        (tcb_bit_x_of_prio node.(TaskStateDef.curPrio))
        (tcb_bit_y_of_prio node.(TaskStateDef.curPrio)))
    (sched_raw_rep sg tasks (sched_remove_ready_task sched tid)).
Proof.
  intros sg tasks sched tid node Hsg Hu Hnode Hp Hr Hy.
  destruct (sched_remove_ready_encoding sg tasks sched tid node Hsg Hu Hnode Hp Hr)
    as [Hgroup _].
  change (encode_ready_grp (sched_remove_ready_task sched tid).(SchedStateDef.readyList) tasks =
    event_task_remove_group
      (encode_ready_tbl_at_or sched.(SchedStateDef.readyList) tasks
        (tcb_y_of_prio node.(TaskStateDef.curPrio)))
      (encode_ready_grp sched.(SchedStateDef.readyList) tasks)
      (tcb_bit_x_of_prio node.(TaskStateDef.curPrio))
      (tcb_bit_y_of_prio node.(TaskStateDef.curPrio))) in Hgroup.
  unfold sched_raw_rep.
  rewrite Hgroup, sched_remove_ready_physical_rep_eq.
  sep_apply_l_atomic (sched_rows_split_cell sg tasks sched.(SchedStateDef.readyList)
    (tcb_y_of_prio node.(TaskStateDef.curPrio)) Hy).
  replace (tcb_y_of_prio node.(TaskStateDef.curPrio) * sizeof(UCHAR))
    with (tcb_y_of_prio node.(TaskStateDef.curPrio)) by (cbn; lia).
  entailer!; apply_sepcon_adjoint.
  rewrite sched_rows_array_equiv.
  rewrite (sched_remove_ready_row_values__ready_bitmap sg tasks sched tid node
    Hsg Hu Hnode Hp Hr Hy).
  pose proof (sched_rows_merge_updated_array sg tasks sched.(SchedStateDef.readyList)
    (tcb_y_of_prio node.(TaskStateDef.curPrio))
    (event_task_remove_cleared
      (encode_ready_tbl_at_or sched.(SchedStateDef.readyList) tasks
        (tcb_y_of_prio node.(TaskStateDef.curPrio)))
      (tcb_bit_x_of_prio node.(TaskStateDef.curPrio))) Hy) as Hmerge.
  replace (tcb_y_of_prio node.(TaskStateDef.curPrio) * sizeof(UCHAR))
    with (tcb_y_of_prio node.(TaskStateDef.curPrio)) in Hmerge by (cbn; lia).
  sep_apply Hmerge; entailer!.
Qed.
Lemma task_delete_live_history_inv_and_lookup__event_and_flag_unlink :
  forall sg requested original initial current acquired priority pointer tid node,
  task_delete_live_history sg requested original initial current acquired
    priority pointer tid node ->
  UCOS2_state_inv sg acquired /\
    acquired.(TskState).(inUsedTaskStates) tid = Some node.
Proof.
  intros sg requested original initial current acquired priority pointer tid node
    [Hhistory [Hselected [Hlookup Hpointer]]].
  split.
  - unfold task_delete_lookup_history, task_delete_phase_rely,
      task_delete_phase_valid in Hhistory; tauto.
  - exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hlookup)).
Qed.
Lemma task_event_handle_zero_implies_none__event_and_flag_unlink :
  forall sg s tid node,
  UCOS2_state_inv sg s ->
  s.(TskState).(inUsedTaskStates) tid = Some node ->
  task_delete_event_handle sg node = 0 -> node.(eventPtr) = None.
Proof.
  intros sg s tid node Hvalid Hnode Hzero.
  destruct (node.(eventPtr)) as [eid|] eqn:Hptr; [|reflexivity].
  destruct Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]].
  destruct (cross_module_invariants.task_event_reference_has_waiter
    sg s tid node eid Hcross Hnode Hptr) as [event [He Hin]].
  destruct (event_pool.event_pool_used_not_free sg s.(EventState) eid event
    (proj1 Hevents) He) as [[Hnonneg Hbound] _].
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Haddresses : valid_stable_global_addresses sg).
  { unfold valid_stable_glob_vars in Hsg; tauto. }
  assert (Hbase : 0 < sg.(g_OSEventTbl)).
  { exact (Forall_inv (proj1 Haddresses)). }
  unfold task_delete_event_handle, encode_event_link in Hzero.
  rewrite Hptr in Hzero; unfold event_pool_addr in Hzero.
  pose proof (event_object_size_positive sg.(osKernelConfig)); nia.
Qed.
Lemma task_delete_event_unlinked_lookup__event_and_flag_unlink :
  forall before tid node after updated,
  before.(TskState).(inUsedTaskStates) tid = Some node ->
  task_delete_event_unlinked before tid node after updated ->
  after.(TskState).(inUsedTaskStates) tid = Some updated.
Proof.
  intros before tid node after updated Hnode Hunlinked.
  unfold task_delete_event_unlinked in Hunlinked.
  destruct node.(eventPtr) as [eid|].
  - destruct Hunlinked as [event [He [-> ->]]].
    cbn [task_delete_event_state replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity.
  - destruct Hunlinked as [-> ->]; exact Hnode.
Qed.
Lemma task_active_links_lookup_id__event_and_flag_unlink :
  forall ids used previous tid node,
  task_active_links used previous ids -> In tid ids ->
  used tid = Some node -> node.(taskID) = tid.
Proof.
  induction ids as [|head rest IH]; intros used previous tid node Hlinks Hin Hnode;
    [contradiction|].
  destruct Hlinks as [first [Hfirst [Hid [Hprev [Hnext Htail]]]]].
  destruct Hin as [->|Hin].
  - assert (node = first) by congruence; subst node; exact Hid.
  - eapply IH; eassumption.
Qed.
Lemma task_live_flag_waiter_domain__event_and_flag_unlink :
  forall sg s tid node,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some node ->
  node.(tcbFlagNode) <> 0 ->
  exists waiter, waiter.(flagTask) = tid /\ node.(eventPtr) = None /\
    flag_unlink_domain sg s.(FlagState) node.(tcbFlagNode) waiter node.
Proof.
  intros sg s tid node Hconfig Hvalid Hnode Hnonzero.
  destruct Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]].
  assert (Hflags : flag.valid_flag_state sg s.(FlagState)).
  { assert (Hconfigured : flag.valid_flag_configuration sg s.(FlagState)) by tauto.
    unfold flag.valid_flag_configuration in Hconfigured.
    rewrite Hconfig in Hconfigured; exact Hconfigured. }
  assert (Hwaiters : cross_module_invariants.task_flag_waiter_consistency
    sg s.(TskState) s.(FlagState)).
  { unfold cross_module_invariants.cross_module_consistency in Hcross; tauto. }
  destruct (proj2 Hwaiters tid node Hnode (or_introl Hnonzero))
    as [waiter [Hwaiter Htid]].
  destruct (proj1 Hwaiters node.(tcbFlagNode) waiter Hwaiter)
    as [_ [live [Hlive [Hgen [Hptr [Haddr [Hphase [Hnull Hmulti]]]]]]]].
  rewrite Htid in Hlive.
  assert (live = node) by congruence; subst live.
  destruct (flag.valid_flag_state_node_position sg s.(FlagState) node.(tcbFlagNode)
    waiter Hflags Hwaiter) as [group [pre [rest [Hg [Horder [Hnodeaddr Hremaining]]]]]].
  assert (Hid : node.(taskID) = tid).
  { destruct Htasks as [_ [Hactive _]].
    destruct Hactive as [_ [_ [_ [Hcover Hlinks]]]].
    eapply task_active_links_lookup_id__event_and_flag_unlink;
      [exact Hlinks|apply Hcover; eauto|exact Hnode]. }
  exists waiter; split; [exact Htid|]. split; [exact Hnull|].
  unfold flag_unlink_domain, flag_unlink_tcb_addr.
  split; [exact Hconfig|]. split; [exact Hflags|].
  split; [exact Hwaiter|]. split; [exact Hnodeaddr|].
  split; [congruence|]. split; [exact Hgen|].
  split; [exact Haddr|reflexivity].
Qed.
Lemma task_delete_event_unlinked_flag_node_eq__event_and_flag_unlink :
  forall before tid node after updated,
  task_delete_event_unlinked before tid node after updated ->
  updated.(tcbFlagNode) = node.(tcbFlagNode).
Proof.
  intros before tid node after updated Hunlinked.
  unfold task_delete_event_unlinked in Hunlinked.
  destruct node.(eventPtr).
  - destruct Hunlinked as [event [He [Ha ->]]]; reflexivity.
  - destruct Hunlinked as [Ha ->]; reflexivity.
Qed.
Lemma task_update_generation_preserves_stack_coverage__event_and_flag_unlink :
  forall tasks tid old updated active,
  tasks.(inUsedTaskStates) tid = Some old ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  task_stack_coverage_spec.task_stack_live_coverage tasks active ->
  task_stack_coverage_spec.task_stack_live_coverage
    (glob_task_set_usedtask tasks tid updated) active.
Proof.
  intros tasks tid old updated active Hold Hgen Hcoverage.
  eapply task_stack_coverage_spec.task_stack_live_coverage_used_map_frame
    with (before := tasks); [|reflexivity|exact Hcoverage].
  intros slot node Hnode.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:E.
  - apply Z.eqb_eq in E; subst slot.
    injection Hnode as Hnode; subst node; exists old; auto.
  - exists node; auto.
Qed.
Lemma task_and_flag_raw_rep_merge_updated__event_and_flag_unlink :
  forall sg state tid old updated flags,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  updated.(curPrio) = old.(curPrio) ->
  task_public_storage sg (glob_task_set_usedtask state.(TskState) tid updated) **
  sched.sched_raw_rep sg state.(TskState) state.(SchedState) **
  flag.flag_configured_rep sg flags **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state |--
  UCOS2_raw_rep sg
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid updated)
      (replace_FlagS flags state)).
Proof.
  intros sg state tid old updated flags Hold Hprio.
  assert (Hsched : sched.sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched.sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid updated) state.(SchedState)).
  { apply sched.sched_raw_rep_priority_ext; intros slot Hin.
    symmetry; eapply glob_task_set_usedtask_observation; eassumption. }
  assert (Hevent : event.event_raw_rep sg state.(TskState) state.(EventState) =
    event.event_raw_rep sg (glob_task_set_usedtask state.(TskState) tid updated) state.(EventState)).
  { apply event.event_raw_rep_change_task_index.
    apply event.event_wait_priority_agreement_encodes.
    eapply event.glob_task_set_usedtask_preserves_event_priority_agreement; eassumption. }
  unfold UCOS2_raw_rep, UCOS2_raw_rep_missing_task_storage_sched_flag,
    task_stack.task_shared_rep.
  cbn [replace_TskS replace_FlagS TskState SchedState IntrState EventState FlagState
    TickState MemoryState TimerState StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
  rewrite <- Hsched, <- Hevent; entailer!.
Qed.
Lemma task_and_event_raw_rep_merge_updated__event_and_flag_unlink :
  forall sg state tid old updated eid ev,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  updated.(curPrio) = old.(curPrio) ->
  state.(EventState).(EventStateDef.inUsedEventStates) eid = Some ev ->
  let events := event.update_event_field_raw state.(EventState) eid
    (event_wait.event_set_wait_list ev (helpers.remove_Z_eqb tid ev.(EventStateDef.waitList))) in
  task_public_storage sg (glob_task_set_usedtask state.(TskState) tid updated) **
  sched.sched_raw_rep sg state.(TskState) state.(SchedState) **
  event.event_raw_rep sg state.(TskState) events **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state |--
  UCOS2_raw_rep sg
    (replace_TskS (glob_task_set_usedtask state.(TskState) tid updated)
      (replace_EventS events state)).
Proof.
  intros sg state tid old updated eid ev Hold Hprio He events.
  assert (Hsched : sched.sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched.sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid updated) state.(SchedState)).
  { apply sched.sched_raw_rep_priority_ext; intros slot Hin.
    symmetry; eapply glob_task_set_usedtask_observation; eassumption. }
  assert (Hevent : event.event_raw_rep sg state.(TskState) events =
    event.event_raw_rep sg (glob_task_set_usedtask state.(TskState) tid updated) events).
  { apply event.event_raw_rep_change_task_index.
    apply event.event_wait_priority_agreement_encodes.
    eapply event.glob_task_set_usedtask_preserves_event_priority_agreement; eassumption. }
  unfold UCOS2_raw_rep, UCOS2_raw_rep_missing_task_storage_sched_event,
    task_stack.task_shared_rep.
  cbn [replace_TskS replace_EventS TskState SchedState IntrState EventState FlagState
    TickState MemoryState TimerState StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
  rewrite <- Hsched, <- Hevent.
  sep_apply_l_atomic (queue_core.queue_set_event_wait_list_preserves_storage
    sg state.(EventState) eid ev (helpers.remove_Z_eqb tid ev.(EventStateDef.waitList)) He).
  entailer!.
Qed.
Lemma tcb64_storage_split_wait_fields__event_and_flag_unlink :
  forall base image row bit_x bit_y event,
  image TCBY = Some row -> image TCBBitX = Some bit_x ->
  image TCBBitY = Some bit_y -> image TCBEventPtr = Some event ->
  tcb64_storage_rep base image |--
  tcb_field_address base TCBY # UChar |-> row **
  tcb_field_address base TCBBitX # UChar |-> bit_x **
  tcb_field_address base TCBBitY # UChar |-> bit_y **
  tcb_field_address base TCBEventPtr # Ptr |-> event **
  event_task_remove_tcb_frame base image.
Proof.
  intros base image row bit_x bit_y event Hrow Hx Hy Hptr.
  set (fields_y := remove TCBField_eq_dec TCBY tcb_fields).
  set (fields_x := remove TCBField_eq_dec TCBBitX fields_y).
  set (fields_bits := remove TCBField_eq_dec TCBBitY fields_x).
  assert (Hnd_y : NoDup fields_y) by
    (unfold fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  assert (Hnd_x : NoDup fields_x) by
    (unfold fields_x, fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  assert (Hnd_bits : NoDup fields_bits) by
    (unfold fields_bits, fields_x, fields_y, tcb_fields; vm_compute;
      repeat constructor; simpl; intuition discriminate).
  sep_apply_l_atomic (tcb64_storage_split base image TCBY).
  unfold tcb64_storage_without; fold fields_y.
  sep_apply_l_atomic (tcb64_fields_rep_split fields_y base image TCBBitX
    Hnd_y ltac:(unfold fields_y, tcb_fields; vm_compute; intuition congruence)).
  fold fields_x.
  sep_apply_l_atomic (tcb64_fields_rep_split fields_x base image TCBBitY
    Hnd_x ltac:(unfold fields_x, fields_y, tcb_fields; vm_compute; intuition congruence)).
  fold fields_bits.
  sep_apply_l_atomic (tcb64_fields_rep_split fields_bits base image TCBEventPtr
    Hnd_bits ltac:(unfold fields_bits, fields_x, fields_y, tcb_fields; vm_compute; intuition congruence)).
  unfold event_task_remove_tcb_frame; fold fields_y; fold fields_x; fold fields_bits.
  rewrite Hrow, Hx, Hy, Hptr; cbn [tcb_cell]; entailer!.
Qed.
Lemma glob_task_set_usedtask_overwrite__prepare_and_completed_window :
  forall tasks tid first last,
  glob_task_set_usedtask (glob_task_set_usedtask tasks tid first) tid last =
  glob_task_set_usedtask tasks tid last.
Proof.
  intros; unfold glob_task_set_usedtask; cbn; f_equal.
  apply functional_extensionality; intro slot.
  destruct (Z.eqb slot tid); reflexivity.
Qed.
Lemma task_delete_unlinked_prepare_eq__prepare_and_completed_window :
  forall acquired tid node evented event_node flagged flag_node loan,
  task_delete_event_unlinked (task_delete_ready_state acquired tid) tid node evented event_node ->
  task_delete_flag_unlinked evented tid event_node flagged flag_node loan ->
  task_delete_prepare_single_wait acquired tid node =
    Some (replace_TskS (glob_task_set_usedtask flagged.(TskState) tid
      (task_prepare_delete flag_node)) flagged, loan).
Proof.
  intros acquired tid node evented event_node flagged flag_node loan Hevent Hflag.
  unfold task_delete_event_unlinked in Hevent.
  destruct node.(eventPtr) as [eid|] eqn:Hptr.
  - destruct Hevent as [event [Hevent [-> ->]]].
    unfold task_delete_flag_unlinked in Hflag.
    cbn [task_set_event_ptr tcbFlagNode] in Hflag.
    destruct (Z.eqb node.(tcbFlagNode) 0) eqn:Hnull.
    + destruct Hflag as [-> [-> ->]].
      unfold task_delete_prepare_single_wait; rewrite Hptr.
      cbn [task_delete_ready_state replace_SchedS EventState] in Hevent.
      rewrite Hevent. cbn [task_set_event_ptr tcbFlagNode]. rewrite Hnull.
      unfold task_delete_prepare_after_unlink, task_delete_event_state, task_delete_ready_state.
      cbn [replace_TskS replace_SchedS replace_EventS TskState SchedState EventState].
      rewrite glob_task_set_usedtask_overwrite__prepare_and_completed_window.
      reflexivity.
    + destruct Hflag as [w [flags [Hflag [-> [-> ->]]]]].
      unfold task_delete_prepare_single_wait; rewrite Hptr.
      cbn [task_delete_ready_state replace_SchedS EventState] in Hevent.
      rewrite Hevent. cbn [task_set_event_ptr tcbFlagNode]. rewrite Hnull.
      cbn [task_delete_event_state task_delete_ready_state replace_TskS replace_SchedS replace_EventS FlagState] in Hflag.
      rewrite Hflag.
      unfold task_delete_prepare_after_unlink, task_delete_event_state, task_delete_flag_state, task_delete_ready_state.
      cbn [replace_TskS replace_SchedS replace_EventS replace_FlagS TskState SchedState EventState FlagState].
      rewrite !glob_task_set_usedtask_overwrite__prepare_and_completed_window.
      reflexivity.
  - destruct Hevent as [-> ->].
    unfold task_delete_flag_unlinked in Hflag.
    destruct (Z.eqb node.(tcbFlagNode) 0) eqn:Hnull.
    + destruct Hflag as [-> [-> ->]].
      unfold task_delete_prepare_single_wait; rewrite Hptr, Hnull.
      destruct acquired; reflexivity.
    + destruct Hflag as [w [flags [Hflag [-> [-> ->]]]]].
      unfold task_delete_prepare_single_wait; rewrite Hptr, Hnull.
      cbn [task_delete_ready_state replace_SchedS FlagState] in Hflag.
      rewrite Hflag.
      unfold task_delete_prepare_after_unlink, task_delete_flag_state, task_delete_ready_state.
      cbn [replace_TskS replace_SchedS replace_EventS replace_FlagS TskState SchedState EventState FlagState].
      rewrite glob_task_set_usedtask_overwrite__prepare_and_completed_window.
      reflexivity.
Qed.
Lemma task_delete_preparation_preserves_running_protocol__prepare_and_completed_window :
  forall sg call state tid old prepared loan,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(curPrio) <> sg.(osLowestPrio) ->
  task_delete_prepare_single_wait state tid old = Some (prepared, loan) ->
  task_delete_running_protocol sg call state ->
  task_delete_running_protocol sg call (task_delete_locked prepared).
Proof.
  intros sg call state tid old prepared loan Hold Hnonidle Hprepare Hrun.
  destruct (task_delete_prepare_single_wait_frame _ _ _ _ _ Hprepare)
    as [updated [Hpost [Hprio [Hstat [Hid [Hgen Hsp]]]]]].
  rewrite Hpost.
  unfold task_delete_running_protocol, task_delete_locked in *.
  cbn [replace_IntrS replace_FlagS replace_EventS replace_SchedS replace_TskS SchedState TskState IntrState].
  intro Hrunning.
  destruct (Hrun Hrunning) as [Hidle [Hstorage Havailable]].
  split.
  - destruct Hidle as [idle [idle_node [Hlookup [Hlowest Hin]]]].
    assert (Hdifferent : idle <> tid).
    { intro Heq; subst idle; rewrite Hold in Hlookup; injection Hlookup as Heq; subst idle_node; contradiction. }
    exists idle, idle_node.
    cbn [replace_IntrS replace_FlagS replace_EventS replace_SchedS replace_TskS TskState SchedState
      glob_task_set_usedtask inUsedTaskStates sched_remove_ready_task sched_set_ready readyList].
    rewrite (proj2 (Z.eqb_neq _ _) Hdifferent).
    repeat split; try assumption.
    apply helpers.remove_Z_eqb_in_neq; assumption.
  - split.
    + unfold os_sched_current_storage_binding in *.
      cbn [replace_IntrS replace_FlagS replace_EventS replace_SchedS replace_TskS TskState SchedState
        glob_task_set_usedtask inUsedTaskStates taskLifecycle sched_remove_ready_task sched_set_ready curTaskID].
      destruct Hstorage as [Horigin [Hcur [Hrange [Haddress Hstorage]]]].
      split; [exact Horigin|]. split; [exact Hcur|].
      split; [exact Hrange|]. split; [exact Haddress|].
      destruct Hstorage as [[stored [Hstored [Hstoredid Hstoredgen]]]|[Hnone Hfree]].
      * destruct (Z.eqb (stackLeaseSlot (os_sched_call_stack call)) tid) eqn:Hsame.
        -- apply Z.eqb_eq in Hsame.
           rewrite Hsame, Hold in Hstored; injection Hstored as Hstored; subst stored.
           left; exists updated; repeat split; congruence.
        -- left; exists stored; auto.
      * destruct (Z.eqb (stackLeaseSlot (os_sched_call_stack call)) tid) eqn:Hsame.
        -- apply Z.eqb_eq in Hsame; rewrite Hsame, Hold in Hnone; discriminate.
        -- right; auto.
    + exact Havailable.
Qed.
Lemma task_prepare_delete_storage_focus__prepare_and_completed_window :
  forall sg tid node,
  used_task_rep sg tid node |--
  (tcb_field_address (task_slot_addr sg tid) TCBDly # UInt |-> node.(dly) **
   tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> Byte.unsigned node.(stat) **
   tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status node.(statPend)) **
  wand
    (tcb_field_address (task_slot_addr sg tid) TCBDly # UInt |-> 0 **
     tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> 0 **
     tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> 0)
    (used_task_rep sg tid (task_prepare_delete node)).
Proof.
  intros sg tid node.
  set (fields := tcb_configured_fields
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)).
  set (fields1 := remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) fields).
  set (fields2 := remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) fields1).
  set (fields3 := remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) fields2).
  set (cell := tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)).
  set (old_image := task_layout_image sg node).
  set (new_image := task_layout_image sg (task_prepare_delete node)).
  assert (Hnd : NoDup fields) by apply tcb_configured_fields_nodup.
  assert (Hnd1 : NoDup fields1) by (apply tcb_configured_fields_remove_nodup; exact Hnd).
  assert (Hnd2 : NoDup fields2) by (apply tcb_configured_fields_remove_nodup; exact Hnd1).
  assert (Hdly : In (TCBCommonField TCBDly) fields) by apply tcb_configured_common_field_in.
  assert (Hstat : In (TCBCommonField TCBStat) fields1).
  { apply in_in_remove; [discriminate|apply tcb_configured_common_field_in]. }
  assert (Hpend : In (TCBCommonField TCBStatPend) fields2).
  { apply in_in_remove; [discriminate|]. apply in_in_remove; [discriminate|apply tcb_configured_common_field_in]. }
  match goal with |- _ |-- ?Q =>
    change (TaskFieldStorage.store_fields TCBLayoutField_eq_dec cell fields old_image |-- Q)
  end.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec cell fields old_image _ Hnd Hdly).
  fold fields1.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec cell fields1 old_image _ Hnd1 Hstat).
  fold fields2.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec cell fields2 old_image _ Hnd2 Hpend).
  fold fields3.
  assert (Hresidual : TaskFieldStorage.store_fields TCBLayoutField_eq_dec cell fields3 new_image =
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec cell fields3 old_image).
  { unfold new_image, old_image; rewrite task_prepare_delete_layout_image_eq.
    unfold tcb_prepare_delete_image, tcb_layout_write.
    rewrite !TaskFieldStorage.store_fields_update_unlisted; try reflexivity.
    all: unfold fields3, fields2, fields1; intro Hin;
      repeat match goal with
      | H : In _ (remove _ _ _) |- _ =>
          apply in_remove in H; let Hne := fresh "Hne" in destruct H as [H Hne]
      end; congruence.
  }
  cbn [cell old_image task_layout_image task_storage.tcb_layout_image task_tcb64_image
    tcb_layout_cell tcb_cell encode_task_status task_status.encode_task_status].
  unfold task.encode_task_status, task_status.encode_task_status.
  entailer!.
  apply_sepcon_adjoint.
  change (TaskFieldStorage.store_fields TCBLayoutField_eq_dec cell fields3 old_image **
    (cell (TCBCommonField TCBDly) (new_image (TCBCommonField TCBDly)) **
     (cell (TCBCommonField TCBStat) (new_image (TCBCommonField TCBStat)) **
     cell (TCBCommonField TCBStatPend) (new_image (TCBCommonField TCBStatPend)))) |--
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec cell fields new_image).
  rewrite <- Hresidual.
  unfold fields3.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec cell fields2 new_image _ Hnd2 Hpend).
  unfold fields2.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec cell fields1 new_image _ Hnd1 Hstat).
  unfold fields1.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec cell fields new_image _ Hnd Hdly).
  entailer!.
Qed.
Lemma task_delete_prepare_raw_focus__prepare_and_completed_window :
  forall sg state tid node,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  UCOS2_raw_rep sg state |--
  coq_prop (0 <= task_delete_locks state <= 255) &&
  (task_delete_prepare_cells sg state tid node false **
   wand (task_delete_prepare_cells sg state tid node true)
     (UCOS2_raw_rep sg (task_delete_prepare_state state tid node))).
Proof.
  intros sg state tid node Hnode.
  assert (Hsched : sched.sched_raw_rep sg state.(TskState) state.(SchedState) =
    sched.sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid (task_prepare_delete node)) state.(SchedState)).
  { apply sched.sched_raw_rep_priority_ext; intros slot Hin; symmetry.
    eapply glob_task_set_usedtask_observation; [exact Hnode|reflexivity]. }
  assert (Hevent : event.event_raw_rep sg state.(TskState) state.(EventState) =
    event.event_raw_rep sg (glob_task_set_usedtask state.(TskState) tid (task_prepare_delete node)) state.(EventState)).
  { apply event.event_raw_rep_change_task_index.
    apply event.event_wait_priority_agreement_encodes.
    eapply event.glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hnode|reflexivity]. }
  unfold UCOS2_raw_rep, task_stack.task_shared_rep, interrupt_inv, store_int_state.
  Intros.
  sep_apply_l_atomic (task_public_storage_split_task sg state.(TskState) tid node Hnode).
  sep_apply_l_atomic (task_prepare_delete_storage_focus__prepare_and_completed_window sg tid node).
  prop_apply_p (store_uchar_range sg.(g_OSLockNesting) state.(IntrState).(lockNesting)).
  Intros_p Hlockrange.
  unfold task_delete_prepare_cells; cbn zeta.
  unfold task_delete_locks.
  entailer!.
  apply_sepcon_adjoint.
  cbn beta iota zeta.
  unfold task_delete_prepare_state.
  cbn [replace_IntrS replace_TskS IntrState TskState SchedState EventState TickState FlagState MemoryState TimerState StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
  rewrite <- Hsched, <- Hevent.
  unfold task_delete_lock_state.
  cbn [intNesting lockNesting].
  entailer!.
  all: try solve [unfold interrupt_in_range in *; cbn in *;
    destruct (Z.ltb state.(IntrState).(lockNesting) 255); lia].
  sep_apply_r_atomic (task_public_storage_merge_updated_task sg state.(TskState) tid (task_prepare_delete node)).
  entailer!.
  match goal with
  | |- context [wand ?P (used_task_rep sg tid (task_prepare_delete node))] =>
      sep_apply_r_atomic (task_delete_focus_reassemble P
        (used_task_rep sg tid (task_prepare_delete node))); entailer!
  end.
Qed.
Lemma task_delete_unlinked_lookup__prepare_and_completed_window :
  forall acquired tid node evented event_node flagged flag_node loan,
  acquired.(TskState).(inUsedTaskStates) tid = Some node ->
  task_delete_event_unlinked (task_delete_ready_state acquired tid) tid node evented event_node ->
  task_delete_flag_unlinked evented tid event_node flagged flag_node loan ->
  flagged.(TskState).(inUsedTaskStates) tid = Some flag_node.
Proof.
  intros acquired tid node evented event_node flagged flag_node loan Hnode Hevent Hflag.
  unfold task_delete_event_unlinked in Hevent.
  assert (Heventnode : evented.(TskState).(inUsedTaskStates) tid = Some event_node).
  { destruct node.(eventPtr) as [eid|].
    - destruct Hevent as [event [Hevent [-> ->]]].
      cbn [task_delete_event_state replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    - destruct Hevent as [-> ->]; exact Hnode. }
  unfold task_delete_flag_unlinked in Hflag.
  destruct (Z.eqb event_node.(tcbFlagNode) 0).
  - destruct Hflag as [-> [-> ->]]; exact Heventnode.
  - destruct Hflag as [w [flags [Hflag [-> [-> ->]]]]].
    cbn [task_delete_flag_state replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Z.eqb_refl; reflexivity.
Qed.
Lemma task_prev_encoded_zero_iff__release_and_recycle_resources : forall sg tasks tid node,
  task_delete_static_profile sg -> task_in_range sg tasks ->
  tasks.(inUsedTaskStates) tid = Some node ->
  encode_task_link sg node.(prevTCB) = 0 <-> node.(prevTCB) = None.
Proof.
  intros sg tasks tid node [Hprofile [Hconfig Hrest]] [Hpool [Hactive HrestTasks]] Hnode.
  destruct node.(prevTCB) as [previous|] eqn:Hprev; [|cbn; tauto].
  split; [|discriminate].
  intro Hzero; cbn [encode_task_link] in Hzero.
  destruct Hactive as [Hnd [Hhead [Hcount [Hmembers Hlinks]]]].
  assert (Hin : In tid tasks.(taskLifecycle).(taskActiveOrder)).
  { apply Hmembers; eexists; exact Hnode. }
  destruct (proj1 (task_active_links_neighbors _ _ _ _ _ Hlinks Hin Hnode))
    as [Hnone|[p [Hp Hpin]]]; [congruence|].
  assert (HpEq : p = previous) by congruence; subst p.
  destruct (proj1 (Hmembers previous) Hpin) as [old Hold].
  assert (Hslot : task_slot_in_range sg previous).
  { apply (proj2 (proj1 Hpool previous)); left; eexists; exact Hold. }
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) (proj1 Hprofile)
    ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
  unfold task_slot_addr in Hzero; rewrite Hconfig in Hzero.
  change (g_OSTCBTbl sg + previous * 64 = 0) in Hzero.
  unfold task_slot_in_range in Hslot; lia.
Qed.
Lemma task_active_link_neighbor_nodes__release_and_recycle_resources :
  forall ids used previous tid node,
  task_active_links used previous ids -> NoDup ids ->
  (forall p, previous = Some p -> ~ In p ids) ->
  used tid = Some node -> In tid ids ->
  ((node.(prevTCB) = previous /\ hd_error ids = Some tid) \/
    exists p pred, node.(prevTCB) = Some p /\ used p = Some pred /\
      pred.(nextTCB) = Some tid /\ In p ids /\ p <> tid) /\
  (forall n, node.(nextTCB) = Some n -> exists successor,
    used n = Some successor /\ successor.(prevTCB) = Some tid /\
    In n ids /\ n <> tid /\ node.(prevTCB) <> Some n).
Proof.
  intro ids; induction ids as [|head rest IH];
    intros used previous tid node Hlinks Hnd Houtside Hnode Hin; [contradiction|].
  inversion Hnd as [|head' rest' Hnotin Hndrest]; subst head' rest'.
  destruct Hlinks as [first [Hfirst [Hid [Hprev [Hnext Htail]]]]].
  destruct Hin as [Heq|Hin].
  - subst tid; assert (Hfirsteq : first = node) by congruence; subst first.
    split; [left; split; [exact Hprev|reflexivity]|].
    intros n Hn; destruct rest as [|next tail]; [cbn in Hnext; congruence|].
    cbn in Hnext; assert (En : next = n) by congruence; subst next.
    destruct Htail as [successor [Hsucc [_ [Hsprev Hsrest]]]].
    exists successor; repeat split; try assumption.
    + right; left; reflexivity.
    + intro E; subst n; apply Hnotin; left; reflexivity.
    + intro E; apply (Houtside n); [congruence|right; left; reflexivity].
  - destruct (IH used (Some head) tid node Htail Hndrest
      ltac:(intros p E; injection E as E; subst p; exact Hnotin) Hnode Hin)
      as [Hpred Hsucc].
    split.
    + right; destruct Hpred as [[Hp Hfirsttail]|[p [pred [Hp [Hpred [Hpn [Hpin Hpne]]]]]]].
      * exists head, first; repeat split; try assumption.
        -- congruence.
        -- left; reflexivity.
        -- intro E; apply Hnotin; rewrite E; exact Hin.
      * exists p, pred; repeat split; try assumption; right; exact Hpin.
    + intros n Hn; destruct (Hsucc n Hn) as [successor [Hs [Hp [Hnin Hrest]]]].
      exists successor; repeat split; try tauto; right; exact Hnin.
Qed.
Lemma used_task_map_remove_focus__release_and_recycle_resources : forall sg used tid node,
  used tid = Some node ->
  store_map (used_task_rep sg) used |-- used_task_rep sg tid node **
    store_map (used_task_rep sg) (fun slot => if Z.eq_dec slot tid then None else used slot).
Proof.
  intros sg used tid node Hnode.
  sep_apply_l_atomic (store_map_split (used_task_rep sg) tid node used Hnode).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (used_task_rep sg) used
    (fun slot => if Z.eq_dec slot tid then None else used slot) tid
    ltac:(intros slot Hne; cbn beta; destruct (Z.eq_dec slot tid); congruence))).
  sep_apply_l_atomic (store_map_missing_equiv_store_map (used_task_rep sg)
    (fun slot => if Z.eq_dec slot tid then None else used slot) tid
    ltac:(cbn beta; destruct (Z.eq_dec tid tid); congruence)).
  entailer!.
Qed.
Lemma used_task_map_insert_merge__release_and_recycle_resources : forall sg remaining after tid node,
  remaining tid = None -> after tid = Some node ->
  (forall slot, slot <> tid -> remaining slot = after slot) ->
  store_map (used_task_rep sg) remaining ** used_task_rep sg tid node |--
    store_map (used_task_rep sg) after.
Proof.
  intros sg remaining after tid node Habsent Hnode Hframe.
  sep_apply_l_atomic (store_map_equiv_store_map_missing (used_task_rep sg) remaining tid Habsent).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (used_task_rep sg)
    remaining after tid Hframe)).
  apply store_map_merge; exact Hnode.
Qed.
Lemma used_task_field_focus_updated__release_and_recycle_resources :
  forall sg tid old new field value,
  In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  task_layout_image sg new = tcb_layout_write (task_layout_image sg old) field value ->
  used_task_rep sg tid old |--
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    field (task_layout_image sg old field) **
  wand (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field value) (used_task_rep sg tid new).
Proof.
  intros sg tid old new field value Hin Himage.
  unfold used_task_rep, task_slot_storage_rep.
  sep_apply_l_atomic (tcb_configured_storage_split_field _ _ (task_slot_addr sg tid)
    (task_layout_image sg old) field Hin).
  cancel; apply_sepcon_adjoint.
  rewrite Himage.
  sep_apply_r_atomic (tcb_configured_storage_merge_updated_field _ _ (task_slot_addr sg tid)
    (task_layout_image sg old) field value Hin).
  entailer!.
Qed.
Lemma task_recycle_preserves_live_coverage__release_and_recycle_resources :
  forall sg tasks active tid priority node name,
  task_stack_coverage_spec.task_stack_live_coverage tasks active ->
  task_stack_coverage_spec.task_stack_live_coverage
    (task_recycle sg tasks tid priority node name) active.
Proof.
  intros sg tasks active tid priority node name Hcoverage slot updated Hupdated.
  change (task_unlink_used_map tasks.(inUsedTaskStates) tid node slot = Some updated) in Hupdated.
  unfold task_unlink_used_map in Hupdated.
  destruct (Z.eq_dec slot tid); [discriminate|].
  destruct (tasks.(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  injection Hupdated as E; subst updated.
  exact (Hcoverage slot old Hold).
Qed.
Lemma task_recycle_preserves_running_protocol__release_and_recycle_resources :
  forall sg state call tid priority node name,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  node.(curPrio) <> sg.(osLowestPrio) ->
  task_delete_running_protocol sg call state ->
  task_delete_running_protocol sg call
    (replace_TskS (task_recycle sg state.(TskState) tid priority node name) state).
Proof.
  intros sg state call tid priority node name Hnode Hnonidle Hprotocol Hrunning.
  destruct (Hprotocol Hrunning) as [[idle [idle_node [Hidle [Hprio Hready]]]]
    [Hstorage Havailable]].
  assert (Hidle_ne : idle <> tid) by (intro E; subst idle; assert (idle_node = node) by congruence; congruence).
  split.
  - unfold task_delete_idle_ready.
    exists idle, (task_set_links idle_node
      (match node.(prevTCB) with
       | Some p => if Z.eq_dec idle p then node.(nextTCB) else idle_node.(nextTCB)
       | None => idle_node.(nextTCB) end)
      (match node.(nextTCB) with
       | Some n => if Z.eq_dec idle n then node.(prevTCB) else idle_node.(prevTCB)
       | None => idle_node.(prevTCB) end)).
    split.
    + cbn [replace_TskS TskState task_recycle inUsedTaskStates].
      unfold task_unlink_used_map; destruct (Z.eq_dec idle tid); [contradiction|rewrite Hidle; reflexivity].
    + split; [exact Hprio|exact Hready].
  - split; [|exact Havailable].
    destruct Hstorage as [Horigin [Hcurrent [Hrange [Haddress Hstored]]]].
    unfold os_sched_current_storage_binding; cbn zeta.
    split; [exact Horigin|]; split; [exact Hcurrent|];
      split; [exact Hrange|]; split; [exact Haddress|].
    destruct (Z.eq_dec call.(os_sched_call_stack).(stackLeaseSlot) tid) as [Heq|Hne].
    + right; cbn [replace_TskS TskState task_recycle inUsedTaskStates taskLifecycle taskFreeStorage].
      unfold task_unlink_used_map; destruct (Z.eq_dec call.(os_sched_call_stack).(stackLeaseSlot) tid);
        [split; [reflexivity|eexists; reflexivity]|contradiction].
    + destruct Hstored as [[old [Hold [Hid Hgen]]]|[Habsent [image Himage]]].
      * left; cbn [replace_TskS TskState task_recycle inUsedTaskStates].
        unfold task_unlink_used_map; destruct (Z.eq_dec call.(os_sched_call_stack).(stackLeaseSlot) tid);
          [contradiction|rewrite Hold].
        eexists; split; [reflexivity|split; assumption].
      * right; cbn [replace_TskS TskState task_recycle inUsedTaskStates taskLifecycle taskFreeStorage].
        unfold task_unlink_used_map; destruct (Z.eq_dec call.(os_sched_call_stack).(stackLeaseSlot) tid);
          [contradiction|rewrite Habsent].
        split; [reflexivity|eexists; exact Himage].
Qed.
Lemma task_recycle_sched_rep_eq__release_and_recycle_resources :
  forall sg state tid generation priority node name,
  task_delete_prepared sg tid generation state.(TskState) state.(SchedState) ->
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  sched.sched_raw_rep sg state.(TskState) state.(SchedState) =
  sched.sched_raw_rep sg (task_recycle sg state.(TskState) tid priority node name) state.(SchedState).
Proof.
  intros sg state tid generation priority node name [[Hstructure Hready] Hphase] Hnode.
  assert (Habsent : ~ In tid state.(SchedState).(readyList)).
  { intro Hin; destruct (proj1 (Hready tid node Hnode) Hin) as [_ Hnot]; apply Hnot; left; reflexivity. }
  apply sched.sched_raw_rep_priority_ext; intros slot Hin.
  cbn [task_recycle inUsedTaskStates].
  rewrite task_unlink_used_map_observation by (intros; reflexivity).
  destruct (Z.eq_dec slot tid); [subst slot; contradiction|reflexivity].
Qed.
Lemma task_recycle_slot_focus__release_and_recycle_resources : forall sg tasks tid node name,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  used_task_rep sg tid node |--
  tcb_field_address (task_slot_addr sg tid) TCBNext # Ptr |-> encode_task_link sg node.(nextTCB) **
  tcb_field_address (task_slot_addr sg tid) TCBPrev # Ptr |-> encode_task_link sg node.(prevTCB) **
  tcb_field_address (task_slot_addr sg tid) TCBTaskName # Ptr |-> node.(tcbTaskName) **
  wand
    (tcb_field_address (task_slot_addr sg tid) TCBNext # Ptr |->
      encode_task_link sg (hd_error tasks.(unUsedTaskStates)) **
     tcb_field_address (task_slot_addr sg tid) TCBPrev # Ptr |-> encode_task_link sg node.(prevTCB) **
     tcb_field_address (task_slot_addr sg tid) TCBTaskName # Ptr |-> name)
    (task_slot_storage_rep sg tid (task_recycle_image sg tasks node name)).
Proof.
  intros sg tasks tid node name Hconfig.
  set (fields := tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)).
  set (without_next := remove TCBLayoutField_eq_dec (TCBCommonField TCBNext) fields).
  set (without_prev := remove TCBLayoutField_eq_dec (TCBCommonField TCBPrev) without_next).
  set (cells := tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)).
  set (named := tcb_layout_write (task_layout_image sg node) (TCBCommonField TCBTaskName) (Some name)).
  set (linked_prev := tcb_layout_write named (TCBCommonField TCBPrev)
    (Some (encode_task_link sg node.(prevTCB)))).
  assert (Hnd : NoDup fields) by apply tcb_configured_fields_nodup.
  assert (Hnd_next : NoDup without_next) by (apply tcb_configured_fields_remove_nodup; exact Hnd).
  assert (Hnd_prev : NoDup without_prev) by (apply tcb_configured_fields_remove_nodup; exact Hnd_next).
  assert (Hnext : In (TCBCommonField TCBNext) fields) by apply tcb_configured_common_field_in.
  assert (Hprev : In (TCBCommonField TCBPrev) without_next).
  { apply in_in_remove; [discriminate|apply tcb_configured_common_field_in]. }
  assert (Hname : In (TCBCommonField TCBTaskName) without_prev).
  { apply in_in_remove; [discriminate|apply in_in_remove; [discriminate|apply tcb_configured_common_field_in]]. }
  assert (Himage : task_recycle_image sg tasks node name =
    tcb_layout_write linked_prev (TCBCommonField TCBNext)
      (Some (encode_task_link sg (hd_error tasks.(unUsedTaskStates))))).
  { unfold linked_prev, named, task_recycle_image; rewrite Hconfig.
    apply functional_extensionality; intros [field| | | | | | |]; try destruct field; reflexivity. }
  unfold used_task_rep, task_slot_storage_rep, tcb_configured_storage_rep.
  fold fields cells.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field TCBLayoutField (option Z)
    TCBLayoutField_eq_dec cells fields (task_layout_image sg node) (TCBCommonField TCBNext) Hnd Hnext).
  fold without_next.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field TCBLayoutField (option Z)
    TCBLayoutField_eq_dec cells without_next (task_layout_image sg node) (TCBCommonField TCBPrev) Hnd_next Hprev).
  fold without_prev.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field TCBLayoutField (option Z)
    TCBLayoutField_eq_dec cells without_prev (task_layout_image sg node) (TCBCommonField TCBTaskName) Hnd_prev Hname).
  cbn [cells tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image].
  cancel; apply_sepcon_adjoint.
  rewrite Himage.
  sep_apply_r_atomic (TaskFieldStorage.store_fields_merge_updated_field TCBLayoutField (option Z)
    TCBLayoutField_eq_dec cells fields linked_prev (TCBCommonField TCBNext)
    (Some (encode_task_link sg (hd_error tasks.(unUsedTaskStates)))) Hnd Hnext).
  unfold linked_prev; fold without_next.
  cbn [cells tcb_layout_cell tcb_cell]; cancel.
  sep_apply_r_atomic (TaskFieldStorage.store_fields_merge_updated_field TCBLayoutField (option Z)
    TCBLayoutField_eq_dec cells without_next named (TCBCommonField TCBPrev)
    (Some (encode_task_link sg node.(prevTCB))) Hnd_next Hprev).
  unfold named; fold without_prev.
  cbn [cells tcb_layout_cell tcb_cell]; cancel.
  sep_apply_r_atomic (TaskFieldStorage.store_fields_merge_updated_field TCBLayoutField (option Z)
    TCBLayoutField_eq_dec cells without_prev (task_layout_image sg node)
    (TCBCommonField TCBTaskName) (Some name) Hnd_prev Hname).
  cbn [cells tcb_layout_cell tcb_cell].
  entailer!.
Qed.
Lemma task_delete_preparation_task_projections__release_and_recycle_resources :
  forall before tid node prepared loan,
  task_delete_prepare_single_wait before tid node = Some (prepared, loan) ->
  prepared.(TskState).(prioTbl) = before.(TskState).(prioTbl) /\
  prepared.(TskState).(inUsedTaskStates) tid = Some (task_delete_prepared_node node).
Proof.
  intros before tid node prepared loan Hstep.
  unfold task_delete_prepare_single_wait in Hstep.
  destruct node.(eventPtr) as [eid|] eqn:Hptr;
    [destruct (before.(EventState).(inUsedEventStates) eid) as [event|] eqn:Hevent;
      [|discriminate]|];
    cbn [task_set_event_ptr tcbFlagNode] in Hstep;
    destruct (Z.eqb node.(tcbFlagNode) 0) eqn:Hflag;
    try (destruct (flag.flag_unlink_node before.(FlagState) node.(tcbFlagNode))
      as [[waiter flags]|] eqn:Hunlink; [|discriminate]);
    injection Hstep as Eprepared Eloan; subst prepared;
    (split; [reflexivity|]);
    cbn [task_delete_prepare_after_unlink replace_TskS replace_SchedS replace_EventS
      replace_FlagS TskState glob_task_set_usedtask inUsedTaskStates];
    rewrite Z.eqb_refl; f_equal;
    try (apply Z.eqb_eq in Hflag);
    destruct node; cbn in Hptr, Hflag; cbn;
    try rewrite Hptr; try rewrite Hflag; reflexivity.
Qed.
Lemma task_delete_preparation_preserves_mutex_owner_exclusion__release_and_recycle_resources :
  forall before tid node prepared loan,
  task_delete_prepare_single_wait before tid node = Some (prepared, loan) ->
  task_delete_mutex_owner_exclusion before tid ->
  task_delete_mutex_owner_exclusion prepared tid.
Proof.
  intros before tid node prepared loan Hstep Howner.
  unfold task_delete_prepare_single_wait in Hstep.
  destruct node.(eventPtr) as [eid|] eqn:Hptr;
    [destruct (before.(EventState).(inUsedEventStates) eid) as [event|] eqn:Hevent;
      [|discriminate]|];
    cbn [task_set_event_ptr tcbFlagNode] in Hstep;
    destruct (Z.eqb node.(tcbFlagNode) 0) eqn:Hflag;
    try (destruct (flag.flag_unlink_node before.(FlagState) node.(tcbFlagNode))
      as [[waiter flags]|] eqn:Hunlink; [|discriminate]);
    injection Hstep as Eprepared Eloan; subst prepared;
    intros slot found mutex Hfound Htype Hmutex;
    cbn [task_delete_prepare_after_unlink replace_TskS replace_SchedS replace_EventS
      replace_FlagS EventState] in Hfound;
    try (eapply Howner; eassumption).
  all: cbn [event.update_event_field_raw inUsedEventStates] in Hfound;
    destruct (Z.eqb slot eid) eqn:Eslot;
    [injection Hfound as Efound; subst found;
      eapply Howner; [exact Hevent|exact Htype|exact Hmutex]
    |eapply Howner; eassumption].
Qed.
Lemma task_public_storage_recycle_focus__release_and_recycle_resources :
  forall sg state tid priority node name,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  task_in_range sg state.(TskState) ->
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  state.(TskState).(prioTbl) priority = PTTask tid ->
  0 <= priority < 64 -> node.(nextTCB) <> None ->
  task_public_storage sg state.(TskState) |--
  task_delete_recycle_cells sg state tid priority node name false **
  wand (task_delete_recycle_cells sg state tid priority node name true)
    (task_public_storage sg (task_recycle sg state.(TskState) tid priority node name)).
Proof.
  intros sg state tid priority node name Hconfig [Hpool [Hactive Htaskrest]]
    Hnode Htable Hpriority Hnext_exists.
  destruct Hactive as [Hnd [Hhead [Hcount [Hmembers Hlinks]]]].
  assert (Hin : In tid state.(TskState).(taskLifecycle).(taskActiveOrder)).
  { apply Hmembers; eexists; exact Hnode. }
  destruct (task_active_link_neighbor_nodes__release_and_recycle_resources _ _ _ _ _
    Hlinks Hnd ltac:(intros p E; discriminate) Hnode Hin) as [Hprev_nodes Hnext_nodes].
  destruct node.(nextTCB) as [next|] eqn:Hnext; [|contradiction].
  destruct (Hnext_nodes next eq_refl) as [successor [Hsuccessor [Hsuccessor_prev
    [Hnext_in [Hnext_ne Hprev_next]]]]].
  assert (Hnotfree : ~ In tid state.(TskState).(unUsedTaskStates)).
  { exact (proj1 (proj1 (proj2 Hpool) tid node Hnode)). }
  set (without_target := fun slot =>
    if Z.eq_dec slot tid then None else state.(TskState).(inUsedTaskStates) slot).
  set (without_next := fun slot => if Z.eq_dec slot next then None else without_target slot).
  set (post := task_unlink_used_map state.(TskState).(inUsedTaskStates) tid node).
  assert (Hnext_lookup : without_target next = Some successor).
  { unfold without_target; destruct (Z.eq_dec next tid); [contradiction|exact Hsuccessor]. }
  assert (Himage_next : task_layout_image sg
      (task_set_links successor successor.(nextTCB) node.(prevTCB)) =
    tcb_layout_write (task_layout_image sg successor) (TCBCommonField TCBPrev)
      (Some (encode_task_link sg node.(prevTCB)))).
  { apply functional_extensionality; intros [field| | | | | | |]; try destruct field; reflexivity. }
  pose proof (used_task_field_focus_updated__release_and_recycle_resources sg next successor
    (task_set_links successor successor.(nextTCB) node.(prevTCB))
    (TCBCommonField TCBPrev) (Some (encode_task_link sg node.(prevTCB)))
    (tcb_configured_common_field_in _ _ _) Himage_next) as Hnext_focus.
  cbn [task_layout_image tcb_layout_image tcb_layout_cell tcb_cell] in Hnext_focus.
  rewrite Hsuccessor_prev in Hnext_focus; cbn [encode_task_link] in Hnext_focus.
  unfold task_public_storage at 1; unfold store_used_task_map.
  sep_apply_l_atomic (array_abstraction.store_prio_tbl_split_cell sg state.(TskState).(prioTbl) priority Hpriority).
  rewrite Htable; cbn [prio_tbl_entry_to_addr].
  sep_apply_l_atomic (used_task_map_remove_focus__release_and_recycle_resources sg _ tid node Hnode).
  fold without_target.
  sep_apply_l_atomic (task_recycle_slot_focus__release_and_recycle_resources sg state.(TskState) tid node name Hconfig).
  pose proof (used_task_map_remove_focus__release_and_recycle_resources sg without_target next successor Hnext_lookup) as Hsplit_next.
  unfold without_target in Hsplit_next; sep_apply_l_atomic Hsplit_next.
  fold without_next; sep_apply_l_atomic Hnext_focus.
  destruct node.(prevTCB) as [previous|] eqn:Hprev.
  - assert (Hprevious_next : previous <> next) by (intro E; subst previous; congruence).
    destruct Hprev_nodes as [[Hbad _]|[p [predecessor [Hp [Hpredecessor [Hprednext [Hp_in Hp_ne]]]]]]];
      [discriminate|].
    assert (Ep : p = previous) by congruence; subst p.
    set (without_previous := fun slot => if Z.eq_dec slot previous then None else without_next slot).
    set (post_without_next := fun slot => if Z.eq_dec slot next then None else post slot).
    assert (Hprevious_lookup : without_next previous = Some predecessor).
    { unfold without_next, without_target; destruct (Z.eq_dec previous next); [contradiction|].
      destruct (Z.eq_dec previous tid); [contradiction|exact Hpredecessor]. }
    assert (Himage_prev : task_layout_image sg
        (task_set_links predecessor (Some next) predecessor.(prevTCB)) =
      tcb_layout_write (task_layout_image sg predecessor) (TCBCommonField TCBNext)
        (Some (encode_task_link sg (Some next)))).
    { apply functional_extensionality; intros [field| | | | | | |]; try destruct field; reflexivity. }
    pose proof (used_task_field_focus_updated__release_and_recycle_resources sg previous predecessor
      (task_set_links predecessor (Some next) predecessor.(prevTCB))
      (TCBCommonField TCBNext) (Some (encode_task_link sg (Some next)))
      (tcb_configured_common_field_in _ _ _) Himage_prev) as Hprev_focus.
    cbn [task_layout_image tcb_layout_image tcb_layout_cell tcb_cell] in Hprev_focus.
    rewrite Hprednext in Hprev_focus; cbn [encode_task_link] in Hprev_focus.
    pose proof (used_task_map_remove_focus__release_and_recycle_resources sg without_next previous predecessor Hprevious_lookup) as Hsplit_prev.
    unfold without_next, without_target in Hsplit_prev; sep_apply_l_atomic Hsplit_prev.
    fold without_previous; sep_apply_l_atomic Hprev_focus.
    unfold task_delete_recycle_cells, task_delete_neighbor_cells, task_delete_tcb_value;
      cbn [task_tcb64_image]; rewrite Hnext, Hprev; cbn [encode_task_link].
    change (sizeof(PTR)) with 4.
    sepcon_assoc_change; cancel; apply_sepcon_adjoint.
    repeat match goal with
    | |- ?P |-- _ => match P with context [wand ?part ?whole] =>
        sep_apply (task_delete_focus_reassemble part whole) end
    end.
    assert (Hprev_post : post_without_next previous =
      Some (task_set_links predecessor (Some next) predecessor.(prevTCB))).
    { unfold post_without_next, post, task_unlink_used_map; rewrite Hprev, Hnext.
      destruct (Z.eq_dec previous next); [contradiction|].
      destruct (Z.eq_dec previous tid); [contradiction|].
      rewrite Hpredecessor; destruct (Z.eq_dec previous previous); [reflexivity|contradiction]. }
    assert (Hprev_frame : forall slot, slot <> previous ->
      without_previous slot = post_without_next slot).
    { intros slot Hne; unfold without_previous, without_next, without_target,
        post_without_next, post, task_unlink_used_map; rewrite Hprev, Hnext.
      repeat match goal with |- context [Z.eq_dec ?a ?b] => destruct (Z.eq_dec a b) end;
        try congruence; try reflexivity.
      destruct (inUsedTaskStates (TskState state) slot) as [other|]; [destruct other|]; reflexivity. }
    pose proof (used_task_map_insert_merge__release_and_recycle_resources sg without_previous
      post_without_next previous (task_set_links predecessor (Some next) predecessor.(prevTCB))
      ltac:(unfold without_previous; destruct (Z.eq_dec previous previous); congruence) Hprev_post Hprev_frame) as Hmerge_prev.
    unfold without_previous, without_next, without_target, post_without_next, post in Hmerge_prev.
    assert (Hnext_post : post next = Some (task_set_links successor successor.(nextTCB) (Some previous))).
    { unfold post, task_unlink_used_map; rewrite Hprev, Hnext.
      destruct (Z.eq_dec next tid); [contradiction|].
      rewrite Hsuccessor; destruct (Z.eq_dec next previous); [congruence|].
      destruct (Z.eq_dec next next); [reflexivity|contradiction]. }
    pose proof (used_task_map_insert_merge__release_and_recycle_resources sg post_without_next post
      next (task_set_links successor successor.(nextTCB) (Some previous))
      ltac:(unfold post_without_next; destruct (Z.eq_dec next next); congruence) Hnext_post
      ltac:(intros slot Hne; unfold post_without_next; destruct (Z.eq_dec slot next); congruence)) as Hmerge_next.
    unfold post_without_next, post in Hmerge_next.
    pose proof (array_abstraction.store_prio_tbl_merge_updated_cell sg state.(TskState).(prioTbl) priority PTFree Hpriority) as Hmerge_table.
    change (sizeof(PTR)) with 4 in Hmerge_table; cbn [prio_tbl_entry_to_addr] in Hmerge_table.
    unfold update_prio_tbl in Hmerge_table.
    pose proof (task_recycle_free_storage_merge sg state.(TskState) tid priority node name Hnotfree) as Hmerge_free.
    cbn [task_recycle unUsedTaskStates taskLifecycle taskFreeStorage] in Hmerge_free.
    unfold task_public_storage, store_used_task_map, post.
    cbn [task_recycle inUsedTaskStates unUsedTaskStates taskLifecycle taskFreeStorage
      tcbListHead taskCount prioTbl]; rewrite Hprev; cbn [encode_task_link].
    sepcon_assoc_change.
    sep_apply_r_atomic Hmerge_next; sepcon_assoc_change.
    sep_apply_r_atomic Hmerge_prev; sepcon_assoc_change.
    sep_apply_r_atomic Hmerge_table; sepcon_assoc_change.
    sep_apply_r_atomic Hmerge_free; sepcon_assoc_change.
    match goal with
    | |- ?P |-- _ => match P with context [wand ?part ?whole] =>
      sep_apply_r_atomic (task_delete_focus_reassemble part whole) end
    end.
    cbn [hd_error encode_task_link task_reg_allocator_rep task_recycle taskRegNextID].
    entailer!.
  - unfold task_delete_recycle_cells, task_delete_neighbor_cells, task_delete_tcb_value;
      cbn [task_tcb64_image]; rewrite Hnext, Hprev; cbn [encode_task_link].
    change (sizeof(PTR)) with 4.
    normalize; sepcon_assoc_change; cancel; apply_sepcon_adjoint.
    repeat match goal with
    | |- ?P |-- _ => match P with context [wand ?part ?whole] =>
        sep_apply (task_delete_focus_reassemble part whole) end
    end.
    assert (Hnext_post : post next = Some (task_set_links successor successor.(nextTCB) None)).
    { unfold post, task_unlink_used_map; rewrite Hprev, Hnext.
      destruct (Z.eq_dec next tid); [contradiction|].
      rewrite Hsuccessor; destruct (Z.eq_dec next next); [reflexivity|contradiction]. }
    assert (Hnext_frame : forall slot, slot <> next -> without_next slot = post slot).
    { intros slot Hne; unfold without_next, without_target, post, task_unlink_used_map;
        rewrite Hprev, Hnext.
      repeat match goal with |- context [Z.eq_dec ?a ?b] => destruct (Z.eq_dec a b) end;
        try congruence; try reflexivity.
      destruct (inUsedTaskStates (TskState state) slot) as [other|]; [destruct other|]; reflexivity. }
    pose proof (used_task_map_insert_merge__release_and_recycle_resources sg without_next post next
      (task_set_links successor successor.(nextTCB) None)
      ltac:(unfold without_next; destruct (Z.eq_dec next next); congruence) Hnext_post Hnext_frame) as Hmerge_next.
    unfold without_next, without_target, post in Hmerge_next.
    pose proof (array_abstraction.store_prio_tbl_merge_updated_cell sg state.(TskState).(prioTbl) priority PTFree Hpriority) as Hmerge_table.
    change (sizeof(PTR)) with 4 in Hmerge_table; cbn [prio_tbl_entry_to_addr] in Hmerge_table.
    unfold update_prio_tbl in Hmerge_table.
    pose proof (task_recycle_free_storage_merge sg state.(TskState) tid priority node name Hnotfree) as Hmerge_free.
    cbn [task_recycle unUsedTaskStates taskLifecycle taskFreeStorage] in Hmerge_free.
    unfold task_public_storage, store_used_task_map, post.
    cbn [task_recycle inUsedTaskStates unUsedTaskStates taskLifecycle taskFreeStorage
      tcbListHead taskCount prioTbl]; rewrite Hprev; cbn [encode_task_link].
    sepcon_assoc_change.
    sep_apply_r_atomic Hmerge_next; sepcon_assoc_change.
    sep_apply_r_atomic Hmerge_table; sepcon_assoc_change.
    sep_apply_r_atomic Hmerge_free; sepcon_assoc_change.
    match goal with
    | |- ?P |-- _ => match P with context [wand ?part ?whole] =>
      sep_apply_r_atomic (task_delete_focus_reassemble part whole) end
    end.
    cbn [hd_error encode_task_link task_reg_allocator_rep task_recycle taskRegNextID].
    entailer!.
    rewrite Hnext; cbn [encode_task_link].
    entailer!.
Qed.
Lemma task_active_prev_encode_zero__byte_and_cut_observations :
  forall sg tasks tid node,
  selected_kernel_profile sg -> task_in_range sg tasks ->
  tasks.(inUsedTaskStates) tid = Some node ->
  encode_task_link sg node.(prevTCB) = 0 -> node.(prevTCB) = None.
Proof.
  intros sg tasks tid node Hprofile [[Hpool _] [Hactive _]] Hnode Hzero.
  destruct Hactive as [_ [_ [_ [Hcover Hlinks]]]].
  assert (Hin : In tid tasks.(taskLifecycle).(taskActiveOrder)).
  { apply (proj2 (Hcover tid)); exists node; exact Hnode. }
  destruct (proj1 (task_active_links_neighbors _ _ None tid node Hlinks Hin Hnode))
    as [Hnone | [previous [Hprevious Hin_previous]]]; [exact Hnone|].
  assert (Hslot : task_slot_in_range sg previous).
  { apply (proj2 (Hpool previous)); left.
    exact (proj1 (Hcover previous) Hin_previous). }
  destruct Hprofile as [Hstable [_ [_ [_ [Hconfig _]]]]].
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable
    ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
  rewrite Hprevious in Hzero; cbn [encode_task_link] in Hzero.
  rewrite task_slot_addr_object_size, (task_object_size_tcb64 _ Hconfig) in Hzero.
  unfold task_slot_in_range in Hslot; lia.
Qed.
Lemma task_active_count_positive__byte_and_cut_observations :
  forall tasks tid node,
  task_active_closure tasks -> tasks.(inUsedTaskStates) tid = Some node ->
  0 < tasks.(taskCount).
Proof.
  intros tasks tid node [_ [_ [Hcount [Hcover _]]]] Hnode.
  assert (Hin : In tid tasks.(taskLifecycle).(taskActiveOrder)).
  { apply (proj2 (Hcover tid)); exists node; exact Hnode. }
  rewrite Hcount.
  destruct tasks.(taskLifecycle).(taskActiveOrder) as [|head rest];
    [contradiction|simpl; lia].
Qed.
