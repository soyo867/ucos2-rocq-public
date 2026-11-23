Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import ListNotations UCOS2_C_Rules.
Local Open Scope sac_scope.

(** Source/os_core.c:869--878 (V2.93.01). The source guard and bitmap/table
    selection remain total: even an empty ready set reads priority slot 0.
    None means the already-running branch, not a fabricated error return.
    This is the C observation before OSStartHighRdy, not a platform call
    contract and not a proof that the new task has started executing. *)
Definition kernel_start_selection (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : option SchedSelection :=
  if s.(SchedState).(isRunning) then None
  else Some (sched_selection sg s.(TskState) s.(SchedState)).

Lemma kernel_start_selection_already_running : forall sg s,
  s.(SchedState).(isRunning) = true -> kernel_start_selection sg s = None.
Proof. intros; unfold kernel_start_selection; rewrite H; reflexivity. Qed.

Lemma kernel_start_selection_empty : forall sg s,
  s.(SchedState).(isRunning) = false -> s.(SchedState).(readyList) = [] ->
  kernel_start_selection sg s = Some
    {| selectionPriority := 0%Z;
       selectionPointer := prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) 0%Z) |}.
Proof.
  intros sg s Hrunning Hempty; unfold kernel_start_selection, sched_selection.
  rewrite Hrunning, sched_empty_selected_priority, sched_empty_reads_slot_zero by assumption.
  reflexivity.
Qed.

(** Completed C assignments on the initialized, nonempty-ready protocol.
    The raw observation above is kept for inputs outside that protocol;
    no live TaskID is invented for a reserved or free priority-table cell. *)
Definition kernel_start_ready_state (s : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_SchedS (sched_install_selected (sched_refresh_high s.(TskState) s.(SchedState))) s.

Lemma kernel_start_ready_selection : forall sg s head tail node,
  UCOS2_state_inv sg s -> s.(SchedState).(isRunning) = false ->
  s.(SchedState).(readyList) = head :: tail ->
  s.(TskState).(inUsedTaskStates) head = Some node ->
  kernel_start_selection sg s = Some
    {| selectionPriority := node.(curPrio); selectionPointer := task_slot_addr sg head |} /\
  (kernel_start_ready_state s).(SchedState).(curTaskID) = Some head /\
  (kernel_start_ready_state s).(SchedState).(curSchedPrio) = Some node.(curPrio) /\
  (kernel_start_ready_state s).(SchedState).(isRunning) = false.
Proof.
  intros sg s head tail node Hvalid Hrunning Hlist Hnode.
  destruct Hvalid as [Hprofile [Htasks [Hsched Hrest]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hregistered : task_current_prio_registered s.(TskState))
    by (unfold task_in_range in Htasks; tauto).
  split.
  - unfold kernel_start_selection, sched_selection; rewrite Hrunning.
    rewrite (sched_selected_priority_eq_head sg _ _ head tail node Hsg (proj1 Hsched) Hlist Hnode).
    rewrite (sched_selected_pointer_eq_head sg _ _ head tail node Hsg (proj1 Hsched)
      Hregistered Hlist Hnode); reflexivity.
  - unfold kernel_start_ready_state, sched_install_selected, sched_refresh_high;
      simpl; rewrite Hlist, Hnode, Hrunning; repeat split; reflexivity.
Qed.

Lemma kernel_start_ready_preserves_validity : forall sg s,
  UCOS2_state_inv sg s -> UCOS2_state_inv sg (kernel_start_ready_state s).
Proof.
  intros sg s Hvalid; apply UCOS2_replace_sched_preserves_validity; [exact Hvalid| |reflexivity].
  apply sched_install_selected_preserves_in_range.
  - apply sched_refresh_high_preserves_in_range.
    + exact (proj1 (proj1 (proj2 Hvalid))).
    + exact (proj1 (proj2 (proj2 Hvalid))).
  - intros p Hp; eapply sched_refresh_high_priority_in_range;
      [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hp].
Qed.

(** The single OSRunning store required by OSStartHighRdy. Stack selection,
    hook execution and context loading remain in the architecture contract.
    This pure transformer supplies none of those resources or effects. *)
Definition sched_set_running (s : SchedAbstractState) (running : bool) : SchedAbstractState :=
  {| readyList := s.(readyList); curTaskID := s.(curTaskID);
     curSchedPrio := s.(curSchedPrio); highRdyTid := s.(highRdyTid);
     highRdyPrio := s.(highRdyPrio); ctxSwCtr := s.(ctxSwCtr); isRunning := running |}.

Definition kernel_running_store (s : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_SchedS (sched_set_running s.(SchedState) true) s.

Lemma kernel_running_store_preserves_validity : forall sg s,
  UCOS2_state_inv sg s -> task_idle_tail sg s.(TskState) ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s.(TimerState)) ->
  UCOS2_state_inv sg (kernel_running_store s).
Proof.
  intros sg s [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hrest]]]]]] Htail Htimer.
  split; [exact Hprofile|]. split; [exact Htasks|]. split; [exact Hsched|].
  split; [exact Hevents|]. split.
  - destruct Hcross as [Htable [Howners [Hwait [Hprotocol [Hunique [Hflags Hphase]]]]]].
    split; [exact Htable|]. split; [exact Howners|]. split; [exact Hwait|].
    split; [exact Hprotocol|]. split; [exact Hunique|]. split; [exact Hflags|].
    intros Henabled _; exact (Htimer Henabled).
  - split; [intro; exact Htail|exact Hrest].
Qed.

Lemma kernel_start_running_task_boundary : forall sg s,
  UCOS2_state_inv sg s -> s.(SchedState).(readyList) <> [] ->
  sched_task_call_boundary (kernel_running_store (kernel_start_ready_state s)).(TskState)
    (kernel_running_store (kernel_start_ready_state s)).(SchedState).
Proof.
  intros sg s Hvalid Hnonempty.
  change (sched_task_call_boundary s.(TskState)
    (sched_install_selected (sched_set_running
      (sched_refresh_high s.(TskState) s.(SchedState)) true))).
  apply (sched_install_selected_task_boundary sg).
  - exact (proj1 (proj1 (proj2 (proj2 Hvalid)))).
  - change (sched_high_ready_consistency s.(TskState)
      (sched_refresh_high s.(TskState) s.(SchedState))).
    apply (sched_refresh_high_establishes_consistency sg).
    exact (proj1 (proj1 (proj2 (proj2 Hvalid)))).
  - reflexivity.
  - exact Hnonempty.
Qed.

Lemma kernel_start_running_preserves_validity : forall sg s,
  UCOS2_state_inv sg s -> task_idle_tail sg s.(TskState) ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s.(TimerState)) ->
  UCOS2_state_inv sg (kernel_running_store (kernel_start_ready_state s)).
Proof.
  intros; apply kernel_running_store_preserves_validity;
    [apply kernel_start_ready_preserves_validity| |]; assumption.
Qed.

(** The caller supplies the actual newly written Scheduler heap. Other
    modules and all parked stacks are retained by the existing complement. *)
Lemma kernel_start_running_resources_merge : forall sg s,
  UCOS2_state_inv sg s -> task_idle_tail sg s.(TskState) ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s.(TimerState)) ->
  let post := kernel_running_store (kernel_start_ready_state s) in
  sched_raw_rep sg post.(TskState) post.(SchedState) **
    UCOS2_raw_rep_missing_sched sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s Hvalid Hidle Htimer post.
  apply (UCOS2_inv_merge_updated_module sg s post SchedModule).
  - apply kernel_start_running_preserves_validity; assumption.
  - reflexivity.
Qed.
