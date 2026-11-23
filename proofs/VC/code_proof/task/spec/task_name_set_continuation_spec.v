(** Source-aware continuation interface for the unchanged OSTaskNameSet body.
    The legacy flat-interval interface remains separate. All histories below
    are the existing source histories, and every spatial output uses their
    actual returned context and state. No platform field or law is added. *)
Require Export Ucos2Verify.VC.code.task.spec.task_name_set_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.timer_execution.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List Coq.micromega.Lia.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition task_name_set_continuation_call_binding environment call platform invocation origin : Prop :=
  platform = environment.(task_stack_call_platform) /\
  invocation = call.(os_sched_call_invocation) /\ origin = call.(os_sched_call_origin).

Definition task_name_set_continuation_closed environment critical saved_local sg call mask state : Assertion :=
  task_create_continuation_input environment critical saved_local sg call mask state ** unmap_table_rep sg.

Definition task_name_set_continuation_resources environment saved_local sg call state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (os_sched_context_resources environment.(task_stack_call_external) call **
   task_tcb_init_continuation_capsules environment saved_local state ** unmap_table_rep sg).

Definition task_name_set_continuation_masked environment critical saved_local sg call saved acquired state : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
  UCOS2_inv sg state ** task_name_set_continuation_resources environment saved_local sg call state.

Definition task_name_set_continuation_save_post environment critical saved_local sg call mask saved before : Assertion :=
  os_sched_continuation_save_history_output environment critical saved_local sg call mask saved before **
  unmap_table_rep sg.

Definition task_name_set_continuation_restore_post environment critical saved_local sg call saved released : Assertion :=
  os_sched_continuation_restore_history_output environment critical saved_local sg call saved released **
  unmap_table_rep sg.

(** This specialization is entered with the actual registered name owner.
    The premise is conditional on reaching Save: early argument/ISR errors
    need no name bytes and SELF needs a live caller only on its real read.
    Boot's explicit priorities do not require a fictitious current task. *)
Definition task_name_set_continuation_admission (sg : StableGlobVars) call (request name : Z) before : Prop :=
  task_name_set_valid_priority request -> name <> 0 -> task_name_set_nesting before = 0 ->
  (request = 255 -> kernel_call_task_source call before) /\
  exists chars, readable_name before.(NameState) name chars.

Definition task_name_set_continuation_program environment critical sg original mask request name
  : program UCOS2_Verify_State Z :=
  if andb (Z.ltb 63 request) (negb (Z.eqb request 255)) then StateRelMonad.ret 42
  else if Z.eqb name 0 then StateRelMonad.ret 12
  else StateRelMonad.bind (get' task_name_set_nesting)
    (fun nesting => if Z.ltb 0 nesting then StateRelMonad.ret 18
      else StateRelMonad.bind (os_sched_continuation_save_program environment critical sg original mask)
        (fun entered => StateRelMonad.bind (task_name_set_protected_program request name)
          (fun error => StateRelMonad.bind
            (os_sched_continuation_restore_program environment critical sg (fst entered))
            (fun _ => StateRelMonad.ret error)))).

Definition task_name_set_continuation_safe environment critical sg call mask request name before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (task_name_set_continuation_program environment critical sg call mask request name) X.

Definition task_name_set_continuation_result environment critical sg original mask request name
  before returned error current : Prop :=
  (64 <= request < 255 /\ error = 42 /\ current = before /\ returned = original) \/
  (task_name_set_valid_priority request /\ name = 0 /\ error = 12 /\ current = before /\ returned = original) \/
  (task_name_set_valid_priority request /\ name <> 0 /\ 0 < task_name_set_nesting before /\
    error = 18 /\ current = before /\ returned = original) \/
  (task_name_set_valid_priority request /\ name <> 0 /\ task_name_set_nesting before = 0 /\
   exists saved active acquired priority released,
     os_sched_continuation_save_effect environment critical sg original mask saved before active acquired /\
     task_name_set_resolved request acquired priority /\
     task_name_set_step priority name acquired error released /\
     os_sched_continuation_restore_effect environment critical sg active released returned current).

Definition task_name_set_continuation_post environment critical sg original mask request name
  before returned error current (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  task_name_set_continuation_result environment critical sg original mask request name before returned error current /\
  safeExec (eq current) (StateRelMonad.ret error) X.

Definition task_name_set_continuation_context environment critical sg original mask request name saved
  before active acquired : Prop :=
  task_name_set_valid_priority request /\ name <> 0 /\ task_name_set_nesting before = 0 /\
  (request = 255 -> exists tid task, task_name_set_current acquired tid task) /\
  (exists chars, readable_name acquired.(NameState) name chars) /\
  os_sched_continuation_save_effect environment critical sg original mask saved before active acquired /\
  task_tcb_init_stack_same_call active original /\ interrupt_saved_value mask saved /\
  UCOS2_state_inv sg acquired.

Lemma task_name_set_continuation_source_phase :
  forall external port clients sg observer event_observer first before stopped last after,
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    first before stopped last after ->
  before.(TimerState).(timerInitPhase) = after.(TimerState).(timerInitPhase).
Proof.
  intros * Htrace.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace) as [Hresource _].
  pose proof (kernel_resumption_resource_trace_timer_projection _ _ _ _ _ _ _ Hresource) as Htimer.
  symmetry; exact (proj1 (timer_public_trace_public_storage_frame _ _ _ Htimer)).
Qed.

Lemma task_name_set_continuation_save_history_phase :
  forall environment critical sg original before returned acquired,
  kernel_call_save_history environment critical sg original before returned acquired ->
  before.(TimerState).(timerInitPhase) = acquired.(TimerState).(timerInitPhase).
Proof.
  intros * Hhistory; destruct Hhistory; try reflexivity;
    match goal with
    | Htrace : kernel_resumption_task_source_trace _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        pose proof (task_name_set_continuation_source_phase _ _ _ _ _ _ _ _ _ _ _ Htrace) as Hphase
    end;
    match type of Hphase with
    | timerInitPhase (TimerState (armv7a_irq_live_parked_state ?initial ?call ?sp ?fragments)) = _ =>
      assert (Hframe : TimerState (armv7a_irq_live_parked_state initial call sp fragments) = TimerState initial)
        by (unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, os_sched_save_current_sp;
            change (TimerState (armv7a_irq_entry_counter_state initial) = TimerState initial);
            unfold armv7a_irq_entry_counter_state;
            destruct (isRunning (SchedState initial)); reflexivity);
      rewrite Hframe in Hphase; exact Hphase
    end.
Qed.

Lemma task_name_set_continuation_restore_history_phase :
  forall environment critical sg original before returned current,
  kernel_call_restore_history environment critical sg original before returned current ->
  before.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase).
Proof.
  intros * Hhistory; destruct Hhistory; try reflexivity;
    match goal with
    | Htrace : kernel_resumption_task_source_trace _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        pose proof (task_name_set_continuation_source_phase _ _ _ _ _ _ _ _ _ _ _ Htrace) as Hphase
    end;
    match type of Hphase with
    | timerInitPhase (TimerState (armv7a_irq_live_parked_state ?initial ?call ?sp ?fragments)) = _ =>
      assert (Hframe : TimerState (armv7a_irq_live_parked_state initial call sp fragments) = TimerState initial)
        by (unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, os_sched_save_current_sp;
            change (TimerState (armv7a_irq_entry_counter_state initial) = TimerState initial);
            unfold armv7a_irq_entry_counter_state;
            destruct (isRunning (SchedState initial)); reflexivity);
      rewrite Hframe in Hphase; exact Hphase
    end.
Qed.

Lemma task_name_set_continuation_save_effect_phase :
  forall environment critical sg original mask saved before returned acquired,
  os_sched_continuation_save_effect environment critical sg original mask saved before returned acquired ->
  before.(TimerState).(timerInitPhase) = acquired.(TimerState).(timerInitPhase).
Proof.
  intros * [[Htrace _]|[Hhistory _]].
  - eapply task_name_set_continuation_source_phase; exact Htrace.
  - eapply task_name_set_continuation_save_history_phase; exact Hhistory.
Qed.

Lemma task_name_set_continuation_restore_effect_phase :
  forall environment critical sg original released returned current,
  os_sched_continuation_restore_effect environment critical sg original released returned current ->
  released.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase).
Proof.
  intros * [[Htrace _]|Hhistory].
  - eapply task_name_set_continuation_source_phase; exact Htrace.
  - eapply task_name_set_continuation_restore_history_phase; exact Hhistory.
Qed.

Lemma task_name_set_continuation_result_phase :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_result environment critical sg original mask request name before returned error current ->
  before.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase).
Proof.
  intros * Hresult; unfold task_name_set_continuation_result in Hresult.
  destruct Hresult as [Hbad|[Hnull|[Hisr|Hresult]]].
  - destruct Hbad as (_ & _ & -> & _); reflexivity.
  - destruct Hnull as (_ & _ & _ & -> & _); reflexivity.
  - destruct Hisr as (_ & _ & _ & _ & -> & _); reflexivity.
  - destruct Hresult as (_ & _ & _ & saved & active & acquired & priority & released & Hsave & _ & Hstep & Hrestore).
  pose proof (task_name_set_continuation_save_effect_phase _ _ _ _ _ _ _ _ _ Hsave) as Hfirst.
  pose proof (task_name_set_continuation_restore_effect_phase _ _ _ _ _ _ _ Hrestore) as Hlast.
  inversion Hstep; subst;
    unfold task_name_set_update in Hlast; cbn [TimerState replace_TskS] in Hlast;
    (etransitivity; [exact Hfirst|exact Hlast]).
Qed.

Lemma task_name_set_continuation_same_call_refl : forall call,
  task_tcb_init_stack_same_call call call.
Proof. intros; repeat split; reflexivity. Qed.

Lemma task_name_set_continuation_result_same_call :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_result environment critical sg original mask request name before returned error current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros * Hresult; unfold task_name_set_continuation_result in Hresult.
  destruct Hresult as [Hbad|[Hnull|[Hisr|Hresult]]].
  - destruct Hbad as (_ & _ & _ & ->); apply task_name_set_continuation_same_call_refl.
  - destruct Hnull as (_ & _ & _ & _ & ->); apply task_name_set_continuation_same_call_refl.
  - destruct Hisr as (_ & _ & _ & _ & _ & ->); apply task_name_set_continuation_same_call_refl.
  - destruct Hresult as (_ & _ & _ & saved & active & acquired & priority & released & Hsave & _ & _ & Hrestore).
  pose proof (os_sched_continuation_save_effect_same_call _ _ _ _ _ _ _ _ _ Hsave) as Hfirst.
  pose proof (os_sched_continuation_restore_effect_same_call _ _ _ _ _ _ _ Hrestore) as Hlast.
  unfold task_tcb_init_stack_same_call in *; intuition congruence.
Qed.

Lemma task_name_set_continuation_valid_guard : forall request,
  task_name_set_valid_priority request ->
  andb (Z.ltb 63 request) (negb (Z.eqb request 255)) = false.
Proof.
  intros request [Hrange | ->]; [|reflexivity].
  assert (H : Z.ltb 63 request = false) by (apply Z.ltb_ge; lia).
  rewrite H; reflexivity.
Qed.

Lemma task_name_set_continuation_result_program :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_result environment critical sg original mask request name before returned error current ->
  task_name_set_continuation_program environment critical sg original mask request name before error current.
Proof.
  intros * Hresult; unfold task_name_set_continuation_result in Hresult.
  destruct Hresult as [Hbad|[Hnull|[Hisr|Hresult]]].
  - destruct Hbad as (Hrange & -> & -> & _).
    unfold task_name_set_continuation_program.
    assert (Hbound : Z.ltb 63 request = true) by (apply Z.ltb_lt; lia).
    assert (Hself : Z.eqb request 255 = false) by (apply Z.eqb_neq; lia).
    rewrite Hbound, Hself; split; reflexivity.
  - destruct Hnull as (Hpriority & -> & -> & -> & _).
    unfold task_name_set_continuation_program.
    rewrite (task_name_set_continuation_valid_guard request Hpriority); split; reflexivity.
  - destruct Hisr as (Hpriority & Hname & Hnest & -> & -> & _).
    unfold task_name_set_continuation_program.
    rewrite (task_name_set_continuation_valid_guard request Hpriority),
      (proj2 (Z.eqb_neq _ _) Hname).
    exists (task_name_set_nesting before), before; split; [split; reflexivity|].
    rewrite (proj2 (Z.ltb_lt _ _) Hnest); split; reflexivity.
  - destruct Hresult as (Hpriority & Hname & Hnest & saved & active & acquired & priority & released & Hsave & Hresolved & Hstep & Hrestore).
    unfold task_name_set_continuation_program.
    rewrite (task_name_set_continuation_valid_guard request Hpriority),
      (proj2 (Z.eqb_neq _ _) Hname).
    exists (task_name_set_nesting before), before; split; [split; reflexivity|].
    rewrite Hnest; cbn.
    exists (active, saved), acquired; split; [exact Hsave|].
    exists error, released; split.
    + exists priority, acquired; split; [split; [exact Hresolved|reflexivity]|exact Hstep].
    + exists returned, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma task_name_set_continuation_safe_return :
  forall environment critical sg original mask request name before returned error current X,
  task_name_set_continuation_result environment critical sg original mask request name before returned error current ->
  task_name_set_continuation_safe environment critical sg original mask request name before X ->
  task_name_set_continuation_post environment critical sg original mask request name before returned error current X.
Proof.
  intros * Hresult Hsafe; split; [exact Hresult|].
  eapply (highstependret_derive
    (task_name_set_continuation_program environment critical sg original mask request name)
    (eq before) error (fun _ => eq current)).
  - intros state ->; exists current; split; [|reflexivity].
    eapply task_name_set_continuation_result_program; exact Hresult.
  - exact Hsafe.
Qed.

Lemma task_name_set_continuation_admission_explicit : forall sg call request name before chars,
  request <> 255 -> readable_name before.(NameState) name chars ->
  task_name_set_continuation_admission sg call request name before.
Proof. intros * Hrequest Hread _ _ _; split; [congruence|eauto]. Qed.

Lemma task_name_set_continuation_admission_early : forall sg call request name before,
  (64 <= request < 255 \/ name = 0 \/ task_name_set_nesting before <> 0) ->
  task_name_set_continuation_admission sg call request name before.
Proof.
  unfold task_name_set_continuation_admission, task_name_set_valid_priority;
    intros; intuition lia.
Qed.

Lemma task_name_set_continuation_closed_split : forall environment critical saved_local sg call mask state,
  task_name_set_continuation_closed environment critical saved_local sg call mask state --||--
  coq_prop (UCOS2_state_inv sg state) &&
  (task_name_set_closed environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) mask state **
   task_name_set_continuation_resources environment saved_local sg call state).
Proof.
  intros; unfold task_name_set_continuation_closed, task_create_continuation_input,
    task_name_set_closed, task_name_set_continuation_resources, kernel_call_execution_owned,
    task_tcb_init_continuation_capsules; split; entailer!.
Qed.

Lemma task_name_set_continuation_masked_restore_input :
  forall environment critical saved_local sg call saved acquired released,
  task_name_set_continuation_masked environment critical saved_local sg call saved acquired released --||--
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired released **
    unmap_table_rep sg.
Proof.
  intros; unfold task_name_set_continuation_masked, task_name_set_continuation_resources,
    task_tcb_init_continuation_restore_input; split; entailer!.
Qed.

Lemma task_name_set_continuation_save_open :
  forall environment critical saved_local sg original mask saved before request name,
  UCOS2_state_inv sg before -> task_name_set_continuation_admission sg original request name before ->
  task_name_set_valid_priority request -> name <> 0 -> task_name_set_nesting before = 0 ->
  task_name_set_continuation_save_post environment critical saved_local sg original mask saved before |--
  EX active acquired,
    coq_prop (task_name_set_continuation_context environment critical sg original mask request name saved
      before active acquired) &&
    task_name_set_continuation_masked environment critical saved_local sg active saved acquired acquired.
Proof.
  intros * Hvalid Hadmit Hpriority Hname Hnest.
  unfold task_name_set_continuation_save_post, os_sched_continuation_save_history_output.
  Intros active acquired.
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired) by tauto.
  destruct (Hhistory Hvalid) as [Hacquired [_ [_ Hnames]]].
  destruct (Hadmit Hpriority Hname Hnest) as [Hself [chars Hread]].
  assert (Hcurrent : request = 255 -> exists tid task, task_name_set_current acquired tid task).
  { intro Hrequest.
    assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired) by tauto.
    pose proof (kernel_call_task_source_current_at original acquired (Hpreserved (Hself Hrequest)))
      as [Hselected [node [Hnode Hgeneration]]].
    exists original.(os_sched_call_stack).(stackLeaseSlot), node; split; assumption. }
  assert (Hreadable : exists chars, readable_name acquired.(NameState) name chars).
  { exists chars; rewrite <- Hnames; exact Hread. }
  Exists active acquired.
  unfold task_name_set_continuation_context, task_name_set_continuation_masked,
    task_name_set_continuation_resources, task_tcb_init_stack_context.
  entailer!; tauto.
Qed.

Lemma task_name_set_continuation_update_live_nodes : forall state tid old name slot node,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  (task_name_set_update state tid old name).(TskState).(inUsedTaskStates) slot = Some node ->
  exists previous, state.(TskState).(inUsedTaskStates) slot = Some previous /\
    previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr).
Proof.
  intros state tid old name slot node Hold Hnode.
  change ((if Z.eqb slot tid then Some (task_set_name old name)
    else state.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
  destruct (Z.eqb slot tid) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot; injection Hnode as Hnode; subst node.
    exists old; repeat split; assumption || reflexivity.
  - exists node; repeat split; assumption || reflexivity.
Qed.

Lemma task_name_set_continuation_update_resources :
  forall environment saved_local sg call state tid old name,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  task_name_set_continuation_resources environment saved_local sg call state |--
  task_name_set_continuation_resources environment saved_local sg call (task_name_set_update state tid old name).
Proof.
  intros * Hold; unfold task_name_set_continuation_resources; Intros.
  assert (Hcoverage : task_stack_live_coverage (task_name_set_update state tid old name).(TskState)
    (task_stack_call_active_key call)).
  { eapply task_stack_live_coverage_used_map_frame with (before := state.(TskState)); [|reflexivity|eassumption].
    intros slot node Hnode.
    destruct (task_name_set_continuation_update_live_nodes _ _ _ _ _ _ Hold Hnode)
      as [previous [Hprevious [Hgeneration Hsp]]].
    exists previous; split; [exact Hprevious|symmetry; exact Hgeneration]. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local state |--
    task_tcb_init_continuation_capsules environment saved_local (task_name_set_update state tid old name)).
  { unfold task_tcb_init_continuation_capsules.
    change (store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState)
        (task_create_continuation_local saved_local)) state.(TskState).(parkedTaskStacks) |--
      store_parked_continuations
      (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
        (task_name_set_update state tid old name).(TskState) (task_create_continuation_local saved_local))
        state.(TskState).(parkedTaskStacks)).
    apply kernel_saved_continuation_map_reindex.
    intros key payload node Hlookup Hnode Hgen.
    eapply task_name_set_continuation_update_live_nodes; eassumption. }
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.

Lemma task_name_set_continuation_restore_open :
  forall environment critical saved_local sg call saved released,
  task_name_set_continuation_restore_post environment critical saved_local sg call saved released |--
  EX returned current,
    coq_prop (os_sched_continuation_restore_effect environment critical sg call released returned current /\
      task_tcb_init_stack_same_call returned call /\
      task_tcb_init_call_preserved sg call.(os_sched_call_invocation) released current) &&
    task_name_set_continuation_closed environment critical saved_local sg returned
      (armv7a_irq_fiq_mask saved) current.
Proof.
  intros; unfold task_name_set_continuation_restore_post, os_sched_continuation_restore_history_output.
  Intros returned current; Exists returned current.
  unfold task_name_set_continuation_closed, task_tcb_init_continuation_save_input; entailer!; tauto.
Qed.

Lemma task_name_set_continuation_context_result :
  forall environment critical sg original mask request name saved before active acquired priority
    error released returned current,
  task_name_set_continuation_context environment critical sg original mask request name saved before active acquired ->
  task_name_set_resolved request acquired priority -> task_name_set_step priority name acquired error released ->
  os_sched_continuation_restore_effect environment critical sg active released returned current ->
  task_name_set_continuation_result environment critical sg original mask request name before returned error current.
Proof.
  intros * Hcontext Hresolved Hstep Hrestore.
  destruct Hcontext as [Hpriority [Hname [Hnest [_ [_ [Hsave _]]]]]].
  right; right; right; split; [exact Hpriority|]. split; [exact Hname|]. split; [exact Hnest|].
  exists saved, active, acquired, priority, released; tauto.
Qed.

(** The strong interface projects to the current NameSet closed view plus
    its current continuation resources. It does not assert that segmented
    source histories are a legacy flat task_name_set_result. *)
Lemma task_name_set_continuation_closed_current_view :
  forall environment critical saved_local sg call mask state,
  task_name_set_continuation_closed environment critical saved_local sg call mask state |--
  task_name_set_closed environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) mask state **
  task_name_set_continuation_resources environment saved_local sg call state.
Proof. intros; rewrite task_name_set_continuation_closed_split; entailer!. Qed.


(** A context-result view for callers that execute another source call.
    Each local relation retains an observation already produced by the
    actual Save/Restore contract. The error-only view above stays intact. *)
Definition task_name_set_continuation_save_call_program environment critical sg original mask
  : program UCOS2_Verify_State (OsSchedCallContext * Z) :=
  fun before result acquired =>
    os_sched_continuation_save_effect environment critical sg original mask (snd result)
      before (fst result) acquired /\
    task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired /\
    (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired).

Definition task_name_set_continuation_restore_call_effect environment critical sg original
  released returned current : Prop :=
  os_sched_continuation_restore_effect environment critical sg original released returned current /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
  (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current).

Definition task_name_set_continuation_restore_call_program environment critical sg original
  : program UCOS2_Verify_State OsSchedCallContext :=
  fun released returned current =>
    task_name_set_continuation_restore_call_effect environment critical sg original released returned current.

Definition task_name_set_continuation_protected_call_program sg call request name
  : program UCOS2_Verify_State Z :=
  fun acquired error released =>
    task_name_set_protected_program request name acquired error released /\
    task_tcb_init_call_preserved sg call.(os_sched_call_invocation) acquired released.

Definition task_name_set_continuation_call_program environment critical sg original mask request name
  : program UCOS2_Verify_State (OsSchedCallContext * Z) :=
  if andb (Z.ltb 63 request) (negb (Z.eqb request 255)) then StateRelMonad.ret (original, 42)
  else if Z.eqb name 0 then StateRelMonad.ret (original, 12)
  else StateRelMonad.bind (get' task_name_set_nesting)
    (fun nesting => if Z.ltb 0 nesting then StateRelMonad.ret (original, 18)
      else StateRelMonad.bind (task_name_set_continuation_save_call_program environment critical sg original mask)
        (fun entered => StateRelMonad.bind (task_name_set_continuation_protected_call_program sg (fst entered) request name)
          (fun error => StateRelMonad.bind
            (task_name_set_continuation_restore_call_program environment critical sg (fst entered))
            (fun returned => StateRelMonad.ret (returned, error))))).

Definition task_name_set_continuation_call_safe environment critical sg call mask request name before
  (X : OsSchedCallContext -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (task_name_set_continuation_call_program environment critical sg call mask request name)
    (fun result current => X (fst result) (snd result) current).

Definition task_name_set_continuation_call_result environment critical sg original mask request name
  before returned error current : Prop :=
  (64 <= request < 255 /\ error = 42 /\ current = before /\ returned = original) \/
  (task_name_set_valid_priority request /\ name = 0 /\ error = 12 /\ current = before /\ returned = original) \/
  (task_name_set_valid_priority request /\ name <> 0 /\ 0 < task_name_set_nesting before /\
    error = 18 /\ current = before /\ returned = original) \/
  (task_name_set_valid_priority request /\ name <> 0 /\ task_name_set_nesting before = 0 /\
   exists saved active acquired priority released,
     task_name_set_continuation_save_call_program environment critical sg original mask before (active, saved) acquired /\
     task_name_set_resolved request acquired priority /\
     task_name_set_step priority name acquired error released /\
     task_tcb_init_call_preserved sg active.(os_sched_call_invocation) acquired released /\
     task_name_set_continuation_restore_call_effect environment critical sg active released returned current).

Definition task_name_set_continuation_call_post environment critical sg original mask request name
  before returned error current (X : OsSchedCallContext -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  task_name_set_continuation_call_result environment critical sg original mask request name before returned error current /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before current /\
  safeExec (eq current) (StateRelMonad.ret (returned, error))
    (fun result final => X (fst result) (snd result) final).

Definition task_name_set_continuation_call_context environment critical sg original mask request name saved
  before active acquired : Prop :=
  task_name_set_continuation_context environment critical sg original mask request name saved before active acquired /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired /\
  (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired).

Lemma task_name_set_continuation_update_preserves_call :
  forall sg invocation state tid old name chars,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  readable_name state.(NameState) name chars ->
  task_tcb_init_call_preserved sg invocation state (task_name_set_update state tid old name).
Proof.
  intros * Hold Hread Hvalid; split.
  - eapply task_name_set_preserves_invariant; eassumption.
  - split; [reflexivity|]. split; [|reflexivity].
    intros origin Hactive; unfold task_name_set_update; cbn [replace_TskS].
    eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hold|reflexivity|exact Hactive].
Qed.

Lemma task_name_set_continuation_step_preserves_call :
  forall sg invocation request name acquired error released chars,
  task_name_set_step request name acquired error released ->
  readable_name acquired.(NameState) name chars ->
  task_tcb_init_call_preserved sg invocation acquired released.
Proof.
  intros * Hstep Hread; inversion Hstep; subst.
  - apply task_tcb_init_call_preserved_refl.
  - apply task_tcb_init_call_preserved_refl.
  - eapply task_name_set_continuation_update_preserves_call;
      [unfold task_name_set_target in *; tauto|exact Hread].
Qed.

Lemma task_name_set_continuation_call_result_forget :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_call_result environment critical sg original mask request name before returned error current ->
  task_name_set_continuation_result environment critical sg original mask request name before returned error current.
Proof.
  intros * Hresult; unfold task_name_set_continuation_call_result in Hresult.
  unfold task_name_set_continuation_result.
  destruct Hresult as [Hbad|[Hnull|[Hisr|Hresult]]]; [tauto|tauto|tauto|].
  destruct Hresult as (Hpriority & Hname & Hnest & saved & active & acquired & priority & released & Hsave & Hresolved & Hstep & Hpreserved & Hrestore).
  right; right; right; split; [exact Hpriority|]. split; [exact Hname|]. split; [exact Hnest|].
  exists saved, active, acquired, priority, released.
  unfold task_name_set_continuation_save_call_program in Hsave.
  unfold task_name_set_continuation_restore_call_effect in Hrestore; cbn in Hsave; tauto.
Qed.

Lemma task_name_set_continuation_call_result_same_call :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_call_result environment critical sg original mask request name before returned error current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros * Hresult; eapply task_name_set_continuation_result_same_call.
  eapply task_name_set_continuation_call_result_forget; exact Hresult.
Qed.

Lemma task_name_set_continuation_call_result_phase :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_call_result environment critical sg original mask request name before returned error current ->
  before.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase).
Proof.
  intros * Hresult; eapply task_name_set_continuation_result_phase.
  eapply task_name_set_continuation_call_result_forget; exact Hresult.
Qed.

Lemma task_name_set_continuation_call_result_preserves_call :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_call_result environment critical sg original mask request name before returned error current ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before current.
Proof.
  intros * Hresult; unfold task_name_set_continuation_call_result in Hresult.
  destruct Hresult as [Hbad|[Hnull|[Hisr|Hresult]]].
  - destruct Hbad as (_ & _ & -> & _); apply task_tcb_init_call_preserved_refl.
  - destruct Hnull as (_ & _ & _ & -> & _); apply task_tcb_init_call_preserved_refl.
  - destruct Hisr as (_ & _ & _ & _ & -> & _); apply task_tcb_init_call_preserved_refl.
  - destruct Hresult as (_ & _ & _ & saved & active & acquired & priority & released & Hsave & _ & _ & Hstep & Hrestore).
    destruct Hsave as [Heffect [Hfirst Hsource]].
    destruct Hrestore as [_ [Hlast _]].
    pose proof (os_sched_continuation_save_effect_same_call _ _ _ _ _ _ _ _ _ Heffect) as [Hinv _].
    cbn in Hinv.
    rewrite Hinv in Hstep, Hlast.
    eapply task_tcb_init_call_preserved_trans; [exact Hfirst|].
    eapply task_tcb_init_call_preserved_trans; eassumption.
Qed.

Lemma task_name_set_continuation_call_result_program :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_call_result environment critical sg original mask request name before returned error current ->
  task_name_set_continuation_call_program environment critical sg original mask request name before (returned, error) current.
Proof.
  intros * Hresult; unfold task_name_set_continuation_call_result in Hresult.
  destruct Hresult as [Hbad|[Hnull|[Hisr|Hresult]]].
  - destruct Hbad as (Hrange & -> & -> & ->).
    unfold task_name_set_continuation_call_program.
    assert (Hbound : Z.ltb 63 request = true) by (apply Z.ltb_lt; lia).
    assert (Hself : Z.eqb request 255 = false) by (apply Z.eqb_neq; lia).
    rewrite Hbound, Hself; split; reflexivity.
  - destruct Hnull as (Hpriority & -> & -> & -> & ->).
    unfold task_name_set_continuation_call_program.
    rewrite (task_name_set_continuation_valid_guard request Hpriority); split; reflexivity.
  - destruct Hisr as (Hpriority & Hname & Hnest & -> & -> & ->).
    unfold task_name_set_continuation_call_program.
    rewrite (task_name_set_continuation_valid_guard request Hpriority), (proj2 (Z.eqb_neq _ _) Hname).
    exists (task_name_set_nesting before), before; split; [split; reflexivity|].
    rewrite (proj2 (Z.ltb_lt _ _) Hnest); split; reflexivity.
  - destruct Hresult as (Hpriority & Hname & Hnest & saved & active & acquired & priority & released & Hsave & Hresolved & Hstep & Hpreserved & Hrestore).
    unfold task_name_set_continuation_call_program.
    rewrite (task_name_set_continuation_valid_guard request Hpriority), (proj2 (Z.eqb_neq _ _) Hname).
    exists (task_name_set_nesting before), before; split; [split; reflexivity|].
    rewrite Hnest; cbn.
    exists (active, saved), acquired; split; [exact Hsave|].
    exists error, released; split.
    + split; [|exact Hpreserved].
      exists priority, acquired; split; [split; [exact Hresolved|reflexivity]|exact Hstep].
    + exists returned, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma task_name_set_continuation_call_safe_return :
  forall environment critical sg original mask request name before returned error current X,
  task_name_set_continuation_call_result environment critical sg original mask request name before returned error current ->
  task_name_set_continuation_call_safe environment critical sg original mask request name before X ->
  task_name_set_continuation_call_post environment critical sg original mask request name before returned error current X.
Proof.
  intros * Hresult Hsafe; split; [exact Hresult|]. split.
  - eapply task_name_set_continuation_call_result_preserves_call; exact Hresult.
  - eapply (highstependret_derive
      (task_name_set_continuation_call_program environment critical sg original mask request name)
      (eq before) (returned, error) (fun _ => eq current)).
    + intros state ->; exists current; split; [|reflexivity].
      eapply task_name_set_continuation_call_result_program; exact Hresult.
    + exact Hsafe.
Qed.

Lemma task_name_set_continuation_call_program_error_projection :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_call_program environment critical sg original mask request name before (returned, error) current ->
  task_name_set_continuation_program environment critical sg original mask request name before error current.
Proof.
  intros * Hrun.
  unfold task_name_set_continuation_call_program, task_name_set_continuation_program in *.
  destruct (andb (Z.ltb 63 request) (negb (Z.eqb request 255))).
  - destruct Hrun as [Hresult Hstate]; inversion Hresult; subst; split; reflexivity.
  - destruct (Z.eqb name 0).
    + destruct Hrun as [Hresult Hstate]; inversion Hresult; subst; split; reflexivity.
    + destruct Hrun as [nesting [entry [[Hnest Hentry] Hrun]]]; subst nesting entry.
      exists (task_name_set_nesting before), before; split; [split; reflexivity|].
      destruct (Z.ltb 0 (task_name_set_nesting before)).
      * destruct Hrun as [Hresult Hstate]; inversion Hresult; subst; split; reflexivity.
      * destruct Hrun as [entered [acquired [Hsave [code [released [Hstep [last [final [Hrestore Hret]]]]]]]]].
        destruct Hret as [Hresult Hstate]; inversion Hresult; subst.
        exists entered, acquired; split; [exact (proj1 Hsave)|].
        exists code, released; split; [exact (proj1 Hstep)|].
        exists last, current; split; [exact (proj1 Hrestore)|split; reflexivity].
Qed.

Lemma task_name_set_continuation_error_safe_implies_call_safe :
  forall environment critical sg original mask request name before X,
  task_name_set_continuation_safe environment critical sg original mask request name before X ->
  task_name_set_continuation_call_safe environment critical sg original mask request name before
    (fun _ error current => X error current).
Proof.
  intros * [start [Hstart Hsafe]]; subst start.
  exists before; split; [reflexivity|].
  intros [returned error] current Hrun; cbn; apply Hsafe.
  eapply task_name_set_continuation_call_program_error_projection; exact Hrun.
Qed.

Lemma task_name_set_continuation_call_post_forget :
  forall environment critical sg original mask request name before returned error current X,
  task_name_set_continuation_call_post environment critical sg original mask request name before returned error current
    (fun _ code final => X code final) ->
  task_name_set_continuation_post environment critical sg original mask request name before returned error current X.
Proof.
  intros * [Hresult [_ [start [Hstart Hsafe]]]]; subst start.
  split; [eapply task_name_set_continuation_call_result_forget; exact Hresult|].
  exists current; split; [reflexivity|].
  intros code final [Hcode Hfinal]; subst code final.
  exact (Hsafe (returned, error) current (conj eq_refl eq_refl)).
Qed.

Lemma task_name_set_continuation_save_call_open :
  forall environment critical saved_local sg original mask saved before request name,
  UCOS2_state_inv sg before -> task_name_set_continuation_admission sg original request name before ->
  task_name_set_valid_priority request -> name <> 0 -> task_name_set_nesting before = 0 ->
  task_name_set_continuation_save_post environment critical saved_local sg original mask saved before |--
  EX active acquired,
    coq_prop (task_name_set_continuation_call_context environment critical sg original mask request name saved
      before active acquired) &&
    task_name_set_continuation_masked environment critical saved_local sg active saved acquired acquired.
Proof.
  intros * Hvalid Hadmit Hpriority Hname Hnest.
  unfold task_name_set_continuation_save_post, os_sched_continuation_save_history_output.
  Intros active acquired.
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired) by tauto.
  destruct (Hhistory Hvalid) as [Hacquired [_ [_ Hnames]]].
  destruct (Hadmit Hpriority Hname Hnest) as [Hself [chars Hread]].
  assert (Hcurrent : request = 255 -> exists tid task, task_name_set_current acquired tid task).
  { intro Hrequest.
    assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired) by tauto.
    pose proof (kernel_call_task_source_current_at original acquired (Hpreserved (Hself Hrequest)))
      as [Hselected [node [Hnode Hgeneration]]].
    exists original.(os_sched_call_stack).(stackLeaseSlot), node; split; assumption. }
  assert (Hreadable : exists chars, readable_name acquired.(NameState) name chars).
  { exists chars; rewrite <- Hnames; exact Hread. }
  Exists active acquired.
  unfold task_name_set_continuation_call_context, task_name_set_continuation_context,
    task_name_set_continuation_masked, task_name_set_continuation_resources, task_tcb_init_stack_context.
  entailer!; tauto.
Qed.

Lemma task_name_set_continuation_restore_call_open :
  forall environment critical saved_local sg call saved released,
  task_name_set_continuation_restore_post environment critical saved_local sg call saved released |--
  EX returned current,
    coq_prop (task_name_set_continuation_restore_call_effect environment critical sg call released returned current /\
      task_tcb_init_stack_same_call returned call) &&
    task_name_set_continuation_closed environment critical saved_local sg returned
      (armv7a_irq_fiq_mask saved) current.
Proof.
  intros; unfold task_name_set_continuation_restore_post, os_sched_continuation_restore_history_output.
  Intros returned current; Exists returned current.
  unfold task_name_set_continuation_restore_call_effect, task_name_set_continuation_closed,
    task_tcb_init_continuation_save_input; entailer!; tauto.
Qed.

Lemma task_name_set_continuation_call_context_result :
  forall environment critical sg original mask request name saved before active acquired priority
    error released returned current,
  task_name_set_continuation_call_context environment critical sg original mask request name saved before active acquired ->
  task_name_set_resolved request acquired priority -> task_name_set_step priority name acquired error released ->
  task_name_set_continuation_restore_call_effect environment critical sg active released returned current ->
  task_name_set_continuation_call_result environment critical sg original mask request name before returned error current.
Proof.
  intros * [Hcontext [Hhistory Hsource]] Hresolved Hstep Hrestore.
  destruct Hcontext as (Hpriority & Hname & Hnest & Hself & Hread & Hsave & Hsame & Hsaved & Hvalid).
  right; right; right; split; [exact Hpriority|]. split; [exact Hname|]. split; [exact Hnest|].
  exists saved, active, acquired, priority, released.
  split; [unfold task_name_set_continuation_save_call_program; cbn; tauto|].
  split; [exact Hresolved|]. split; [exact Hstep|]. split; [|exact Hrestore].
  destruct Hread as [chars Hread].
  eapply task_name_set_continuation_step_preserves_call; eassumption.
Qed.


Lemma task_name_set_continuation_call_program_preserves_call :
  forall environment critical sg original mask request name before returned error current,
  task_name_set_continuation_call_program environment critical sg original mask request name before (returned, error) current ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before current.
Proof.
  intros * Hrun; unfold task_name_set_continuation_call_program in Hrun.
  destruct (andb (Z.ltb 63 request) (negb (Z.eqb request 255))).
  - destruct Hrun as [_ ->]; apply task_tcb_init_call_preserved_refl.
  - destruct (Z.eqb name 0).
    + destruct Hrun as [_ ->]; apply task_tcb_init_call_preserved_refl.
    + destruct Hrun as [nesting [entry [[Hnest Hentry] Hrun]]]; subst nesting entry.
      destruct (Z.ltb 0 (task_name_set_nesting before)).
      * destruct Hrun as [_ ->]; apply task_tcb_init_call_preserved_refl.
      * destruct Hrun as [entered [acquired [[Heffect [Hfirst Hsource]]
          [code [released [[Hprotected Hstep] [last [final [[Hrestore [Hlast Hlast_source]] [_ Hcurrent]]]]]]]]]].
        subst final.
        pose proof (os_sched_continuation_save_effect_same_call _ _ _ _ _ _ _ _ _ Heffect) as [Hinv _].
        rewrite Hinv in Hstep, Hlast.
        eapply task_tcb_init_call_preserved_trans; [exact Hfirst|].
        eapply task_tcb_init_call_preserved_trans; eassumption.
Qed.
