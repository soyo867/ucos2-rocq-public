Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Relations.Relation_Operators.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Facts about the actual input state of one call.  No ready relation,
    future step, waiter projection or Timer trace occurs in this packet. *)
Definition sem_pend_source_state_facts sg state : Prop :=
  selected_kernel_profile sg /\ task_in_range sg state.(TskState) /\
  event_in_range sg state.(TskState) state.(EventState) /\
  cross_module_consistency sg state.

Lemma sem_pend_source_state_facts_from_ready : forall sg state ready,
  UCOS2_state_inv_with_ready sg state ready -> sem_pend_source_state_facts sg state.
Proof.
  intros sg state ready [Hprofile [Htasks [_ [Hevents [Hcross _]]]]].
  exact (conj Hprofile (conj Htasks (conj Hevents Hcross))).
Qed.

Lemma sem_pend_source_state_facts_from_valid : forall sg state,
  UCOS2_state_inv sg state -> sem_pend_source_state_facts sg state.
Proof. intros; eapply sem_pend_source_state_facts_from_ready; exact H. Qed.

Lemma sem_pend_source_state_facts_from_delete_phase : forall phase sg state,
  task_delete_phase_valid phase sg state -> sem_pend_source_state_facts sg state.
Proof.
  intros phase sg state Hphase; destruct phase; cbn [task_delete_phase_valid] in Hphase.
  - apply sem_pend_source_state_facts_from_valid; exact Hphase.
  - apply sem_pend_source_state_facts_from_valid; exact (proj1 Hphase).
  - eapply sem_pend_source_state_facts_from_ready; exact Hphase.
Qed.

Lemma sem_pend_delete_phase_resources_facts : forall phase loan sg state heap frame,
  (task_delete_phase_resources phase loan sg state ** frame) heap ->
  sem_pend_source_state_facts sg state.
Proof.
  intros phase loan sg state heap frame [owned [rest [Hjoin [[Hvalid Hbody] Hframe]]]].
  eapply sem_pend_source_state_facts_from_delete_phase; exact Hvalid.
Qed.

Lemma sem_pend_creation_call_projection : forall action sg before after tid old,
  task_in_range sg before.(TskState) ->
  kernel_client_step (task_creation_client action) sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros action sg before after tid old Htasks [Hguard [_ ->]] Hold.
  destruct action as [priority entry slot rest image|priority entry allocation image|
    priority invocation node|invocation].
  - eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - pose proof (task_commit_identity_private before.(TskState) priority invocation node
      (proj1 Hguard)) as Hprivate.
    pose proof (proj1 (task_private_excludes_public sg before.(TskState) node.(taskID)
      (proj1 Htasks) Hprivate)) as Hfresh.
    destruct (task_commit_transports_old_fields before.(TskState) priority invocation node
      tid old Hfresh Hold) as [current [Hcurrent Hfields]].
    exists current; split; [exact Hcurrent|].
    apply rt_step, tmr_task_sem_links_equal_wait_effect; exact Hfields.
  - eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
Qed.

Lemma sem_pend_nontimer_call_projection : forall action sg before after tid old,
  tmr_task_nontimer_source_client action -> task_in_range sg before.(TskState) ->
  kernel_client_step action sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros action sg before after tid old Hsource Htasks; destruct Hsource; intros Hstep Hold.
  - eapply sem_pend_creation_call_projection; eassumption.
  - destruct (task_create_stack_publication_raw_projection sg publication before after Hstep)
      as [Hraw ->].
    change (sem_pend_task_projection before.(TskState)
      (task_create_stack_publication_raw_state sg publication before).(TskState) tid old).
    eapply sem_pend_creation_call_projection; eassumption.
  - destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ [result Hstep]]. unfold event_create_allocate_critical in Hstep.
    destruct before.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
    + destruct Hstep as [image [_ [_ ->]]];
        eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ ->]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ [_ ->]]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ [_ [_ [_ [result [a [Ha Hstep]]]]]]].
    destruct free; destruct Hstep as [_ ->];
      (eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold]).
  - destruct Hstep as [_ [_ [_ [_ ->]]]];
      eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - eapply sem_pend_resume_client_projection; eassumption.
  - destruct Hstep as [event [_ [_ [node [fields [_ [_ [_ ->]]]]]]]].
    unfold sem_pend_task_projection.
    exists old; split.
    + change ((if Z.ltb 0 fields.(semCount)
          then sem_count_update_state before eid node (fields.(semCount) - 1)
          else before).(TskState).(inUsedTaskStates) tid = Some old).
      destruct (Z.ltb 0 fields.(semCount)); exact Hold.
    + apply rt_refl.
Qed.

Lemma sem_pend_flag_ready_call_projection : forall sg before pointer bits result schedule after
  tid old eid generation,
  task_flag_waiter_consistency sg before.(TskState) before.(FlagState) ->
  flag_task_rdy sg before pointer bits result = Some (schedule, after) ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg before pointer bits result schedule after tid old eid generation
    Hflags Hstep Hold [_ [_ [Hnull _]]].
  destruct (flag_task_rdy_result sg before pointer bits result schedule after Hstep)
    as [waiter [flags [node [Hunlink [Hnode [-> Hschedule]]]]]].
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hwaiter.
  assert (Hother : tid <> waiter.(flagTask)).
  { intro Heq; apply (task_flag_null_pointer_has_no_waiter sg before.(TskState)
      before.(FlagState) tid old Hflags Hold Hnull).
    exists pointer, waiter; split; [exact Hwaiter|symmetry; exact Heq]. }
  exists old; split; [|apply rt_refl].
  change ((if Z.eqb tid waiter.(flagTask) then Some (task_flag_wake node bits result)
    else before.(TskState).(inUsedTaskStates) tid) = Some old).
  lazymatch goal with
  | |- context [if ?condition then _ else _] => destruct condition eqn:Hsame
  end.
  - apply Z.eqb_eq in Hsame; contradiction.
  - exact Hold.
Qed.

Lemma sem_pend_event_ready_local_call_projection : forall sg before after actor event kind message result
  tid old eid generation,
  sem_pend_source_state_facts sg before ->
  tmr_task_sem_event_ready_call_input sg before event kind result ->
  kernel_client_step (event_task_rdy_source_client actor event kind message result) sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros sg before after actor event kind message result tid old eid generation
    [Hprofile [Htasks [Hevents Hcross]]]
    [node [head [tail [Hnode [Hlist [Hkind Hresult]]]]]] [priority Hstep] Hold Hcont.
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  eapply tmr_task_sem_event_ready_projection;
    [exact (proj1 Hprofile)|exact Htasks|exact (Hentries event node Hnode)|
     exact Hnode|exact Hlist|exact Hkind|exact Hresult|exact Hstep|exact Hold|exact Hcont].
Qed.

(** The Mutex critical receipt already retains its actual parent entry.
    Its stable invariant is obtained there, not invented for Prepared. *)
Lemma sem_pend_mutex_delete_call_entry_valid : forall sg event before,
  CriticalComponent.mutex_del_no_pend_critical_call_guard sg event before ->
  UCOS2_state_inv sg before.
Proof.
  intros sg event before [node [mutex [[Hentry _] Hpointer]]]; exact Hentry.
Qed.

Lemma sem_pend_critical_call_projection : forall action sg before after tid old eid generation,
  tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros action sg before after tid old eid generation Hsource;
    destruct Hsource; intros Hstep Hold Hcont.
  - destruct Hstep as [Hguard [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply tmr_task_sem_mutex_delete_projection;
      [eapply sem_pend_mutex_delete_call_entry_valid; exact Hguard|eassumption|eassumption|eassumption|eassumption].
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply tmr_task_sem_mutex_delete_projection;
        [eapply sem_pend_mutex_delete_call_entry_valid; exact Hguard|eassumption|eassumption|eassumption|eassumption].
    + apply sem_pend_task_projection_refl; exact Hold.
  - destruct Hstep as [_ [error Hsource]].
    eapply tmr_task_sem_change_prio_projection; eassumption.
Qed.

Lemma sem_pend_source_call_local_projection : forall external action sg before after tid old eid generation,
  tmr_task_source_call_receipt external action sg before after ->
  sem_pend_source_state_facts sg before ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external action sg before after tid old eid generation Hcall Hfacts Hold Hcont.
  destruct Hcall as [action0 sg0 before0 after0 Hnontimer Hstep|cut sg0 before0 after0 Hstep|
    actor requested priority sg0 before0 after0 Hstep|actor pointer bits result sg0 before0 after0 Hstep|
    actor event kind message result sg0 before0 after0 Hinput Hstep|slot previous sg0 before0 after0 Hstep|
    context outgoing incoming resumed sg0 before0 after0 Hstep|action0 sg0 before0 after0 Hsem Hstep|
    action0 sg0 before0 after0 Hcritical Hstep|actor cut sg0 before0 after0 Hstep|
    actor cut sg0 before0 after0 Hstep|actor source_sg cut entry timers sg0 before0 after0 Hstep|
    actor event option result sg0 before0 after0 Hstep|
    actor source_sg priority result entry returned sg0 before0 after0 Hstep].
  - eapply sem_pend_nontimer_call_projection;
      [exact Hnontimer|exact (proj1 (proj2 Hfacts))|exact Hstep|exact Hold].
  - eapply tmr_task_sem_profile_projection; eassumption.
  - destruct Hstep as [code Hstep]; eapply tmr_task_sem_change_prio_projection; eassumption.
  - destruct Hstep as [schedule Hstep].
    eapply sem_pend_flag_ready_call_projection; [|exact Hstep|exact Hold|exact Hcont].
    destruct Hfacts as [_ [_ [_ Hcross]]]; unfold cross_module_consistency in Hcross; tauto.
  - eapply sem_pend_event_ready_local_call_projection; eassumption.
  - destruct Hstep as [Hprevious ->]; eapply sem_pend_tick_task_projection; eassumption.
  - eapply sem_pend_source_client_projection;
      [apply SemPendSourceSchedulerInstall|exact Hstep|exact Hold].
  - eapply sem_pend_source_client_projection;
      [apply tmr_task_sem_source_client_wait_projection; exact Hsem|exact Hstep|exact Hold].
  - eapply sem_pend_critical_call_projection; eassumption.
  - exact (tmr_task_sem_tick_projection _ cut _ _ _ _ Hstep Hold).
  - destruct Hstep as [timers [_ ->]]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [_ [_ [_ ->]]]; eapply tmr_task_sem_projection_map_eq; [reflexivity|exact Hold].
  - destruct Hstep as [node [_ [_ Habort]]]; eapply sem_pend_abort_critical_projection; eassumption.
  - eapply tmr_task_sem_suspend_projection; eassumption.
Qed.

(** Input facts are attached only to leaves of this finite trace.  The
    observer and every original action/proof index are unchanged. *)
Inductive sem_pend_source_trace_receipt external clients sg observer event_observer :
  forall before stopped after,
  kernel_client_resource_trace clients sg observer event_observer before stopped after -> Prop :=
| SemPendSourceTraceReceiptNil : forall state,
    sem_pend_source_trace_receipt external clients sg observer event_observer state false state
      (@KernelClientTraceNil clients sg observer event_observer state)
| SemPendSourceTraceReceiptStep : forall action before middle after stopped
    (member : clients action) (foreign : kernel_client_actor action <> Some observer)
    (event_foreign : forall invocation, event_observer = Some invocation ->
      kernel_client_event_actor action <> Some invocation)
    (step : kernel_client_step action sg before middle)
    (tail : kernel_client_resource_trace clients sg observer event_observer middle stopped after),
    tmr_task_source_call_receipt external action sg before middle ->
    sem_pend_source_state_facts sg before ->
    sem_pend_source_trace_receipt external clients sg observer event_observer middle stopped after tail ->
    sem_pend_source_trace_receipt external clients sg observer event_observer before
      (orb (kernel_client_stops action observer) stopped) after
      (@KernelClientTraceStep clients sg observer event_observer action before middle after stopped
        member foreign event_foreign step tail).

Lemma sem_pend_source_trace_receipt_calls :
  forall external clients sg observer event_observer before stopped after
    (trace : kernel_client_resource_trace clients sg observer event_observer before stopped after),
  sem_pend_source_trace_receipt external clients sg observer event_observer before stopped after trace ->
  tmr_task_source_trace_calls external clients sg observer event_observer before stopped after trace.
Proof. intros until trace; intro Hreceipt; induction Hreceipt; constructor; assumption. Qed.

Lemma sem_pend_source_trace_local_projection :
  forall external clients sg observer event_observer before stopped after
    (trace : kernel_client_resource_trace clients sg observer event_observer before stopped after),
  sem_pend_source_trace_receipt external clients sg observer event_observer before stopped after trace ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external clients sg observer event_observer before stopped after trace Hreceipt.
  induction Hreceipt as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail
    Hcall Hfacts Hreceipt IH]; intros tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - destruct (sem_pend_source_call_local_projection external action sg before middle tid old eid generation
      Hcall Hfacts Hold Hcont) as [current [Hcurrent Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH tid current eid generation Hcurrent Hcontinue) as [last [Hlast Hsecond]].
    exists last; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

Lemma sem_pend_source_trace_receipt_from_valid :
  forall external critical sg observer event_observer before stopped after
    (trace : kernel_client_resource_trace critical.(critical_region_clients)
      sg observer event_observer before stopped after),
  tmr_task_source_trace_calls external critical.(critical_region_clients) sg observer event_observer
    before stopped after trace ->
  UCOS2_state_inv sg before ->
  sem_pend_source_trace_receipt external critical.(critical_region_clients) sg observer event_observer
    before stopped after trace.
Proof.
  intros external critical sg observer event_observer before stopped after trace Hcalls.
  induction Hcalls; intro Hvalid; [constructor|].
  constructor; [assumption|apply sem_pend_source_state_facts_from_valid; exact Hvalid|].
  apply IHHcalls; eapply kernel_client_preserves_validity;
    [apply (critical_region_client_certificates critical); eassumption|exact Hvalid|eassumption].
Qed.

(** The corresponding annotation of an EXISTING execution-origin trace.
    It adds only the same call receipt and its actual local input facts. *)
Inductive sem_pend_client_source_local_receipt external port clients sg observer event_observer :
  forall first before stopped last after,
  kernel_client_task_source_trace external port clients sg observer event_observer
    first before stopped last after -> Prop :=
| SemPendClientSourceLocalNil : forall origin state,
    sem_pend_client_source_local_receipt external port clients sg observer event_observer
      origin state false origin state
      (@KernelClientTaskSourceNil external port clients sg observer event_observer origin state)
| SemPendClientSourceLocalStep : forall action first before middle transient last after stopped
    (member : clients action) (foreign : kernel_client_actor action <> Some observer)
    (event_foreign : forall invocation, event_observer = Some invocation ->
      kernel_client_event_actor action <> Some invocation)
    (step : kernel_client_step action sg before transient)
    (execution : task_execution_source_step external port sg first before middle transient)
    (tail : kernel_client_task_source_trace external port clients sg observer event_observer
      middle transient stopped last after),
    tmr_task_source_call_receipt external action sg before transient ->
    sem_pend_source_state_facts sg before ->
    sem_pend_client_source_local_receipt external port clients sg observer event_observer
      middle transient stopped last after tail ->
    sem_pend_client_source_local_receipt external port clients sg observer event_observer
      first before (orb (kernel_client_stops action observer) stopped) last after
      (@KernelClientTaskSourceStep external port clients sg observer event_observer
        action first before middle transient last after stopped member foreign event_foreign step execution tail).

Lemma sem_pend_client_source_local_receipt_calls :
  forall external port clients sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_client_source_local_receipt external port clients sg observer event_observer
    first before stopped last after trace ->
  sem_pend_client_source_calls external port clients sg observer event_observer
    first before stopped last after trace.
Proof. intros until trace; intro Hreceipt; induction Hreceipt; constructor; assumption. Qed.

Lemma sem_pend_client_source_local_projection :
  forall external port clients sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_client_source_local_receipt external port clients sg observer event_observer
    first before stopped last after trace ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external port clients sg observer event_observer first before stopped last after trace Hreceipt.
  induction Hreceipt as [origin state|action first before middle transient last after stopped
    Hin Hforeign Hevent Hstep Hexecution Htail Hcall Hfacts Hreceipt IH];
    intros tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - destruct (sem_pend_source_call_local_projection external action sg before transient tid old eid generation
      Hcall Hfacts Hold Hcont) as [current [Hcurrent Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH tid current eid generation Hcurrent Hcontinue) as [last_node [Hlast Hsecond]].
    exists last_node; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

(** A pre-existing public segment retains its pre-existing Timer proof.
    No new Timer premise is imposed on individual client leaves. *)
Inductive sem_pend_resumption_source_local_receipt external port clients sg observer event_observer :
  forall first before stopped last after,
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    first before stopped last after -> Prop :=
| SemPendResumptionSourceLocalNil : forall origin state,
    sem_pend_resumption_source_local_receipt external port clients sg observer event_observer
      origin state false origin state
      (@KernelResumptionTaskSourceNil external port clients sg observer event_observer origin state)
| SemPendResumptionSourceLocalSegment : forall first before stopped1 middle transient stopped2 last after
    (segment : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped1 middle transient)
    (timer : timer_public_trace sg before.(TimerState) transient.(TimerState))
    (tail : kernel_resumption_task_source_trace external port clients sg observer event_observer
      middle transient stopped2 last after),
    sem_pend_client_source_local_receipt external port clients sg observer event_observer
      first before stopped1 middle transient segment ->
    sem_pend_resumption_source_local_receipt external port clients sg observer event_observer
      middle transient stopped2 last after tail ->
    sem_pend_resumption_source_local_receipt external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after
      (@KernelResumptionTaskSourceSegment external port clients sg observer event_observer
        first before stopped1 middle transient stopped2 last after segment timer tail).

Lemma sem_pend_resumption_source_local_receipt_calls :
  forall external port clients sg observer event_observer first before stopped last after
    (trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_resumption_source_local_receipt external port clients sg observer event_observer
    first before stopped last after trace ->
  sem_pend_resumption_source_calls external port clients sg observer event_observer
    first before stopped last after trace.
Proof.
  intros until trace; intro Hreceipt; induction Hreceipt; constructor; [|assumption].
  eapply sem_pend_client_source_local_receipt_calls; eassumption.
Qed.

Lemma sem_pend_resumption_source_local_projection :
  forall external port clients sg observer event_observer first before stopped last after
    (trace : kernel_resumption_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_resumption_source_local_receipt external port clients sg observer event_observer
    first before stopped last after trace ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros external port clients sg observer event_observer first before stopped last after trace Hreceipt.
  induction Hreceipt as [origin state|first before stopped1 middle transient stopped2 last after
    segment timer tail Hsegment Htail IH]; intros tid old eid generation Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - destruct (sem_pend_client_source_local_projection external port clients sg observer event_observer
      first before stopped1 middle transient segment Hsegment tid old eid generation Hold Hcont)
      as [current [Hcurrent Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation current).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IH tid current eid generation Hcurrent Hcontinue) as [last_node [Hlast Hsecond]].
    exists last_node; split; [exact Hlast|eapply rt_trans; eassumption].
Qed.

(** This exact producer already exists.  Its actual completed execution,
    caller, heaps and pre-owner select the trace; no new trace is chosen
    from equal endpoints.  Its observer remains TaskDelete's observer. *)
Definition sem_pend_delete_environment_trace environment critical saved_local requested sg
  completed phase loan original before returned after mask initial_heap final_heap frame
  (execution : sched_task_delete_environment_execution environment critical saved_local requested
    sg completed phase loan original before returned after mask initial_heap final_heap frame) :=
  proj1 (sched_task_delete_environment_source_resources environment critical saved_local requested
    sg completed phase loan original before returned after mask initial_heap final_heap frame execution).

Definition sem_pend_delete_environment_receipt environment critical saved_local requested sg
  completed phase loan original before returned after mask initial_heap final_heap frame
  (execution : sched_task_delete_environment_execution environment critical saved_local requested
    sg completed phase loan original before returned after mask initial_heap final_heap frame) : Prop :=
  sem_pend_resumption_source_local_receipt environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin) before false
    returned.(os_sched_call_origin) after
    (sem_pend_delete_environment_trace environment critical saved_local requested sg
      completed phase loan original before returned after mask initial_heap final_heap frame execution).

Lemma sem_pend_delete_environment_receipt_projection :
  forall environment critical saved_local requested sg completed phase loan original before returned after
    mask initial_heap final_heap frame
    (execution : sched_task_delete_environment_execution environment critical saved_local requested
      sg completed phase loan original before returned after mask initial_heap final_heap frame),
  sem_pend_delete_environment_receipt environment critical saved_local requested sg completed phase loan
    original before returned after mask initial_heap final_heap frame execution ->
  forall tid old eid generation,
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old /\
    (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame) final_heap.
Proof.
  intros environment critical saved_local requested sg completed phase loan original before returned after
    mask initial_heap final_heap frame execution Hreceipt tid old eid generation Hold Hcont.
  split.
  - eapply sem_pend_resumption_source_local_projection; [exact Hreceipt|exact Hold|exact Hcont].
  - destruct (sched_task_delete_environment_source_resources environment critical saved_local requested
      sg completed phase loan original before returned after mask initial_heap final_heap frame execution)
      as [_ [_ [_ [_ Howned]]]]; exact Howned.
Qed.

(** Normal return excludes retirement of THIS observer incarnation.
    No conclusion about an unrelated tid is extracted from stopped=false.
    Prepared leaves still require their actual wait-field effect. *)
Lemma sem_pend_selected_c_return_not_stopped :
  forall environment critical sg original returned state before input stopped current after output
    (run : kernel_c_sequence
      (SelectedCProgram.kernel_program_selected_c_step environment critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin))
      state before input stopped current after output),
  task_observer_lifetime state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_tcb_init_stack_same_call returned original -> kernel_call_task_source returned current ->
  stopped = false.
Proof.
  intros environment critical sg original returned state before input stopped current after output
    run Hlife Hsame Hreturned.
  pose proof (SelectedCProgram.kernel_program_selected_c_sequence_observer_lifetime
    environment critical sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
    state before input stopped current after output run) as [_ Hstop].
  destruct stopped; [|reflexivity].
  exfalso; apply (Hstop Hlife eq_refl).
  eapply kernel_call_same_return_observer_active; eassumption.
Qed.
