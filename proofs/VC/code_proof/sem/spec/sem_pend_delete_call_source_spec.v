Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Relations.Relation_Operators.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_context Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.task_status Ucos2Verify.lib.tick Ucos2Verify.lib.event_wait Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.helpers Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.timer Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_timeout_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Import UCOS2_C_Rules TaskStateDef DeleteComponent ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The pure status lemmas below are copied without statement/body changes
    from the checked entry consumer, from [sem_pend_status_clear_transport]
    through [sem_pend_source_critical_preserves_clear_status].  Keeping this
    finite pure prefix local avoids a lower-source -> observer -> consumer
    import cycle.  No whole-table survival is claimed for Delete. *)
Module DeleteCallClearStatus.
Definition sem_pend_status_clear_transport before after : Prop :=
  forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
  task_non_suspension_bits old.(stat) = 0 ->
  exists current, after.(TskState).(inUsedTaskStates) slot = Some current /\
    task_non_suspension_bits current.(stat) = 0.

Lemma sem_pend_wait_effect_preserves_clear_status : forall before after,
  sem_pend_wait_effect before after -> task_non_suspension_bits before.(stat) = 0 ->
  task_non_suspension_bits after.(stat) = 0.
Proof.
  intros before after Hstep Hclear; destruct Hstep.
  - unfold tick_task_update; destruct (dly t =? 0); [exact Hclear|].
    cbn [stat]; destruct (dly t - 1 =? 0); [|exact Hclear].
    apply task_status_after_timeout_no_multi_pending_bits,
      task_status_no_pending_reserved_bits_clear; exact Hclear.
  - change (task_non_suspension_bits (task_clear_pending_status t.(stat) PendSem) = 0).
    rewrite task_clear_pending_status_none by exact Hclear; exact Hclear.
  - exact Hclear.
  - change (task_non_suspension_bits (task_status_suspend t.(stat)) = 0).
    rewrite (proj1 (task_status_suspend_observations t.(stat))); exact Hclear.
  - change (task_non_suspension_bits (task_status_resume t.(stat)) = 0).
    rewrite (proj1 (task_status_resume_observations t.(stat))); exact Hclear.
  - destruct H as [_ [_ [Hstatus Hrest]]]; rewrite Hstatus; exact Hclear.
  - change (task_non_suspension_bits (task_status_after_timeout t.(stat)) = 0).
    apply task_status_after_timeout_no_multi_pending_bits,
      task_status_no_pending_reserved_bits_clear; exact Hclear.
Qed.

Lemma sem_pend_wait_trace_preserves_clear_status : forall before after,
  clos_refl_trans TaskAbstractState sem_pend_wait_effect before after ->
  task_non_suspension_bits before.(stat) = 0 -> task_non_suspension_bits after.(stat) = 0.
Proof.
  intros before after Htrace; induction Htrace; intro Hclear.
  - eapply sem_pend_wait_effect_preserves_clear_status; eassumption.
  - exact Hclear.
  - apply IHHtrace2, IHHtrace1; exact Hclear.
Qed.

Lemma sem_pend_status_clear_transport_map_eq : forall before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  sem_pend_status_clear_transport before after.
Proof. intros before after Hmap slot old Hold Hclear; exists old; rewrite Hmap; auto. Qed.

Lemma sem_pend_status_clear_transport_trans : forall before middle after,
  sem_pend_status_clear_transport before middle -> sem_pend_status_clear_transport middle after ->
  sem_pend_status_clear_transport before after.
Proof.
  intros before middle after Hfirst Hsecond slot old Hold Hclear.
  destruct (Hfirst slot old Hold Hclear) as [current [Hcurrent Hclear']].
  exact (Hsecond slot current Hcurrent Hclear').
Qed.

Lemma sem_pend_source_projection_preserves_clear_status : forall before after,
  (forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
    sem_pend_task_projection before.(TskState) after.(TskState) slot old) ->
  sem_pend_status_clear_transport before after.
Proof.
  intros before after Hprojection slot old Hold Hclear.
  destruct (Hprojection slot old Hold) as [current [Hcurrent Htrace]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_clear_status; eassumption.
Qed.

Lemma sem_pend_source_update_preserves_clear_status : forall before after selected old updated,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  after.(TskState).(inUsedTaskStates) =
    (glob_task_set_usedtask before.(TskState) selected updated).(inUsedTaskStates) ->
  (task_non_suspension_bits old.(stat) = 0 -> task_non_suspension_bits updated.(stat) = 0) ->
  sem_pend_status_clear_transport before after.
Proof.
  intros before after selected old updated Hold Htasks Hupdate slot node Hnode Hclear.
  rewrite Htasks.
  change (exists current,
    (if Z.eqb slot selected then Some updated else before.(TskState).(inUsedTaskStates) slot) = Some current /\
    task_non_suspension_bits current.(stat) = 0).
  destruct (Z.eqb slot selected) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst slot. assert (node = old) by congruence; subst node.
    exists updated; split; [reflexivity|apply Hupdate; exact Hclear].
  - exists node; split; [exact Hnode|exact Hclear].
Qed.

Lemma sem_pend_source_event_ready_preserves_clear_status : forall sg before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  sem_pend_status_clear_transport before after.
Proof.
  intros sg before eid kind message result priority after Hsource.
  unfold event_task_rdy in Hsource.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event)) as [| |selected]; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold; [|discriminate].
  injection Hsource as Hpriority Hafter; subst after.
  eapply sem_pend_source_update_preserves_clear_status; [exact Hold|reflexivity|].
  intro Hclear.
  change (task_non_suspension_bits (task_clear_pending_status old.(stat) kind) = 0).
  rewrite task_clear_pending_status_none by exact Hclear; exact Hclear.
Qed.

Lemma sem_pend_source_broadcast_preserves_clear_status : forall sg eid kind message result before priorities after,
  event_broadcast sg eid kind message result before priorities after ->
  sem_pend_status_clear_transport before after.
Proof.
  intros sg eid kind message result before priorities after Hsource; induction Hsource.
  - apply sem_pend_status_clear_transport_map_eq; reflexivity.
  - eapply sem_pend_status_clear_transport_trans; [|exact IHHsource].
    eapply sem_pend_source_event_ready_preserves_clear_status; eassumption.
Qed.

Lemma sem_pend_source_mutex_prepare_preserves_clear_status : forall sg mutex before after,
  mutex_del_prepare sg mutex before after -> sem_pend_status_clear_transport before after.
Proof.
  intros sg mutex before after Hprepare.
  apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
  eapply tmr_task_sem_mutex_prepare_projection; eassumption.
Qed.

Lemma sem_pend_source_mutex_delete_preserves_clear_status : forall sg eid option before result after,
  mutex_del_critical sg eid option before result after -> sem_pend_status_clear_transport before after.
Proof.
  intros sg eid option before result after [event [mutex [_ [_ [_ Hsource]]]]].
  destruct (Z.eq_dec option 0).
  - destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) before.(TskState)) 0).
    + destruct Hsource as [prepared [Hprepare [-> Hresult]]].
      change (sem_pend_status_clear_transport before prepared).
      eapply sem_pend_source_mutex_prepare_preserves_clear_status; exact Hprepare.
    + destruct Hsource as [-> Hresult]; apply sem_pend_status_clear_transport_map_eq; reflexivity.
  - destruct (Z.eq_dec option 1).
    + destruct Hsource as [prepared [priorities [drained [Hprepare [Hbroadcast [-> Hresult]]]]]].
      change (sem_pend_status_clear_transport before drained).
      eapply sem_pend_status_clear_transport_trans.
      * eapply sem_pend_source_mutex_prepare_preserves_clear_status; exact Hprepare.
      * eapply sem_pend_source_broadcast_preserves_clear_status; exact Hbroadcast.
    + destruct Hsource as [-> Hresult]; apply sem_pend_status_clear_transport_map_eq; reflexivity.
Qed.

Lemma sem_pend_source_critical_preserves_clear_status : forall action sg before after,
  tmr_task_critical_source_client action -> kernel_client_step action sg before after ->
  sem_pend_status_clear_transport before after.
Proof.
  intros action sg before after Hsource; destruct Hsource; intro Hstep.
  - destruct Hstep as [_ [result [code [request [error [scheduled [Hcritical Hencoding]]]]]]].
    eapply sem_pend_source_mutex_delete_preserves_clear_status; exact Hcritical.
  - destruct Hstep as [result [code [request Hsource]]].
    destruct Hsource as [result code request checkpoint Hguard Hobservation|kind Htype Hnotmutex].
    + destruct Hobservation as [error [scheduled [Hcritical Hencoding]]].
      eapply sem_pend_source_mutex_delete_preserves_clear_status; exact Hcritical.
    + apply sem_pend_status_clear_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [error Hsource]].
    apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_change_prio_projection; eassumption.
Qed.

End DeleteCallClearStatus.

Lemma sem_pend_delete_mutex_post_clear_status : forall sg eid caller before result schedule after,
  mutex_post_critical sg eid caller before result schedule after ->
  DeleteCallClearStatus.sem_pend_status_clear_transport before after.
Proof.
  intros sg eid caller before result schedule after Hcritical.
  destruct Hcritical as [entry event mutex Hlookup Htype Hfields Howner
    |entry event mutex prepared Hlookup Htype Hfields Howner Hprepare Hempty
    |entry event mutex prepared priority woken found owner Hlookup Htype Hfields Howner
      Hprepare Hnonempty Hwake Hfound Htable].
  - apply DeleteCallClearStatus.sem_pend_status_clear_transport_map_eq; reflexivity.
  - change (DeleteCallClearStatus.sem_pend_status_clear_transport entry prepared).
    apply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply sem_pend_mutex_post_prepare_projection; eassumption.
  - change (DeleteCallClearStatus.sem_pend_status_clear_transport entry woken).
    eapply DeleteCallClearStatus.sem_pend_status_clear_transport_trans with (middle := prepared).
    + apply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
      eapply sem_pend_mutex_post_prepare_projection; eassumption.
    + eapply DeleteCallClearStatus.sem_pend_source_event_ready_preserves_clear_status; exact Hwake.
Qed.

Lemma sem_pend_delete_mutex_inheritance_clear_status : forall sg call,
  PendComponent.mutex_pend_inheritance_c_source sg call ->
  DeleteCallClearStatus.sem_pend_status_clear_transport call.(PendComponent.mutex_pend_inheritance_entry)
    call.(PendComponent.mutex_pend_inheritance_returned).
Proof.
  intros sg call Hsource.
  apply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
  eapply sem_pend_mutex_inheritance_c_projection; eassumption.
Qed.

Lemma sem_pend_delete_wake_clear_status : forall sg before after,
  WakeComponent.kernel_wake_c_source sg before after ->
  DeleteCallClearStatus.sem_pend_status_clear_transport before after.
Proof.
  intros sg before after Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply DeleteCallClearStatus.sem_pend_source_update_preserves_clear_status; [exact Hold|reflexivity|].
    intro Hclear; change (task_non_suspension_bits (task_clear_pending_status old.(stat) PendFlag) = 0).
    rewrite task_clear_pending_status_none by exact Hclear; exact Hclear.
  - eapply DeleteCallClearStatus.sem_pend_source_event_ready_preserves_clear_status; eassumption.
  - apply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status; intros slot' previous Hold.
    eapply sem_pend_tick_task_projection; eassumption.
Qed.

Lemma sem_pend_delete_prepare_clear_status : forall state selected node prepared loan,
  state.(TskState).(inUsedTaskStates) selected = Some node ->
  task_delete_prepare_single_wait state selected node = Some (prepared, loan) ->
  DeleteCallClearStatus.sem_pend_status_clear_transport state prepared.
Proof.
  intros state selected node prepared loan Hselected Hprepare tid old Hold Hclear.
  destruct (Z.eq_dec tid selected) as [->|Hdifferent].
  - exists (task_delete_prepared_node node); split.
    + exact (proj2 (task_delete_preparation_task_projections__release_and_recycle_resources
        state selected node prepared loan Hprepare)).
    + reflexivity.
  - destruct (task_delete_prepare_single_wait_frame state selected node prepared loan Hprepare)
      as [next [Hstate Hfields]].
    exists old; split; [|exact Hclear].
    rewrite Hstate; cbn [replace_FlagS replace_EventS replace_SchedS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq tid selected) Hdifferent); exact Hold.
Qed.

(** Clear status needs neither a Sem wait continuation nor a particular
    Pend result.  The actual live caller is selected only at the return
    boundary; the raw Delete branches still include retirement. *)
Lemma sem_pend_delete_program_step_clear_status :
  forall environment critical sg stored_observer stored_origin before before_heap input stopped after after_heap output,
  kernel_program_c_step environment critical sg stored_observer stored_origin
    before before_heap input stopped after after_heap output ->
  forall slot old, before.(TskState).(inUsedTaskStates) slot = Some old ->
    task_non_suspension_bits old.(stat) = 0 ->
    (exists live, after.(TskState).(inUsedTaskStates) slot = Some live) ->
    exists current, after.(TskState).(inUsedTaskStates) slot = Some current /\
      task_non_suspension_bits current.(stat) = 0.
Proof.
  intros environment critical sg stored_observer stored_origin before before_heap input stopped after after_heap output Hstep.
  destruct Hstep; intros slot old Hold Hclear Hlive.
  - destruct H as [Hcompletion [Hphysical [Hsource Hpacket]]].
    clear Hpacket Hphysical Hcompletion.
    destruct call as [actual|actual]; cbn in *.
    + destruct Hsource as [error [Hcritical Hcode]].
      eapply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status;
        [|exact Hold|exact Hclear]. intros tid node Hnode.
      eapply tmr_task_sem_change_prio_projection; eassumption.
    + unfold CriticalComponent.mutex_del_critical_fields_observation in Hsource.
      destruct Hsource.
      * destruct H0 as [error [scheduled [Hcritical Hcode]]].
        eapply DeleteCallClearStatus.sem_pend_source_mutex_delete_preserves_clear_status; eassumption.
      * exists old; auto.
  - eapply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_builtin_c_projection; eassumption.
  - eapply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_install_c_projection; eassumption.
  - eapply sem_pend_delete_wake_clear_status; [|exact Hold|exact Hclear].
    eapply WakeComponent.kernel_wake_c_segment_source; exact H.
  - eapply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_status_c_source_projection;
      [exact (StatusComponent.kernel_status_c_segment_code _ _ _ _ _ _ H)|exact Hnode].
  - eapply DeleteCallClearStatus.sem_pend_source_projection_preserves_clear_status;
      [|exact Hold|exact Hclear]. intros tid node Hnode.
    eapply sem_pend_task_creation_c_source_projection;
      [eapply CreationComponent.kernel_task_creation_c_segment_source; exact H|exact Hnode].
  - eapply DeleteCallClearStatus.sem_pend_status_clear_transport_map_eq; [|exact Hold|exact Hclear].
    rewrite (proj1 (NamedSourceFrames.kernel_event_creation_c_source_other_fields _ _
      (EventCreationComponent.kernel_event_creation_c_segment_source _ _ _ _ _ _ _ H))); reflexivity.
  - eapply DeleteCallClearStatus.sem_pend_status_clear_transport_map_eq; [|exact Hold|exact Hclear].
    rewrite (proj1 (NamedSourceFrames.kernel_queue_creation_c_source_other_fields _ _ _
      (QueueCreationComponent.kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ H))); reflexivity.
  - destruct H as [Hsource Hinput Houtput].
    eapply sem_pend_delete_mutex_inheritance_clear_status; eassumption.
  - destruct H as [[Hcaller Hsource] Hinput Houtput].
    eapply sem_pend_delete_mutex_post_clear_status; eassumption.
  - destruct H; exists old; auto.
  - destruct H; [destruct H| |]; exists old; auto.
  - destruct H as [inputs before_heap prepared_heap Hcontext Hcompletion|capture after_heap Hcontext Hcompletion].
    + destruct Hcompletion as [[Hhistory [Hprepare Hprotocol]] Hinput Houtput].
      destruct Hhistory as [Hlookup [Hselected [Hnode Hpointer]]].
      change (exists current, inputs.(delete_capture_prepared).(TskState).(inUsedTaskStates) slot = Some current /\
        task_non_suspension_bits current.(stat) = 0).
      eapply sem_pend_delete_prepare_clear_status;
        [exact (proj2 (task_delete_table_lookup_live _ _ _ _ Hnode))|exact Hprepare|exact Hold|exact Hclear].
    + destruct (sem_pend_delete_recycle_live_wait_projection _ _ _ _ _ _ _ _ Hold Hlive)
        as [current [Hcurrent Htrace]].
      exists current; split; [exact Hcurrent|].
      eapply DeleteCallClearStatus.sem_pend_wait_trace_preserves_clear_status; eassumption.
Qed.

(** These finite receipts decorate the existing program proof.  Eleven
    cases are already structural; Wake and MutexPost retain the actual
    typed call facts supplied by their checked module post.  No endpoint
    property is a receipt field. *)
Definition sem_pend_delete_interval_receipt environment critical sg stored_observer stored_origin
  state before input stopped current after output
  (run : kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output) : Prop :=
  kernel_c_sequence_has_source (kernel_program_c_step environment critical sg stored_observer stored_origin)
    (sem_pend_program_c_step_receipt environment critical sg stored_observer stored_origin)
    state before input stopped current after output run.

Lemma sem_pend_delete_interval_lifetime :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output ->
  forall observer origin,
    task_observer_lifetime_transport observer origin state.(TskState) current.(TskState).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output run.
  induction run; intros observer origin.
  - apply task_observer_lifetime_transport_refl.
  - eapply sem_pend_program_c_step_lifetime_transport; eassumption.
  - eapply task_observer_lifetime_transport_trans; [apply IHrun1|apply IHrun2].
  - apply IHrun.
Qed.

(** A real later return is transported backwards through the same run.
    A different task may be recycled; there is no all-used-slots survival
    claim and no restriction on the run's stored observer or origin. *)
Lemma sem_pend_delete_interval_multi_pointer :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output ->
  forall observer tid old generation,
    task_observer_lifetime state.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output run.
  induction run; intros observer tid old generation Hlife Hactive Hold.
  - exists old; auto.
  - eapply sem_pend_program_c_step_multi_pointer; [exact H|exact Hold|].
    destruct Hactive as [Hregistered [Hretired [live [Hlive Hgeneration]]]]; eauto.
  - destruct (sem_pend_delete_interval_lifetime environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ run1 observer (RunningInvocation tid generation) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_delete_interval_lifetime environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ run2 observer (RunningInvocation tid generation) Hmiddle_life) Hactive) as Hmiddle_active.
    destruct (IHrun1 observer tid old generation Hlife Hmiddle_active Hold) as [middle_node [Hmiddle [Hgen Hptr]]].
    destruct (IHrun2 observer tid middle_node generation Hmiddle_life Hactive Hmiddle)
      as [last_node [Hlast [Hgen' Hptr']]].
    exists last_node; split; [exact Hlast|]. split; congruence.
  - eapply IHrun; eassumption.
Qed.

Lemma sem_pend_delete_interval_clear_status :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output,
  kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
    state before input stopped current after output ->
  forall observer tid old generation,
    task_observer_lifetime state.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    task_non_suspension_bits old.(stat) = 0 ->
    exists node, current.(TskState).(inUsedTaskStates) tid = Some node /\
      task_non_suspension_bits node.(stat) = 0.
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output run.
  induction run; intros observer tid old generation Hlife Hactive Hold Hclear.
  - exists old; auto.
  - eapply sem_pend_delete_program_step_clear_status; [exact H|exact Hold|exact Hclear|].
    destruct Hactive as [_ [_ [live [Hlive _]]]]; eauto.
  - destruct (sem_pend_delete_interval_lifetime environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ run1 observer (RunningInvocation tid generation) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_delete_interval_lifetime environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ run2 observer (RunningInvocation tid generation) Hmiddle_life) Hactive) as Hmiddle_active.
    destruct (IHrun1 observer tid old generation Hlife Hmiddle_active Hold Hclear) as [middle_node [Hmiddle Hbits]].
    eapply IHrun2; eassumption.
  - eapply IHrun; eassumption.
Qed.

Lemma sem_pend_delete_interval_waiter_projection :
  forall environment critical sg stored_observer stored_origin state before input stopped current after output
    (run : kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
      state before input stopped current after output),
  sem_pend_delete_interval_receipt environment critical sg stored_observer stored_origin
    state before input stopped current after output run ->
  forall observer tid old eid generation,
    task_observer_lifetime state.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active current.(TskState) observer (RunningInvocation tid generation) ->
    state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection state.(TskState) current.(TskState) tid old.
Proof.
  intros environment critical sg stored_observer stored_origin state before input stopped current after output run Hreceipt.
  induction Hreceipt; intros observer tid old eid generation Hlife Hactive Hold Hcont.
  - apply sem_pend_task_projection_refl; exact Hold.
  - eapply sem_pend_program_c_step_receipt_projection; [exact H|exact Hold|exact Hcont|].
    destruct Hactive as [Hregistered [Hretired [live [Hlive Hgeneration]]]]; eauto.
  - destruct (sem_pend_delete_interval_lifetime environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ first observer (RunningInvocation tid generation) Hlife) as [Hmiddle_life Hfirst_back].
    pose proof (proj2 (sem_pend_delete_interval_lifetime environment critical sg stored_observer stored_origin
      _ _ _ _ _ _ _ last observer (RunningInvocation tid generation) Hmiddle_life) Hactive) as Hmiddle_active.
    destruct (IHHreceipt1 observer tid old eid generation Hlife Hmiddle_active Hold Hcont)
      as [middle_node [Hmiddle Hfirst]].
    assert (Hcontinue : sem_pend_wait_continuation eid generation middle_node).
    { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
    destruct (IHHreceipt2 observer tid middle_node eid generation Hmiddle_life Hactive Hmiddle Hcontinue)
      as [last_node [Hlast Hsecond]].
    exists last_node; split; [exact Hlast|eapply rt_trans; eassumption].
  - eapply IHHreceipt; eassumption.
Qed.

(** The original selection and rely are retained.  Pattern matching this
    joint window exposes its very run/selection/owned triple; no unrelated
    endpoint-equal trace or proof-irrelevance conversion is accepted. *)
Inductive sem_pend_delete_joint_window_receipt
  event_observer environment critical saved_local sg stored_observer stored_origin selected requested rely :
  forall phase loan original before returned after mask before_heap after_heap frame history stopped,
  task_delete_joint_c_window environment critical saved_local sg
    (kernel_program_c_step environment critical sg stored_observer stored_origin) selected requested rely
    phase loan original before returned after mask before_heap after_heap frame history stopped -> Prop :=
| SemPendDeleteJointWindowReceipt :
    forall phase loan original before returned after mask before_heap after_heap frame stopped run selection owned,
    sem_pend_delete_interval_receipt environment critical sg stored_observer stored_origin
      before before_heap (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame)
      stopped after after_heap (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame) run ->
    kernel_program_c_sequence_call_source environment critical sg stored_observer stored_origin event_observer
      before before_heap (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame)
      stopped after after_heap (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame) run ->
    sem_pend_delete_joint_window_receipt event_observer environment critical saved_local sg stored_observer stored_origin
      selected requested rely phase loan original before returned after mask before_heap after_heap frame
      (task_delete_selected_c_history environment critical saved_local sg
        (kernel_program_c_step environment critical sg stored_observer stored_origin) selected requested rely
        phase loan original before returned after mask before_heap after_heap frame stopped run selection owned) stopped
      (@TaskDeleteJointCWindow environment critical saved_local sg
        (kernel_program_c_step environment critical sg stored_observer stored_origin) selected requested rely
        phase loan original before returned after mask before_heap after_heap frame stopped run selection owned).

(** This is the exact selected-call packaging point.  Both the old
    history and the new attachment use the supplied run/selection/owned
    triple, before the old aggregate return forgets its leaf evidence. *)
Lemma sem_pend_delete_joint_window_receipt_from_run :
  forall event_observer environment critical saved_local sg stored_observer stored_origin selected requested rely
    phase loan original before returned after mask before_heap after_heap frame stopped
    (run : kernel_c_sequence (kernel_program_c_step environment critical sg stored_observer stored_origin)
      before before_heap (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame)
      stopped after after_heap (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame))
    selection owned,
  sem_pend_delete_interval_receipt environment critical sg stored_observer stored_origin
    _ _ _ _ _ _ _ run ->
  kernel_program_c_sequence_call_source environment critical sg stored_observer stored_origin event_observer
    _ _ _ _ _ _ _ run ->
  sem_pend_delete_joint_window_receipt event_observer environment critical saved_local sg stored_observer stored_origin
    selected requested rely phase loan original before returned after mask before_heap after_heap frame
    (task_delete_selected_c_history environment critical saved_local sg
      (kernel_program_c_step environment critical sg stored_observer stored_origin) selected requested rely
      phase loan original before returned after mask before_heap after_heap frame stopped run selection owned) stopped
    (@TaskDeleteJointCWindow environment critical saved_local sg
      (kernel_program_c_step environment critical sg stored_observer stored_origin) selected requested rely
      phase loan original before returned after mask before_heap after_heap frame stopped run selection owned).
Proof. intros; constructor; assumption. Qed.

Inductive sem_pend_delete_restore_window_receipt event_observer stored_observer stored_origin restore selected rely stopped :
  task_delete_restore_capture_c_window
    (kernel_program_c_step restore.(delete_restore_inputs).(delete_capture_environment)
      restore.(delete_restore_inputs).(delete_capture_critical) restore.(delete_restore_inputs).(delete_capture_globals)
      stored_observer stored_origin) restore selected rely stopped -> Prop :=
| SemPendDeleteRestoreWindowReceipt : forall prefix_heap environment_heap prefix joint suffix,
    sem_pend_delete_joint_window_receipt event_observer
      restore.(delete_restore_inputs).(delete_capture_environment)
      restore.(delete_restore_inputs).(delete_capture_critical)
      restore.(delete_restore_inputs).(delete_capture_saved_local)
      restore.(delete_restore_inputs).(delete_capture_globals) stored_observer stored_origin selected
      restore.(delete_restore_inputs).(delete_capture_requested) rely
      (task_delete_capture_phase restore.(delete_restore_inputs)) restore.(delete_restore_inputs).(delete_capture_loan)
      restore.(delete_restore_inputs).(delete_capture_first)
      (task_delete_locked restore.(delete_restore_inputs).(delete_capture_prepared))
      restore.(delete_restore_middle) restore.(delete_restore_between) restore.(delete_restore_inputs).(delete_capture_mask)
      prefix_heap environment_heap restore.(delete_restore_inputs).(delete_capture_frame)
      restore.(delete_restore_history) stopped joint ->
    sem_pend_delete_restore_window_receipt event_observer stored_observer stored_origin restore selected rely stopped
      (ex_intro _ prefix_heap (ex_intro _ environment_heap (conj prefix (conj joint suffix)))).

Inductive sem_pend_delete_save_window_receipt event_observer stored_observer stored_origin capture selected rely stopped :
  task_delete_save_capture_c_window (task_delete_program_segment stored_observer stored_origin capture)
    capture selected rely stopped -> Prop :=
| SemPendDeleteSaveWindowReceipt : forall environment_heap joint suffix,
    let restore := capture.(delete_save_restore) in
    let inputs := restore.(delete_restore_inputs) in
    sem_pend_delete_joint_window_receipt event_observer inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) stored_observer stored_origin selected
      inputs.(delete_capture_requested) rely (task_delete_capture_phase inputs) inputs.(delete_capture_loan)
      restore.(delete_restore_middle) restore.(delete_restore_between) capture.(delete_save_returned)
      capture.(delete_save_resumed) inputs.(delete_capture_mask) restore.(delete_restore_middle_heap)
      environment_heap inputs.(delete_capture_frame)
      (task_delete_save_observation_history inputs.(delete_capture_environment) inputs.(delete_capture_critical)
        inputs.(delete_capture_requested) (task_delete_capture_phase inputs) inputs.(delete_capture_globals)
        restore.(delete_restore_middle) inputs.(delete_capture_mask) capture.(delete_save_saved)
        restore.(delete_restore_between) capture.(delete_save_returned) capture.(delete_save_resumed)
        capture.(delete_save_observation)) stopped joint ->
    sem_pend_delete_save_window_receipt event_observer stored_observer stored_origin capture selected rely stopped
      (ex_intro _ environment_heap (conj joint suffix)).

Lemma sem_pend_delete_restore_capture_from_c_window :
  forall event_observer stored_observer stored_origin inputs selected rely before_heap prepared_heap middle between middle_heap
    prefix_heap environment_heap stopped preparation history prefix joint suffix,
  let segment := kernel_program_c_step inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) stored_observer stored_origin in
  let restore := task_delete_restore_capture_from_c_window inputs segment selected rely
    before_heap prepared_heap middle between middle_heap prefix_heap environment_heap stopped
    preparation history prefix joint suffix in
  sem_pend_delete_joint_window_receipt event_observer inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) stored_observer stored_origin
    selected inputs.(delete_capture_requested) rely (task_delete_capture_phase inputs) inputs.(delete_capture_loan)
    inputs.(delete_capture_first) (task_delete_locked inputs.(delete_capture_prepared)) middle between
    inputs.(delete_capture_mask) prefix_heap environment_heap inputs.(delete_capture_frame) history stopped joint ->
  exists window : task_delete_restore_capture_c_window segment restore selected rely stopped,
    sem_pend_delete_restore_window_receipt event_observer stored_observer stored_origin restore selected rely stopped window.
Proof.
  intros event_observer stored_observer stored_origin inputs selected rely before_heap prepared_heap middle between middle_heap
    prefix_heap environment_heap stopped preparation history prefix joint suffix segment restore Hreceipt.
  refine (ex_intro _ (ex_intro _ prefix_heap (ex_intro _ environment_heap (conj prefix (conj joint suffix)))) _).
  constructor; exact Hreceipt.
Qed.

Lemma sem_pend_delete_save_capture_from_c_window :
  forall event_observer stored_observer stored_origin restore selected rely saved returned resumed resumed_heap environment_heap
    stopped history saved_value joint suffix,
  let inputs := restore.(delete_restore_inputs) in
  let segment := kernel_program_c_step inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) stored_observer stored_origin in
  let capture := task_delete_save_capture_from_c_window restore segment selected rely saved returned resumed
    resumed_heap environment_heap stopped history saved_value joint suffix in
  sem_pend_delete_joint_window_receipt event_observer inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) stored_observer stored_origin
    selected inputs.(delete_capture_requested) rely (task_delete_capture_phase inputs) inputs.(delete_capture_loan)
    restore.(delete_restore_middle) restore.(delete_restore_between) returned resumed inputs.(delete_capture_mask)
    restore.(delete_restore_middle_heap) environment_heap inputs.(delete_capture_frame) history stopped joint ->
  exists window : task_delete_save_capture_c_window segment capture selected rely stopped,
    sem_pend_delete_save_window_receipt event_observer stored_observer stored_origin capture selected rely stopped window.
Proof.
  intros event_observer stored_observer stored_origin restore selected rely saved returned resumed resumed_heap environment_heap
    stopped history saved_value joint suffix inputs segment capture Hreceipt.
  destruct history as [source [[[invocation [origin stack]] available] [phase_rely protocol]]].
  refine (ex_intro _ (ex_intro _ environment_heap (conj joint suffix)) _).
  constructor; exact Hreceipt.
Qed.

(** This packet is assembled while the original capture/window witnesses
    are still available.  It has no waiter, scalar, current-task, running,
    or future-return conclusion among its fields. *)
Record sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
  restore_selected restore_rely save_selected save_rely restore_stopped save_stopped : Prop := {
  sem_pend_delete_restore_window : task_delete_restore_capture_c_window
    (task_delete_program_segment stored_observer stored_origin capture)
    capture.(delete_save_restore) restore_selected restore_rely restore_stopped;
  sem_pend_delete_restore_receipt : sem_pend_delete_restore_window_receipt event_observer stored_observer stored_origin
    capture.(delete_save_restore) restore_selected restore_rely restore_stopped sem_pend_delete_restore_window;
  sem_pend_delete_save_window : task_delete_save_capture_c_window
    (task_delete_program_segment stored_observer stored_origin capture)
    capture save_selected save_rely save_stopped;
  sem_pend_delete_save_receipt : sem_pend_delete_save_window_receipt event_observer stored_observer stored_origin
    capture save_selected save_rely save_stopped sem_pend_delete_save_window;
  sem_pend_delete_body_completed : task_delete_capture_completed capture after_heap
}.

Definition sem_pend_delete_call_run event_observer stored_observer stored_origin capture after_heap
  restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
  (source : sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped) :=
  kernel_program_task_delete_body_sequence stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    (sem_pend_delete_restore_window event_observer _ _ _ _ _ _ _ _ _ _ source)
    (sem_pend_delete_save_window event_observer _ _ _ _ _ _ _ _ _ _ source)
    (sem_pend_delete_body_completed event_observer _ _ _ _ _ _ _ _ _ _ source).

Lemma sem_pend_delete_call_resources :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  task_delete_capture_before_owner capture.(delete_save_restore).(delete_restore_inputs)
    capture.(delete_save_restore).(delete_restore_before_heap) /\
  task_delete_capture_recycled_owner capture after_heap.
Proof.
  intros * source.
  split; [exact capture.(delete_save_restore).(delete_restore_before_owned)|].
  exact (task_delete_fields_after_owner _ _ _ _ _ _ _ _ _ _ _ _ _
    (sem_pend_delete_body_completed event_observer _ _ _ _ _ _ _ _ _ _ source)).
Qed.

(** Immediate consequence of the actual recycled-body C post.  The two
    interval attachments are the ones retained at their real call returns;
    this factory neither decodes the weaker API summary nor supplies them
    from a final owner. *)
Lemma sem_pend_delete_call_from_recycled_post :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped
    (restore_window : task_delete_restore_capture_c_window
      (task_delete_program_segment stored_observer stored_origin capture)
      capture.(delete_save_restore) restore_selected restore_rely restore_stopped)
    (save_window : task_delete_save_capture_c_window
      (task_delete_program_segment stored_observer stored_origin capture)
      capture save_selected save_rely save_stopped),
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  sem_pend_delete_restore_window_receipt event_observer stored_observer stored_origin capture.(delete_save_restore)
    restore_selected restore_rely restore_stopped restore_window ->
  sem_pend_delete_save_window_receipt event_observer stored_observer stored_origin capture
    save_selected save_rely save_stopped save_window ->
  (task_delete_recycled_body inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_saved_local) inputs.(delete_capture_globals) inputs.(delete_capture_requested)
    inputs.(delete_capture_original) inputs.(delete_capture_initial) capture.(delete_save_returned)
    capture.(delete_save_saved) capture.(delete_save_resumed) (task_delete_capture_cut capture)
    inputs.(delete_capture_loan) inputs.(delete_capture_name) ** inputs.(delete_capture_frame)) after_heap ->
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped /\
  task_delete_capture_recycled_owner capture after_heap.
Proof.
  intros event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped restore_window save_window inputs Hrestore Hsave Hpost.
  destruct (task_delete_capture_recycled_body_output capture after_heap Hpost)
    as [actual_heap [Hcompleted [Heq Howned]]].
  subst actual_heap; split; [|exact Howned].
  exact (@Build_sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    restore_window Hrestore save_window Hsave Hcompleted).
Qed.

Lemma sem_pend_delete_call_lifetime :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  forall observer origin,
    task_observer_lifetime_transport observer origin
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
      (task_delete_capture_cut capture).(TskState).
Proof.
  intros * source observer origin.
  eapply sem_pend_delete_interval_lifetime.
  exact (sem_pend_delete_call_run event_observer _ _ _ _ _ _ _ _ _ _ source).
Qed.

Lemma sem_pend_delete_call_observer_lifetime :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  task_observer_lifetime_result stored_observer stored_origin
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
    (task_delete_capture_cut capture).(TskState)
    (task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped).
Proof.
  intros * source.
  eapply kernel_program_c_sequence_observer_lifetime.
  exact (sem_pend_delete_call_run event_observer _ _ _ _ _ _ _ _ _ _ source).
Qed.

Lemma sem_pend_delete_call_multi_pointer :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  forall observer tid old generation,
    task_observer_lifetime capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
      observer (RunningInvocation tid generation) ->
    task_invocation_active (task_delete_capture_cut capture).(TskState) observer (RunningInvocation tid generation) ->
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState).(inUsedTaskStates) tid = Some old ->
    exists node, (task_delete_capture_cut capture).(TskState).(inUsedTaskStates) tid = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr).
Proof.
  intros * source observer tid old generation Hlife Hactive Hold.
  eapply sem_pend_delete_interval_multi_pointer;
    [exact (sem_pend_delete_call_run event_observer _ _ _ _ _ _ _ _ _ _ source)|exact Hlife|exact Hactive|exact Hold].
Qed.

Lemma sem_pend_delete_call_clear_status :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  forall observer tid old generation,
    task_observer_lifetime capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
      observer (RunningInvocation tid generation) ->
    task_invocation_active (task_delete_capture_cut capture).(TskState) observer (RunningInvocation tid generation) ->
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState).(inUsedTaskStates) tid = Some old ->
    task_non_suspension_bits old.(stat) = 0 ->
    exists node, (task_delete_capture_cut capture).(TskState).(inUsedTaskStates) tid = Some node /\
      task_non_suspension_bits node.(stat) = 0.
Proof.
  intros * source observer tid old generation Hlife Hactive Hold Hclear.
  eapply sem_pend_delete_interval_clear_status;
    [exact (sem_pend_delete_call_run event_observer _ _ _ _ _ _ _ _ _ _ source)|
      exact Hlife|exact Hactive|exact Hold|exact Hclear].
Qed.

Lemma sem_pend_delete_call_preserves_observer :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped = false ->
  task_invocation_active capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
      stored_observer stored_origin /\
    sched_observer_current_cache stored_origin capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired) ->
  task_invocation_active (task_delete_capture_cut capture).(TskState) stored_observer stored_origin /\
    sched_observer_current_cache stored_origin (task_delete_capture_cut capture).
Proof.
  intros * source Hstop Hbefore.
  eapply kernel_program_c_sequence_preserves_observer;
    [exact (sem_pend_delete_call_run event_observer _ _ _ _ _ _ _ _ _ _ source)|exact Hstop|exact Hbefore].
Qed.

Lemma sem_pend_delete_joint_window_waiter_projection :
  forall event_observer environment critical saved_local sg stored_observer stored_origin selected requested rely
    phase loan original before returned after mask before_heap after_heap frame history stopped
    (window : task_delete_joint_c_window environment critical saved_local sg
      (kernel_program_c_step environment critical sg stored_observer stored_origin) selected requested rely
      phase loan original before returned after mask before_heap after_heap frame history stopped),
  sem_pend_delete_joint_window_receipt event_observer environment critical saved_local sg stored_observer stored_origin
    selected requested rely phase loan original before returned after mask before_heap after_heap frame history stopped window ->
  forall observer tid old eid generation,
    task_observer_lifetime before.(TskState) observer (RunningInvocation tid generation) ->
    task_invocation_active after.(TskState) observer (RunningInvocation tid generation) ->
    before.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection before.(TskState) after.(TskState) tid old.
Proof.
  intros event_observer environment critical saved_local sg stored_observer stored_origin selected requested rely
    phase loan original before returned after mask before_heap after_heap frame history stopped window Hreceipt.
  destruct Hreceipt.
  intros observer tid old eid generation Hlife Hactive Hold Hcont.
  eapply sem_pend_delete_interval_waiter_projection; eassumption.
Qed.

Lemma sem_pend_delete_restore_window_waiter_projection :
  forall event_observer stored_observer stored_origin restore selected rely stopped
    (window : task_delete_restore_capture_c_window
      (kernel_program_c_step restore.(delete_restore_inputs).(delete_capture_environment)
        restore.(delete_restore_inputs).(delete_capture_critical) restore.(delete_restore_inputs).(delete_capture_globals)
        stored_observer stored_origin) restore selected rely stopped),
  sem_pend_delete_restore_window_receipt event_observer stored_observer stored_origin restore selected rely stopped window ->
  forall observer tid old eid generation,
    task_observer_lifetime (task_delete_locked restore.(delete_restore_inputs).(delete_capture_prepared)).(TskState)
      observer (RunningInvocation tid generation) ->
    task_invocation_active restore.(delete_restore_between).(TskState) observer (RunningInvocation tid generation) ->
    (task_delete_locked restore.(delete_restore_inputs).(delete_capture_prepared)).(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection (task_delete_locked restore.(delete_restore_inputs).(delete_capture_prepared)).(TskState)
      restore.(delete_restore_between).(TskState) tid old.
Proof.
  intros event_observer stored_observer stored_origin restore selected rely stopped window Hreceipt.
  destruct Hreceipt.
  intros observer tid old eid generation Hlife Hactive Hold Hcont.
  eapply sem_pend_delete_joint_window_waiter_projection; eassumption.
Qed.

Lemma sem_pend_delete_save_window_waiter_projection :
  forall event_observer stored_observer stored_origin capture selected rely stopped
    (window : task_delete_save_capture_c_window (task_delete_program_segment stored_observer stored_origin capture)
      capture selected rely stopped),
  sem_pend_delete_save_window_receipt event_observer stored_observer stored_origin capture selected rely stopped window ->
  forall observer tid old eid generation,
    task_observer_lifetime capture.(delete_save_restore).(delete_restore_between).(TskState)
      observer (RunningInvocation tid generation) ->
    task_invocation_active capture.(delete_save_resumed).(TskState) observer (RunningInvocation tid generation) ->
    capture.(delete_save_restore).(delete_restore_between).(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection capture.(delete_save_restore).(delete_restore_between).(TskState)
      capture.(delete_save_resumed).(TskState) tid old.
Proof.
  intros event_observer stored_observer stored_origin capture selected rely stopped window Hreceipt.
  destruct Hreceipt.
  intros observer tid old eid generation Hlife Hactive Hold Hcont.
  eapply sem_pend_delete_joint_window_waiter_projection; eassumption.
Qed.

Lemma sem_pend_delete_call_waiter_projection :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  forall observer tid old eid generation,
    task_observer_lifetime capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
      observer (RunningInvocation tid generation) ->
    task_invocation_active (task_delete_capture_cut capture).(TskState) observer (RunningInvocation tid generation) ->
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    sem_pend_task_projection capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
      (task_delete_capture_cut capture).(TskState) tid old.
Proof.
  intros event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped [Hrestore Hrestore_receipt Hsave Hsave_receipt Hcompleted]
    observer tid old eid generation Hlife Hactive Hold Hcont.
  set (restore := capture.(delete_save_restore)) in *.
  set (inputs := restore.(delete_restore_inputs)) in *.
  assert (Hcontext : task_delete_capture_context inputs.(delete_capture_environment)
    inputs.(delete_capture_critical) inputs.(delete_capture_globals) inputs) by (repeat split; reflexivity).
  pose (Hprepare := @TaskDeleteCPrepare inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) stored_observer stored_origin inputs restore.(delete_restore_before_heap)
    restore.(delete_restore_prepared_heap) Hcontext (task_delete_restore_capture_prepare_completion restore)).
  pose (Hrecycle := @TaskDeleteCRecycle inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) stored_observer stored_origin capture after_heap Hcontext Hcompleted).
  assert (Hprimitive : forall state before input stop returned after output,
    task_delete_primitive_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals) state before input stop returned after output ->
    kernel_program_c_step inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals) stored_observer stored_origin state before input stop returned after output).
  { intros; apply KernelProgramCDeletePrimitive; assumption. }
  pose proof (task_delete_restore_capture_c_window_sequence _ restore restore_selected restore_rely
    restore_stopped Hprimitive Hrestore) as restore_run.
  pose proof (task_delete_save_capture_c_window_sequence _ capture save_selected save_rely
    save_stopped Hprimitive Hsave) as save_run.
  pose proof (sem_pend_program_c_step_lifetime_transport _ _ _ _ _ _ _ _ _ _ _ _
    (@KernelProgramCDelete _ _ _ stored_observer stored_origin _ _ _ _ _ _ _ Hprepare)
    observer (RunningInvocation tid generation) Hlife) as [Hprepared_life Hprepare_back].
  pose proof (sem_pend_delete_interval_lifetime _ _ _ _ _ _ _ _ _ _ _ _ restore_run
    observer (RunningInvocation tid generation) Hprepared_life) as [Hmiddle_life Hrestore_back].
  pose proof (sem_pend_delete_interval_lifetime _ _ _ _ _ _ _ _ _ _ _ _ save_run
    observer (RunningInvocation tid generation) Hmiddle_life) as [Hresumed_life Hsave_back].
  pose proof (sem_pend_program_c_step_lifetime_transport _ _ _ _ _ _ _ _ _ _ _ _
    (@KernelProgramCDelete _ _ _ stored_observer stored_origin _ _ _ _ _ _ _ Hrecycle)
    observer (RunningInvocation tid generation) Hresumed_life) as [Hfinal_life Hrecycle_back].
  pose proof (Hrecycle_back Hactive) as Hresumed_active.
  pose proof (Hsave_back Hresumed_active) as Hmiddle_active.
  pose proof (Hrestore_back Hmiddle_active) as Hprepared_active.
  assert (Hprepared_live : exists live,
    (task_delete_locked inputs.(delete_capture_prepared)).(TskState).(inUsedTaskStates) tid = Some live).
  { destruct Hprepared_active as [_ [_ [live [Hlive _]]]]; eauto. }
  assert (Hfinal_live : exists live, (task_delete_capture_cut capture).(TskState).(inUsedTaskStates) tid = Some live).
  { destruct Hactive as [_ [_ [live [Hlive _]]]]; eauto. }
  destruct (sem_pend_delete_own_c_projection _ _ _ _ _ _ _ _ _ _ _ _ Hprepare
    tid old eid generation Hold Hcont Hprepared_live) as [prepared_node [Hprepared Hfirst]].
  assert (Hprepared_cont : sem_pend_wait_continuation eid generation prepared_node).
  { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
  destruct (sem_pend_delete_restore_window_waiter_projection event_observer stored_observer stored_origin restore
    restore_selected restore_rely restore_stopped Hrestore Hrestore_receipt observer tid prepared_node eid generation
    Hprepared_life Hmiddle_active Hprepared Hprepared_cont) as [middle_node [Hmiddle Hsecond]].
  assert (Hmiddle_cont : sem_pend_wait_continuation eid generation middle_node).
  { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
  destruct (sem_pend_delete_save_window_waiter_projection event_observer stored_observer stored_origin capture
    save_selected save_rely save_stopped Hsave Hsave_receipt observer tid middle_node eid generation
    Hmiddle_life Hresumed_active Hmiddle Hmiddle_cont) as [resumed_node [Hresumed Hthird]].
  assert (Hresumed_cont : sem_pend_wait_continuation eid generation resumed_node).
  { eapply sem_pend_wait_trace_preserves_continuation; eassumption. }
  destruct (sem_pend_delete_own_c_projection _ _ _ _ _ _ _ _ _ _ _ _ Hrecycle
    tid resumed_node eid generation Hresumed Hresumed_cont Hfinal_live) as [node [Hnode Hlast]].
  exists node; split; [exact Hnode|].
  eapply rt_trans; [exact Hfirst|]. eapply rt_trans; [exact Hsecond|].
  eapply rt_trans; eassumption.
Qed.

(** The final association is a consequence of the finite typed calls and
    the actual returning incarnation.  Timeout/Abort/OK remain distinct;
    deleting another task remains possible. *)
Lemma sem_pend_delete_call_return_endpoint :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  forall original returned old eid,
    task_in_range capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals)
      capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState) ->
    kernel_call_task_source original capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired) ->
    task_tcb_init_stack_same_call returned original ->
    kernel_call_task_source returned (task_delete_capture_cut capture) ->
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState).(inUsedTaskStates)
      original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
    sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) old ->
    exists node, (task_delete_capture_cut capture).(TskState).(inUsedTaskStates)
        original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
      node.(taskGeneration) = old.(taskGeneration) /\ node.(tcbEventMultiPtr) = old.(tcbEventMultiPtr) /\
      sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node /\
      (node.(statPend) = PendTimeout -> node.(eventPtr) = Some eid).
Proof.
  intros * source original returned old eid Hrange Hsource Hsame Hreturned Hold Hcont.
  assert (Hlife : task_observer_lifetime
    capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TskState)
    original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); eapply task_observer_lifetime_from_active;
      [exact Hrange|exact (proj1 (proj2 Hsource))]. }
  assert (Hactive : task_invocation_active (task_delete_capture_cut capture).(TskState)
    original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration))).
  { rewrite <- (proj1 Hsource); eapply kernel_call_same_return_observer_active; eassumption. }
  destruct (sem_pend_delete_call_waiter_projection event_observer _ _ _ _ _ _ _ _ _ _ source _ _ old eid _
    Hlife Hactive Hold Hcont) as [node [Hnode Htrace]].
  destruct (sem_pend_delete_call_multi_pointer event_observer _ _ _ _ _ _ _ _ _ _ source _ _ old _
    Hlife Hactive Hold) as [same_node [Hsame_node [Hgen Hptr]]].
  assert (same_node = node) by congruence; subst same_node.
  pose proof (sem_pend_wait_trace_preserves_continuation _ _ _ _ Htrace Hcont) as Hcontinued.
  exists node; split; [exact Hnode|]. split; [exact Hgen|]. split; [exact Hptr|].
  split; [exact Hcontinued|]. eapply sem_pend_wait_continuation_timeout_pointer; exact Hcontinued.
Qed.

(** Public-handle and allocation observations use the actual source
    metadata on that same run.  The waiter receipt alone does not contain
    the allocation actor or lifetime protocol and is not used to guess it. *)
Lemma sem_pend_delete_joint_window_frames :
  forall event_observer environment critical saved_local sg stored_observer stored_origin selected requested rely
    phase loan original before returned after mask before_heap after_heap frame history stopped
    (window : task_delete_joint_c_window environment critical saved_local sg
      (kernel_program_c_step environment critical sg stored_observer stored_origin) selected requested rely
      phase loan original before returned after mask before_heap after_heap frame history stopped),
  sem_pend_delete_joint_window_receipt event_observer environment critical saved_local sg stored_observer stored_origin
    selected requested rely phase loan original before returned after mask before_heap after_heap frame history stopped window ->
  task_creation_frame stored_observer before.(TskState) after.(TskState) /\
  (forall invocation, event_observer = Some invocation -> event_creation_frame invocation before.(EventState) after.(EventState)) /\
  before.(NameState) = after.(NameState) /\ timer_public_trace sg before.(TimerState) after.(TimerState) /\
  tmr_task_live_sem_identity before after.
Proof.
  intros event_observer environment critical saved_local sg stored_observer stored_origin selected requested rely
    phase loan original before returned after mask before_heap after_heap frame history stopped window Hreceipt.
  destruct Hreceipt as [phase loan original before returned after mask before_heap after_heap frame stopped run selection owned
    Hreceipt Hsource].
  destruct (kernel_program_c_sequence_call_source_frames environment critical sg stored_observer stored_origin
    event_observer _ _ _ _ _ _ _ run Hsource) as [Htask [Hevent [Hname Htimer]]].
  split; [exact Htask|]. split; [exact Hevent|]. split; [exact Hname|]. split; [exact Htimer|].
  eapply tmr_task_program_c_sequence_source_preserves_live_sem; exact Hsource.
Qed.

Lemma sem_pend_delete_restore_window_frames :
  forall event_observer stored_observer stored_origin restore selected rely stopped
    (window : task_delete_restore_capture_c_window
      (kernel_program_c_step restore.(delete_restore_inputs).(delete_capture_environment)
        restore.(delete_restore_inputs).(delete_capture_critical) restore.(delete_restore_inputs).(delete_capture_globals)
        stored_observer stored_origin) restore selected rely stopped),
  sem_pend_delete_restore_window_receipt event_observer stored_observer stored_origin restore selected rely stopped window ->
  let before := task_delete_locked restore.(delete_restore_inputs).(delete_capture_prepared) in
  let after := restore.(delete_restore_between) in
  task_creation_frame stored_observer before.(TskState) after.(TskState) /\
  (forall invocation, event_observer = Some invocation -> event_creation_frame invocation before.(EventState) after.(EventState)) /\
  before.(NameState) = after.(NameState) /\
  timer_public_trace restore.(delete_restore_inputs).(delete_capture_globals) before.(TimerState) after.(TimerState) /\
  tmr_task_live_sem_identity before after.
Proof.
  intros event_observer stored_observer stored_origin restore selected rely stopped window Hreceipt.
  destruct Hreceipt; eapply sem_pend_delete_joint_window_frames; eassumption.
Qed.

Lemma sem_pend_delete_save_window_frames :
  forall event_observer stored_observer stored_origin capture selected rely stopped
    (window : task_delete_save_capture_c_window (task_delete_program_segment stored_observer stored_origin capture)
      capture selected rely stopped),
  sem_pend_delete_save_window_receipt event_observer stored_observer stored_origin capture selected rely stopped window ->
  let before := capture.(delete_save_restore).(delete_restore_between) in
  let after := capture.(delete_save_resumed) in
  task_creation_frame stored_observer before.(TskState) after.(TskState) /\
  (forall invocation, event_observer = Some invocation -> event_creation_frame invocation before.(EventState) after.(EventState)) /\
  before.(NameState) = after.(NameState) /\
  timer_public_trace capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals)
    before.(TimerState) after.(TimerState) /\ tmr_task_live_sem_identity before after.
Proof.
  intros event_observer stored_observer stored_origin capture selected rely stopped window Hreceipt.
  destruct Hreceipt; eapply sem_pend_delete_joint_window_frames; eassumption.
Qed.

Lemma sem_pend_delete_call_frames :
  forall event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped,
  sem_pend_delete_call_source event_observer stored_observer stored_origin capture after_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped ->
  let inputs := capture.(delete_save_restore).(delete_restore_inputs) in
  let before := inputs.(delete_capture_acquired) in
  let after := task_delete_capture_cut capture in
  task_creation_frame stored_observer before.(TskState) after.(TskState) /\
  (forall invocation, event_observer = Some invocation -> event_creation_frame invocation before.(EventState) after.(EventState)) /\
  before.(NameState) = after.(NameState) /\
  timer_public_trace inputs.(delete_capture_globals) before.(TimerState) after.(TimerState) /\
  tmr_task_live_sem_identity before after.
Proof.
  intros event_observer stored_observer stored_origin capture after_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped [Hrestore Hrestore_receipt Hsave Hsave_receipt Hcompleted] inputs before after.
  pose proof (task_delete_restore_capture_prepare_completion capture.(delete_save_restore)) as Hprepare.
  destruct (TaskDeletePhaseFrames.task_delete_prepare_c_creation_name_timer_frames _ _ _ Hprepare)
    as [Htask0 [Hevent0 [Hname0 Htimer0]]].
  destruct (sem_pend_delete_restore_window_frames event_observer stored_observer stored_origin _ _ _ _ Hrestore Hrestore_receipt)
    as [Htask1 [Hevent1 [Hname1 [Htimer1 Hsem1]]]].
  destruct (sem_pend_delete_save_window_frames event_observer stored_observer stored_origin _ _ _ _ Hsave Hsave_receipt)
    as [Htask2 [Hevent2 [Hname2 [Htimer2 Hsem2]]]].
  destruct (TaskDeletePhaseFrames.task_delete_recycle_c_creation_name_timer_frames capture)
    as [Htask3 [Hevent3 [Hname3 Htimer3]]].
  assert (Hsem0 : tmr_task_live_sem_identity before (task_delete_locked inputs.(delete_capture_prepared))).
  { destruct Hprepare as [[Hlive [Hstep Hprotocol]] Howned Hprepared].
    change (tmr_task_live_sem_identity inputs.(delete_capture_acquired) inputs.(delete_capture_prepared)).
    eapply tmr_task_delete_prepare_preserves_live_sem; exact Hstep. }
  assert (Hsem3 : tmr_task_live_sem_identity capture.(delete_save_resumed) after).
  { apply tmr_task_event_state_eq_preserves_live_sem; reflexivity. }
  unfold before, after, inputs in *.
  split.
  - specialize (Htask0 stored_observer); specialize (Htask3 stored_observer).
    unfold task_creation_frame in *; congruence.
  - split.
    + intros invocation Hobserver; specialize (Hevent0 invocation); specialize (Hevent3 invocation).
      specialize (Hevent1 invocation Hobserver); specialize (Hevent2 invocation Hobserver).
      unfold event_creation_frame in *; congruence.
    + split; [congruence|]. split.
      * change (timer_public_trace capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_globals)
          capture.(delete_save_restore).(delete_restore_inputs).(delete_capture_acquired).(TimerState)
          (task_delete_capture_cut capture).(TimerState)).
        rewrite Htimer0, <- Htimer3; eapply timer_public_trace_trans; eassumption.
      * eapply tmr_task_live_sem_identity_trans; [exact Hsem0|].
        eapply tmr_task_live_sem_identity_trans; [exact Hsem1|].
        eapply tmr_task_live_sem_identity_trans; eassumption.
Qed.
