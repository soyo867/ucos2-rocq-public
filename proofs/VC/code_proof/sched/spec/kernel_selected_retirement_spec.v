Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_c_step_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module SelectedRetirementTransport.
Import CriticalComponent PrimitiveComponent SelectedCProgram SelectedReturnPrimitive.
Import BuiltinComponent InstallComponent WakeComponent StatusComponent CreationComponent.
Import EventCreationComponent QueueCreationComponent PendComponent PostComponent DeleteComponent.
Import IRQSelectedCompletion IRQAcquiredReturn TaskSuspendActualC TaskSuspendMaskedC.

Definition task_unretired_transport (before after : Glob_TaskAbstractState) : Prop :=
  forall invocation, before.(taskLifecycle).(taskRetiredInvocations) invocation = false ->
    after.(taskLifecycle).(taskRetiredInvocations) invocation = false.

Lemma task_change_prio_critical_preserves_unretired :
  forall sg requested priority before code after,
  task_change_prio_critical sg requested priority before code after ->
  task_unretired_transport before.(TskState) after.(TskState).
Proof.
  intros sg requested priority before code after Hstep.
  unfold task_change_prio_critical in Hstep.
  destruct (before.(TskState).(prioTbl) priority).
  - destruct Hstep as [selected [Hselected Hstep]].
    unfold task_change_prio_selected_effect in Hstep.
    destruct (Z.eqb selected sg.(osLowestPrio)).
    + destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
    + destruct (before.(TskState).(prioTbl) selected).
      * destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
      * destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
      * destruct Hstep as [node [Hnode [_ ->]]]; intros invocation Hret; exact Hret.
  - destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
  - destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
Qed.

Lemma kernel_critical_c_source_preserves_unretired : forall sg call,
  kernel_critical_c_source sg call ->
  task_unretired_transport (kernel_critical_c_entry call).(TskState)
    (kernel_critical_c_returned call).(TskState).
Proof.
  intros sg [call|call] Hsource; cbn in Hsource |- *.
  - destruct Hsource as [error [Hcode Hresult]].
    eapply task_change_prio_critical_preserves_unretired; exact Hcode.
  - destruct (mutex_del_critical_call_observation_fields _ _ _ _ _ _ _ _ Hsource)
      as [[Hnodes [Hstacks [Hlife Hrest]]] Hother].
    intros invocation Hret; unfold task_unretired_transport in *; rewrite Hlife; exact Hret.
Qed.

Lemma kernel_wake_c_source_preserves_unretired : forall sg entry returned,
  kernel_wake_c_source sg entry returned ->
  task_unretired_transport entry.(TskState) returned.(TskState).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    intros invocation Hret; exact Hret.
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    intros invocation Hret; exact Hret.
  - rewrite (tick_task_step_task_state_eq sg slot old entry H).
    intros invocation Hret; exact Hret.
Qed.

Lemma kernel_task_creation_c_source_preserves_unretired : forall sg entry returned,
  kernel_task_creation_c_source sg entry returned ->
  task_unretired_transport entry.(TskState) returned.(TskState).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - intros retired_observer Hret; unfold task_begin_invocation; simpl.
    destruct Nat.eq_dec; [reflexivity|exact Hret].
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; intros retired_observer Hret; exact Hret.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; intros retired_observer Hret; exact Hret.
  - destruct H2 as [_ ->]; intros retired_observer Hret; exact Hret.
  - intros retired_observer Hret; exact Hret.
  - intros retired_observer Hret; exact Hret.
  - intros retired_observer Hret; exact Hret.
Qed.

Lemma kernel_status_c_source_preserves_unretired : forall sg entry returned,
  kernel_status_c_source sg entry returned ->
  task_unretired_transport entry.(TskState) returned.(TskState).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
    + destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
    + destruct Hstep as [old [Hold [_ ->]]]; intros invocation Hret; exact Hret.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
    + destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat));
        destruct Hstep as [_ ->]; intros invocation Hret; exact Hret.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount));
      intros invocation Hret; exact Hret.
Qed.

Lemma kernel_builtin_c_segment_preserves_unretired :
  forall environment critical local sg state before returned after input output,
  kernel_builtin_c_segment environment critical local sg state before returned after input output ->
  task_unretired_transport state.(TskState) returned.(TskState).
Proof.
  intros until output; intro Hsegment; destruct Hsegment.
  - destruct operation; intros invocation Hret; exact Hret.
  - destruct (task_create_stack_publication_raw_projection sg publication state
      (task_create_stack_publication_state sg publication state) effect) as [Hraw Heq].
    rewrite Heq; destruct Hraw as [Hguard [Hnames Hraw_eq]]; rewrite Hraw_eq.
    intros invocation Hret; exact Hret.
  - pose proof (kernel_irq_transfer_c_completion_source _ _ _ _ _ _ _ _ _ _ H) as Hsource.
    destruct (os_int_exit_configured_transfer_state_frame _ _ _ _ _ Hsource)
      as [Hlookup [Hlife Hrest]].
    intros invocation Hret; rewrite Hlife; exact Hret.
Qed.

Lemma task_delete_own_c_segment_preserves_unretired :
  forall environment critical sg observer origin state before input stopped returned after output,
  task_delete_own_c_segment environment critical sg observer origin
    state before input stopped returned after output ->
  task_unretired_transport state.(TskState) returned.(TskState).
Proof.
  intros until output; intro Hsegment.
  destruct Hsegment as [inputs before_heap prepared_heap Hcontext Hcomplete|
    capture after_heap Hcontext Hcomplete].
  - destruct Hcomplete as [[Hlive [Hprepare Hprotocol]] Hbefore Hafter].
    pose proof (proj1 (TaskDeleteCompletedMacro.task_delete_prepare_single_wait_metadata_frame
      _ _ _ _ _ Hprepare)) as Hlife.
    intros invocation Hret; change
      ((delete_capture_prepared inputs).(TskState).(taskLifecycle).(taskRetiredInvocations) invocation = false).
    rewrite Hlife; exact Hret.
  - intros invocation Hret; exact Hret.
Qed.

Lemma kernel_program_c_step_preserves_unretired :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_program_c_step environment critical sg observer origin state before input stopped returned after output ->
  task_unretired_transport state.(TskState) returned.(TskState).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - destruct H as [complete [physical [source packet]]].
    eapply kernel_critical_c_source_preserves_unretired; exact source.
  - eapply kernel_builtin_c_segment_preserves_unretired; exact H.
  - destruct H; intros invocation Hret; exact Hret.
  - eapply kernel_wake_c_source_preserves_unretired.
    eapply kernel_wake_c_segment_source; exact H.
  - destruct H as [Hcode Hbefore Hafter].
    eapply kernel_status_c_source_preserves_unretired; exact Hcode.
  - eapply kernel_task_creation_c_source_preserves_unretired.
    eapply kernel_task_creation_c_segment_source; exact H.
  - pose proof (kernel_event_creation_c_segment_source _ _ _ _ _ _ _ H) as Hsource.
    destruct (kernel_event_creation_c_source_fields_eq _ _ Hsource) as [Htasks Hsched].
    rewrite Htasks; intros invocation Hret; exact Hret.
  - pose proof (kernel_queue_creation_c_segment_source _ _ _ _ _ _ _ H) as Hsource.
    destruct (kernel_queue_creation_c_source_fields_eq _ _ _ Hsource) as [Htasks Hsched].
    rewrite Htasks; intros invocation Hret; exact Hret.
  - destruct H as [[Hnode [Hother Hcode]] Hbefore Hafter].
    destruct (mutex_pend_inherit_call_fields_eq _ _ _ _ _ _ _ _ Hcode) as [Hlife Hrest].
    intros invocation Hret; rewrite Hlife; exact Hret.
  - destruct H as [[Hcaller Hcode] Hbefore Hafter].
    destruct (mutex_post_critical_observer_fields _ _ _ _ _ _ _ Hcode) as [Hlife Hrest].
    intros invocation Hret; rewrite Hlife; exact Hret.
  - destruct H; intros invocation Hret; exact Hret.
  - destruct H; try (intros invocation Hret; exact Hret).
    destruct H; intros invocation Hret; exact Hret.
  - eapply task_delete_own_c_segment_preserves_unretired; exact H.
Qed.

Lemma kernel_program_return_c_step_preserves_unretired :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_program_return_c_step environment critical sg observer origin
    state before input stopped returned after output ->
  task_unretired_transport state.(TskState) returned.(TskState).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_c_step_preserves_unretired; exact H.
  - destruct H; intros invocation Hret; exact Hret.
  - intros invocation Hret; exact Hret.
  - intros invocation Hret; exact Hret.
Qed.

Lemma kernel_program_selected_c_step_preserves_unretired :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_program_selected_c_step environment critical sg observer origin
    state before input stopped returned after output ->
  task_unretired_transport state.(TskState) returned.(TskState).
Proof.
  intros until output; intro Hstep; destruct Hstep.
  - eapply kernel_program_return_c_step_preserves_unretired; exact H.
  - destruct H.
    pose proof (os_int_exit_configured_transfer_state_frame _ _ _ _ _ source)
      as [Hlookup [Hlife Hrest]].
    intros invocation Hret; rewrite Hlife; exact Hret.
  - destruct H; destruct H as [[Hread Hcode] Hbefore Hafter].
    destruct (task_suspend_step_state_cases _ _ _ _ _ _ _ Hcode)
      as [->|[slot [node [Hnode ->]]]]; intros invocation Hret; exact Hret.
Qed.

Lemma kernel_program_selected_c_sequence_preserves_unretired :
  forall environment critical sg observer origin state before input stopped returned after output,
  kernel_c_sequence (kernel_program_selected_c_step environment critical sg observer origin)
    state before input stopped returned after output ->
  task_unretired_transport state.(TskState) returned.(TskState).
Proof.
  intros until output; intro Hrun; induction Hrun.
  - intros invocation Hret; exact Hret.
  - eapply kernel_program_selected_c_step_preserves_unretired; exact H.
  - intros invocation Hret; apply IHHrun2, IHHrun1; exact Hret.
  - exact IHHrun.
Qed.

End SelectedRetirementTransport.

