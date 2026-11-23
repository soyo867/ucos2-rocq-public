Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_status Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_clear_status_wait_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_source_acquire_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_program_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_sem_source_projection_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_call_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_c_segment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_masked_c_step_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_return_source_spec.
Import TaskStateDef ListNotations DeleteComponent.
Local Open Scope Z_scope.

(** This observation allows suspension. It records the same caller's actual
    status bits; empty Event/Flag pointers alone do not establish it. *)
Definition sem_pend_caller_status_clear (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  forall node, state.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    task_non_suspension_bits node.(stat) = 0.

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

(** Every constructor is the original receipt of this same action and
    step. This proof does not infer a receipt from a resource trace. *)
Lemma sem_pend_source_call_receipt_preserves_clear_status : forall external action sg before after,
  tmr_task_source_call_receipt external action sg before after -> UCOS2_state_inv sg before ->
  sem_pend_status_clear_transport before after.
Proof.
  intros external action sg before after Hcall Hvalid.
  destruct Hcall as [action0 sg0 before0 after0 Hnontimer Hstep|cut sg0 before0 after0 Hstep|
    actor requested priority sg0 before0 after0 Hstep|actor pointer bits result sg0 before0 after0 Hstep|
    actor event kind message result sg0 before0 after0 Hinput Hstep|slot previous sg0 before0 after0 Hstep|
    context outgoing incoming resumed sg0 before0 after0 Hstep|action0 sg0 before0 after0 Hsem Hstep|
    action0 sg0 before0 after0 Hcritical Hstep|actor cut sg0 before0 after0 Hstep|
    actor cut sg0 before0 after0 Hstep|actor source_sg cut entry timers sg0 before0 after0 Hstep|
    actor event option result sg0 before0 after0 Hstep|
    actor source_sg priority result entry returned sg0 before0 after0 Hstep].
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_nontimer_projection; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_profile_projection; eassumption.
  - destruct Hstep as [code Hchange].
    apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_change_prio_projection; eassumption.
  - destruct Hstep as [schedule Hready].
    destruct (flag_task_rdy_result _ _ _ _ _ _ _ Hready)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply sem_pend_source_update_preserves_clear_status; [exact Hold|reflexivity|].
    intro Hclear.
    change (task_non_suspension_bits (task_clear_pending_status old.(stat) PendFlag) = 0).
    rewrite task_clear_pending_status_none by exact Hclear; exact Hclear.
  - destruct Hstep as [priority Hready].
    eapply sem_pend_source_event_ready_preserves_clear_status; exact Hready.
  - destruct Hstep as [Hold ->].
    apply sem_pend_source_projection_preserves_clear_status; intros tid node Hnode.
    eapply sem_pend_tick_task_projection; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply sem_pend_source_client_projection; [apply SemPendSourceSchedulerInstall|exact Hstep|exact Hold].
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply sem_pend_source_client_projection;
      [apply tmr_task_sem_source_client_wait_projection; exact Hsem|exact Hstep|exact Hold].
  - eapply sem_pend_source_critical_preserves_clear_status; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    exact (tmr_task_sem_tick_projection _ cut _ _ _ _ Hstep Hold).
  - destruct Hstep as [timers [_ ->]]; apply sem_pend_status_clear_transport_map_eq; reflexivity.
  - destruct Hstep as [_ [_ [_ ->]]]; apply sem_pend_status_clear_transport_map_eq; reflexivity.
  - destruct Hstep as [node [_ [_ Habort]]].
    apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply sem_pend_abort_critical_projection; eassumption.
  - apply sem_pend_source_projection_preserves_clear_status; intros slot old Hold.
    eapply tmr_task_sem_suspend_projection; eassumption.
Qed.

Lemma sem_pend_client_source_calls_preserves_clear_status :
  forall external port critical sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port critical.(critical_region_clients)
      sg observer event_observer first before stopped last after),
  sem_pend_client_source_calls external port critical.(critical_region_clients)
    sg observer event_observer first before stopped last after trace ->
  UCOS2_state_inv sg before -> sem_pend_status_clear_transport before after.
Proof.
  intros external port critical sg observer event_observer first before stopped last after trace Hcalls.
  induction Hcalls as [origin state|action first before middle transient last after stopped
    Hin Hforeign Hevent Hstep Hsource Htail Hcall Hcalls IH]; intro Hvalid.
  - apply sem_pend_status_clear_transport_map_eq; reflexivity.
  - eapply sem_pend_status_clear_transport_trans.
    + eapply sem_pend_source_call_receipt_preserves_clear_status; eassumption.
    + apply IH. exact (kernel_client_preserves_validity action
        (critical.(critical_region_client_certificates) action Hin) sg before transient Hvalid Hstep).
Qed.

Lemma sem_pend_observed_caller_clear_status :
  forall external port critical sg observer event_observer first before stopped last after,
  sem_pend_observed_client_trace external port critical.(critical_region_clients) sg
    observer event_observer first before stopped last after ->
  stopped = false -> UCOS2_state_inv sg before ->
  forall tid generation old,
  task_invocation_active before.(TskState) observer (RunningInvocation tid generation) ->
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  task_non_suspension_bits old.(stat) = 0 ->
  exists current, after.(TskState).(inUsedTaskStates) tid = Some current /\
    task_non_suspension_bits current.(stat) = 0.
Proof.
  intros external port critical sg observer event_observer first before stopped last after Htrace.
  induction Htrace as [first before stopped last after trace Hcalls
    |action first before last after Hmember Htyped Hevent Hstep Hcontrol Hreceipt
    |irq_environment irq_critical first before before_heap input last after after_heap output
      Hexternal Hport Hclients Hcompletion
    |entry_environment first initial node handler suspended publication local frame
      entry_heap saved_heap body_heap Hexternal Hport Hentry
    |post_environment post_critical source_env post_local post_frame post_call
      before_heap after_heap post_origin Hsegment Hexternal Hport Hclients Hreceipt
    |inherit_environment inherit_critical inherit_local inherit_frame inherit_call
      before_heap after_heap inherit_origin Hsegment Hexternal Hport Hclients
    |suspend_environment suspend_critical suspend_local suspend_caller suspend_saved suspend_call
      suspend_frame before_heap after_heap suspend_origin Hcompletion Hexternal Hport Hclients
    |install_environment install_local install_frame install_call before_heap after_heap sp Hactual
      Hsegment Hexternal Hport
    |stored_origin capture body_heap restore_selected restore_rely save_selected save_rely
      restore_stopped save_stopped Hdelete_source Hexternal Hport Hclients Hsg Hregistered
    |first before stopped1 middle transient stopped2 last after Hfirst IHfirst Hlast IHlast];
    intros Hstop Hvalid tid generation old Hactive Hold Hclear.
  - exact (sem_pend_client_source_calls_preserves_clear_status _ _ critical _ _ _ _ _ _ _ _
      trace Hcalls Hvalid tid old Hold Hclear).
  - exact (sem_pend_source_call_receipt_preserves_clear_status _ _ _ _ _
      Hreceipt Hvalid tid old Hold Hclear).
  - exists old; split; [|exact Hclear].
    rewrite (sem_pend_irq_cut_tasks _ _
      (sem_pend_irq_completion_source_frame _ _ _ _ _ _ _ _ _ _ _ Hcompletion)); exact Hold.
  - destruct (sem_pend_irq_entry_task_at _ _ _ _ _ _ _ _ _ _ _ _ Hentry tid old Hold)
      as [current [Hcurrent Hfields]].
    pose proof (f_equal stat Hfields) as Hstatus.
    change (current.(stat) = old.(stat)) in Hstatus.
    exists current; split; [exact Hcurrent|]. rewrite Hstatus; exact Hclear.
  - pose proof (sem_pend_delete_mutex_post_clear_status _ _ _ _ _ _ _
      (proj2 (PostComponent.mutex_post_critical_segment_source source_env
      post_environment.(task_stack_call_external) post_environment.(task_stack_call_platform)
      post_critical post_local sg post_frame post_call before_heap after_heap Hsegment))) as Htransport.
    exact (Htransport tid old Hold Hclear).
  - pose proof (sem_pend_delete_mutex_inheritance_clear_status sg inherit_call
      (PendComponent.mutex_pend_inheritance_segment_source inherit_environment inherit_critical
        inherit_local sg inherit_frame inherit_call before_heap after_heap Hsegment)) as Htransport.
    exact (Htransport tid old Hold Hclear).
  - pose proof (TaskSuspendMaskedC.suspend_masked_source _ _ _ _ _ _ _ _ _ _ Hcompletion)
      as [_ Hcode].
    destruct (sem_pend_suspend_step_projection _ _ _ _ _ _ _ Hcode tid old Hold)
      as [current [Hcurrent Hsteps]].
    exists current; split; [exact Hcurrent|].
    eapply sem_pend_wait_trace_preserves_clear_status; eassumption.
  - destruct Hsegment as [Hsource Hcompletion].
    destruct (os_sched_install_client_state_frame _ _ _ _ _ sg _ _ Hsource) as [Hmap _].
    exists old; split; [rewrite Hmap; exact Hold|exact Hclear].
  - assert (Horigin : stored_origin = RunningInvocation tid generation).
    { pose proof (proj1 Hactive) as Hactual_registered; congruence. }
    subst stored_origin.
    eapply sem_pend_delete_call_clear_status.
    + exact Hdelete_source.
    + eapply task_observer_lifetime_from_active with (sg := sg);
        [exact (proj1 (proj2 Hvalid))|exact Hactive].
    + eapply sem_pend_delete_capture_body_preserves_active; eassumption.
    + exact Hold.
    + exact Hclear.
  - apply orb_false_iff in Hstop; destruct Hstop as [Hstop1 Hstop2].
    destruct (sem_pend_observed_client_trace_resources _ _ _ _ _ _ _ _ _ _ _
      critical.(critical_region_client_certificates) Hfirst Hvalid) as [Hvalid' [_ [_ Hlive]]].
    destruct (IHfirst Hstop1 Hvalid tid generation old Hactive Hold Hclear)
      as [middle_node [Hmiddle Hclear_middle]].
    exact (IHlast Hstop2 Hvalid' tid generation middle_node
      (Hlive Hstop1 (RunningInvocation tid generation) Hactive) Hmiddle Hclear_middle).
Qed.

Lemma sem_pend_client_return_preserves_clear_status : forall environment critical sg call before returned after,
  sem_pend_client_return_source environment critical sg call before returned after ->
  UCOS2_state_inv sg before -> kernel_call_task_source call before ->
  sem_pend_caller_status_clear call before -> sem_pend_caller_status_clear returned after.
Proof.
intros environment critical sg call before returned after Hreturn Hvalid Hsource Hclear.
  pose proof (sem_pend_client_return_source_same_call _ _ _ _ _ _ _ Hreturn) as [_ [_ Hstack]].
  destruct (kernel_call_task_source_current_at call before Hsource) as [Hcurrent [old [Hold Hg]]].
  destruct Hsource as [Horigin [Hactive Hcurrent_before]]; rewrite Horigin in Hactive.
  destruct Hreturn as [Htrace Hnormal].
  destruct (sem_pend_observed_caller_clear_status environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call.(os_sched_call_invocation) None
    call.(os_sched_call_origin) before false returned.(os_sched_call_origin) after Htrace eq_refl Hvalid
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration)
    old Hactive Hold (Hclear old Hold)) as [node [Hnode Hbits]].
  intros actual Hactual; rewrite Hstack in Hactual.
  assert (actual = node) by congruence; subst actual; exact Hbits.
Qed.

(** The real wait update needs clear pending bits, not ready membership.
    The raw helper, its layouts and exact same-node heap remain unchanged. *)
Definition sem_pend_clear_status_wait_entry sg entry eid current tid old : Prop :=
  UCOS2_state_inv sg entry /\ encode_event_cnt_value current = 0 /\
  entry.(SchedState).(curTaskID) = Some tid /\
  entry.(TskState).(inUsedTaskStates) tid = Some old /\
  mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
  old.(curPrio) <> sg.(osLowestPrio) /\ old.(eventPtr) = None /\
  old.(eventMultiWaitEvents) = [] /\ old.(tcbFlagNode) = 0 /\
  task_non_suspension_bits old.(stat) = 0 /\ event_object_layout_prop sg eid.

Lemma sem_pend_clear_status_wait_entry_first_critical : forall sg entry eid current tid old timeout,
  sem_pend_clear_status_wait_entry sg entry eid current tid old ->
  sem_pend_first_critical sg eid timeout entry (SemPendWaiting tid old.(taskGeneration))
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * [Hvalid [Hcount [Hcur [Hold [He [Htype Hrest]]]]]].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current He); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  unfold encode_event_cnt_value in Hcount; rewrite Htype, Hfields in Hcount.
  exists current, fields; split; [exact He|]; split; [exact Hfields|].
  rewrite Hcount; cbn; exists tid, old; repeat split; assumption || reflexivity.
Qed.

Lemma sem_pend_clear_status_wait_entry_preserves_validity : forall sg entry eid current tid old timeout,
  sem_pend_clear_status_wait_entry sg entry eid current tid old ->
  UCOS2_state_inv sg (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * [Hvalid [Hcount [Hcur [Hold [He [Htype [Hnonidle [Hnone [Hmulti [Hflag [Hclear Hlayout]]]]]]]]]]].
  pose proof Hvalid as [_ [Htasks [_ [Hevents _]]]].
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriorities _]]]]]]]].
  pose proof (Hpriorities tid old Hold) as Hrange.
  assert (Hprio : valid_task_prio sg old.(curPrio))
    by (unfold valid_task_prio, task_priority_in_range in *; lia).
  assert (Hunavailable : event_wait_resource_unavailable current).
  { pose proof Hevents as [_ [_ [_ [_ [Hpayload _]]]]].
    specialize (Hpayload eid current He); unfold event_payload_consistency in Hpayload.
    unfold event_wait_resource_unavailable; rewrite Htype in Hpayload |- *.
    destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
    unfold encode_event_cnt_value in Hcount; rewrite Htype, Hfields in Hcount; exact Hcount. }
  eapply event_pend_preserves_validity_from_clear_status; try eassumption.
  - rewrite Htype; reflexivity.
  - intros; congruence.
Qed.

Lemma sem_pend_clear_status_wait_continuation : forall eid old timeout,
  task_non_suspension_bits old.(stat) = 0 -> old.(eventMultiWaitEvents) = [] -> old.(tcbFlagNode) = 0 ->
  sem_pend_wait_continuation eid old.(taskGeneration)
    (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)).
Proof.
  intros eid old timeout Hclear Hmulti Hflag.
  split; [reflexivity|]. split; [exact Hmulti|]. split; [exact Hflag|].
  left; split; [reflexivity|]. left; apply task_prepare_event_wait_pending_bits; exact Hclear.
Qed.
