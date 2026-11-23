From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_client_entry_return_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_selected_sched_signal_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_signal_lifetime_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_task_scheduler_adapter_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.interrupt.
Import UCOS2_C_Rules.
Import SchedulerPhaseCandidate FlagPendSchedulerResources PrimitiveComponent.
Local Open Scope sac_scope.

(** The old generic Scheduler admission includes Idle readiness but permits
    an Idle caller. This Timer-specific call also carries the real caller's
    non-Idle observation, already present at the enclosing Task entry. *)
Definition tmr_task_sched_entry_pre environment critical local active sg call mask state : Assertion :=
  coq_prop (flag_pend_non_idle_at sg call state) &&
  os_sched_unlock_task_scheduler_pre environment critical local active sg call mask state.

Lemma tmr_task_unlock_entry_sched_observations : forall sg call state,
  UCOS2_state_inv sg state -> tmr_task_unlock_entry sg call state ->
  task_idle_ready sg state.(TskState) /\ flag_pend_non_idle_at sg call state.
Proof.
  intros sg call state Hvalid Hentry.
  destruct (tmr_task_unlock_entry_invariants sg call state Hvalid Hentry)
    as [Hcurrent [Hidle [Hclear Hready]]].
  exact (proj2 (proj2 Hidle)).
Qed.

(** Consume the actual Restore once, after the body's producer has retained
    Idle and the returning caller's identity. The endpoint packet belongs
    to that very execution; proving its source remains the Restore producer's
    obligation, not a new assumption on the enclosing Task API. *)
Lemma tmr_task_scoped_restore_history_entry_post :
  forall environment critical sg original scheduled resumed returned mask saved before entry released current
    save_local saved_local active first_heap save_stop acquired_heap
    restore_local next_local released_heap restore_stop final_heap,
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_save_execution environment critical
    save_local saved_local active sg original mask before first_heap saved save_stop scheduled entry acquired_heap ->
  os_sched_task_save_observation environment critical sg original mask saved before scheduled entry ->
  kernel_call_task_source scheduled entry ->
  os_sched_task_body_observation environment critical sg scheduled entry resumed released ->
  tmr_task_signal_lifetime critical sg resumed.(os_sched_call_invocation) released ->
  task_idle_ready sg released.(TskState) -> flag_pend_non_idle_at sg resumed released ->
  SelectedEnvironmentPhaseEffects.os_sched_continuation_c_restore_execution environment critical
    restore_local next_local active sg resumed saved entry released released_heap restore_stop returned current final_heap ->
  os_sched_task_restore_observation environment critical sg resumed released returned current ->
  tmr_task_sched_history_entry_post environment critical active sg original mask before final_heap.
Proof.
  intros until final_heap; intros Hsave Hsave_observation Hscheduled Hbody Hlife Hidle Hnonidle
    Hrestore Hrestore_observation.
  destruct (SelectedEnvironmentPhaseProperties.os_sched_continuation_c_restore_execution_resources
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrestore) as [Hinput [Hendpoints Houtput]].
  pose proof (proj1 (flag_pend_caller_restore_input_state_inv environment critical restore_local active sg
    (FlagPendTaskCaller resumed) resumed saved entry released released_heap Hinput)) as Hvalid.
  pose proof (proj2 (proj2 (proj2 (proj2 Hbody))) Hscheduled) as Hresumed.
  cbn [flag_pend_call_endpoint_observations] in Hendpoints.
  destruct Hendpoints as [_ [Hidle_return [Hnonidle_return Hremaining]]].
  specialize (Hidle_return (conj Hresumed Hidle)).
  specialize (Hnonidle_return (conj Hresumed Hnonidle)).
  pose proof (os_sched_task_observations_compose environment critical sg original scheduled resumed returned
    mask saved before entry released current Hsave_observation Hbody Hrestore_observation Hvalid)
    as [_ Hfacts].
  destruct (tmr_task_sched_scoped_return_signal environment critical sg original scheduled resumed returned
    mask saved before entry released current save_local saved_local active first_heap save_stop acquired_heap
    restore_local next_local released_heap restore_stop final_heap Hsave Hbody Hlife Hrestore)
    as [Hhistory [Hsignal Hcontinue]].
  assert (Hmask : armv7a_irq_fiq_mask saved = mask).
  { destruct Hsave_observation as [_ [_ [Hsaved _]]]; exact (proj2 Hsaved). }
  pose proof (proj1 (flag_pend_task_save_input_closed_equiv environment critical next_local active sg
    returned (armv7a_irq_fiq_mask saved) current) final_heap Houtput) as Hclosed.
  rewrite Hmask in Hclosed.
  exists returned, current, next_local; split; [|exact Hclosed].
  exact (conj (conj (conj Hhistory Hfacts) Hsignal) (conj Hidle_return Hnonidle_return)).
Qed.

Lemma tmr_task_sched_entry_pre_implies_ordinary :
  forall environment critical local active sg call mask state,
  tmr_task_sched_entry_pre environment critical local active sg call mask state |--
  os_sched_unlock_task_scheduler_pre environment critical local active sg call mask state.
Proof.
  intros environment critical local active sg call mask state heap [Hnonidle Hpre]; exact Hpre.
Qed.

(** Produce this observation at the actual Restore cut, using its original
    same-call source intervals and original input validity. No fact about an
    unobserved future Scheduler return is added to a public precondition. *)
Lemma tmr_task_unlock_fields_scheduler_entry_pre :
  forall environment critical local sg original mask before acquired restored unlocked X,
  tmr_task_unlock_call_facts environment critical sg original mask before X ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_requests acquired = true ->
  os_sched_fields_closed environment local sg restored mask unlocked |--
  tmr_task_sched_entry_pre environment critical local
    (PendPhaseCandidate.flag_pend_fresh_observation restored) sg restored mask unlocked.
Proof.
  intros environment critical local sg original mask before acquired restored unlocked X
    Hcalls Hfacts Hrequest.
  pose proof Hcalls as [Hentry [Hclients [Hsafe [Hready [Hlayout Hvalid]]]]].
  destruct (tmr_task_unlock_entry_sched_observations sg original before Hvalid Hentry)
    as [Hidle Hnonidle].
  destruct Hclients as [Hcurrent_clients [Hidle_clients Hclear_clients]].
  destruct (os_sched_unlock_fields_prefix_idle_non_idle environment critical sg original mask
    before acquired restored unlocked Hidle_clients Hfacts Hvalid Hidle Hnonidle)
    as [Hidle_return Hnonidle_return].
  intros heap Howned; split; [exact Hnonidle_return|].
  exact (tmr_task_unlock_fields_fresh_scheduler_pre environment critical local sg original mask
    before acquired restored unlocked X Hcalls Hfacts Hrequest heap Howned).
Qed.
