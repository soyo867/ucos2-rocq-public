Require Export Ucos2Verify.VC.code.tick.spec.time_tick_hook_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_api_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The counter must be a real exclusive cell owned by this invocation.
    This is a spatial impossibility lemma, not an assumption that any
    reentrant Tick happens to preserve a shared counter. *)
Lemma time_tick_hook_counter_exclusive : forall address first second,
  address # UShort |-> first ** address # UShort |-> second |-- coq_prop False.
Proof.
  intros; unfold store_ushort, UCOS2_Base_Rules.store_ushort; pureIntros.
  sep_apply_l_atomic (dup_store_2bytes address first second); entailer!.
Qed.

(** Reassemble the existing generic call input from the actual masked
    caller heap. The borrowed outer inside token stays in frame; execution
    view ownership and the immutable lookup table are supplied physically.
    This rule does not turn a generic interval into an identity. *)
Lemma time_tick_hook_masked_frame_from_owned : forall environment critical saved_local
  sg view region_entry counter_address counter before,
  UCOS2_state_inv sg before ->
  counter_address # UShort |-> counter **
  UCOS2_inv sg before **
  interrupt_platform_running environment.(task_stack_call_platform)
    view.(os_execution_invocation) view.(os_execution_origin) 192 **
  os_execution_view_resources environment.(task_stack_call_external) view **
  unmap_table_rep sg **
  critical_region_inside critical sg view.(os_execution_invocation) region_entry |--
  time_tick_hook_frame environment critical saved_local sg (ResumeGenericCaller view) 192
    counter_address counter before **
  critical_region_inside critical sg view.(os_execution_invocation) region_entry.
Proof.
  intros environment critical saved_local sg view region_entry counter_address counter before Hvalid.
  unfold time_tick_hook_frame.
  rewrite (q_post_closed_equiv environment critical saved_local sg
    (ResumeGenericCaller view) 192 before Hvalid).
  cbn [q_post_outside_frame]; entailer!.
Qed.

Lemma time_tick_hook_sem_critical_control : forall sg eid before result after,
  sem_post_critical sg eid before result after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  after.(IntrState) = before.(IntrState).
Proof.
  intros sg eid before result after [event [Hevent Hstep]].
  cbn in Hstep.
  lazymatch type of Hstep with
  | (if ?guard then _ else _) => destruct guard eqn:Hempty
  end.
  - destruct Hstep as [fields [Hfields Hstep]]; cbn in Hstep.
    lazymatch type of Hstep with
    | (if ?guard then _ else _) => destruct guard eqn:Hroom
    end; destruct Hstep as [_ ->]; split; reflexivity.
  - destruct Hstep as [_ [priority Hstep]].
    unfold event_task_rdy in Hstep; rewrite Hevent in Hstep.
    destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (before.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
    inversion Hstep; subst after; split; [apply sched_wake_by_status_running_eq|reflexivity].
Qed.

Lemma time_tick_hook_sem_critical_isr_source : forall sg eid before result after view,
  sem_post_critical sg eid before result after ->
  sched_disabled_isr_source view before -> sched_disabled_isr_source view after.
Proof.
  intros sg eid before result after view Hstep Hsource.
  destruct (time_tick_hook_sem_critical_control _ _ _ _ _ Hstep) as [Hrunning Hintr].
  unfold sched_disabled_isr_source in *; rewrite Hrunning, Hintr; exact Hsource.
Qed.

(** This is a consequence of the EXISTING completed-client contract on
    the SAME interval. A source owner must construct that contract from its
    actual completed clients. No such guarantee is added to the leaf pre,
    Pend pre, CPU ABI, or an arbitrary elementary Enter/Exit registry. *)
Lemma time_tick_hook_isr_interval : forall critical sg view before after,
  sched_disabled_completed_clients critical view ->
  UCOS2_state_inv sg before -> sched_disabled_isr_source view before ->
  critical_region_interval critical sg view.(os_execution_invocation) before after ->
  UCOS2_state_inv sg after /\ sched_disabled_isr_source view after.
Proof.
  intros critical sg view before after Hclients Hvalid Hsource Hinterval.
  destruct (sched_disabled_interval_preserves_context critical sg view
    view.(os_execution_invocation) before after Hclients Hvalid Hinterval)
    as [Hafter [Hisr Hlock]].
  split; [exact Hafter|apply Hisr; exact Hsource].
Qed.

Lemma time_tick_hook_sem_prefix_isr : forall environment critical sg view mask pe eid before
  observed error schedule returned restored,
  sched_disabled_completed_clients critical view ->
  UCOS2_state_inv sg before -> sched_disabled_isr_source view before ->
  sem_post_api_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sem_post_api_prefix_program environment critical sg (ResumeGenericCaller view) mask pe eid before
    ((error, schedule), returned) restored ->
  returned = ResumeGenericCaller view /\ UCOS2_state_inv sg restored /\
  sched_disabled_isr_source view restored.
Proof.
  intros environment critical sg view mask pe eid before observed error schedule returned restored
    Hclients Hvalid Hsource Hinput Hprefix.
  unfold sem_post_api_prefix_program in Hprefix.
  lazymatch type of Hprefix with
  | (if ?guard then _ else _) => destruct guard eqn:Hpe
  end.
  - destruct Hprefix as [Hresult ->]; inversion Hresult; subst; auto.
  - lazymatch type of Hprefix with
    | (if ?guard then _ else _) => destruct guard eqn:Htype
    end.
    + apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype.
      destruct Hprefix as [active [saved [acquired [code [request [released [next
        [Hsave [Hstep [Hrestore Hresult]]]]]]]]]].
      injection Hresult as Herror Hrequest Hnext; subst request next.
      pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
      destruct (sem_post_api_acquire_identity environment critical sg (ResumeGenericCaller view)
        active mask saved pe before acquired eid observed Hvalid Hpe Hinput Htype Hfacts)
        as [node [_ [_ [_ [Hnode [Hsem Hg]]]]]].
      pose proof (sem_post_critical_preserves_validity sg acquired eid node
        (code, schedule) released (proj1 Hfacts) Hnode Hsem Hstep) as Hreleased.
      destruct active as [active_task|active_view]; [contradiction|].
      destruct Hsave as [-> [Hinterval Hsaved]].
      destruct (time_tick_hook_isr_interval critical sg view before acquired
        Hclients Hvalid Hsource Hinterval) as [_ Hacquired_source].
      pose proof (time_tick_hook_sem_critical_isr_source _ _ _ _ _ _ Hstep Hacquired_source)
        as Hreleased_source.
      destruct returned as [returned_task|returned_view]; [contradiction|].
      destruct Hrestore as [-> Hreturn].
      destruct (time_tick_hook_isr_interval critical sg view released restored
        Hclients Hreleased Hreleased_source Hreturn) as [Hrestored Hrestored_source].
      auto.
    + destruct Hprefix as [Hresult ->]; inversion Hresult; subst; auto.
Qed.

Lemma time_tick_hook_disabled_schedule_isr : forall environment critical sg view mask
  before returned current,
  sched_disabled_completed_clients critical view ->
  UCOS2_state_inv sg before -> sched_disabled_isr_source view before ->
  task_resume_schedule_program environment critical sg (ResumeGenericCaller view)
    mask before returned current ->
  returned = ResumeGenericCaller view /\ UCOS2_state_inv sg current /\
  sched_disabled_isr_source view current.
Proof.
  intros environment critical sg view mask before returned current Hclients Hvalid Hsource Hprogram.
  destruct Hprogram as [[active saved] [acquired [Hsave [[] [released [Hstep Hrestore]]]]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hsave as [-> [Hinterval Hsaved]].
  destruct Hstep as [Hdisabled ->].
  destruct (time_tick_hook_isr_interval critical sg view before acquired
    Hclients Hvalid Hsource Hinterval) as [Hacquired Hacquired_source].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn].
  destruct (time_tick_hook_isr_interval critical sg view acquired current
    Hclients Hacquired Hacquired_source Hreturn) as [Hcurrent Hcurrent_source].
  auto.
Qed.

Lemma time_tick_hook_caller_result_isr : forall environment critical sg view mask eid counter before
  observed returned current,
  sched_disabled_completed_clients critical view ->
  UCOS2_state_inv sg before -> sched_disabled_isr_source view before ->
  time_tick_hook_call_inputs environment critical sg (ResumeGenericCaller view) mask
    counter before eid observed ->
  time_tick_hook_caller_result environment critical sg (ResumeGenericCaller view) mask eid
    counter before returned current ->
  returned = ResumeGenericCaller view /\ UCOS2_state_inv sg current /\
  sched_disabled_isr_source view current.
Proof.
  intros environment critical sg view mask eid counter before observed returned current
    Hclients Hvalid Hsource Hinput Hresult.
  unfold time_tick_hook_caller_result in Hresult.
  destruct (time_tick_hook_signals counter) eqn:Hsignal.
  - destruct (Hinput Hsignal) as [_ [_ [Hcall_input _]]].
    destruct Hresult as [error [prefix_caller [restored [schedule [Hprefix Htail]]]]].
    destruct (time_tick_hook_sem_prefix_isr environment critical sg view mask
      (tmr_signal_pointer before) eid before observed error schedule prefix_caller restored
      Hclients Hvalid Hsource Hcall_input Hprefix) as [-> [Hrestored Hrestored_source]].
    destruct schedule.
    + eapply time_tick_hook_disabled_schedule_isr; eassumption.
    + destruct Htail as [-> ->]; auto.
  - destruct Hresult as [-> ->]; auto.
Qed.

Lemma time_tick_hook_same_isr_running_nesting : forall view before after,
  sched_disabled_isr_source view before -> sched_disabled_isr_source view after ->
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  after.(IntrState).(intNesting) = before.(IntrState).(intNesting).
Proof.
  intros view before after
    [handler [interrupted [Hcontext [Hrunning Hagrees]]]]
    [handler_after [interrupted_after [Hcontext_after [Hrunning_after Hagrees_after]]]].
  split; [congruence|].
  unfold kernel_interrupt_nesting_agrees in Hagrees, Hagrees_after.
  rewrite (Hagrees_after eq_refl), (Hagrees eq_refl); reflexivity.
Qed.

(** Export the actual returned descriptor, full program and same-X return.
    Only Running and intNesting are concluded from the existing ISR contract;
    lockNesting/full control still need their actual completed-call source. *)
Lemma time_tick_hook_post_isr : forall environment critical saved_local sg view mask eid counter
  counter_address before observed X,
  sched_disabled_completed_clients critical view ->
  UCOS2_state_inv sg before -> sched_disabled_isr_source view before ->
  time_tick_hook_call_inputs environment critical sg (ResumeGenericCaller view) mask
    counter before eid observed ->
  time_tick_hook_post environment critical saved_local sg (ResumeGenericCaller view) mask eid
    counter_address counter before X |--
  EX current,
    coq_prop (time_tick_hook_call_program environment critical sg (ResumeGenericCaller view)
      mask eid counter before tt current /\
      time_tick_hook_return_safe current X /\ UCOS2_state_inv sg current /\
      current.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
      current.(IntrState).(intNesting) = before.(IntrState).(intNesting)) &&
    time_tick_hook_frame environment critical saved_local sg (ResumeGenericCaller view) mask
      counter_address (time_tick_hook_counter_after counter) current.
Proof.
  intros environment critical saved_local sg view mask eid counter counter_address before observed X
    Hclients Hvalid Hsource Hinput.
  unfold time_tick_hook_post.
  intros heap [returned [current [[Hresult Hsafe] Hframe]]].
  pose proof (time_tick_hook_result_program _ _ _ _ _ _ _ _ _ _ Hresult) as Hprogram.
  destruct (time_tick_hook_caller_result_isr _ _ _ _ _ _ _ _ _ _ _ Hclients
    Hvalid Hsource Hinput Hresult) as [-> [Hcurrent Hcurrent_source]].
  destruct (time_tick_hook_same_isr_running_nesting _ _ _ Hsource Hcurrent_source)
    as [Hrunning Hnesting].
  exists current; split.
  - exact (conj Hprogram (conj Hsafe (conj Hcurrent (conj Hrunning Hnesting)))).
  - exact Hframe.
Qed.

