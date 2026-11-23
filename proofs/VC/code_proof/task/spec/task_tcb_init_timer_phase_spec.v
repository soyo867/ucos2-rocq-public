Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_sched_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_sched_publication_spec.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Additive observations for the actual TCBInit Save/Restore endpoints.
    Keep the old call/history relations untouched. A future C annotation must
    transport phase alongside them through the actual detach/commit cuts;
    the old weak post alone does not establish that missing prefix fact. *)
Lemma task_tcb_init_modular_save_phase_observation :
  forall environment critical saved_local sg original mask saved before,
  task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before |--
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired /\
      (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired) /\
      interrupt_saved_value mask saved /\
      kernel_call_normal_return original before returned acquired /\
      kernel_call_control_rely sg before acquired /\
      before.(TimerState).(timerInitPhase) = acquired.(TimerState).(timerInitPhase)) &&
    task_tcb_init_continuation_restore_input environment critical saved_local
       sg returned saved acquired acquired.
Proof.
  intros environment critical saved_local sg original mask saved before.
  unfold task_tcb_init_modular_save_output, kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsource : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before returned acquired) by tauto.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsource) as Hinterval.
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  assert (Hphase : before.(TimerState).(timerInitPhase) = acquired.(TimerState).(timerInitPhase)).
  { symmetry; exact (proj1 (timer_public_trace_public_storage_frame sg _ _
      (critical_region_interval_timer_public_trace _ _ _ _ _ Hinterval))). }
  destruct Hsource as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; assumption).
  assert (Hordinary : UCOS2_state_inv sg before ->
    task_tcb_init_stack_source_preserved original before acquired).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_restore_input_world
    environment critical saved_local sg returned saved acquired acquired)).
  Exists returned acquired; entailer!.
Qed.

Lemma task_tcb_init_modular_restore_phase_observation :
  forall environment critical saved_local sg original saved released,
  task_tcb_init_modular_restore_output environment critical saved_local sg original saved released |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current) /\
      kernel_call_normal_return original released returned current /\
      kernel_call_control_rely sg released current /\
      released.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase)) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned
      (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical saved_local sg original saved released.
  unfold task_tcb_init_modular_restore_output, kernel_call_modular_restore_post; Intros returned current.
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  assert (Hnormal : kernel_call_normal_return original released returned current) by tauto.
  pose proof (proj1 Hnormal) as Hsame.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hinterval Hcontrol].
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  assert (Hphase : released.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase)).
  { symmetry; exact (proj1 (timer_public_trace_public_storage_frame sg _ _
      (critical_region_interval_timer_public_trace _ _ _ _ _ Hinterval))). }
  assert (Hordinary : UCOS2_state_inv sg released ->
    task_tcb_init_stack_source_preserved original released current).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_save_input_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  Exists returned current; entailer!.
Qed.


(** Actual protected mutations preserve Timer, independently of the surrounding
    interference. These are projection equalities, not a complete C proof. *)
Lemma task_tcb_init_detached_timer_state_eq :
  forall args invocation origin state slot rest image,
  (task_tcb_init_detached_state args invocation origin state slot rest image).(TimerState) =
  state.(TimerState).
Proof. intros; reflexivity. Qed.

Lemma task_tcb_init_published_timer_state_eq :
  forall sg args invocation acquired current slot image,
  (task_tcb_init_published_state sg args invocation acquired current slot image).(TimerState) =
  current.(TimerState).
Proof. intros; reflexivity. Qed.

Lemma task_create_stack_publication_timer_state_eq :
  forall sg publication current,
  (task_create_stack_publication_state sg publication current).(TimerState) =
  current.(TimerState).
Proof. intros; reflexivity. Qed.

Definition task_tcb_init_modular_phase_call_post environment critical saved_local sg
  region args task_return lower upper initial_name invocation origin mask initial original result : Assertion :=
  EX released,
    coq_prop (task_tcb_init_stack_call_result critical sg region args task_return lower upper
      initial_name invocation origin initial result released) &&
    coq_prop (UCOS2_state_inv sg released /\
      task_tcb_init_stack_source_preserved original initial released) &&
    ((EX returned current,
      coq_prop (task_tcb_init_stack_same_call returned original /\
        task_tcb_init_stack_return_preserved original released current /\
        (result = 0 -> current.(SchedState).(readyList) <> []) /\
        task_tcb_init_runtime_history sg original initial returned current /\
        initial.(NameState) = current.(NameState) /\
        initial.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase)) &&
      task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current) **
     task_tcb_init_stack_buffer_result region args task_return lower upper result).


Lemma task_tcb_init_modular_phase_call_post_forget :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result,
  task_tcb_init_modular_phase_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result |--
  task_tcb_init_modular_name_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result.
Proof.
  intros; unfold task_tcb_init_modular_phase_call_post; Intros released returned current.
  unfold task_tcb_init_modular_name_call_post; Exists released returned current; entailer!; tauto.
Qed.

Lemma task_tcb_init_modular_return_phase_post :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result released actual saved,
  kernel_sched_ready_clients critical ->
  UCOS2_state_inv sg initial ->
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial result released ->
  UCOS2_state_inv sg released ->
  task_tcb_init_stack_source_preserved original initial released ->
  task_tcb_init_runtime_history sg original initial actual released ->
  initial.(TimerState).(timerInitPhase) = released.(TimerState).(timerInitPhase) ->
  interrupt_saved_value mask saved ->
  task_tcb_init_modular_restore_output environment critical saved_local sg actual saved released **
    task_tcb_init_stack_buffer_result region args task_return lower upper result |--
  task_tcb_init_modular_phase_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result released actual saved
    Hclients Hinitial Hresult Hvalid Hprefix Hbody Hphase Hsaved.
  unfold task_tcb_init_modular_restore_output, kernel_call_modular_restore_post; Intros returned current.
  assert (Hnormal : kernel_call_normal_return actual released returned current) by tauto.
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    actual.(os_sched_call_invocation) None actual.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  assert (Hhistory : task_tcb_init_runtime_history sg original initial returned current).
  { eapply task_tcb_init_runtime_history_trans; [exact Hbody|split; tauto]. }
  pose proof (proj1 (proj1 Hbody)) as [Hi [Ho Hstack]].
  rewrite Hi, Ho in Htrace.
  pose proof (proj1 (proj1 Hhistory)) as Hsame.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg original.(os_sched_call_invocation)
    released current Hinterval Hvalid) as [Hcurrent [Hframe Hactive]].
  pose proof (task_tcb_init_stack_registered_source_preserved _ _ _ _ _ _ _ _
    Hvalid Hsame Htrace) as Hsource.
  assert (Hreturn : task_tcb_init_stack_return_preserved original released current).
  { split; [exact Hframe|]. split; [apply Hactive|exact Hsource]. }
  assert (Hready : result = 0 -> current.(SchedState).(readyList) <> []).
  { intro Hsuccess; subst result.
    eapply critical_region_interval_preserves_sched_ready; [exact Hclients|exact Hinterval|exact Hvalid|].
    eapply task_tcb_init_stack_success_ready; exact Hresult. }
  pose proof (task_tcb_init_stack_call_result_preserves_names _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinitial Hresult) as Hreleased_names.
  pose proof (critical_region_interval_preserves_name_state critical sg
    original.(os_sched_call_invocation) released current Hinterval) as Hreturned_names.
  pose proof (proj1 (timer_public_trace_public_storage_frame sg _ _
    (critical_region_interval_timer_public_trace _ _ _ _ _ Hinterval))) as Hreturned_phase.
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_save_input_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  rewrite (proj2 Hsaved).
  unfold task_tcb_init_modular_phase_call_post; Exists released returned current; entailer!; intuition congruence.
Qed.

(** Parser-facing projection equality, carried at the real C cuts. This is
    not a new caller precondition or a stronger platform source relation. *)
Definition task_tcb_init_timer_phase_eq (before after : UCOS2_Verify_State) : Prop :=
  before.(TimerState).(timerInitPhase) = after.(TimerState).(timerInitPhase).

Lemma task_tcb_init_modular_save_phase_entry :
  forall environment critical saved_local sg args original mask saved before,
  task_tcb_init_entry sg args original.(os_sched_call_invocation) original.(os_sched_call_origin) before ->
  task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before |--
  EX returned acquired,
    coq_prop (task_tcb_init_entry sg args original.(os_sched_call_invocation)
      original.(os_sched_call_origin) acquired /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired /\
      task_tcb_init_stack_source_preserved original before acquired /\
      interrupt_saved_value mask saved /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned) /\
      task_tcb_init_runtime_history sg original before returned acquired /\
      task_tcb_init_timer_phase_eq before acquired) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment returned ** UCOS2_raw_rep sg acquired **
     task_tcb_init_continuation_capsules environment saved_local acquired).
Proof.
  intros environment critical saved_local sg args original mask saved before Hentry.
  sep_apply_l_atomic (task_tcb_init_modular_save_phase_observation environment critical saved_local
    sg original mask saved before); Intros returned acquired.
  assert (Hinterval : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    before acquired) by tauto.
  pose proof (task_tcb_init_call_preserves_entry sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) before acquired Hentry Hinterval) as Hacquired.
  pose proof (proj1 Hentry) as Hbefore.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  destruct Hsame as [Hi [Ho Hstack]].
  unfold task_tcb_init_continuation_restore_input; Intros.
  Exists returned acquired.
  unfold task_tcb_init_runtime_history, task_tcb_init_stack_same_call,
    task_tcb_init_timer_phase_eq, UCOS2_inv.
  rewrite Hi, Ho; entailer!; tauto.
Qed.

Lemma task_tcb_init_modular_save_phase_commit :
  forall environment critical saved_local sg args original checkpoint_call mask saved
    initial first slot rest image checkpoint,
  task_tcb_init_stack_same_call checkpoint_call original ->
  task_tcb_init_entry sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first ->
  task_tcb_init_detach_observation args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first slot rest image ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    (task_tcb_init_detached_state args original.(os_sched_call_invocation)
      original.(os_sched_call_origin) first slot rest image) checkpoint ->
  task_tcb_init_runtime_history sg original initial checkpoint_call checkpoint ->
  task_tcb_init_timer_phase_eq initial checkpoint ->
  task_tcb_init_modular_save_output environment critical saved_local sg checkpoint_call mask saved checkpoint |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_commit_binding args original.(os_sched_call_invocation)
        original.(os_sched_call_origin) first current slot /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
        (task_tcb_init_detached_state args original.(os_sched_call_invocation)
          original.(os_sched_call_origin) first slot rest image) current /\
      task_tcb_init_stack_source_preserved checkpoint_call checkpoint current /\
      interrupt_saved_value mask saved /\ UCOS2_state_inv sg current /\
      task_stack_live_coverage current.(TskState) (task_stack_call_active_key returned) /\
      task_tcb_init_runtime_history sg original initial returned current /\
      task_tcb_init_timer_phase_eq initial current) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       original.(os_sched_call_invocation) original.(os_sched_call_origin) saved current **
     task_tcb_init_stack_context environment returned ** UCOS2_raw_rep sg current **
     task_tcb_init_continuation_capsules environment saved_local current).
Proof.
  intros environment critical saved_local sg args original checkpoint_call mask saved
    initial first slot rest image checkpoint Hsame Hentry Hdetach Hprevious Hprefix Hphase.
  sep_apply_l_atomic (task_tcb_init_modular_save_phase_observation environment critical saved_local
    sg checkpoint_call mask saved checkpoint); Intros returned current.
  assert (Hlast : task_tcb_init_call_preserved sg checkpoint_call.(os_sched_call_invocation)
    checkpoint current) by tauto.
  assert (Hcheckpoint : UCOS2_state_inv sg checkpoint).
  { apply (proj1 (Hprevious (task_tcb_init_detach_preserves_validity sg args
      original.(os_sched_call_invocation) original.(os_sched_call_origin)
      first slot rest image Hentry Hdetach))). }
  assert (Hhistory : task_tcb_init_runtime_history sg original initial returned current).
  { eapply task_tcb_init_runtime_history_trans; [exact Hprefix|split; tauto]. }
  destruct Hsame as [Hi [Ho Hstack]].
  rewrite Hi in Hlast.
  pose proof (task_tcb_init_call_preserved_trans sg original.(os_sched_call_invocation)
    _ checkpoint current Hprevious Hlast) as Hinterval.
  destruct (task_tcb_init_call_preserves_allocation sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) first slot rest image current Hentry Hdetach Hinterval)
    as [Hvalid [Hcommit Hactive]].
  assert (Hreturned : task_tcb_init_stack_same_call returned checkpoint_call) by tauto.
  destruct Hreturned as [Hi' [Ho' Hstack']].
  unfold task_tcb_init_continuation_restore_input; Intros.
  Exists returned current.
  unfold task_tcb_init_timer_phase_eq in *.
  unfold task_tcb_init_stack_same_call, UCOS2_inv.
  rewrite Hi', Ho', Hi, Ho; entailer!; intuition congruence.
Qed.
