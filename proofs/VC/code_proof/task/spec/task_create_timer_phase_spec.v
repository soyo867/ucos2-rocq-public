Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_interleaving_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_create_modular_init_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Timer initialization needs the phase of the SAME returned world.  The
    existing StackInit C store/source producer already provides the actual
    resumption intervals.  This additive view retains their Timer projection;
    it does not strengthen CPU contracts, assume a future return, or change
    the existing output/program.  Actual C consumer wiring is a later step. *)
Definition task_create_modular_init_phase_output environment critical saved_local sg region args
  task_return lower upper call mask before returned_sp : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      task_create_stack_init_entry_preserved sg args call before current /\
      task_tcb_init_stack_source_preserved call before current /\
      task_tcb_init_runtime_history sg call before returned current /\
      before.(NameState) = current.(NameState) /\
      before.(TimerState).(timerInitPhase) = current.(TimerState).(timerInitPhase)) &&
    (task_stack_init_post TaskStackNoVFP region.(stackRegionBase) args.(createStackTop)
       args.(createEntry) args.(createArgument) task_return (task_create_options args)
       lower upper returned_sp **
     task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current).

Fixpoint task_create_modular_init_phase_execution (schedule : list nat)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) sg args region task_return lower upper
  (original : OsSchedCallContext) mask initial
  (call : OsSchedCallContext) state (prefix suffix : list Z)
  (before : model) (frame : Assertion) {struct schedule} : Prop :=
  match schedule with
  | [] => exists initialized,
      kernel_heap_execution (task_stack_push_writes
        (task_stack_init_aligned_top args.(createStackTop) - 4 * Zlength prefix) suffix) before initialized /\
      (task_create_modular_init_phase_output environment critical saved_local sg region args task_return
        lower upper original mask initial (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** frame) initialized
  | count :: remaining =>
      let chunk := firstn count suffix in
      let rest := skipn count suffix in
      exists cut,
        kernel_heap_execution (task_stack_push_writes
          (task_stack_init_aligned_top args.(createStackTop) - 4 * Zlength prefix) chunk) before cut /\
        (task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop)
           lower upper (prefix ++ chunk) rest **
         task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** frame) cut /\
        (forall returned current final,
          kernel_resumption_task_source_trace environment.(task_stack_call_external)
            environment.(task_stack_call_port) critical.(critical_region_clients) sg
            call.(os_sched_call_invocation) None call.(os_sched_call_origin)
            state false returned.(os_sched_call_origin) current ->
          kernel_call_normal_return call state returned current ->
          kernel_call_control_rely sg state current ->
          (task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop)
             lower upper (prefix ++ chunk) rest **
           task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current ** frame) final ->
          task_create_modular_init_phase_execution remaining environment critical saved_local sg args region
            task_return lower upper original mask initial returned current (prefix ++ chunk) rest final frame)
  end.

Lemma task_create_modular_init_phase_execution_source : forall schedule environment critical saved_local
  sg args region task_return lower upper original mask initial call state prefix suffix before frame,
  UCOS2_state_inv sg state ->
  task_tcb_init_stack_same_call call original ->
  task_create_stack_init_entry_preserved sg args original initial state ->
  task_tcb_init_stack_source_preserved original initial state ->
  task_tcb_init_runtime_history sg original initial call state ->
  initial.(NameState) = state.(NameState) ->
  initial.(TimerState).(timerInitPhase) = state.(TimerState).(timerInitPhase) ->
  prefix ++ suffix = task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return ->
  Forall (fun value => 0 <= value < 4294967296) suffix ->
  (task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
   task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** frame) before ->
  task_create_modular_init_phase_execution schedule environment critical saved_local sg args region
    task_return lower upper original mask initial call state prefix suffix before frame.
Proof.
  induction schedule as [|count remaining IH]; intros environment critical saved_local sg args region
    task_return lower upper original mask initial call state prefix suffix before frame
    Hvalid Hsame Hentry Hsource Hhistory Hnames Hphase Hwords Hranges Hpre.
  - cbn [task_create_modular_init_phase_execution].
    match type of Hpre with ?P before => assert (Horder : P |--
      task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
      (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** frame))
      by entailer! end.
    destruct (task_stack_init_suffix_store_execution region.(stackRegionBase) args.(createStackTop)
      args.(createEntry) args.(createArgument) task_return (task_create_options args)
      lower upper prefix suffix _ before Hwords Hranges (Horder before Hpre))
      as [initialized [Hrun Hinitialized]].
    exists initialized; split; [exact Hrun|].
    match type of Hinitialized with ?P initialized => match goal with |- ?Q initialized =>
      assert (Hpack : P |-- Q) end end.
    { unfold task_create_modular_init_phase_output; Exists call state; entailer!. }
    exact (Hpack initialized Hinitialized).
  - cbn [task_create_modular_init_phase_execution].
    set (chunk := firstn count suffix); set (rest := skipn count suffix).
    assert (Hsplit : chunk ++ rest = suffix) by (unfold chunk, rest; apply firstn_skipn).
    assert (Hlength : Zlength prefix + Zlength chunk + Zlength rest = 16).
    { rewrite <- Z.add_assoc, <- Zlength_app, Hsplit, <- Zlength_app, Hwords; reflexivity. }
    assert (Hchunk : Forall (fun value => 0 <= value < 4294967296) chunk).
    { rewrite <- Hsplit, Forall_app in Hranges; tauto. }
    assert (Hrest : Forall (fun value => 0 <= value < 4294967296) rest).
    { rewrite <- Hsplit, Forall_app in Hranges; tauto. }
    match type of Hpre with ?P before => assert (Horder : P |--
      task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix (chunk ++ rest) **
      (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** frame)) end.
    { rewrite Hsplit; entailer!. }
    destruct (task_stack_init_partial_store_execution region.(stackRegionBase) args.(createStackTop)
      lower upper prefix chunk rest _ before Hlength Hchunk (Horder before Hpre))
      as [cut [Hstores Hcut]].
    exists cut; split; [exact Hstores|]. split.
    { match type of Hcut with ?P cut => match goal with |- ?Q cut =>
        assert (Horder_cut : P |-- Q) by entailer! end end.
      exact (Horder_cut cut Hcut). }
    intros returned current final Htrace Hnormal Hcontrol Hfinal.
    pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
    pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
    pose proof (proj1 (Hpreserved Hvalid)) as Hcurrent.
    pose proof (task_tcb_init_stack_registered_source_preserved _ _ _ _ _ _ _ _
      Hvalid (proj1 Hnormal) Htrace) as Hstep_source.
    assert (Hnext : task_tcb_init_runtime_history sg original initial returned current).
    { eapply task_tcb_init_runtime_history_trans; [exact Hhistory|split; assumption]. }
    eapply IH; [exact Hcurrent|exact (proj1 (proj1 Hnext))| | |exact Hnext| | | |exact Hrest|exact Hfinal].
    + intros name Hinitial; specialize (Hentry name Hinitial).
      destruct Hsame as [Hi [Ho Hstack]]; rewrite Hi in Hpreserved.
      exact (task_tcb_init_call_preserves_entry sg
        (task_tcb_init_stack_call_args args name) original.(os_sched_call_invocation)
        original.(os_sched_call_origin) state current Hentry Hpreserved).
    + intro Hinitial.
      apply (proj1 (task_tcb_init_stack_same_call_source_iff call original current Hsame)).
      apply Hstep_source.
      apply (proj2 (task_tcb_init_stack_same_call_source_iff call original state Hsame)); apply Hsource; exact Hinitial.
    + transitivity state.(NameState); [exact Hnames|].
      exact (proj2 (proj2 (proj2 (Hpreserved Hvalid)))).
    + transitivity state.(TimerState).(timerInitPhase); [exact Hphase|].
      symmetry; exact (proj1 (timer_public_trace_public_storage_frame sg _ _
        (critical_region_interval_timer_public_trace _ _ _ _ _ Hinterval))).
    + rewrite <- app_assoc, Hsplit; exact Hwords.
Qed.

Lemma task_create_modular_init_phase_input_execution : forall schedule environment critical saved_local
  sg region args task_return lower old_frame upper call mask state before (frame : Assertion),
  UCOS2_state_inv sg state ->
  (task_create_continuation_init_input environment critical saved_local sg region args task_return
    lower old_frame upper call mask state ** frame) before ->
  exists prepared,
    kernel_heap_execution [] before prepared /\
    task_create_modular_init_phase_execution schedule environment critical saved_local sg args region task_return
      lower upper call mask state call state []
      (task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return) prepared frame.
Proof.
  intros schedule environment critical saved_local sg region args task_return lower old_frame upper
    call mask state before frame Hvalid Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
    (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** frame)) end.
  { unfold task_create_continuation_init_input; entailer!. }
  destruct (task_stack_init_prefix_store_execution region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper []
    (task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return) _ before eq_refl
    (Horder before Hpre)) as [prepared [Hrun [Hranges Hprepared]]].
  exists prepared; split; [exact Hrun|].
  eapply task_create_modular_init_phase_execution_source.
  - exact Hvalid.
  - unfold task_tcb_init_stack_same_call; auto.
  - intros name Hinitial; exact Hinitial.
  - apply task_tcb_init_stack_source_preserved_refl.
  - apply task_tcb_init_runtime_history_refl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hranges.
  - match type of Hprepared with ?P prepared => match goal with |- ?Q prepared =>
      assert (Hclose : P |-- Q) by entailer! end end.
    exact (Hclose prepared Hprepared).
Qed.


Lemma task_create_modular_init_phase_output_forget :
  forall environment critical saved_local sg region args task_return lower upper
    call mask before returned_sp,
  task_create_modular_init_phase_output environment critical saved_local sg region args
    task_return lower upper call mask before returned_sp |--
  task_create_modular_init_output environment critical saved_local sg region args
    task_return lower upper call mask before returned_sp.
Proof.
  intros; unfold task_create_modular_init_phase_output; Intros returned current.
  unfold task_create_modular_init_output; Exists returned current; entailer!; tauto.
Qed.

Lemma task_create_modular_init_phase_execution_forget :
  forall schedule environment critical saved_local sg args region task_return lower upper
    original mask initial call state prefix suffix before frame,
  task_create_modular_init_phase_execution schedule environment critical saved_local sg args region
    task_return lower upper original mask initial call state prefix suffix before frame ->
  task_create_modular_init_execution schedule environment critical saved_local sg args region
    task_return lower upper original mask initial call state prefix suffix before frame.
Proof.
  induction schedule as [|count remaining IH]; intros environment critical saved_local sg args region
    task_return lower upper original mask initial call state prefix suffix before frame Hrun.
  - cbn [task_create_modular_init_phase_execution] in Hrun.
    cbn [task_create_modular_init_execution].
    destruct Hrun as [initialized [Hstores Hfinal]].
    exists initialized; split; [exact Hstores|].
    match type of Hfinal with ?P initialized => match goal with |- ?Q initialized =>
      assert (Hforget : P |-- Q) end end.
    { sep_apply_l_atomic (task_create_modular_init_phase_output_forget
        environment critical saved_local sg region args task_return lower upper
        original mask initial (task_stack_init_sp TaskStackNoVFP args.(createStackTop)));
      entailer!. }
    exact (Hforget initialized Hfinal).
  - cbn [task_create_modular_init_phase_execution] in Hrun.
    cbn [task_create_modular_init_execution].
    destruct Hrun as [cut [Hstores [Hcut Htail]]].
    exists cut; split; [exact Hstores|]. split; [exact Hcut|].
    intros returned current final Htrace Hnormal Hcontrol Hfinal.
    eapply IH; eapply Htail; eassumption.
Qed.
