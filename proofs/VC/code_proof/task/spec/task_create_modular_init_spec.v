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
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected no-VFP C initializer. The buffer stores are proved below;
    only a matched environmental return uses the shared normal-return
    observation and the C control rely. No whole-C-function platform law
    is postulated, and no future return is required at the public entry. *)
Definition task_create_modular_init_output environment critical saved_local sg region args
  task_return lower upper call mask before returned_sp : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      task_create_stack_init_entry_preserved sg args call before current /\
      task_tcb_init_stack_source_preserved call before current /\
      task_tcb_init_runtime_history sg call before returned current /\
      before.(NameState) = current.(NameState)) &&
    (task_stack_init_post TaskStackNoVFP region.(stackRegionBase) args.(createStackTop)
       args.(createEntry) args.(createArgument) task_return (task_create_options args)
       lower upper returned_sp **
     task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current).

Lemma task_create_modular_init_output_tcb_pre :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    original mask before returned_sp,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) before ->
  task_create_modular_init_output environment critical saved_local sg region args task_return
    lower upper original mask before returned_sp |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      returned_sp = task_stack_init_sp TaskStackNoVFP args.(createStackTop) /\
      task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
        original.(os_sched_call_invocation) original.(os_sched_call_origin) current /\
      task_tcb_init_stack_source_preserved original before current /\
      task_tcb_init_runtime_history sg original before returned current /\
      before.(NameState) = current.(NameState)) &&
    task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return
      lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
      mask current returned.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name original
    mask before returned_sp Hlayout Hentry.
  unfold task_create_modular_init_output; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hpreserved : task_create_stack_init_entry_preserved sg args original before current) by tauto.
  pose proof (Hpreserved initial_name Hentry) as Hcurrent.
  sep_apply_l_atomic (task_create_stack_init_post_storage TaskStackNoVFP region args task_return
    lower upper returned_sp Hlayout).
  Intros; Exists returned current.
  unfold task_tcb_init_continuation_call_pre, task_tcb_init_stack_pre, task_tcb_init_pre,
    task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_continuation_capsules, kernel_call_execution_owned.
  destruct Hsame as [Hi [Ho Hstack]]; rewrite Hi, Ho; entailer!; tauto.
Qed.

(** Each list element is a cut after a prefix of the remaining actual C
    stores. The environment is allowed any number of such cuts. Its
    premises are observations of an already matched return: registered
    source trace, the shared normal-return/control relations, and the
    returned callable world with the private child buffer in its frame.
    This is the explicit conditional port/RG boundary, not an ISA proof
    and not a statement that an arbitrary handler returns or preserves
    arbitrary C invariants. *)
Fixpoint task_create_modular_init_execution (schedule : list nat)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion) sg args region task_return lower upper
  (original : OsSchedCallContext) mask initial
  (call : OsSchedCallContext) state (prefix suffix : list Z)
  (before : model) (frame : Assertion) {struct schedule} : Prop :=
  match schedule with
  | [] => exists initialized,
      kernel_heap_execution (task_stack_push_writes
        (task_stack_init_aligned_top args.(createStackTop) - 4 * Zlength prefix) suffix) before initialized /\
      (task_create_modular_init_output environment critical saved_local sg region args task_return
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
          task_create_modular_init_execution remaining environment critical saved_local sg args region
            task_return lower upper original mask initial returned current (prefix ++ chunk) rest final frame)
  end.

Lemma task_create_modular_init_execution_source : forall schedule environment critical saved_local
  sg args region task_return lower upper original mask initial call state prefix suffix before frame,
  UCOS2_state_inv sg state ->
  task_tcb_init_stack_same_call call original ->
  task_create_stack_init_entry_preserved sg args original initial state ->
  task_tcb_init_stack_source_preserved original initial state ->
  task_tcb_init_runtime_history sg original initial call state ->
  initial.(NameState) = state.(NameState) ->
  prefix ++ suffix = task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return ->
  Forall (fun value => 0 <= value < 4294967296) suffix ->
  (task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
   task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** frame) before ->
  task_create_modular_init_execution schedule environment critical saved_local sg args region
    task_return lower upper original mask initial call state prefix suffix before frame.
Proof.
  induction schedule as [|count remaining IH]; intros environment critical saved_local sg args region
    task_return lower upper original mask initial call state prefix suffix before frame
    Hvalid Hsame Hentry Hsource Hhistory Hnames Hwords Hranges Hpre.
  - cbn [task_create_modular_init_execution].
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
    { unfold task_create_modular_init_output; Exists call state; entailer!. }
    exact (Hpack initialized Hinitialized).
  - cbn [task_create_modular_init_execution].
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
    eapply IH; [exact Hcurrent|exact (proj1 (proj1 Hnext))| | |exact Hnext| | |exact Hrest|exact Hfinal].
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
    + rewrite <- app_assoc, Hsplit; exact Hwords.
Qed.

Lemma task_create_modular_init_input_execution : forall schedule environment critical saved_local
  sg region args task_return lower old_frame upper call mask state before (frame : Assertion),
  UCOS2_state_inv sg state ->
  (task_create_continuation_init_input environment critical saved_local sg region args task_return
    lower old_frame upper call mask state ** frame) before ->
  exists prepared,
    kernel_heap_execution [] before prepared /\
    task_create_modular_init_execution schedule environment critical saved_local sg args region task_return
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
  eapply task_create_modular_init_execution_source.
  - exact Hvalid.
  - unfold task_tcb_init_stack_same_call; auto.
  - intros name Hinitial; exact Hinitial.
  - apply task_tcb_init_stack_source_preserved_refl.
  - apply task_tcb_init_runtime_history_refl.
  - reflexivity.
  - reflexivity.
  - exact Hranges.
  - match type of Hprepared with ?P prepared => match goal with |- ?Q prepared =>
      assert (Hclose : P |-- Q) by entailer! end end.
    exact (Hclose prepared Hprepared).
Qed.
