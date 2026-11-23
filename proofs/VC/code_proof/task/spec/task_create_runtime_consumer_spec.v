Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_runtime_flow_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_modular_init_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Error/rollback consumers use the original complete weaker summaries.
    Forgetting observations preserves their buffer and returned resources. *)
Lemma task_tcb_init_modular_save_output_weaken : forall environment critical saved_local sg call mask saved before,
  task_tcb_init_modular_save_output environment critical saved_local sg call mask saved before |--
  task_tcb_init_continuation_save_output environment critical saved_local sg call mask saved before.
Proof.
  intros; sep_apply_l_atomic (task_tcb_init_modular_save_observation environment critical saved_local
    sg call mask saved before); Intros returned acquired.
  unfold task_tcb_init_continuation_restore_input; Intros.
  unfold task_tcb_init_continuation_save_output, task_tcb_init_stack_context.
  Exists returned acquired; entailer!; tauto.
Qed.

(** The actual successful TaskCreate call carries more information than
    the guarded generic Scheduler entry.  Its published ready list,
    running invocation and available stack discharge Scheduler's acquired
    Save cut using the common port post and the registered C rely.  None
    of these C facts is installed as an ARM postcondition. *)
Lemma task_create_modular_sched_save_output :
  forall environment critical saved_local sg args original mask saved before,
  kernel_sched_ready_clients critical -> kernel_tcb_stack_field_layout sg ->
  UCOS2_state_inv sg before -> args.(createPriority) <= 63 ->
  task_create_runtime_call_input args original before ->
  task_create_stack_nesting before = 0 -> task_create_stack_running before = 1 ->
  before.(SchedState).(readyList) <> [] ->
  task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before |--
  os_sched_continuation_call_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros environment critical saved_local sg args original mask saved before
    Hclients Hlayout Hvalid Hpriority Hadmit Hnesting Hrunning Hready.
  assert (Hrun : before.(SchedState).(isRunning) = true).
  { unfold task_create_stack_running in Hrunning.
    destruct (SchedStateDef.isRunning (SchedState before)); [reflexivity|discriminate]. }
  destruct (Hadmit Hpriority Hnesting Hrun) as [Hsource Havailable].
  pose proof (kernel_call_task_source_stack_field_address sg original before
    Hlayout Hvalid Hsource) as Haddress.
  unfold task_tcb_init_modular_save_output, kernel_call_modular_save_post.
  Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before returned acquired) by tauto.
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_restore_input_world
    environment critical saved_local sg returned saved acquired acquired)).
  sep_apply_l_atomic (os_sched_registered_save_call_output
    environment critical saved_local sg original returned mask saved before acquired
    Hclients Hvalid Hready Hsource Hsave (proj2 Hnormal Havailable) Haddress).
  entailer!.
Qed.

(** Immediate consumer of that acquired cut: the existing generic
    kernel_program_inv Scheduler proof executes the actual C nesting
    guards, selector, cache load and counter increment.  The next cut is
    precisely OSCtxSw or final Restore; their explicit port contracts stay
    separate from these C statements. *)
Lemma task_create_modular_sched_save_prefix :
  forall environment critical saved_local sg args original mask saved before heap (frame : Assertion),
  kernel_sched_ready_clients critical -> kernel_tcb_stack_field_layout sg ->
  UCOS2_state_inv sg before -> args.(createPriority) <= 63 ->
  task_create_runtime_call_input args original before ->
  task_create_stack_nesting before = 0 -> task_create_stack_running before = 1 ->
  before.(SchedState).(readyList) <> [] ->
  (task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before **
    unmap_table_rep sg ** frame) heap ->
  exists returned acquired after,
    task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
    task_tcb_init_stack_source_preserved original before acquired /\
    os_sched_call_cut sg returned acquired /\
    os_sched_modular_prefix_execution sg acquired heap after /\
    ((if os_sched_requests_switch acquired
      then os_sched_continuation_switch_pre environment critical saved_local kernel_program_inv
        sg returned saved acquired acquired
      else os_sched_continuation_body_post environment critical saved_local kernel_program_inv
        sg returned saved acquired acquired) ** frame) after.
Proof.
  intros environment critical saved_local sg args original mask saved before heap frame
    Hclients Hlayout Hvalid Hpriority Hadmit Hnesting Hrunning Hready Hpre.
  assert (Hadapt :
    task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before **
      unmap_table_rep sg ** frame |--
    os_sched_continuation_call_save_output environment critical saved_local sg original mask saved before **
      unmap_table_rep sg ** frame).
  { sep_apply_l_atomic (task_create_modular_sched_save_output
      environment critical saved_local sg args original mask saved before
      Hclients Hlayout Hvalid Hpriority Hadmit Hnesting Hrunning Hready).
    entailer!. }
  exact (os_sched_call_save_output_prefix environment critical saved_local sg
    original mask saved before heap frame (Hadapt heap Hpre)).
Qed.

Lemma task_tcb_init_modular_restore_output_weaken : forall environment critical saved_local sg call saved released,
  task_tcb_init_modular_restore_output environment critical saved_local sg call saved released |--
  task_tcb_init_continuation_restore_output environment critical saved_local sg call saved released.
Proof.
  intros; sep_apply_l_atomic (task_tcb_init_modular_restore_observation environment critical saved_local
    sg call saved released); Intros returned current.
  unfold task_tcb_init_continuation_restore_output; Exists returned current; entailer!; tauto.
Qed.

Lemma task_tcb_init_modular_call_post_weaken : forall environment critical saved_local sg region args task_return
  lower upper initial_name invocation origin mask initial original result,
  task_tcb_init_modular_call_post environment critical saved_local sg region args task_return lower upper
    initial_name invocation origin mask initial original result |--
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return lower upper
    initial_name invocation origin mask initial original result.
Proof.
  intros; unfold task_tcb_init_modular_call_post; Intros released returned current.
  unfold task_tcb_init_continuation_call_post, task_tcb_init_continuation_call_return_post.
  Exists released returned current; entailer!; tauto.
Qed.

Lemma task_create_modular_tcb_result_codes :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result,
  task_tcb_init_modular_call_post environment critical saved_local sg region args task_return lower upper
    initial_name invocation origin mask initial original result |--
  coq_prop (result = 0 \/ result = 66) &&
  task_tcb_init_modular_call_post environment critical saved_local sg region args task_return lower upper
    initial_name invocation origin mask initial original result.
Proof.
  intros; unfold task_tcb_init_modular_call_post; Intros released returned current.
  assert (Hresult : task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name invocation origin initial result released) by tauto.
  assert (Hcodes : result = 0 \/ result = 66) by (inversion Hresult; auto).
  Exists released returned current; entailer!.
Qed.

Lemma task_create_runtime_nesting_after_return : forall sg initial current,
  kernel_call_control_rely sg initial current -> task_create_stack_nesting initial = 0 ->
  task_create_stack_nesting current = 0.
Proof.
  intros sg initial current [_ Hinterrupt] Hinitial.
  unfold task_create_stack_nesting in *; rewrite Hinterrupt; exact Hinitial.
Qed.

Lemma task_create_modular_init_runtime_tcb_pre :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    original mask before returned_sp,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) before ->
  task_create_runtime_call_input args original before -> task_create_stack_nesting before = 0 ->
  task_create_modular_init_output environment critical saved_local sg region args task_return
    lower upper original mask before returned_sp |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      returned_sp = task_stack_init_sp TaskStackNoVFP args.(createStackTop) /\
      task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
        original.(os_sched_call_invocation) original.(os_sched_call_origin) current /\
      task_tcb_init_stack_source_preserved original before current /\
      task_create_runtime_call_input args returned current /\ task_create_stack_nesting current = 0) &&
    task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return
      lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
      mask current returned.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name original
    mask before returned_sp Hlayout Hentry Hadmit Hnesting.
  sep_apply_l_atomic (task_create_modular_init_output_tcb_pre environment critical saved_local sg region args
    task_return lower upper initial_name original mask before returned_sp Hlayout Hentry).
  Intros returned current.
  assert (Hhistory : task_tcb_init_runtime_history sg original before returned current) by tauto.
  assert (Hsource : task_tcb_init_stack_source_preserved original before current) by tauto.
  pose proof (task_create_runtime_call_input_after_return sg args original before returned current
    Hadmit (proj2 Hhistory) (proj1 Hhistory) Hsource) as Hruntime.
  pose proof (task_create_runtime_nesting_after_return sg before current (proj2 Hhistory) Hnesting) as Hzero.
  Exists returned current; entailer!.
Qed.

Lemma task_create_modular_tcb_success :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin original mask initial,
  task_create_runtime_call_input args original initial -> task_create_stack_nesting initial = 0 ->
  task_tcb_init_modular_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original 0 |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_source_preserved original initial current /\
      task_create_runtime_call_input args returned current /\ task_create_stack_nesting current = 0 /\
      current.(SchedState).(readyList) <> []) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin original mask initial Hadmit Hnesting.
  unfold task_tcb_init_modular_call_post; Intros released returned current.
  assert (Hprefix : task_tcb_init_stack_source_preserved original initial released) by tauto.
  assert (Htail : task_tcb_init_stack_source_preserved original released current)
    by (unfold task_tcb_init_stack_return_preserved in *; tauto).
  pose proof (task_tcb_init_stack_source_preserved_trans original initial released current Hprefix Htail) as Hsource.
  assert (Hhistory : task_tcb_init_runtime_history sg original initial returned current) by tauto.
  pose proof (task_create_runtime_call_input_after_return sg args original initial returned current
    Hadmit (proj2 Hhistory) (proj1 Hhistory) Hsource) as Hruntime.
  pose proof (task_create_runtime_nesting_after_return sg initial current (proj2 Hhistory) Hnesting) as Hzero.
  unfold task_tcb_init_stack_buffer_result; destruct (Z.eq_dec 0 66); [discriminate|].
  Exists returned current; entailer!; tauto.
Qed.

Lemma task_create_modular_running_sched_pre : forall environment critical saved_local sg args call mask state,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg state ->
  args.(createPriority) <= 63 -> task_create_runtime_call_input args call state ->
  task_create_stack_nesting state = 0 -> task_create_stack_running state = 1 ->
  state.(SchedState).(readyList) <> [] ->
  sg.(g_OSRunning) # UChar |-> task_create_stack_running state **
    task_create_continuation_without_running environment critical saved_local sg call mask state **
    unmap_table_rep sg |--
  os_sched_continuation_call_pre environment saved_local kernel_program_inv sg call mask state.
Proof.
  intros environment critical saved_local sg args call mask state Hlayout Hvalid Hpriority Hadmit Hnesting Hrunning Hready.
  assert (Hrun : state.(SchedState).(isRunning) = true).
  { unfold task_create_stack_running in Hrunning.
    destruct (SchedStateDef.isRunning (SchedState state)); [reflexivity|discriminate]. }
  destruct (Hadmit Hpriority Hnesting Hrun) as [Hsource Havailable].
  assert (Hcut : os_sched_call_cut sg call state).
  { eapply os_sched_call_cut_from_source; try eassumption.
    eapply kernel_call_task_source_stack_field_address; eassumption. }
  sep_apply_l_atomic (task_create_continuation_running_sched_pre environment critical saved_local sg call mask state Hvalid).
  unfold os_sched_continuation_call_pre; entailer!.
Qed.
