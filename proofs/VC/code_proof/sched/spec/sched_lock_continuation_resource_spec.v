Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_program_storage.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition os_sched_lock_continuation_pre environment critical saved_local sg call mask before X : Assertion :=
  coq_prop (os_sched_lock_continuation_safe environment critical sg call mask before X) &&
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask before **
   unmap_table_rep sg).

Definition os_sched_lock_continuation_post environment critical saved_local sg original mask before X : Assertion :=
  EX returned current,
    coq_prop (os_sched_lock_continuation_history environment critical sg original mask before returned current /\
      kernel_call_normal_return original before returned current /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_lock_continuation_control before current /\
      safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X) &&
    (task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current **
     unmap_table_rep sg).

Definition os_sched_lock_continuation_observation_frame environment critical saved_local sg call mask before : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\
    task_stack_live_coverage before.(TskState) (task_stack_call_active_key call)) &&
  (os_sched_lock_outside_frame environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) mask before **
   os_sched_context_resources environment.(task_stack_call_external) call **
   task_tcb_init_continuation_capsules environment saved_local before).

Lemma os_sched_lock_continuation_split_running : forall environment critical saved_local sg call mask before,
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask before --||--
  (sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
   os_sched_lock_continuation_observation_frame environment critical saved_local sg call mask before).
Proof.
  intros; unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
    os_sched_lock_continuation_observation_frame, os_sched_lock_outside_frame,
    task_tcb_init_continuation_capsules, kernel_call_execution_owned,
    critical_region_outside, os_sched_lock_running.
  rewrite logic_equiv_sepcon_coq_prop_andp.
  split; Intros; entailer!; tauto.
Qed.

Lemma os_sched_lock_continuation_pre_open : forall environment critical saved_local sg call mask before X,
  os_sched_lock_continuation_pre environment critical saved_local sg call mask before X |--
  coq_prop (os_sched_lock_continuation_safe environment critical sg call mask before X /\
    UCOS2_state_inv sg before) &&
  (sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
   os_sched_lock_continuation_observation_frame environment critical saved_local sg call mask before **
   unmap_table_rep sg).
Proof.
  intros; unfold os_sched_lock_continuation_pre.
  apply coq_prop_andp_left; intro Hsafe.
  sep_apply_l_atomic (proj1 (os_sched_lock_continuation_split_running
    environment critical saved_local sg call mask before)).
  unfold os_sched_lock_continuation_observation_frame.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]).
  entailer!.
Qed.

Definition os_sched_lock_continuation_saved_facts environment critical sg original mask saved
  before entered acquired : Prop :=
  before.(SchedState).(isRunning) = true /\
  os_sched_continuation_save_effect environment critical sg original mask saved before entered acquired /\
  kernel_call_normal_return original before entered acquired /\
  kernel_call_control_rely sg before acquired /\
  (kernel_call_task_source original before -> kernel_call_task_source entered acquired) /\
  interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
  task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key entered).

Definition os_sched_lock_continuation_counter_frame environment critical saved_local sg entered saved acquired : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    entered.(os_sched_call_invocation) entered.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) entered **
  task_tcb_init_continuation_capsules environment saved_local acquired **
  UCOS2_raw_rep_missing_interrupt sg acquired ** unmap_table_rep sg.

(** The C declaration below reuses TaskCreate's actual modular Save output.
    In particular its current map and source are opened together. *)
Lemma os_sched_lock_continuation_save_counters : forall environment critical saved_local sg
  original mask saved before,
  UCOS2_state_inv sg before -> os_sched_lock_running before = 1 ->
  task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before **
    unmap_table_rep sg |--
  EX entered acquired,
    coq_prop (os_sched_lock_continuation_saved_facts environment critical sg
      original mask saved before entered acquired /\
      0 <= os_sched_lock_locks acquired <= 255) &&
    (sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints acquired **
     sg.(g_OSLockNesting) # UChar |-> os_sched_lock_locks acquired **
     os_sched_lock_continuation_counter_frame environment critical saved_local sg entered saved acquired).
Proof.
  intros environment critical saved_local sg original mask saved before Hvalid Hrunning.
  assert (Hrun : before.(SchedState).(isRunning) = true).
  { unfold os_sched_lock_running in Hrunning.
    destruct before.(SchedState).(isRunning); [reflexivity|discriminate]. }
  unfold task_tcb_init_modular_save_output, kernel_call_modular_save_post.
  Intros entered acquired.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Hsource : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original entered mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before entered acquired) by tauto.
  assert (Hcontrol : kernel_call_control_rely sg before acquired) by tauto.
  assert (Heffect : os_sched_continuation_save_effect environment critical sg
    original mask saved before entered acquired) by (left; exact Hsource).
  pose proof Hsource as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call entered original) by (repeat split; assumption).
  assert (Hpreserved : kernel_call_task_source original before -> kernel_call_task_source entered acquired).
  { intro Hinitial.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff entered original acquired Hsame)).
    eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_restore_input_world
    environment critical saved_local sg entered saved acquired acquired)).
  unfold task_tcb_init_continuation_restore_input.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  sep_apply_l_atomic (os_sched_lock_split_counters sg acquired).
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  Exists entered acquired.
  unfold os_sched_lock_continuation_saved_facts, os_sched_lock_continuation_counter_frame.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

Lemma os_sched_lock_continuation_merge_counters : forall environment critical saved_local sg
  entered saved acquired,
  UCOS2_state_inv sg acquired ->
  task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key entered) ->
  sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints acquired **
  sg.(g_OSLockNesting) # UChar |-> os_sched_lock_updated_locks acquired **
  os_sched_lock_continuation_counter_frame environment critical saved_local sg entered saved acquired |--
  task_tcb_init_continuation_restore_input environment critical saved_local sg entered saved acquired
    (os_sched_lock_checkpoint true acquired) ** unmap_table_rep sg.
Proof.
  intros environment critical saved_local sg entered saved acquired Hvalid Hcoverage.
  unfold os_sched_lock_continuation_counter_frame.
  sep_apply_l_atomic (os_sched_lock_merge_counters sg acquired Hvalid).
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_continuation_capsules.
  cbn [os_sched_lock_checkpoint replace_IntrS TskState].
  repeat rewrite logic_equiv_coq_prop_andp_sepcon.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; exact Hcoverage|].
  entailer!.
Qed.

(** The original observation and final Restore use different state indices.
    Current capsules come from this actual modular Restore, never from an
    outside frame retained across its environment interval. *)
Lemma os_sched_lock_continuation_restore_return : forall environment critical saved_local sg
  original mask saved before entered acquired X,
  os_sched_lock_continuation_saved_facts environment critical sg original mask saved before entered acquired ->
  os_sched_lock_continuation_safe environment critical sg original mask before X ->
  task_tcb_init_modular_restore_output environment critical saved_local sg entered saved
    (os_sched_lock_checkpoint true acquired) ** unmap_table_rep sg |--
  os_sched_lock_continuation_post environment critical saved_local sg original mask before X.
Proof.
  intros environment critical saved_local sg original mask saved before entered acquired X
    [Hrun [Hsave [Hnormal_save [Hcontrol_save [Hsource_save [Hsaved [Hvalid Hcoverage]]]]]]] Hsafe.
  unfold task_tcb_init_modular_restore_output, kernel_call_modular_restore_post.
  Intros returned current.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    entered.(os_sched_call_invocation) None entered.(os_sched_call_origin)
    (os_sched_lock_checkpoint true acquired) false returned.(os_sched_call_origin) current) by tauto.
  assert (Hnormal_restore : kernel_call_normal_return entered
    (os_sched_lock_checkpoint true acquired) returned current) by tauto.
  assert (Hcontrol_restore : kernel_call_control_rely sg
    (os_sched_lock_checkpoint true acquired) current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call returned entered) by exact (proj1 Hnormal_restore).
  assert (Hrestore : os_sched_continuation_restore_effect environment critical sg entered
    (os_sched_lock_checkpoint true acquired) returned current) by (left; split; assumption).
  assert (Hhistory : os_sched_lock_continuation_history environment critical sg
    original mask before returned current).
  { unfold os_sched_lock_continuation_history; rewrite Hrun.
    exists entered, acquired, saved; split; assumption. }
  assert (Hnormal : kernel_call_normal_return original before returned current).
  { eapply kernel_call_normal_return_trans; [exact Hnormal_save|].
    eapply kernel_call_normal_return_trans; [apply os_sched_lock_checkpoint_normal_return|exact Hnormal_restore]. }
  assert (Hsource : kernel_call_task_source original before -> kernel_call_task_source returned current).
  { intro Hinitial.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned entered current Hsame)).
    eapply task_tcb_init_stack_registered_source_preserved.
    - apply os_sched_lock_checkpoint_preserves_validity; exact Hvalid.
    - exact Hsame.
    - exact Htrace.
    - apply os_sched_lock_checkpoint_preserves_task_source; apply Hsource_save; exact Hinitial. }
  pose proof (os_sched_lock_continuation_control_running sg before acquired current
    Hrun Hcontrol_save Hcontrol_restore) as Hcontrol.
  pose proof (os_sched_lock_continuation_safeexec_return environment critical sg original mask
    before returned current X Hhistory Hsafe) as Hcontinue.
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_save_input_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  rewrite (proj2 Hsaved).
  unfold os_sched_lock_continuation_post; Exists returned current.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

Lemma os_sched_lock_continuation_not_running_return : forall environment critical saved_local sg
  original mask before X,
  os_sched_lock_running before <> 1 ->
  os_sched_lock_continuation_safe environment critical sg original mask before X ->
  sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
  os_sched_lock_continuation_observation_frame environment critical saved_local sg original mask before **
  unmap_table_rep sg |--
  os_sched_lock_continuation_post environment critical saved_local sg original mask before X.
Proof.
  intros environment critical saved_local sg original mask before X Hnotrunning Hsafe.
  assert (Hrun : before.(SchedState).(isRunning) = false).
  { unfold os_sched_lock_running in Hnotrunning.
    destruct before.(SchedState).(isRunning); [contradiction|reflexivity]. }
  assert (Hhistory : os_sched_lock_continuation_history environment critical sg
    original mask before original before).
  { unfold os_sched_lock_continuation_history; rewrite Hrun; split; reflexivity. }
  pose proof (os_sched_lock_continuation_safeexec_return environment critical sg original mask
    before original before X Hhistory Hsafe) as Hcontinue.
  pose proof (kernel_call_normal_return_refl original before) as Hnormal.
  pose proof (os_sched_lock_continuation_control_not_running before Hrun) as Hcontrol.
  sep_apply_l_atomic (proj2 (os_sched_lock_continuation_split_running
    environment critical saved_local sg original mask before)).
  unfold os_sched_lock_continuation_post; Exists original before.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

(** Client opening: same X and the actual returned world are available in
    one post.  This is an observation of the completed Lock invocation,
    not a new scheduler-ready or semaphore-admission premise. *)
Lemma os_sched_lock_continuation_post_current_world : forall environment critical saved_local sg
  original mask before X,
  os_sched_lock_continuation_post environment critical saved_local sg original mask before X |--
  EX returned current,
    coq_prop (os_sched_lock_continuation_program environment critical sg original mask before returned current /\
      kernel_call_normal_return original before returned current /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_lock_continuation_control before current /\
      safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X) &&
    kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
      (task_create_continuation_local saved_local) sg (task_stack_call_active_key returned)
      returned mask current.
Proof.
  intros; unfold os_sched_lock_continuation_post; Intros returned current.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Hprogram : os_sched_lock_continuation_program environment critical sg original mask before returned current).
  { apply os_sched_lock_continuation_program_iff; tauto. }
  sep_apply_l_atomic (proj1 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned mask current)).
  Exists returned current.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.
