Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_lock_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.

Import UCOS2_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition os_sched_unlock_continuation_pre environment critical saved_local sg call mask before X : Assertion :=
  coq_prop (os_sched_unlock_continuation_safe environment critical sg call mask before X /\
    kernel_sched_ready_clients critical /\ kernel_tcb_stack_field_layout sg) &&
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask before ** unmap_table_rep sg).

Definition os_sched_unlock_continuation_return_facts environment critical sg original mask before X returned current : Prop :=
  os_sched_unlock_continuation_history environment critical sg original mask before returned current /\
  kernel_call_normal_return original before returned current /\
  (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
  os_sched_unlock_continuation_control before current /\
  safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X.

(** The native no-schedule branch returns its exact current saved-local
    family. The scheduled branch retains the actual Scheduler next_local,
    Fresh receipt and the ORIGINAL padding frame at its real state index.
    This sum never upgrades field resources to a full current Flag map. *)
Definition os_sched_unlock_continuation_return_world environment critical saved_local sg returned mask current : Assertion :=
  (task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current ** unmap_table_rep sg) ||
  (EX reference scheduler_entry next_local,
    coq_prop (os_sched_task_current_ready returned current /\
      flag_active_fresh_registration reference returned current) &&
    (kernel_continuation_call_closed (task_sw_hook_call_environment environment).(task_stack_call_continuations)
      kernel_program_fields_inv next_local sg (task_stack_call_active_key returned) returned mask current **
     flag_configured_padding_rep sg scheduler_entry.(FlagState))).

Definition os_sched_unlock_continuation_post environment critical saved_local sg original mask before X : Assertion :=
  EX returned current,
    coq_prop (os_sched_unlock_continuation_return_facts environment critical sg original mask before X returned current) &&
    os_sched_unlock_continuation_return_world environment critical saved_local sg returned mask current.

Definition os_sched_unlock_continuation_observation_frame := os_sched_lock_continuation_observation_frame.
Definition os_sched_unlock_continuation_counter_frame := os_sched_lock_continuation_counter_frame.

Lemma os_sched_unlock_continuation_pre_open : forall environment critical saved_local sg call mask before X,
  os_sched_unlock_continuation_pre environment critical saved_local sg call mask before X |--
  coq_prop (os_sched_unlock_continuation_safe environment critical sg call mask before X /\
    kernel_sched_ready_clients critical /\ kernel_tcb_stack_field_layout sg /\ UCOS2_state_inv sg before) &&
  (sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
   os_sched_unlock_continuation_observation_frame environment critical saved_local sg call mask before **
   unmap_table_rep sg).
Proof.
  intros; unfold os_sched_unlock_continuation_pre, os_sched_unlock_continuation_observation_frame.
  apply coq_prop_andp_left; intros [Hsafe [Hclients Hlayout]].
  sep_apply_l_atomic (proj1 (os_sched_lock_continuation_split_running environment critical saved_local sg call mask before)).
  unfold os_sched_lock_continuation_observation_frame, os_sched_unlock_running, os_sched_lock_running.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]).
  entailer!.
Qed.

Definition os_sched_unlock_continuation_saved_facts environment critical sg original mask saved before entered acquired : Prop :=
  os_sched_lock_continuation_saved_facts environment critical sg original mask saved before entered acquired /\
  UCOS2_state_inv sg before /\
  kernel_call_save_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical sg original entered mask saved before acquired.

Lemma os_sched_unlock_continuation_save_counters : forall environment critical saved_local sg original mask saved before,
  UCOS2_state_inv sg before -> os_sched_unlock_running before = 1 ->
  task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before ** unmap_table_rep sg |--
  EX entered acquired,
    coq_prop (os_sched_unlock_continuation_saved_facts environment critical sg original mask saved before entered acquired /\
      0 <= os_sched_ints acquired <= 255 /\ 0 <= os_sched_locks acquired <= 255) &&
    (sg.(g_OSIntNesting) # UChar |-> os_sched_ints acquired **
     sg.(g_OSLockNesting) # UChar |-> os_sched_locks acquired **
     os_sched_unlock_continuation_counter_frame environment critical saved_local sg entered saved acquired).
Proof.
  intros environment critical saved_local sg original mask saved before Hvalid Hrunning.
  assert (Hrun : before.(SchedState).(isRunning) = true).
  { unfold os_sched_unlock_running in Hrunning; destruct before.(SchedState).(isRunning); [reflexivity|discriminate]. }
  unfold task_tcb_init_modular_save_output, kernel_call_modular_save_post; Intros entered acquired.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Hsource : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original entered mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before entered acquired) by tauto.
  assert (Hcontrol : kernel_call_control_rely sg before acquired) by tauto.
  assert (Heffect : os_sched_continuation_save_effect environment critical sg original mask saved before entered acquired)
    by (left; exact Hsource).
  pose proof Hsource as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call entered original) by (repeat split; assumption).
  assert (Hpreserved : kernel_call_task_source original before -> kernel_call_task_source entered acquired).
  { intro Hinitial; apply (proj2 (task_tcb_init_stack_same_call_source_iff entered original acquired Hsame)).
    eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_restore_input_world environment critical saved_local sg entered saved acquired acquired)).
  unfold task_tcb_init_continuation_restore_input, UCOS2_inv.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  sep_apply_l_atomic (os_sched_unlock_split_counters sg acquired).
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  Exists entered acquired.
  unfold os_sched_unlock_continuation_saved_facts, os_sched_lock_continuation_saved_facts,
    os_sched_unlock_continuation_counter_frame, os_sched_lock_continuation_counter_frame.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

Lemma os_sched_unlock_continuation_merge_counters : forall environment critical saved_local sg entered saved acquired,
  UCOS2_state_inv sg acquired ->
  task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key entered) ->
  sg.(g_OSIntNesting) # UChar |-> os_sched_ints acquired **
  sg.(g_OSLockNesting) # UChar |-> os_sched_unlock_counted_locks acquired **
  os_sched_unlock_continuation_counter_frame environment critical saved_local sg entered saved acquired |--
  task_tcb_init_continuation_restore_input environment critical saved_local sg entered saved acquired
    (os_sched_unlock_checkpoint true acquired) ** unmap_table_rep sg.
Proof.
  intros environment critical saved_local sg entered saved acquired Hvalid Hcoverage.
  unfold os_sched_unlock_continuation_counter_frame, os_sched_lock_continuation_counter_frame.
  sep_apply_l_atomic (os_sched_unlock_merge_counters sg acquired Hvalid).
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_continuation_capsules.
  cbn [os_sched_unlock_checkpoint replace_IntrS TskState].
  repeat rewrite logic_equiv_coq_prop_andp_sepcon.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; exact Hcoverage|].
  entailer!.
Qed.

Definition os_sched_unlock_continuation_restored_facts environment critical sg original mask before acquired restored unlocked : Prop :=
  os_sched_unlock_continuation_prefix environment critical sg original mask before acquired restored unlocked /\
  kernel_call_normal_return original before restored unlocked /\
  (kernel_call_task_source original before -> kernel_call_task_source restored unlocked) /\
  os_sched_unlock_continuation_control before unlocked /\
  kernel_call_control_rely sg (os_sched_unlock_checkpoint true acquired) unlocked /\
  UCOS2_state_inv sg unlocked /\
  (before.(SchedState).(readyList) <> [] -> unlocked.(SchedState).(readyList) <> []).

Definition os_sched_unlock_continuation_restored_post environment critical saved_local sg original mask
  before acquired : Assertion :=
  EX restored unlocked,
    coq_prop (os_sched_unlock_continuation_restored_facts environment critical sg original mask before acquired restored unlocked) &&
    (task_tcb_init_continuation_save_input environment critical saved_local sg restored mask unlocked ** unmap_table_rep sg).

Lemma os_sched_unlock_continuation_restore_return : forall environment critical saved_local sg original mask saved
  before entered acquired,
  kernel_sched_ready_clients critical ->
  os_sched_unlock_continuation_saved_facts environment critical sg original mask saved before entered acquired ->
  task_tcb_init_modular_restore_output environment critical saved_local sg entered saved
    (os_sched_unlock_checkpoint true acquired) ** unmap_table_rep sg |--
  os_sched_unlock_continuation_restored_post environment critical saved_local sg original mask before acquired.
Proof.
  intros environment critical saved_local sg original mask saved before entered acquired Hclients
    [[Hrun [Hsave [Hnormal_save [Hcontrol_save [Hsource_save [Hsaved [Hvalid Hcoverage]]]]]]] [Hinitial Hsave_source]].
  unfold task_tcb_init_modular_restore_output, kernel_call_modular_restore_post; Intros restored unlocked.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg entered.(os_sched_call_invocation)
    None entered.(os_sched_call_origin) (os_sched_unlock_checkpoint true acquired) false restored.(os_sched_call_origin) unlocked) by tauto.
  assert (Hnormal_restore : kernel_call_normal_return entered (os_sched_unlock_checkpoint true acquired) restored unlocked) by tauto.
  assert (Hcontrol_restore : kernel_call_control_rely sg (os_sched_unlock_checkpoint true acquired) unlocked) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call restored entered) by exact (proj1 Hnormal_restore).
  assert (Hrestore : os_sched_continuation_restore_effect environment critical sg entered
    (os_sched_unlock_checkpoint true acquired) restored unlocked) by (left; split; assumption).
  assert (Hprefix : os_sched_unlock_continuation_prefix environment critical sg original mask before acquired restored unlocked).
  { split; [exact Hrun|]. exists entered, saved; split; assumption. }
  assert (Hnormal : kernel_call_normal_return original before restored unlocked).
  { eapply kernel_call_normal_return_trans; [exact Hnormal_save|].
    eapply kernel_call_normal_return_trans; [apply os_sched_unlock_checkpoint_normal_return|exact Hnormal_restore]. }
  assert (Hsource : kernel_call_task_source original before -> kernel_call_task_source restored unlocked).
  { intro Horiginal; apply (proj2 (task_tcb_init_stack_same_call_source_iff restored entered unlocked Hsame)).
    eapply task_tcb_init_stack_registered_source_preserved.
    - apply os_sched_unlock_checkpoint_preserves_validity; exact Hvalid.
    - exact Hsame.
    - exact Htrace.
    - apply os_sched_unlock_checkpoint_preserves_task_source; apply Hsource_save; exact Horiginal. }
  pose proof (os_sched_unlock_continuation_control_running sg before acquired unlocked Hrun Hcontrol_save Hcontrol_restore) as Hcontrol.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave_source) as Hsave_interval.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hrestore_interval.
  assert (Hready : before.(SchedState).(readyList) <> [] -> unlocked.(SchedState).(readyList) <> []).
  { intro Hready_before.
    eapply critical_region_interval_preserves_sched_ready.
    - exact Hclients.
    - exact Hrestore_interval.
    - apply os_sched_unlock_checkpoint_preserves_validity; exact Hvalid.
    - change (acquired.(SchedState).(readyList) <> []).
      eapply critical_region_interval_preserves_sched_ready; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_save_input_world environment critical saved_local sg restored (armv7a_irq_fiq_mask saved) unlocked)).
  rewrite (proj2 Hsaved).
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  unfold os_sched_unlock_continuation_restored_post; Exists restored unlocked.
  unfold os_sched_unlock_continuation_restored_facts,
    task_tcb_init_continuation_save_input, task_create_continuation_input.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]).
  entailer!.
Qed.

(** One real SOURCE consequence at this endpoint. It is only sufficient,
    not a stronger public precondition: retired-storage callers may instead
    supply their existing direct cut. No locked cut is used in this proof. *)
Lemma os_sched_unlock_restored_cut_from_source : forall environment critical sg original mask before acquired restored unlocked,
  os_sched_unlock_continuation_restored_facts environment critical sg original mask before acquired restored unlocked ->
  kernel_tcb_stack_field_layout sg -> kernel_call_task_source original before ->
  kernel_call_stack_available original before -> before.(SchedState).(readyList) <> [] ->
  os_sched_call_cut sg restored unlocked.
Proof.
  intros environment critical sg original mask before acquired restored unlocked
    [Hprefix [Hnormal [Hsource [Hcontrol [Hrestore_control [Hvalid Hready]]]]]] Hlayout Hinitial Havailable Hnonempty.
  assert (Hcurrent : kernel_call_task_source restored unlocked) by (apply Hsource; exact Hinitial).
  eapply os_sched_call_cut_from_source; try eassumption.
  - apply Hready; exact Hnonempty.
  - apply (proj2 Hnormal); exact Havailable.
  - eapply kernel_call_task_source_stack_field_address; eassumption.
Qed.

(** The branch decision was made at acquired. The actual modular Restore
    returns its own state, and its C control rely transports exactly the
    two counters needed by the selected Scheduler interface. *)
Lemma os_sched_unlock_restored_schedule_control : forall environment critical sg original mask
  before acquired restored unlocked,
  os_sched_unlock_continuation_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_requests acquired = true ->
  os_sched_ints unlocked = 0 /\ os_sched_locks unlocked = 0 /\
  unlocked.(SchedState).(isRunning) = true /\ os_sched_selection_enabled unlocked = true.
Proof.
  intros environment critical sg original mask before acquired restored unlocked
    [Hprefix [Hnormal [Hsource [[Hrunning Hcounter] [Hrestore_control [Hvalid Hready]]]]]] Hrequest.
  pose proof (os_sched_unlock_request_checkpoint true acquired Hrequest) as [Hints Hlocks].
  pose proof (proj2 Hrestore_control) as Hcurrent.
  split; [unfold os_sched_ints; rewrite Hcurrent; exact Hints|].
  split; [unfold os_sched_locks; rewrite Hcurrent; exact Hlocks|].
  split; [rewrite Hrunning; exact (proj1 Hprefix)|].
  unfold os_sched_selection_enabled; rewrite Hcurrent, Hints, Hlocks; reflexivity.
Qed.

Lemma os_sched_unlock_continuation_no_schedule_return : forall environment critical saved_local sg original mask
  before acquired X,
  os_sched_unlock_requests acquired = false ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  os_sched_unlock_continuation_restored_post environment critical saved_local sg original mask before acquired |--
  os_sched_unlock_continuation_post environment critical saved_local sg original mask before X.
Proof.
  intros environment critical saved_local sg original mask before acquired X Hrequest Hsafe heap
    [restored [unlocked [[Hprefix [Hnormal [Hsource [Hcontrol [Hrestore_control [Hvalid Hready]]]]]] Howned]]].
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before restored unlocked).
  { unfold os_sched_unlock_continuation_history; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hprefix|].
    unfold os_sched_unlock_tail_program; rewrite Hrequest; split; reflexivity. }
  exists restored, unlocked; split.
  - unfold os_sched_unlock_continuation_return_facts.
    split; [exact Hhistory|]. split; [exact Hnormal|].
    split; [exact Hsource|]. split; [exact Hcontrol|].
    eapply os_sched_unlock_continuation_safeexec_return; eassumption.
  - left; exact Howned.
Qed.

Lemma os_sched_unlock_continuation_scheduled_return : forall environment critical saved_local sg original mask
  before acquired restored unlocked X,
  os_sched_unlock_requests acquired = true ->
  os_sched_unlock_continuation_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  SchedulerPhaseCandidate.os_sched_task_history_return_post (task_sw_hook_call_environment environment) critical
    (PendPhaseCandidate.flag_pend_fresh_observation restored) sg restored mask unlocked **
    flag_configured_padding_rep sg unlocked.(FlagState) |--
  os_sched_unlock_continuation_post environment critical saved_local sg original mask before X.
Proof.
  intros environment critical saved_local sg original mask before acquired restored unlocked X Hrequest
    [Hprefix [Hnormal_prefix [Hsource_prefix [Hcontrol_prefix [Hrestore_control [Hvalid Hready_prefix]]]]]] Hsafe.
  sep_apply_l_atomic (os_sched_unlock_task_scheduler_fresh_return environment critical sg restored mask unlocked
    (flag_configured_padding_rep sg unlocked.(FlagState))).
  Intros returned current next_local.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Hsched : SchedulerPhaseCandidate.os_sched_task_call_history (task_sw_hook_call_environment environment)
    critical sg restored mask unlocked returned current) by tauto.
  assert (Hnormal_sched : kernel_call_normal_return restored unlocked returned current) by tauto.
  assert (Hsource_sched : kernel_call_task_source restored unlocked -> kernel_call_task_source returned current) by tauto.
  assert (Hcontrol_sched : kernel_call_control_rely sg unlocked current) by tauto.
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before returned current).
  { unfold os_sched_unlock_continuation_history; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hprefix|].
    unfold os_sched_unlock_tail_program; rewrite Hrequest.
    apply SchedulerPhaseCandidate.os_sched_task_program_iff; exact Hsched. }
  assert (Hnormal : kernel_call_normal_return original before returned current)
    by (eapply kernel_call_normal_return_trans; eassumption).
  assert (Hsource : kernel_call_task_source original before -> kernel_call_task_source returned current) by auto.
  assert (Hcontrol : os_sched_unlock_continuation_control before current)
    by (eapply os_sched_unlock_continuation_control_sched; eassumption).
  pose proof (os_sched_unlock_continuation_safeexec_return environment critical sg original mask before returned current X Hhistory Hsafe) as Hcontinue.
  unfold os_sched_unlock_continuation_post; Exists returned current.
  unfold os_sched_unlock_continuation_return_facts, os_sched_unlock_continuation_return_world.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  Right; Exists restored unlocked next_local.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

Lemma os_sched_unlock_continuation_not_running_return : forall environment critical saved_local sg original mask before X,
  os_sched_unlock_running before <> 1 ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
  os_sched_unlock_continuation_observation_frame environment critical saved_local sg original mask before ** unmap_table_rep sg |--
  os_sched_unlock_continuation_post environment critical saved_local sg original mask before X.
Proof.
  intros environment critical saved_local sg original mask before X Hnotrunning Hsafe.
  assert (Hrun : before.(SchedState).(isRunning) = false).
  { unfold os_sched_unlock_running in Hnotrunning; destruct before.(SchedState).(isRunning); [contradiction|reflexivity]. }
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before original before).
  { unfold os_sched_unlock_continuation_history; rewrite Hrun; split; reflexivity. }
  pose proof (os_sched_unlock_continuation_safeexec_return environment critical sg original mask before original before X Hhistory Hsafe) as Hcontinue.
  pose proof (kernel_call_normal_return_refl original before) as Hnormal.
  pose proof (os_sched_unlock_continuation_control_not_running before Hrun) as Hcontrol.
  change ((sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
    os_sched_lock_continuation_observation_frame environment critical saved_local sg original mask before ** unmap_table_rep sg) |--
    os_sched_unlock_continuation_post environment critical saved_local sg original mask before X).
  sep_apply_l_atomic (proj2 (os_sched_lock_continuation_split_running environment critical saved_local sg original mask before)).
  unfold os_sched_unlock_continuation_post; Exists original before.
  unfold os_sched_unlock_continuation_return_facts, os_sched_unlock_continuation_return_world.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]. Left; entailer!.
Qed.
