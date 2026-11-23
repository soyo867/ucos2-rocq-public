Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_fields_resource_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_continuation_resource_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_task_scheduler_adapter_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_idle_ready.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Import UCOS2_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition os_sched_unlock_fields_pre environment critical local sg call mask before X : Assertion :=
  coq_prop (os_sched_unlock_continuation_safe environment critical sg call mask before X /\
    kernel_sched_ready_clients critical /\ kernel_tcb_stack_field_layout sg) &&
  os_sched_fields_closed environment local sg call mask before.

Definition os_sched_unlock_fields_return_sources environment critical sg original mask before returned current : Prop :=
  if before.(SchedState).(isRunning) then
    exists acquired restored unlocked,
      os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
        environment critical sg original mask before acquired restored unlocked /\
      os_sched_unlock_tail_program environment critical sg mask (os_sched_unlock_requests acquired)
        restored unlocked returned current
  else returned = original /\ current = before.

(** The native branch retains the current arbitrary input family. The
    Scheduler branch returns its ACTUAL next_local. No full Flag owner is
    required or discarded; an existing padding owner remains an outer frame. *)
Definition os_sched_unlock_fields_return_world environment local sg returned mask current : Assertion :=
  os_sched_fields_closed environment local sg returned mask current ||
  (EX reference next_local,
    coq_prop (os_sched_task_current_ready returned current /\
      flag_active_fresh_registration reference returned current) &&
    os_sched_fields_closed environment next_local sg returned mask current).

Definition os_sched_unlock_fields_post environment critical local sg original mask before X : Assertion :=
  EX returned current,
    coq_prop (os_sched_unlock_continuation_return_facts environment critical sg original mask before X returned current /\
      os_sched_unlock_fields_return_sources environment critical sg original mask before returned current) &&
    os_sched_unlock_fields_return_world environment local sg returned mask current.

Lemma os_sched_unlock_fields_pre_open : forall environment critical local sg call mask before X,
  os_sched_unlock_fields_pre environment critical local sg call mask before X |--
  coq_prop (os_sched_unlock_continuation_safe environment critical sg call mask before X /\
    kernel_sched_ready_clients critical /\ kernel_tcb_stack_field_layout sg /\ UCOS2_state_inv sg before) &&
  (sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
   os_sched_fields_observation_frame environment local sg call mask before).
Proof.
  intros; unfold os_sched_unlock_fields_pre.
  apply coq_prop_andp_left; intros [Hsafe [Hclients Hlayout]].
  rewrite os_sched_fields_split_running; unfold os_sched_fields_observation_frame,
    os_sched_unlock_running, os_sched_lock_running.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]).
  entailer!.
Qed.

Lemma os_sched_unlock_fields_save_counters : forall environment critical local sg original mask saved before,
  UCOS2_state_inv sg before -> os_sched_unlock_running before = 1 ->
  os_sched_fields_save_output environment critical local sg original mask saved before |--
  EX entered acquired,
    coq_prop (os_sched_unlock_continuation_saved_facts environment critical sg
      original mask saved before entered acquired /\
      0 <= os_sched_ints acquired <= 255 /\ 0 <= os_sched_locks acquired <= 255) &&
    (sg.(g_OSIntNesting) # UChar |-> os_sched_ints acquired **
     sg.(g_OSLockNesting) # UChar |-> os_sched_locks acquired **
     os_sched_fields_counter_frame environment critical local sg entered saved acquired).
Proof.
  intros environment critical local sg original mask saved before Hvalid Hrunning.
  assert (Hrun : before.(SchedState).(isRunning) = true).
  { unfold os_sched_unlock_running in Hrunning; destruct before.(SchedState).(isRunning);
      [reflexivity|discriminate]. }
  unfold os_sched_fields_save_output, kernel_call_modular_save_post; Intros entered acquired.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Hsource : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original entered mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before entered acquired) by tauto.
  assert (Hcontrol : kernel_call_control_rely sg before acquired) by tauto.
  assert (Heffect : os_sched_continuation_save_effect environment critical sg original mask saved before entered acquired)
    by (left; exact Hsource).
  assert (Hpreserved : kernel_call_task_source original before -> kernel_call_task_source entered acquired).
  { intro Hinitial; eapply kernel_call_save_source_preserves_task_source; eassumption. }
  pose proof Hsource as [Htrace [Hi [Ho [Hs Hsaved]]]].
  lazymatch goal with |- _ |-- ?post =>
    change (os_sched_fields_masked environment critical local sg entered saved acquired acquired |-- post)
  end.
  sep_apply_l_atomic (os_sched_fields_masked_split_counters environment critical local sg entered saved acquired).
  apply coq_prop_andp_left; intro Hcounters.
  Exists entered acquired; unfold os_sched_unlock_continuation_saved_facts,
    os_sched_lock_continuation_saved_facts, os_sched_lock_ints, os_sched_lock_locks,
    os_sched_ints, os_sched_locks.
  unfold os_sched_lock_ints, os_sched_lock_locks in Hcounters.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

Lemma os_sched_unlock_fields_merge_counters : forall environment critical local sg entered saved acquired,
  UCOS2_state_inv sg acquired ->
  task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key entered) ->
  sg.(g_OSIntNesting) # UChar |-> os_sched_ints acquired **
  sg.(g_OSLockNesting) # UChar |-> os_sched_unlock_counted_locks acquired **
  os_sched_fields_counter_frame environment critical local sg entered saved acquired |--
  os_sched_fields_masked environment critical local sg entered saved acquired
    (os_sched_unlock_checkpoint true acquired).
Proof.
  intros environment critical local sg entered saved acquired Hvalid Hcoverage.
  pose proof (os_sched_fields_merge_interrupt environment critical local sg entered saved acquired
    (sched_unlock_state true acquired.(IntrState))
    (os_sched_unlock_checkpoint_preserves_validity sg true acquired Hvalid) Hcoverage) as Hmerge.
  unfold store_int_state in Hmerge.
  assert (Hint : (sched_unlock_state true acquired.(IntrState)).(intNesting) = acquired.(IntrState).(intNesting)).
  { unfold sched_unlock_state; simpl; destruct (acquired.(IntrState).(intNesting) =? 0);
      [destruct (0 <? acquired.(IntrState).(lockNesting))|]; reflexivity. }
  rewrite Hint in Hmerge; unfold os_sched_ints, os_sched_unlock_counted_locks.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Definition os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked : Prop :=
  os_sched_unlock_continuation_restored_facts environment critical sg original mask before acquired restored unlocked /\
  os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked.

Definition os_sched_unlock_fields_restored_post environment critical local sg original mask before acquired : Assertion :=
  EX restored unlocked,
    coq_prop (os_sched_unlock_fields_restored_facts environment critical sg
      original mask before acquired restored unlocked) &&
    os_sched_fields_closed environment local sg restored mask unlocked.

Lemma os_sched_unlock_fields_restore_return : forall environment critical local sg original mask saved
  before entered acquired,
  kernel_sched_ready_clients critical ->
  os_sched_unlock_continuation_saved_facts environment critical sg original mask saved before entered acquired ->
  os_sched_fields_restore_output environment critical local sg entered saved
    (os_sched_unlock_checkpoint true acquired) |--
  os_sched_unlock_fields_restored_post environment critical local sg original mask before acquired.
Proof.
  intros environment critical local sg original mask saved before entered acquired Hclients
    [[Hrun [Hsave [Hnormal_save [Hcontrol_save [Hsource_save [Hsaved [Hvalid Hcoverage]]]]]]] [Hinitial Hsave_source]].
  unfold os_sched_fields_restore_output, kernel_call_modular_restore_post; Intros restored unlocked.
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
  assert (Hsources : os_sched_fields_checkpoint_sources (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked).
  { exists entered, saved; split; [exact Hsave_source|]. split; assumption. }
  rewrite (proj2 Hsaved).
  unfold kernel_continuation_call_closed, kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  unfold os_sched_unlock_fields_restored_post; Exists restored unlocked.
  unfold os_sched_unlock_fields_restored_facts, os_sched_unlock_continuation_restored_facts, os_sched_fields_closed,
    kernel_continuation_call_closed, kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]).
  entailer!.
Qed.

(** The exact acquired branch decision plus real Restore control gives
    the enabled entry. Source/available and a nonempty ready list use the
    actual prefix producers; current-cache consistency, Idle and clear
    fields are still separate observations of THIS restored endpoint. *)
Lemma os_sched_unlock_fields_fresh_scheduler_pre : forall environment critical local sg original mask
  before acquired restored unlocked,
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_requests acquired = true ->
  kernel_sched_ready_clients critical -> kernel_tcb_stack_field_layout sg ->
  kernel_call_task_source original before -> kernel_call_stack_available original before ->
  before.(SchedState).(readyList) <> [] ->
  sched_current_consistency unlocked.(TskState) unlocked.(SchedState) ->
  task_idle_ready sg unlocked.(TskState) ->
  (forall node, unlocked.(TskState).(inUsedTaskStates)
    restored.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    flag_active_event_clear node /\ node.(tcbFlagNode) = 0) ->
  os_sched_fields_closed environment local sg restored mask unlocked |--
  os_sched_unlock_task_scheduler_pre environment critical local
    (PendPhaseCandidate.flag_pend_fresh_observation restored) sg restored mask unlocked.
Proof.
  intros environment critical local sg original mask before acquired restored unlocked Hfacts Hrequest
    Hclients Hlayout Hsource Havailable Hready Hcache Hidle Hfields.
  destruct Hfacts as [Hfacts Hsources].
  pose proof (os_sched_unlock_restored_cut_from_source environment critical sg original mask before acquired
    restored unlocked Hfacts Hlayout Hsource Havailable Hready) as Hcut.
  destruct (os_sched_unlock_restored_schedule_control environment critical sg original mask before acquired
    restored unlocked Hfacts Hrequest) as [Hints [Hlocks [Hrunning Henabled]]].
  destruct Hfacts as [Hprefix [Hnormal [Hsource' Hrest]]].
  specialize (Hsource' Hsource).
  pose proof (proj2 Hnormal Havailable) as Havailable'.
  assert (Hentry : SchedulerCalleePhaseComponent.os_sched_task_entry_observation restored unlocked).
  { split; [exact Hsource'|]. split; assumption. }
  destruct (kernel_call_task_source_current_at restored unlocked Hsource') as [_ [node [Hnode Hgen]]].
  destruct (Hfields node Hnode) as [Hclear Hflag].
  assert (Hfresh : flag_active_fresh_registration restored restored unlocked).
  { eapply os_sched_unlock_source_fresh_registration; eassumption. }
  unfold os_sched_fields_closed.
  rewrite <- (os_sched_unlock_configured_closed_world_eq environment kernel_program_fields_inv
    local sg (task_stack_call_active_key restored) restored mask unlocked).
  apply os_sched_unlock_task_scheduler_fresh_pre; assumption.
Qed.

Lemma os_sched_unlock_fields_no_schedule_return : forall environment critical local sg original mask before acquired X,
  os_sched_unlock_requests acquired = false ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  os_sched_unlock_fields_restored_post environment critical local sg original mask before acquired |--
  os_sched_unlock_fields_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before acquired X Hrequest Hsafe heap
    [restored [unlocked [[[Hprefix [Hnormal [Hsource [Hcontrol [Hrestore_control [Hvalid Hready]]]]]] Hsources] Howned]]].
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before restored unlocked).
  { unfold os_sched_unlock_continuation_history; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hprefix|].
    unfold os_sched_unlock_tail_program; rewrite Hrequest; split; reflexivity. }
  exists restored, unlocked; split.
  - split; [|unfold os_sched_unlock_fields_return_sources; rewrite (proj1 Hprefix);
      exists acquired, restored, unlocked; split; [exact Hsources|];
      unfold os_sched_unlock_tail_program; rewrite Hrequest; split; reflexivity].
    unfold os_sched_unlock_continuation_return_facts.
    split; [exact Hhistory|]. split; [exact Hnormal|]. split; [exact Hsource|].
    split; [exact Hcontrol|]. eapply os_sched_unlock_continuation_safeexec_return; eassumption.
  - left; exact Howned.
Qed.

Lemma os_sched_unlock_fields_scheduled_return : forall environment critical local sg original mask
  before acquired restored unlocked X,
  os_sched_unlock_requests acquired = true ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  SchedulerPhaseCandidate.os_sched_task_history_return_post (task_sw_hook_call_environment environment) critical
    (PendPhaseCandidate.flag_pend_fresh_observation restored) sg restored mask unlocked |--
  os_sched_unlock_fields_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before acquired restored unlocked X Hrequest
    [[Hprefix [Hnormal_prefix [Hsource_prefix [Hcontrol_prefix [Hrestore_control [Hvalid Hready_prefix]]]]]] Hsources] Hsafe.
  unfold SchedulerPhaseCandidate.os_sched_task_history_return_post,
    PendPhaseCandidate.flag_pend_fresh_observation; Intros returned current next_local.
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
  pose proof (os_sched_unlock_continuation_safeexec_return environment critical sg original mask
    before returned current X Hhistory Hsafe) as Hcontinue.
  assert (Hreturn_sources : os_sched_unlock_fields_return_sources environment critical sg original mask before returned current).
  { unfold os_sched_unlock_fields_return_sources; rewrite (proj1 Hprefix).
    exists acquired, restored, unlocked; split; [exact Hsources|].
    unfold os_sched_unlock_tail_program; rewrite Hrequest.
    apply SchedulerPhaseCandidate.os_sched_task_program_iff; exact Hsched. }
  rewrite (os_sched_unlock_configured_closed_world_eq environment kernel_program_fields_inv
    next_local sg (task_stack_call_active_key returned) returned mask current).
  unfold os_sched_unlock_fields_post; Exists returned current.
  unfold os_sched_unlock_continuation_return_facts, os_sched_unlock_fields_return_world.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  Right; Exists restored next_local.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  unfold os_sched_fields_closed; entailer!.
Qed.

Lemma os_sched_unlock_fields_not_running_return : forall environment critical local sg original mask before X,
  os_sched_unlock_running before <> 1 ->
  os_sched_unlock_continuation_safe environment critical sg original mask before X ->
  sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
    os_sched_fields_observation_frame environment local sg original mask before |--
  os_sched_unlock_fields_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before X Hnotrunning Hsafe.
  assert (Hrun : before.(SchedState).(isRunning) = false).
  { unfold os_sched_unlock_running in Hnotrunning; destruct before.(SchedState).(isRunning);
      [contradiction|reflexivity]. }
  assert (Hhistory : os_sched_unlock_continuation_history environment critical sg original mask before original before).
  { unfold os_sched_unlock_continuation_history; rewrite Hrun; split; reflexivity. }
  pose proof (os_sched_unlock_continuation_safeexec_return environment critical sg original mask
    before original before X Hhistory Hsafe) as Hcontinue.
  pose proof (kernel_call_normal_return_refl original before) as Hnormal.
  pose proof (os_sched_unlock_continuation_control_not_running before Hrun) as Hcontrol.
  assert (Hsources : os_sched_unlock_fields_return_sources environment critical sg original mask before original before).
  { unfold os_sched_unlock_fields_return_sources; rewrite Hrun; split; reflexivity. }
  lazymatch goal with |- _ |-- ?post =>
    change ((sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
      os_sched_fields_observation_frame environment local sg original mask before) |-- post)
  end.
  sep_apply_l_atomic (proj2 (os_sched_fields_split_running environment local sg original mask before)).
  unfold os_sched_unlock_fields_post; Exists original before.
  unfold os_sched_unlock_continuation_return_facts, os_sched_unlock_fields_return_world.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]. Left; entailer!.
Qed.

Lemma os_sched_unlock_fields_return_current_world : forall environment local sg returned mask current,
  os_sched_unlock_fields_return_world environment local sg returned mask current |--
  EX next_local, os_sched_fields_closed environment next_local sg returned mask current.
Proof.
  intros environment local sg returned mask current heap [Hnative | [reference [next_local [Hfacts Hscheduled]]]].
  - exists local; exact Hnative.
  - exists next_local; exact Hscheduled.
Qed.
