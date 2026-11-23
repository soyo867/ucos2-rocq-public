Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_continuation_resource_spec.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Generic CURRENT field worlds. [local] is the actual input family;
    it is not reconstructed from TaskCreate or strengthened with padding.
    The modular primitive's source obligation is to return this selected
    resource family, as in kernel_call_modular_spec. Byte localization
    below does not itself prove that environmental source obligation. *)
Definition os_sched_fields_closed environment local sg call mask state : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state.

Definition os_sched_fields_masked environment critical local sg call saved acquired state : Assertion :=
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sg (task_stack_call_active_key call)
    call saved acquired state.

Definition os_sched_fields_save_output environment critical local sg original mask saved before : Assertion :=
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical kernel_call_control_rely sg original mask saved before.

Definition os_sched_fields_restore_output environment critical local sg original saved released : Assertion :=
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical kernel_call_control_rely sg original
    (armv7a_irq_fiq_mask saved) released.

(** The SAME two actual modular intervals, retained before a sum-shaped
    high-level history could forget which source alternative was used. *)
Definition os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask
  before acquired returned current : Prop :=
  exists entered saved,
    kernel_call_save_source environment.(task_stack_call_external) environment.(task_stack_call_port)
      critical sg original entered mask saved before acquired /\
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      entered.(os_sched_call_invocation) None entered.(os_sched_call_origin)
      (checkpoint acquired) false returned.(os_sched_call_origin) current /\
    task_tcb_init_stack_same_call returned entered.

Definition os_sched_lock_fields_saved_facts environment critical sg original mask saved before entered acquired : Prop :=
  os_sched_lock_continuation_saved_facts environment critical sg original mask saved before entered acquired /\
  kernel_call_save_source environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical sg original entered mask saved before acquired.

Definition os_sched_lock_fields_return_sources environment critical sg original mask before returned current : Prop :=
  if before.(SchedState).(isRunning) then
    exists acquired, os_sched_fields_checkpoint_sources (os_sched_lock_checkpoint true)
      environment critical sg original mask before acquired returned current
  else returned = original /\ current = before.

Definition os_sched_fields_observation_frame environment local sg call mask state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask **
   sched_raw_rep_without_running sg state.(TskState) state.(SchedState) **
   UCOS2_fields_raw_rep_missing_module sg state SchedModule ** unmap_table_rep sg **
   store_parked_continuations
     (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState) local)
     state.(TskState).(parkedTaskStacks)).

Lemma os_sched_fields_split_running : forall environment local sg call mask state,
  os_sched_fields_closed environment local sg call mask state --||--
  (sg.(g_OSRunning) # UChar |-> os_sched_lock_running state **
   os_sched_fields_observation_frame environment local sg call mask state).
Proof.
  intros; unfold os_sched_fields_closed, kernel_continuation_call_closed,
    kernel_continuation_inv, kernel_program_fields_inv, kernel_program_fields_rep.
  rewrite (UCOS2_fields_raw_rep_split_module sg state SchedModule) by discriminate.
  cbn [UCOS2_module_rep]. rewrite sched_raw_rep_split_running.
  unfold os_sched_fields_observation_frame, os_sched_lock_running.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  split; repeat (apply coq_prop_andp_left; intro);
    repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]);
    entailer!.
Qed.

Definition os_sched_fields_counter_frame environment critical local sg call saved acquired : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  UCOS2_fields_raw_rep_missing_module sg acquired InterruptModule ** unmap_table_rep sg **
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations) acquired.(TskState) local)
    acquired.(TskState).(parkedTaskStacks).

Lemma os_sched_fields_masked_split_counters : forall environment critical local sg call saved acquired,
  os_sched_fields_masked environment critical local sg call saved acquired acquired |--
  coq_prop (UCOS2_state_inv sg acquired /\
    task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key call) /\
    0 <= os_sched_lock_ints acquired <= 255 /\ 0 <= os_sched_lock_locks acquired <= 255) &&
  (sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints acquired **
   sg.(g_OSLockNesting) # UChar |-> os_sched_lock_locks acquired **
   os_sched_fields_counter_frame environment critical local sg call saved acquired).
Proof.
  intros; unfold os_sched_fields_masked, kernel_continuation_call_masked,
    kernel_continuation_inv, kernel_program_fields_inv, kernel_program_fields_rep.
  rewrite (UCOS2_fields_raw_rep_split_module sg acquired InterruptModule) by discriminate.
  cbn [UCOS2_module_rep]. unfold interrupt_inv, store_int_state,
    os_sched_lock_ints, os_sched_lock_locks, os_sched_fields_counter_frame.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  apply UCOS2_C_Rules._derivable1_andp_intros.
  - sep_apply_l_atomic (store_uchar_range sg.(g_OSIntNesting) acquired.(IntrState).(intNesting)).
    sep_apply_l_atomic (store_uchar_range sg.(g_OSLockNesting) acquired.(IntrState).(lockNesting)).
    entailer!; apply derivable1s_coq_prop_r;
    change (UCOS2_state_inv sg acquired /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key call) /\
      0 <= acquired.(IntrState).(intNesting) <= Byte.max_unsigned /\
      0 <= acquired.(IntrState).(lockNesting) <= Byte.max_unsigned);
    tauto.
  - entailer!.
Qed.

Lemma os_sched_fields_interrupt_frame_replace : forall sg state counters,
  UCOS2_fields_raw_rep_missing_module sg state InterruptModule =
  UCOS2_fields_raw_rep_missing_module sg (replace_IntrS counters state) InterruptModule.
Proof.
  intros; apply UCOS2_fields_raw_rep_missing_module_frame_eq; [reflexivity|].
  intros [] Hflag Hint; try contradiction; reflexivity.
Qed.

Lemma os_sched_fields_merge_interrupt : forall environment critical local sg call saved acquired counters,
  UCOS2_state_inv sg (replace_IntrS counters acquired) ->
  task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key call) ->
  store_int_state sg counters **
    os_sched_fields_counter_frame environment critical local sg call saved acquired |--
  os_sched_fields_masked environment critical local sg call saved acquired
    (replace_IntrS counters acquired).
Proof.
  intros environment critical local sg call saved acquired counters Hvalid Hcoverage.
  unfold os_sched_fields_counter_frame, os_sched_fields_masked,
    kernel_continuation_call_masked, kernel_continuation_inv,
    kernel_program_fields_inv, kernel_program_fields_rep.
  sep_apply_l_atomic (interrupt_inv_merge_counters sg counters).
  rewrite (UCOS2_fields_raw_rep_split_module sg (replace_IntrS counters acquired) InterruptModule)
    by discriminate.
  rewrite <- (os_sched_fields_interrupt_frame_replace sg acquired counters).
  cbn [UCOS2_module_rep replace_IntrS TskState IntrState].
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]).
  entailer!.
Qed.

Definition os_sched_lock_fields_pre environment critical local sg original mask before X : Assertion :=
  coq_prop (os_sched_lock_continuation_safe environment critical sg original mask before X) &&
  os_sched_fields_closed environment local sg original mask before.

Definition os_sched_lock_fields_post environment critical local sg original mask before X : Assertion :=
  EX returned current,
    coq_prop (os_sched_lock_continuation_history environment critical sg original mask before returned current /\
      kernel_call_normal_return original before returned current /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_lock_continuation_control before current /\
      os_sched_lock_fields_return_sources environment critical sg original mask before returned current /\
      safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X) &&
    os_sched_fields_closed environment local sg returned mask current.

Lemma os_sched_lock_fields_pre_open : forall environment critical local sg original mask before X,
  os_sched_lock_fields_pre environment critical local sg original mask before X |--
  coq_prop (os_sched_lock_continuation_safe environment critical sg original mask before X /\
    UCOS2_state_inv sg before) &&
  (sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
   os_sched_fields_observation_frame environment local sg original mask before).
Proof.
  intros; unfold os_sched_lock_fields_pre.
  apply coq_prop_andp_left; intro Hsafe.
  rewrite os_sched_fields_split_running; unfold os_sched_fields_observation_frame.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]).
  entailer!.
Qed.

Lemma os_sched_lock_fields_save_counters : forall environment critical local sg original mask saved before,
  UCOS2_state_inv sg before -> os_sched_lock_running before = 1 ->
  os_sched_fields_save_output environment critical local sg original mask saved before |--
  EX entered acquired,
    coq_prop (os_sched_lock_fields_saved_facts environment critical sg
      original mask saved before entered acquired /\ 0 <= os_sched_lock_locks acquired <= 255) &&
    (sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints acquired **
     sg.(g_OSLockNesting) # UChar |-> os_sched_lock_locks acquired **
     os_sched_fields_counter_frame environment critical local sg entered saved acquired).
Proof.
  intros environment critical local sg original mask saved before Hvalid Hrunning.
  assert (Hrun : before.(SchedState).(isRunning) = true).
  { unfold os_sched_lock_running in Hrunning; destruct before.(SchedState).(isRunning);
      [reflexivity|discriminate]. }
  unfold os_sched_fields_save_output, kernel_call_modular_save_post; Intros entered acquired.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  assert (Hsource : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original entered mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before entered acquired) by tauto.
  assert (Hcontrol : kernel_call_control_rely sg before acquired) by tauto.
  assert (Heffect : os_sched_continuation_save_effect environment critical sg
    original mask saved before entered acquired) by (left; exact Hsource).
  assert (Hpreserved : kernel_call_task_source original before -> kernel_call_task_source entered acquired).
  { intro Hinitial; eapply kernel_call_save_source_preserves_task_source; eassumption. }
  pose proof Hsource as [Htrace [Hi [Ho [Hs Hsaved]]]].
  lazymatch goal with
  | |- _ |-- ?post =>
      change (os_sched_fields_masked environment critical local sg entered saved acquired acquired |-- post)
  end.
  sep_apply_l_atomic (os_sched_fields_masked_split_counters environment critical local sg entered saved acquired).
  apply coq_prop_andp_left; intro Hcounters.
  Exists entered acquired; unfold os_sched_lock_fields_saved_facts,
    os_sched_lock_continuation_saved_facts.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

Lemma os_sched_lock_fields_merge_counters : forall environment critical local sg entered saved acquired,
  UCOS2_state_inv sg acquired ->
  task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key entered) ->
  sg.(g_OSIntNesting) # UChar |-> os_sched_lock_ints acquired **
  sg.(g_OSLockNesting) # UChar |-> os_sched_lock_updated_locks acquired **
  os_sched_fields_counter_frame environment critical local sg entered saved acquired |--
  os_sched_fields_masked environment critical local sg entered saved acquired
    (os_sched_lock_checkpoint true acquired).
Proof.
  intros environment critical local sg entered saved acquired Hvalid Hcoverage.
  pose proof (os_sched_fields_merge_interrupt environment critical local sg entered saved acquired
    (sched_lock_state true acquired.(IntrState))
    (os_sched_lock_checkpoint_preserves_validity sg true acquired Hvalid) Hcoverage) as Hmerge.
  unfold store_int_state in Hmerge.
  pose proof (os_sched_lock_checkpoint_ints_eq true acquired) as Hints.
  unfold os_sched_lock_ints, os_sched_lock_checkpoint in Hints; cbn [replace_IntrS IntrState] in Hints.
  rewrite Hints in Hmerge.
  unfold os_sched_lock_ints, os_sched_lock_updated_locks.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma os_sched_lock_fields_restore_return : forall environment critical local sg
  original mask saved before entered acquired X,
  os_sched_lock_fields_saved_facts environment critical sg original mask saved before entered acquired ->
  os_sched_lock_continuation_safe environment critical sg original mask before X ->
  os_sched_fields_restore_output environment critical local sg entered saved
    (os_sched_lock_checkpoint true acquired) |--
  os_sched_lock_fields_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask saved before entered acquired X
    [[Hrun [Hsave [Hnormal_save [Hcontrol_save [Hsource_save [Hsaved [Hvalid Hcoverage]]]]]]]
     Hsave_source] Hsafe.
  unfold os_sched_fields_restore_output, kernel_call_modular_restore_post; Intros returned current.
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
  assert (Hhistory : os_sched_lock_continuation_history environment critical sg original mask before returned current).
  { unfold os_sched_lock_continuation_history; rewrite Hrun.
    exists entered, acquired, saved; split; assumption. }
  assert (Hnormal : kernel_call_normal_return original before returned current).
  { eapply kernel_call_normal_return_trans; [exact Hnormal_save|].
    eapply kernel_call_normal_return_trans; [apply os_sched_lock_checkpoint_normal_return|exact Hnormal_restore]. }
  assert (Hsource : kernel_call_task_source original before -> kernel_call_task_source returned current).
  { intro Hinitial; apply (proj2 (task_tcb_init_stack_same_call_source_iff returned entered current Hsame)).
    eapply task_tcb_init_stack_registered_source_preserved.
    - apply os_sched_lock_checkpoint_preserves_validity; exact Hvalid.
    - exact Hsame.
    - exact Htrace.
    - apply os_sched_lock_checkpoint_preserves_task_source; apply Hsource_save; exact Hinitial. }
  pose proof (os_sched_lock_continuation_control_running sg before acquired current
    Hrun Hcontrol_save Hcontrol_restore) as Hcontrol.
  pose proof (os_sched_lock_continuation_safeexec_return environment critical sg original mask
    before returned current X Hhistory Hsafe) as Hcontinue.
  assert (Hsources : os_sched_lock_fields_return_sources environment critical sg original mask before returned current).
  { unfold os_sched_lock_fields_return_sources; rewrite Hrun.
    exists acquired, entered, saved; split; [exact Hsave_source|]. split; assumption. }
  rewrite (proj2 Hsaved).
  unfold os_sched_lock_fields_post, os_sched_fields_closed; Exists returned current.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

Lemma os_sched_lock_fields_not_running_return : forall environment critical local sg original mask before X,
  os_sched_lock_running before <> 1 ->
  os_sched_lock_continuation_safe environment critical sg original mask before X ->
  sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
    os_sched_fields_observation_frame environment local sg original mask before |--
  os_sched_lock_fields_post environment critical local sg original mask before X.
Proof.
  intros environment critical local sg original mask before X Hnotrunning Hsafe.
  assert (Hrun : before.(SchedState).(isRunning) = false).
  { unfold os_sched_lock_running in Hnotrunning; destruct before.(SchedState).(isRunning);
      [contradiction|reflexivity]. }
  assert (Hhistory : os_sched_lock_continuation_history environment critical sg original mask before original before).
  { unfold os_sched_lock_continuation_history; rewrite Hrun; split; reflexivity. }
  pose proof (os_sched_lock_continuation_safeexec_return environment critical sg original mask
    before original before X Hhistory Hsafe) as Hcontinue.
  pose proof (kernel_call_normal_return_refl original before) as Hnormal.
  pose proof (os_sched_lock_continuation_control_not_running before Hrun) as Hcontrol.
  assert (Hsources : os_sched_lock_fields_return_sources environment critical sg original mask before original before).
  { unfold os_sched_lock_fields_return_sources; rewrite Hrun; split; reflexivity. }
  sep_apply_l_atomic (proj2 (os_sched_fields_split_running environment local sg original mask before)).
  unfold os_sched_lock_fields_post; Exists original before.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

Lemma os_sched_lock_fields_post_current_world : forall environment critical local sg original mask before X,
  os_sched_lock_fields_post environment critical local sg original mask before X |--
  EX returned current,
    coq_prop (os_sched_lock_continuation_program environment critical sg original mask before returned current /\
      kernel_call_normal_return original before returned current /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_lock_continuation_control before current /\
      os_sched_lock_fields_return_sources environment critical sg original mask before returned current /\
      safeExec (fun observed => observed = current) (StateRelMonad.ret returned) X) &&
    os_sched_fields_closed environment local sg returned mask current.
Proof.
  intros; unfold os_sched_lock_fields_post; Intros returned current.
  repeat (apply coq_prop_andp_left; intro).
  assert (Hprogram : os_sched_lock_continuation_program environment critical sg original mask before returned current).
  { apply os_sched_lock_continuation_program_iff; tauto. }
  Exists returned current.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.
