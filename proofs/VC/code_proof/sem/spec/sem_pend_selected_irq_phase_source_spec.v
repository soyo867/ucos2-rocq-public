Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The shared producer executes the actual OSIntExit decrement, selector,
    cache installation, saved-frame restore and final Scheduler MSR/BX.
    The SAME source edge extends the original SemPend wait. Readiness and
    zero nesting/lock follow at this selected return cut, not across every
    intermediate registered client. No future-ready public premise is used. *)
Lemma sem_pend_selected_irq_scheduler_phase_source : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state handler call suspended saved acquired before original mask initial observed eid timeout
  waiting scheduler_entry (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let checkpoint := os_int_exit_ready_checkpoint true state in
  let cached := replace_SchedS (sched_install_selected checkpoint.(SchedState)) checkpoint in
  let current := os_int_exit_wrapper_restored_state cached call.(os_sched_call_stack) in
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call state ->
  interrupt_saved_value mask saved ->
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some call ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  state.(SchedState).(isRunning) = true -> os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  checkpoint.(SchedState).(highRdyTid) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg checkpoint checkpoint ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_client_call_stack_world abi sg focus payload state **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) acquired ** frame))) before ->
  exists prepared installed selected,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    kernel_heap_execution [] prepared prepared /\
    kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg checkpoint checkpoint /\
    sched_install_heap_fragment sg prepared installed
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    current.(IntrState).(intNesting) = 0 /\ current.(IntrState).(lockNesting) = 0 /\
    sched_current_consistency current.(TskState) current.(SchedState) /\
    (forall irq_return cursor written middle final_cursor after,
      armv7a_restore_transition abi handler selected installed irq_return ->
      cursor.(kernel_restore_r0) = saved ->
      cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
      armv7a_restore_prefix_transition restore cursor irq_return written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
      (sem_pend_phase_sched_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
        environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
        critical sg call mask scheduler_entry **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) after).
Proof.
  intros environment critical arch restore sg state handler call suspended saved acquired before original mask
    initial observed eid timeout waiting scheduler_entry frame abi focus payload checkpoint cached current
    Hwait Hsaved Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hfacts : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold kernel_client_call_stack_world, kernel_program_inv, UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hfacts before Hpre)). }
  assert (Henabled : os_sched_selection_enabled (os_int_exit_after_nesting state) = true).
  { exact (proj1 (proj1 (os_sched_requests_switch_iff _) Hswitch)). }
  pose proof (proj1 (os_sched_selection_enabled_iff _) Henabled) as [Hints Hlocks].
  assert (Hcache : sched_current_consistency current.(TskState) current.(SchedState)).
  { change (sched_current_consistency state.(TskState)
      (sched_install_selected (os_sched_ready_checkpoint (os_int_exit_after_nesting state)))).
    apply sched_install_selected_synchronizes_current.
    exact (os_sched_ready_checkpoint_high_consistency sg (os_int_exit_after_nesting state)
      (proj1 (proj1 (proj2 (proj2 Hvalid)))) Henabled). }
  match type of Hpre with ?P before => assert (Hopen : P |--
    kernel_client_call_stack_world abi sg focus payload state **
    (interrupt_platform_running environment.(task_stack_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) acquired ** (emp ** frame))))
    by entailer! end.
  destruct (sched_selected_irq_return_resources environment critical arch restore (fun _ _ => emp)
    sg state handler call suspended saved acquired before frame (derivable1_refl emp)
    Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress
    (Hopen before Hpre)) as [prepared [installed [selected [Hprefix [Hnone [Hhooked [Hinstall
      [Hcpsr [Hregisters [Hsame [Hlive [Hready Hreturn]]]]]]]]]]]].
  exists prepared, installed, selected.
  split; [exact Hprefix|]. split; [exact Hnone|]. split; [exact Hhooked|]. split; [exact Hinstall|].
  split; [exact Hints|]. split; [exact Hlocks|]. split; [exact Hcache|].
  intros irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix.
  destruct (Hreturn irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix)
    as [Hrun [Hsource Hafter]].
  split; [exact Hrun|].
  set (transfer := {| os_int_exit_hooked_state := checkpoint;
    os_int_exit_incoming_stack := call.(os_sched_call_stack);
    os_int_exit_incoming_sp := selected.(armv7a_continuation_sp);
    os_int_exit_incoming_fragments := selected.(armv7a_continuation_fragments) |}).
  assert (Htail : os_int_exit_source_selected_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
    sg state handler transfer selected before irq_return).
  { exists prepared, prepared, installed; repeat first [assumption | split]. }
  assert (Hcurrent_wait : sem_pend_wait_at (Some environment) critical sg original mask initial observed
    eid timeout waiting (armv7a_continuation_resumed_call selected call) current).
  { destruct Hwait as [owned [Henv [Hsame_initial [Hinitial Hpath]]]].
    inversion Henv; subst owned.
    exists environment; split; [reflexivity|]. split.
    - unfold kernel_stack_call_same_call in *; intuition congruence.
    - split; [exact Hinitial|]. eapply SemPendWaitSourceTrans; [exact Hpath|].
      change (sem_pend_wait_source_history environment critical sg original eid
        original.(os_sched_call_stack).(stackLeaseGeneration) state (os_int_exit_installed_state transfer)).
      eapply SemPendWaitSourceInterruptSelection; [reflexivity|exact Htail]. }
  assert (Hselected_wait : sem_pend_wait_selected_at (Some environment) critical sg original mask initial
    observed eid timeout waiting (armv7a_continuation_resumed_call selected call) current).
  { split; [exact Hcurrent_wait|].
    pose proof Hcurrent_wait as [owned [Henv [Hsame_initial [Hinitial Hpath]]]].
    destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hinitial)
      as [first [Hfirst Hfirst_wait]].
    destruct (sem_pend_wait_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath
      first Hfirst Hfirst_wait) as [last [Hlast Hlast_wait]].
    pose proof Hwait as [owned0 [Henv0 [Hcall_same _]]].
    pose proof (proj2 (proj2 Hcall_same)) as Hlease.
    destruct Hready as [node [Hnode Heffective]].
    change (current.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node) in Hnode.
    rewrite Hlease in Hnode; assert (last = node) by congruence; subst last.
    destruct (sem_pend_wait_ready_resume_registration _ _ _ Hlast_wait Heffective)
      as [Hregistration Hrest].
    assert (Hcurrent_valid : UCOS2_state_inv sg current).
    { match type of Hafter with ?P after => assert (Hfacts : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
      { unfold kernel_stack_call_closed, kernel_stack_inv, kernel_program_inv, UCOS2_inv;
          entailer!; intros ? ?; exact I. }
      exact (proj1 (Hfacts after Hafter)). }
    exists node; unfold sem_pend_resume_entry.
    split; [exact Hcurrent_valid|]. split.
    - change (checkpoint.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
      rewrite <- Hlease; exact Hhigh.
    - split; [exact Hnode|]. split; [exact Hregistration|].
      exact (proj1 (proj2 (proj2 (proj1 (proj1 (proj2 (proj2 Hcurrent_valid))))))
        _ _ Hnode Heffective). }
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { cbn [sem_pend_phase_sched_output]; Exists (armv7a_continuation_resumed_call selected call) current.
    rewrite sem_pend_stack_save_input_owned, task_tcb_init_stack_save_input_closed_world.
    assert (Hkey : task_stack_call_active_key call =
      task_stack_call_active_key (armv7a_continuation_resumed_call selected call)).
    { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
    unfold kernel_stack_call_closed, kernel_stack_inv.
    rewrite Hkey, (proj2 Hsaved); entailer!. }
  exact (Hclose after Hafter).
Qed.
