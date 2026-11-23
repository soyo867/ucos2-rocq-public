Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Task publication may change the old waiter's Prev link. Its actual
    result, registration and ready fields are preserved. The new global
    ready invariant yields membership, even if the new child ranks first. *)
Lemma sem_pend_task_publication_preserves_resume_entry : forall sg publication state eid tid old,
  task_create_stack_publication_input sg publication state ->
  sem_pend_resume_entry sg state eid tid old ->
  exists current,
    sem_pend_resume_entry sg (task_create_stack_publication_state sg publication state) eid tid current.
Proof.
  intros sg publication state eid tid old Hinput [Hvalid [Hcurrent [Hold [Hregistration Hin]]]].
  set (args := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node).
  { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfresh : state.(TskState).(inUsedTaskStates) node.(taskID) = None).
  { exact (proj1 (task_private_excludes_public sg state.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) (task_commit_identity_private _ _ _ _ Hidentity))). }
  destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node tid old Hfresh Hold)
    as [updated [Hupdated Hfields]].
  set (published := task_create_stack_publication_state sg publication state).
  assert (Hpost : UCOS2_state_inv sg published).
  { eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
    split; [exact Hinput|reflexivity]. }
  assert (Hlookup : published.(TskState).(inUsedTaskStates) tid = Some updated) by exact Hupdated.
  assert (Heffective : is_effectively_ready old.(stat) old.(dly) = true).
  { destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) tid Hin)
      as [found [Hfound [Hrange Hready]]].
    assert (found = old) by congruence; subst found; exact Hready. }
  assert (Hready_updated : is_effectively_ready updated.(stat) updated.(dly) = true).
  { pose proof (f_equal stat Hfields) as Hstat; change (updated.(stat) = old.(stat)) in Hstat.
    pose proof (f_equal dly Hfields) as Hdly; change (updated.(dly) = old.(dly)) in Hdly.
    rewrite Hstat, Hdly; exact Heffective. }
  assert (Hmember : In tid published.(SchedState).(readyList)).
  { exact (proj1 (proj2 (proj2 (proj1 (proj1 (proj2 (proj2 Hpost))))))
      _ _ Hlookup Hready_updated). }
  assert (Hregistration_updated : sem_pend_resume_registration eid updated).
  { pose proof (f_equal eventMultiWaitEvents Hfields) as Hmulti;
      change (updated.(eventMultiWaitEvents) = old.(eventMultiWaitEvents)) in Hmulti.
    pose proof (f_equal tcbFlagNode Hfields) as Hflag;
      change (updated.(tcbFlagNode) = old.(tcbFlagNode)) in Hflag.
    pose proof (f_equal statPend Hfields) as Hpend;
      change (updated.(statPend) = old.(statPend)) in Hpend.
    pose proof (f_equal eventPtr Hfields) as Hptr;
      change (updated.(eventPtr) = old.(eventPtr)) in Hptr.
    unfold sem_pend_resume_registration; rewrite Hmulti, Hflag, Hpend, Hptr; exact Hregistration. }
  exists updated; split; [exact Hpost|]. split; [exact Hcurrent|].
  split; [exact Hlookup|]. split; assumption.
Qed.

(** This no-selection family starts after the waiter was actually made
    ready. An extension that suspends it or switches away needs its own
    selected-return producer, and cannot use this preservation theorem. *)
Lemma sem_pend_client_step_preserves_resume_entry : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg eid tid,
  (forall cut state next returned old, extra_effect sg cut state next returned ->
    sem_pend_resume_entry sg state eid tid old ->
    exists current, sem_pend_resume_entry sg returned eid tid current) ->
  forall cut state next returned old,
  kernel_client_heap_state_step extra_effect sg cut state next returned ->
  sem_pend_resume_entry sg state eid tid old ->
  exists current, sem_pend_resume_entry sg returned eid tid current.
Proof.
  intros Extra extra_effect sg eid tid Hextra cut state next returned old Hstep Hresume.
  destruct Hstep.
  - exists old; destruct Hresume as [Hvalid Hrest]; split;
      [apply os_int_enter_preserves_validity; exact Hvalid|exact Hrest].
  - exists old; exact Hresume.
  - eapply sem_pend_task_publication_preserves_resume_entry; eassumption.
  - eapply Hextra; eassumption.
Qed.

Lemma sem_pend_client_trace_preserves_resume_entry : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg eid tid,
  (forall cut state next returned old, extra_effect sg cut state next returned ->
    sem_pend_resume_entry sg state eid tid old ->
    exists current, sem_pend_resume_entry sg returned eid tid current) ->
  forall cut state next returned old,
  kernel_client_heap_state_trace extra_effect sg cut state next returned ->
  sem_pend_resume_entry sg state eid tid old ->
  exists current, sem_pend_resume_entry sg returned eid tid current.
Proof.
  intros Extra extra_effect sg eid tid Hextra cut state next returned old Htrace.
  revert old; induction Htrace; intros old Hresume; [exists old; exact Hresume|].
  destruct (sem_pend_client_step_preserves_resume_entry Extra extra_effect sg eid tid Hextra
    cut state middle_cut middle old H Hresume) as [current Hcurrent].
  exact (IHHtrace current Hcurrent).
Qed.

Lemma sem_pend_irq_deposit_resume_entry : forall sg state call sp fragments eid old,
  state.(SchedState).(isRunning) = true ->
  sem_pend_resume_entry sg state eid call.(os_sched_call_stack).(stackLeaseSlot) old ->
  UCOS2_state_inv sg (armv7a_irq_live_parked_state state call sp fragments) ->
  sem_pend_resume_entry sg (armv7a_irq_live_parked_state state call sp fragments) eid
    call.(os_sched_call_stack).(stackLeaseSlot) (task_set_saved_sp old sp).
Proof.
  intros * Hrunning [Hvalid [Hcurrent [Hold [Hregistration Hin]]]] Hparked.
  split; [exact Hparked|].
  unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state;
    rewrite Hrunning; unfold os_sched_save_current_sp;
    cbn [replace_IntrS TskState]; rewrite Hold.
  split; [exact Hcurrent|]. split.
  - cbn [replace_TskS TskState glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates];
      rewrite Z.eqb_refl; reflexivity.
  - split; assumption.
Qed.
