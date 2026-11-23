Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A different task may be published while this invocation is waiting.
    The new slot is private, and therefore differs from the old public
    waiter. Publication can change the waiter's Prev link; its registration,
    result and generation remain the actual old fields. *)
Lemma sem_pend_task_publication_preserves_wait_continuation :
  forall sg publication state tid old eid generation,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  exists current,
    (task_create_stack_publication_state sg publication state).(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros sg publication state tid old eid generation Hvalid Hinput Hold Hwait.
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
    as [current [Hcurrent Hfields]].
  assert (Hwait_fields : sem_pend_wait_fields_equal old current).
  { unfold sem_pend_wait_fields_equal; repeat split.
    - exact (f_equal taskID Hfields).
    - exact (f_equal taskGeneration Hfields).
    - exact (f_equal stat Hfields).
    - exact (f_equal statPend Hfields).
    - exact (f_equal dly Hfields).
    - exact (f_equal eventPtr Hfields).
    - exact (f_equal eventMultiWaitEvents Hfields).
    - exact (f_equal tcbFlagNode Hfields). }
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_fields_equal_preserves_continuation; eassumption.
Qed.

(** The selector supplies current readiness only at its actual return cut.
    The same waiter lookup is transported by the registered source trace;
    combining the two produces the fields read by SemPend's cleanup. *)
Lemma sem_pend_selected_source_resume_entry : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg focus incoming selected node state eid generation waiting,
  state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid generation waiting ->
  os_sched_source_selected_post external platform port abi
    sg focus incoming selected node state |--
  coq_prop (sem_pend_resume_entry sg state eid incoming.(stackLeaseSlot) waiting) && TT.
Proof.
  intros external platform port abi sg focus incoming selected node state eid generation waiting
    Hwaiting Hwait.
  unfold os_sched_source_selected_post; Intros.
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState)
    incoming.(stackLeaseSlot) node) by tauto.
  destruct Hready as [Hnode [Hcurrent [Hpriority [Hmember Heffective]]]].
  assert (node = waiting) by congruence; subst node.
  destruct (sem_pend_wait_ready_resume_registration eid generation waiting Hwait Heffective)
    as [Hregistration _].
  unfold UCOS2_inv; Intros.
  unfold sem_pend_resume_entry; entailer!; intros ? ?; exact I.
Qed.

(** This follows the actual registry cuts. Intermediate current/ready
    membership is deliberately absent: another task may be running.
    An extension has to prove the effect of its own source operation on
    the original waiter; an arbitrary callback is not declared harmless. *)
Lemma sem_pend_client_step_preserves_wait_continuation : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg tid eid generation,
  (forall cut state next returned old, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    UCOS2_state_inv sg returned /\ exists current,
      returned.(TskState).(inUsedTaskStates) tid = Some current /\
      sem_pend_wait_continuation eid generation current) ->
  forall cut state next returned old,
  kernel_client_heap_state_step extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  UCOS2_state_inv sg returned /\ exists current,
    returned.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros Extra extra_effect sg tid eid generation Hextra cut state next returned old
    Hstep Hvalid Hold Hwait; destruct Hstep.
  - split; [apply os_int_enter_preserves_validity; exact Hvalid|].
    exists old; split; assumption.
  - split; [exact Hvalid|]. exists old; split; assumption.
  - split.
    + eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
      split; [exact H|reflexivity].
    + eapply sem_pend_task_publication_preserves_wait_continuation; eassumption.
  - eapply Hextra; eassumption.
Qed.

Lemma sem_pend_client_trace_preserves_wait_continuation : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg tid eid generation,
  (forall cut state next returned old, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    UCOS2_state_inv sg returned /\ exists current,
      returned.(TskState).(inUsedTaskStates) tid = Some current /\
      sem_pend_wait_continuation eid generation current) ->
  forall cut state next returned old,
  kernel_client_heap_state_trace extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  UCOS2_state_inv sg returned /\ exists current,
    returned.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros Extra extra_effect sg tid eid generation Hextra cut state next returned old Htrace.
  revert old; induction Htrace; intros old Hvalid Hold Hwait.
  - split; [exact Hvalid|]. exists old; split; assumption.
  - destruct (sem_pend_client_step_preserves_wait_continuation Extra extra_effect sg tid eid generation
      Hextra cut state middle_cut middle old H Hvalid Hold Hwait)
      as [Hmiddle [current [Hcurrent Hcurrent_wait]]].
    exact (IHHtrace current Hmiddle Hcurrent Hcurrent_wait).
Qed.

(** Actual resource consumer: source trace, current waiter observation
    and the strong focused stack world all have the same final heap.
    This proves the registered prefix only. The final selector must still
    establish readiness, and a returning Save must provide its own suffix.
    No new premise is installed in OSSemPend's public Require. *)
Lemma sem_pend_client_trace_source_wait : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload
  extra_step extra_effect clients sg observer event_observer tid eid generation,
  @kernel_client_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  (forall cut state next returned old, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
    sem_pend_wait_continuation eid generation old ->
    UCOS2_state_inv sg returned /\ exists current,
      returned.(TskState).(inUsedTaskStates) tid = Some current /\
      sem_pend_wait_continuation eid generation current) ->
  forall cut before next after state origin old (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  kernel_client_heap_observer_cut observer cut ->
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
  exists returned stopped returned_origin current,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    UCOS2_state_inv sg returned /\
    returned.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_step extra_effect
    clients sg observer event_observer tid eid generation Hspatial Henter Hexit Hpublish Hsource Hwait_step
    cut before next after state origin old frame Htrace Hcompatible Hvalid Hold Hwait Hpre.
  destruct (kernel_client_call_stack_trace_source_resources external platform port Extra abi
    extra_resources focus payload extra_step extra_effect clients sg observer event_observer
    Hspatial Henter Hexit Hpublish Hsource cut before next after frame Htrace state origin
    Hcompatible Hpre) as [returned [stopped [returned_origin [Hstates [Hrun [Hcut Hpost]]]]]].
  destruct (sem_pend_client_trace_preserves_wait_continuation Extra extra_effect sg tid eid generation
    Hwait_step cut state next returned old Hstates Hvalid Hold Hwait)
    as [Hreturned [current [Hcurrent Hcurrent_wait]]].
  exists returned, stopped, returned_origin, current; repeat first [assumption | split].
Qed.
