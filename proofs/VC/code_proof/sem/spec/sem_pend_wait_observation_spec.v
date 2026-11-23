Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Internal provenance of ONE waiting invocation. Registered interference,
    Scheduler C execution and actual Save/Restore histories retain their
    own source cuts. The C-level constructors consume registered intervals
    or the Scheduler's existing C-return relation, with proved client/hook
    projections. They do not require an instruction-level port proof, and
    cannot manufacture history merely from a desired final observation.
    The finer source constructors remain available. This finite returning
    path asserts neither termination nor coverage of unclassified clients. *)
Inductive sem_pend_wait_source_history environment critical sg original eid generation :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| SemPendWaitSourceRefl : forall state,
    sem_pend_wait_source_history environment critical sg original eid generation state state
| SemPendWaitSourceClients : forall before after stopped returned_origin,
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      before stopped returned_origin after ->
    (forall previous,
      before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
      sem_pend_wait_continuation eid generation previous ->
      exists current,
        after.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
        sem_pend_wait_continuation eid generation current) ->
    sem_pend_wait_source_history environment critical sg original eid generation before after
| SemPendWaitSourceSwitch : forall
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    before call old_sp cpsr registers lr saved incoming selected heap prefix after,
    os_sched_source_switch_prefix_execution sg heap prefix ->
    os_sched_source_switch_execution environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) task_abi sg
      (os_sched_prefix_state before) call old_sp cpsr registers lr saved incoming selected prefix after ->
    sem_pend_wait_source_history environment critical sg original eid generation before
      (os_sched_install_context call saved.(armv7a_continuation_fragments) incoming
        (os_sched_save_current_sp (os_sched_prefix_state before)
          call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)))
| SemPendWaitSourceNonswitch : forall before heap after,
    os_sched_requests_switch before = false ->
    os_sched_source_nonswitch_prefix_execution sg heap after ->
    sem_pend_wait_source_history environment critical sg original eid generation before
      (os_sched_prefix_state before)
| SemPendWaitSourceInterruptSelection : forall before handler transfer selected heap after,
    transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true before ->
    os_int_exit_source_selected_execution environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) sg before handler transfer selected heap after ->
    sem_pend_wait_source_history environment critical sg original eid generation before
      (os_int_exit_installed_state transfer)
| SemPendWaitSourceSave : forall call before returned after,
    kernel_stack_call_same_call call original ->
    kernel_call_save_history environment critical sg call before returned after ->
    (forall previous,
      before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
      sem_pend_wait_continuation eid generation previous ->
      exists current,
        after.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
        sem_pend_wait_continuation eid generation current) ->
    sem_pend_wait_source_history environment critical sg original eid generation before after
| SemPendWaitSourceRestore : forall call before returned after,
    kernel_stack_call_same_call call original ->
    kernel_call_restore_history environment critical sg call before returned after ->
    (forall previous,
      before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
      sem_pend_wait_continuation eid generation previous ->
      exists current,
        after.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
        sem_pend_wait_continuation eid generation current) ->
    sem_pend_wait_source_history environment critical sg original eid generation before after
| SemPendWaitSourceSequentialEntry : forall
    (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform))
    previous_call before heap entered,
    task_invocation_origin_live before.(TskState) previous_call.(os_sched_call_origin) ->
    kernel_sequential_call_source boundary previous_call
      before.(TskState).(taskLifecycle).(taskNextInvocation) heap entered ->
    sem_pend_wait_source_history environment critical sg original eid generation before
      (replace_TskS (task_begin_invocation previous_call.(os_sched_call_origin)
        before.(TskState)) before)
| SemPendWaitSourceInitialEntry : forall
    (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    before previous_call selected installed restored (frame : Assertion),
    armv7a_task_restore_transition task_abi previous_call selected installed restored ->
    selected.(armv7a_continuation_call) = None ->
    armv7a_initial_frame_binding selected ->
    task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
      0 selected.(armv7a_continuation_fragments) ->
    task_current_at before selected.(armv7a_continuation_stack).(stackLeaseSlot)
      selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
    (UCOS2_inv sg before ** armv7a_initial_execution environment.(task_stack_call_continuations) selected **
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) ** frame) restored ->
    sem_pend_wait_source_history environment critical sg original eid generation before
      (armv7a_initial_call_registered selected before)
| SemPendWaitSourceCInterval : forall before after,
    (forall action, critical.(critical_region_clients) action ->
      sem_pend_projected_source_client action) ->
    critical_region_interval critical sg original.(os_sched_call_invocation) before after ->
    sem_pend_wait_source_history environment critical sg original eid generation before after
| SemPendWaitSourceCScheduler : forall before entered returned after,
    (forall action, critical.(critical_region_clients) action ->
      sem_pend_projected_source_client action) ->
    sem_pend_projected_source_client environment.(task_stack_call_external).(os_sched_hook_action) ->
    os_sched_c_return environment.(task_stack_call_external) critical sg before entered returned after ->
    sem_pend_wait_source_history environment critical sg original eid generation before after
| SemPendWaitSourceTrans : forall before middle after,
    sem_pend_wait_source_history environment critical sg original eid generation before middle ->
    sem_pend_wait_source_history environment critical sg original eid generation middle after ->
    sem_pend_wait_source_history environment critical sg original eid generation before after.

Lemma sem_pend_wait_source_history_preserves_waiter : forall environment critical sg original
  eid generation before after,
  sem_pend_wait_source_history environment critical sg original eid generation before after ->
  forall previous,
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
  sem_pend_wait_continuation eid generation previous ->
  exists current,
    after.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros environment critical sg original eid generation before after Hhistory.
  induction Hhistory; intros previous Hprevious Hwait.
  - exists previous; split; assumption.
  - eapply H0; eassumption.
  - destruct (sem_pend_sched_save_sp_projection (os_sched_prefix_state before)
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)
      original.(os_sched_call_stack).(stackLeaseSlot) previous Hprevious)
      as [current [Hcurrent Hprojection]].
    exists current; split; [exact Hcurrent|].
    eapply sem_pend_wait_trace_preserves_continuation; eassumption.
  - exists previous; split; assumption.
  - unfold os_int_exit_installed_state; rewrite H.
    exists previous; split; assumption.
  - eapply H1; eassumption.
  - eapply H1; eassumption.
  - exists previous; split; assumption.
  - exists previous; split; assumption.
  - eapply sem_pend_resumption_trace_preserves_continuation; eassumption.
  - destruct (sem_pend_sched_return_projection environment.(task_stack_call_external)
      critical sg before entered returned after original.(os_sched_call_stack).(stackLeaseSlot)
      previous H H0 H1 Hprevious) as [current [Hcurrent Hprojection]].
    exists current; split; [exact Hcurrent|].
    eapply sem_pend_wait_trace_preserves_continuation; eassumption.
  - destruct (IHHhistory1 previous Hprevious Hwait) as [intermediate [Hmiddle Hmiddle_wait]].
    exact (IHHhistory2 intermediate Hmiddle Hmiddle_wait).
Qed.

(** Record the SAME heap/state/source trace returned by the registered
    resource consumer. No independent existential client path is chosen. *)
Lemma sem_pend_client_trace_wait_history : forall environment critical Extra extra_resources
  focus payload extra_step extra_effect sg original eid generation,
  let abi := environment.(task_stack_call_continuations) in
  @kernel_client_call_stack_extension_valid _ _ _ Extra
    abi extra_resources focus payload extra_step extra_effect ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None extra_effect ->
  (forall cut state next returned old, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates)
      original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
    sem_pend_wait_continuation eid generation old ->
    UCOS2_state_inv sg returned /\ exists current,
      returned.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation eid generation current) ->
  forall cut before next after state old (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  kernel_client_heap_observer_cut original.(os_sched_call_invocation) cut ->
  UCOS2_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  sem_pend_wait_continuation eid generation old ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
  exists returned stopped returned_origin current,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      state stopped returned_origin returned /\
    sem_pend_wait_source_history environment critical sg original eid generation state returned /\
    kernel_client_heap_observer_cut original.(os_sched_call_invocation) next /\
    UCOS2_state_inv sg returned /\
    returned.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.
Proof.
  intros environment critical Extra extra_resources focus payload extra_step extra_effect sg original
    eid generation abi Hspatial Henter Hexit Hpublish Hsource Hwait_step cut before next after
    state old frame Htrace Hcompatible Hvalid Hold Hwait Hpre.
  destruct (sem_pend_client_trace_source_wait _ _ _ Extra abi extra_resources focus payload
    extra_step extra_effect critical.(critical_region_clients) sg original.(os_sched_call_invocation)
    None original.(os_sched_call_stack).(stackLeaseSlot) eid generation
    Hspatial Henter Hexit Hpublish Hsource Hwait_step cut before next after state
    original.(os_sched_call_origin) old frame Htrace Hcompatible Hvalid Hold Hwait Hpre)
    as [returned [stopped [returned_origin [current
      [Hstates [Hrun [Hcut [Hreturned [Hcurrent [Hcurrent_wait Hpost]]]]]]]]]].
  assert (Hhistory : sem_pend_wait_source_history environment critical sg original
    eid generation state returned).
  { eapply SemPendWaitSourceClients; [exact Hrun|].
    intros previous Hprevious Hprevious_wait.
    assert (previous = old) by congruence; subst previous.
    exists current; split; assumption. }
  exists returned, stopped, returned_origin, current; repeat first [assumption | split].
Qed.

(** The final node is selected from the real current resource world.
    Equality with the transported waiter prevents matching an unrelated
    later wait or another incarnation merely because it has legal fields. *)
Lemma sem_pend_wait_source_selected_resume : forall environment critical sg original eid generation
  before current previous focus incoming selected node,
  sem_pend_wait_source_history environment critical sg original eid generation before current ->
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some previous ->
  sem_pend_wait_continuation eid generation previous ->
  incoming.(stackLeaseSlot) = original.(os_sched_call_stack).(stackLeaseSlot) ->
  os_sched_source_selected_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg focus incoming selected node current |--
  EX waiter, coq_prop (sem_pend_resume_entry sg current eid incoming.(stackLeaseSlot) waiter /\
    waiter.(taskGeneration) = generation) && TT.
Proof.
  intros environment critical sg original eid generation before current previous
    focus incoming selected node Hhistory Hprevious Hwait Hslot.
  destruct (sem_pend_wait_source_history_preserves_waiter environment critical sg original
    eid generation before current Hhistory previous Hprevious Hwait) as [waiter [Hwaiter Hcontinuation]].
  assert (Hincoming : current.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some waiter)
    by (rewrite Hslot; exact Hwaiter).
  pose proof (sem_pend_selected_source_resume_entry _ _ _
    environment.(task_stack_call_continuations) sg focus incoming selected node current eid
    generation waiter Hincoming Hcontinuation) as Hresume.
  intros heap Hselected; exists waiter; split.
  - split; [exact (proj1 (Hresume heap Hselected))|exact (proj1 Hcontinuation)].
  - exact I.
Qed.
