Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The canonical first Save already returns [source_preserved].  Once
    actual ordinary-call entry has established its current-task identity,
    the existing post transports that fact to the same acquired world.
    No stronger CPU Ensure, ready-caller condition, or source-trace wrapper
    is needed for this part of the C call chain.

    This is the ordinary-entry consumer, not a change to TaskCreate's
    public input domain.  Boot and ISR early-error branches still consume
    [task_create_continuation_save_output_entry] without [Hinitial]. *)
Lemma task_create_first_save_current_source :
  forall environment critical saved_local sg args initial_name original mask saved before,
  task_create_stack_entry sg args initial_name original before ->
  kernel_call_task_source original before ->
  task_tcb_init_continuation_save_output environment critical saved_local sg
    original mask saved before |--
  EX returned acquired,
    coq_prop (task_create_stack_entry sg args initial_name original acquired /\
      task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      kernel_call_task_source returned acquired) &&
    task_tcb_init_continuation_restore_input environment critical saved_local sg
      returned saved acquired acquired.
Proof.
  intros environment critical saved_local sg args initial_name original mask saved before
    Hentry Hinitial.
  sep_apply_l_atomic (task_create_continuation_save_output_entry environment critical saved_local
    sg args initial_name original mask saved before Hentry).
  Intros returned acquired.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired) by tauto.
  assert (Hcurrent : kernel_call_task_source returned acquired).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original acquired Hsame)).
    apply Hpreserved; exact Hinitial. }
  Exists returned acquired; entailer!.
Qed.

(** TCBInit's successful C publication gives a nonempty ready list even
    when its outgoing caller is blocked.  For this actual builtin
    Closed-to-Closed C return family, the existing generic-map producer
    also proves that the scheduler fields are unchanged.  Hence the
    selector's needed nonemptiness is derived from the new publication,
    not from an added caller-ready premise.

    [parked] is supplied by the existing IRQ-entry resource producer and
    [current] is exactly the existing take/Restore endpoint.  The theorem
    retains the same returned map and heap; it does not fabricate their
    source, assume a callee's whole output, or claim arbitrary extensions
    cannot delete/block a task.  Extending this family needs the actual
    completed C effect's corresponding preservation proof. *)
Lemma task_create_tcb_success_builtin_return_ready :
  forall environment critical local Extra sg region args task_return lower upper
    initial_name invocation origin initial released call sp fragments before after (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state released call sp fragments in
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial 0 released ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients)
    (task_create_stack_publication_client publication)) ->
  @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
    KernelClientHeapClosed before KernelClientHeapClosed after ->
  (kernel_client_continuation_world abi local sg parked ** frame) before ->
  exists returned,
    @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
      KernelClientHeapClosed parked KernelClientHeapClosed returned /\
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      call.(os_sched_call_invocation) None call.(os_sched_call_origin)
      parked false call.(os_sched_call_origin) returned /\
    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))
      .(SchedState).(readyList) <> [] /\
    (kernel_client_continuation_world abi local sg returned ** frame) after.
Proof.
  intros environment critical local Extra sg region args task_return lower upper initial_name
    invocation origin initial released call sp fragments before after frame abi parked
    Hresult Henter Hexit Hpublish Htrace Hpre.
  assert (Hpublication_ready : forall publication state,
    (task_create_stack_publication_state sg publication state).(SchedState).(readyList) <> []).
  { intros publication state Hempty.
    assert (Hin : In publication.(stack_publication_slot)
      (task_create_stack_publication_state sg publication state).(SchedState).(readyList)).
    { change (In publication.(stack_publication_slot)
        (insert_sorted_by
          (sched_task_key sg (task_commit state.(TskState)
            (task_create_stack_publication_args publication).(initPrio)
            publication.(stack_publication_invocation)
            (task_tcb_init_commit_node (task_create_stack_publication_args publication)
              publication.(stack_publication_acquired) publication.(stack_publication_slot)
              publication.(stack_publication_image))))
          publication.(stack_publication_slot) state.(SchedState).(readyList))).
      apply insert_sorted_by_in; left; reflexivity. }
    rewrite Hempty in Hin; contradiction. }
  assert (Hreleased_ready : released.(SchedState).(readyList) <> []).
  { inversion Hresult; subst; apply Hpublication_ready. }
  assert (Hparked_sched : parked.(SchedState) = released.(SchedState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    destruct released.(SchedState).(isRunning); reflexivity. }
  destruct (kernel_client_continuation_trace_resources
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) Extra abi local critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None Henter Hexit Hpublish
    KernelClientHeapClosed before KernelClientHeapClosed after frame Htrace
    parked call.(os_sched_call_origin) I Hpre)
    as [returned [Hstates [Hsource [Hobserver Hpost]]]].
  destruct (kernel_client_builtin_closed_trace_task_fields Extra sg
    KernelClientHeapClosed parked KernelClientHeapClosed returned Hstates eq_refl)
    as [Hclosed [Htasks Hsched]].
  exists returned; split; [exact Hstates|]. split; [exact Hsource|].
  split; [|exact Hpost].
  change (returned.(SchedState).(readyList) <> []).
  rewrite Hsched, Hparked_sched; exact Hreleased_ready.
Qed.
