Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_phase_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_pending_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_event_ready_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_save_interpreter_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_selected_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_c_call_connection_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_clear_status_phase_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_module_assembly_spec.

Import UCOS2_C_Rules TaskStateDef.
Import PrimitiveComponent SelectedEnvironmentPhaseEffects SemPendEventReadySource.
Import SelectedEnvironmentCProgram SelectedEnvironmentCSource SelectedEnvironmentScopedEnvironment.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The existing active-caller producer already proves the real open/close
    and endpoint observations. Preserve its single returned run and attach
    that producer's own observed trace; no second execution is selected. *)
Lemma sem_pend_scoped_sem_post_module_run :
  forall environment critical sg original local mask actor entry event node returned before after
    (frame private : Assertion),
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> original.(os_sched_call_invocation) ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller original) original mask entry ** private) before ->
  sem_post_waiter_execution sg (event_addr sg event) returned before after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists run : flag_pend_scoped_environment_run environment critical local local (fun _ _ => frame) sg
      original mask entry before private false original wake after private,
    sem_pend_client_module_run environment critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) _ _ _ _ _ _ _ run
      original.(os_sched_call_origin) original.(os_sched_call_origin) /\
    sem_pend_client_return_source environment critical sg original entry original wake /\
    (coq_prop (flag_pend_call_endpoint_observations environment sg
      (FlagPendTaskCaller original) original entry original wake) &&
      (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
        (FlagPendTaskCaller original) original mask wake ** private)) after.
Proof.
  intros environment critical sg original local mask actor entry event node returned before after
    frame private Hmember Hforeign Hlookup Htype Hgroup Hlayout Hinput Hactual.
  destruct (sem_pend_sem_post_scoped_restore_body environment critical sg original local mask
    actor entry event node returned before after frame private Hmember Hforeign Hlookup Htype
    Hgroup Hlayout Hinput Hactual) as [selected [old [run [Hsource [Hcalls [Hreturn Howner]]]]]].
  exists selected, old, run; split.
  - split; [exact Hsource|exact (proj1 Hreturn)].
  - exact (conj Hreturn Howner).
Qed.

(** The existing full Restore producer constructs the prefix, actual helper
    and suffix together. Consume that one completion and its own return
    observation in the current phase proof. *)
Lemma sem_pend_scoped_sem_post_restore_phase_output :
  forall phase environment critical local sg call mask saved acquired entry first_heap
    (frame private : Assertion) private_before whole_before actor event node helper_returned
    environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after,
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> call.(os_sched_call_invocation) ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  sem_pend_client_phase_context sg call entry ->
  sem_pend_clear_status_phase_restore_pre phase environment critical sg call mask entry ->
  interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller call) call saved acquired entry first_heap ->
  private private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  sem_post_waiter_execution sg (event_addr sg event) helper_returned prefix_heap environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local local
      (fun _ _ => frame) sg call saved acquired entry first_heap false call wake last_heap),
    (sem_pend_clear_status_phase_restore_output phase environment local critical sg call mask entry ** frame) last_heap.
Proof.
  intros phase environment critical local sg call mask saved acquired entry first_heap frame private
    private_before whole_before actor event node helper_returned environment_heap arch restore cursor written
    prefix_heap final_cursor whole_after Hmember Hforeign Hlookup Htype Hgroup Hlayout Hcontext Hpre
    Hsaved Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hactual Hsuffix.
  destruct (sem_pend_sem_post_selected_restore environment critical local sg call saved acquired entry
    first_heap frame private private_before whole_before actor event node helper_returned environment_heap
    arch restore cursor written prefix_heap final_cursor whole_after Hmember Hforeign Hlookup Htype
    Hgroup Hlayout Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hactual Hsuffix)
    as [selected [old [last_heap [actual [Hreceipt [[Hreturn Hendpoint] Howner]]]]]].
  exists selected, old, last_heap, actual.
  exact (sem_pend_completed_restore_phase_output phase environment critical local local
    (fun _ _ => frame) sg call mask saved acquired entry first_heap call
    (event_wake_state sg entry event node selected old PendSem 0 PendOK) last_heap
    actual Hcontext Hpre Hsaved (proj1 Hreturn)).
Qed.

Lemma sem_pend_scoped_sem_post_waiting_restore_sched_input :
  forall environment critical local sg original mask initial observed eid timeout waiting
    call saved acquired entry first_heap (frame private : Assertion) private_before whole_before
    actor event node helper_returned environment_heap arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    cursor written prefix_heap final_cursor whole_after,
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> call.(os_sched_call_invocation) ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  sem_pend_client_sched_entry environment critical sg original mask initial observed eid timeout waiting call entry ->
  interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  flag_pend_caller_restore_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller call) call saved acquired entry first_heap ->
  private private_before -> join first_heap private_before whole_before ->
  armv7a_restore_prefix_transition restore cursor whole_before written prefix_heap ->
  sem_post_waiter_execution sg (event_addr sg event) helper_returned prefix_heap environment_heap ->
  armv7a_restore_suffix_transition restore written environment_heap final_cursor whole_after ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    exists last_heap (actual : os_sched_continuation_c_restore_execution environment critical local local
      (fun _ _ => frame) sg call saved acquired entry first_heap false call wake last_heap),
    ((coq_prop (sem_pend_client_return_source environment critical sg call entry call wake /\
       kernel_call_control_rely sg entry wake) &&
      sem_pend_client_sched_input environment local critical sg original mask initial observed eid timeout
        waiting call wake) ** frame) last_heap.
Proof.
  intros environment critical local sg original mask initial observed eid timeout waiting call saved acquired
    entry first_heap frame private private_before whole_before actor event node helper_returned environment_heap
    arch restore cursor written prefix_heap final_cursor whole_after Hmember Hforeign Hlookup Htype Hgroup
    Hlayout Hentry Hsaved Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hactual Hsuffix.
  destruct (sem_pend_sem_post_selected_restore environment critical local sg call saved acquired entry
    first_heap frame private private_before whole_before actor event node helper_returned environment_heap
    arch restore cursor written prefix_heap final_cursor whole_after Hmember Hforeign Hlookup Htype
    Hgroup Hlayout Hr0 Hmask Hinput Hprivate Hjoin Hprefix Hactual Hsuffix)
    as [selected [old [last_heap [actual [Hreceipt [[Hreturn Hendpoint] Howner]]]]]].
  exists selected, old, last_heap, actual.
  exact (sem_pend_completed_waiting_restore_sched_input environment critical local local
    (fun _ _ => frame) sg original mask initial observed eid timeout waiting call saved acquired
    entry first_heap call (event_wake_state sg entry event node selected old PendSem 0 PendOK)
    last_heap actual Hentry Hsaved (proj1 Hreturn)).
Qed.

(** Choose the actual helper result first. The continuation below accepts
    only the Save suffix at that chosen state and heap; it does not require
    a suffix for arbitrary hypothetical helper results. *)
Lemma sem_pend_scoped_sem_post_save_phase_completion :
  forall phase environment critical local sg call mask entry first_heap
    (frame private : Assertion) private_before whole_before actor event node helper_returned
    environment_heap,
  critical.(critical_region_clients) (sem_pend_post_source_client actor event) ->
  actor <> call.(os_sched_call_invocation) ->
  sem_post_lookup entry event node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_group entry node <> 0 -> event_object_layout_prop sg event ->
  sem_pend_clear_status_phase_save_pre phase environment critical sg call mask entry ->
  flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller call) call mask entry first_heap ->
  private private_before -> join first_heap private_before whole_before ->
  sem_post_waiter_execution sg (event_addr sg event) helper_returned whole_before environment_heap ->
  exists selected old,
    let wake := event_wake_state sg entry event node selected old PendSem 0 PendOK in
    forall arch (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical arch)
      registers final_registers whole_after,
    registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
    armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) wake environment_heap
      final_registers wake whole_after ->
    exists last_heap (actual : os_sched_continuation_c_save_execution environment critical local local
      (fun _ _ => frame) sg call mask entry first_heap final_registers.(kernel_save_r0)
      false call wake last_heap),
    (sem_pend_clear_status_phase_save_output phase environment local critical sg call mask
      final_registers.(kernel_save_r0) entry ** frame) last_heap.
Proof.
  intros phase environment critical local sg call mask entry first_heap frame private private_before
    whole_before actor event node helper_returned environment_heap Hmember Hforeign Hlookup Htype Hgroup
    Hlayout Hpre Hinput Hprivate Hjoin Hactual.
  assert (Hwhole : (flag_pend_caller_save_input environment critical local (fun _ _ => frame) sg
    (FlagPendTaskCaller call) call mask entry ** private) whole_before).
  { exists first_heap, private_before; exact (conj Hjoin (conj Hinput Hprivate)). }
  destruct (sem_pend_scoped_sem_post_module_run environment critical sg call local mask actor entry event
    node helper_returned whole_before environment_heap frame private Hmember Hforeign Hlookup Htype
    Hgroup Hlayout Hwhole Hactual) as [selected [old [run [Hmodule [Hreturn Howner]]]]].
  exists selected, old.
  cbn zeta.
  intros arch save registers final_registers whole_after Hword Hvalid Hmask Hsuffix.
  exact (sem_pend_module_save_phase_output phase environment critical local local (fun _ _ => frame)
    sg mask call entry first_heap private private private_before whole_before call
    (event_wake_state sg entry event node selected old PendSem 0 PendOK) environment_heap arch save
    registers final_registers whole_after run Hpre Hmodule Hinput Hprivate Hjoin Hword Hvalid Hmask Hsuffix).
Qed.
