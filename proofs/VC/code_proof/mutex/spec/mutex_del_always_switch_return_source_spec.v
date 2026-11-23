Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_sched_return_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The body has already established its historical deletion observation.
    The final error-byte store uses the current returned owner, even if the
    deleted slot has since been reused. Its public post never restores the
    old checkpoint's memory. *)
Lemma mutex_del_always_return_store_source : forall environment sg original mask initial pe eid
  observed checkpoint perr old_error before after (frame : Assertion),
  mutex_del_parent_prefix_ok pe initial eid ->
  mutex_owner_source_history sg initial observed ->
  mutex_del_parent_critical_observation sg eid 1 0 0 1 observed checkpoint ->
  (mutex_del_source_return environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg original mask **
   (perr # UChar |-> old_error) ** frame) before ->
  kernel_heap_execution [(perr, 0)] before after ->
  (mutex_del_runtime_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg original mask initial pe 1 eid 0 0 **
   (perr # UChar |-> 0) ** frame) after.
Proof.
  intros environment sg original mask initial pe eid observed checkpoint perr old_error before after
    frame Hprefix Hhistory Hobservation Hpre Hstore.
  match type of Hpre with ?P before => assert (Hopen : P |--
    perr # UChar |-> old_error **
    (mutex_del_runtime_return environment environment.(mutex_del_call_external)
       environment.(mutex_del_call_platform) sg original mask ** frame)) end.
  { sep_apply_l_atomic (mutex_del_source_return_forget environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg original mask); entailer!. }
  destruct (kernel_heap_framed_uchar_store perr old_error 0 _ before ltac:(lia)
    (Hopen before Hpre)) as [written [Hwrite Hwritten]].
  assert (written = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst written.
  match type of Hwritten with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold mutex_del_runtime_post; Left; Right; Exists observed checkpoint 1; entailer!. }
  exact (Hclose after Hwritten).
Qed.

(** Consume the actual creator/IRQ heap trace, OSIntExit selector/install,
    original saved frame and final Restore before executing Del's success
    error-byte store. The historical deletion observation is supplied by
    the earlier proved body. This is the returning Scheduler tail; the
    original saved token and inside handle remain explicit input resources. *)
Lemma mutex_del_always_selected_irq_return_post : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  actor creator sg state source_origin handler original suspended saved acquired
  initial pe eid observed checkpoint perr old_error before registry_heap (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  mutex_del_parent_prefix_ok pe initial eid ->
  mutex_owner_source_history sg initial observed ->
  mutex_del_parent_critical_observation sg eid 1 0 0 1 observed checkpoint ->
  (forall action, mutex_del_creator_source_client actor creator action ->
    critical.(critical_region_clients) action) ->
  actor <> Some original.(os_sched_call_invocation) -> mutex_del_creator_arguments creator ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
    KernelClientHeapClosed before KernelClientHeapClosed registry_heap ->
  (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state **
   (interrupt_platform_running environment.(mutex_del_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(mutex_del_call_port) handler **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** ((perr # UChar |-> old_error) ** frame)))) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg
      KernelClientHeapClosed state KernelClientHeapClosed returned /\
    kernel_resumption_task_source_trace environment.(mutex_del_call_external)
      environment.(mutex_del_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None source_origin state false returned_origin returned /\
    (forall
      (Hrunning : returned.(SchedState).(isRunning) = true)
      (Hswitch : os_int_exit_requests_switch true returned = true)
      (Hnonempty : returned.(SchedState).(readyList) <> [])
      (Hhigh : (os_int_exit_ready_checkpoint true returned).(SchedState).(highRdyTid) =
        Some original.(os_sched_call_stack).(stackLeaseSlot))
      (Hhook : kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg
        (os_int_exit_ready_checkpoint true returned) (os_int_exit_ready_checkpoint true returned))
      (Haddress : tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
        TCBStkPtr = task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)),
      exists prepared installed selected,
        os_int_exit_source_switch_prefix_execution sg registry_heap prepared /\
        sched_install_heap_fragment sg prepared installed
          (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        (forall irq_return cursor written middle final_cursor after finished,
          armv7a_restore_transition abi handler selected installed irq_return ->
          cursor.(kernel_restore_r0) = saved ->
          cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
          armv7a_restore_prefix_transition restore cursor irq_return written middle ->
          armv7a_restore_suffix_transition restore written middle final_cursor after ->
          kernel_heap_execution [(perr, 0)] after finished ->
          kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
          (mutex_del_runtime_post environment environment.(mutex_del_call_external)
             environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved)
             initial pe 1 eid 0 0 ** (perr # UChar |-> 0) **
           (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
              handler.(os_int_exit_handler_fragments) ** frame)) finished)).

Proof.
  intros environment critical arch restore actor creator sg state source_origin handler original suspended saved
    acquired initial pe eid observed checkpoint perr old_error before registry_heap frame abi focus payload
    Hprefix Hhistory Hobservation Hinclude Hforeign Hargs Horigin Hbinding Hcall Hslice Hmask
    Hactive Hpointer Htrace Hpre.
  destruct (mutex_del_creator_trace_sched_return environment critical arch restore actor creator sg state
    source_origin handler original suspended saved acquired before registry_heap
    ((perr # UChar |-> old_error) ** frame) Hinclude Hforeign Hargs Horigin Hbinding Hcall Hslice
    Hmask Hactive Hpointer Htrace Hpre)
    as [returned [returned_origin [Hstates [Hsource Hselected]]]].
  exists returned, returned_origin; split; [exact Hstates|]. split; [exact Hsource|].
  intros Hrunning Hswitch Hnonempty Hhigh Hhook Haddress.
  destruct (Hselected Hrunning Hswitch Hnonempty Hhigh Hhook Haddress)
    as [prepared [installed [selected [Hexit [Hinstall Hreturn]]]]].
  exists prepared, installed, selected; split; [exact Hexit|]. split; [exact Hinstall|].
  intros irq_return cursor written middle final_cursor after finished Hirq Hr0 Hcursor Hrestore Hsuffix Hstore.
  destruct (Hreturn irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix)
    as [Hexecution Hreturned].
  split; [exact Hexecution|].
  eapply (mutex_del_always_return_store_source environment sg original (armv7a_irq_fiq_mask saved)
    initial pe eid observed checkpoint perr old_error after finished
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)); try eassumption.
  match type of Hreturned with ?P after => match goal with |- ?Q after =>
    assert (Horder : P |-- Q) by entailer! end end.
  exact (Horder after Hreturned).
Qed.
