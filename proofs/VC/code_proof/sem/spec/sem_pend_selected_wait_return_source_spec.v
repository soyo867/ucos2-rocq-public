Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_irq_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_selected_irq_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Open the actual Scheduler phase result once and retain that SAME
    returned call and state for the subsequent Save and cleanup. The
    selected IRQ producer below consumes this lemma immediately. *)
Lemma sem_pend_scheduler_phase_return_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid pevent timeout waiting call scheduler_entry perr
  (frame : Assertion) X before,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
  (sem_pend_phase_sched_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
     environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
     critical sg call mask scheduler_entry ** perr # UChar |->_ ** frame) before ->
  exists returned current,
    kernel_stack_call_same_call returned call /\
    (forall second second_final second_acquired second_heap,
      second.(kernel_save_return_word) = None -> valid_os_cpu_sr second.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask second.(kernel_save_cpsr) = mask ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr second) current before
        second_final second_acquired second_heap ->
      kernel_call_save_uninterrupted_execution arch second current before second_final second_acquired second_heap /\
      second_acquired = current /\
      exists resumed node branch_heap cleaned,
        sem_pend_resume_branch_fragment sg resumed eid original.(os_sched_call_stack).(stackLeaseSlot)
          node second_heap branch_heap /\
        sem_pend_cleanup_fragment sg perr
          (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend)))) branch_heap cleaned /\
        (forall cursor written middle final_cursor after,
          cursor.(kernel_restore_r0) = second_final.(kernel_save_r0) ->
          armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore cursor cleaned written middle ->
          armv7a_restore_suffix_transition restore written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
          (sem_pend_stack_call_post environment.(task_stack_call_external)
            environment.(task_stack_call_platform) (Some environment) critical sg original mask
            pevent timeout perr initial X ** frame) after)).
Proof.
  intros environment critical arch save restore sg original mask initial observed eid pevent timeout waiting call
    scheduler_entry perr frame X before Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    EX returned current,
      coq_prop (kernel_stack_call_same_call returned call /\
        sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
          waiting returned current) &&
      (sem_pend_stack_save_input environment.(task_stack_call_external) environment.(task_stack_call_platform)
        (Some environment) critical sg returned mask current ** unmap_table_rep sg **
        perr # UChar |->_ ** frame)) end.
  { cbn [sem_pend_phase_sched_output]; Intros returned current; Exists returned current; entailer!. }
  destruct (Hopen before Hpre) as [returned [current [[Hsame Hselected] Hinput]]].
  exists returned, current; split; [exact Hsame|].
  intros second second_final second_acquired second_heap Hreturn Hcpsr Hmask Hsave.
  exact (sem_pend_second_save_return_source environment critical arch save restore sg original mask initial observed
    eid pevent timeout waiting returned current perr frame X second before second_final second_acquired second_heap
    Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec Hselected Hreturn Hcpsr Hmask Hinput Hsave).
Qed.

(** Execute the actual interrupt exit selector and same-frame restore of
    the waiting call, then consume its canonical Scheduler phase directly
    in the second Save, all three C result branches, cleanup and public
    return. Readiness is produced by the actual selector, not assumed of
    every state in the registered wait history. *)
Lemma sem_pend_selected_irq_wait_return_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state handler call suspended saved acquired before original mask initial observed eid pevent timeout
  waiting perr (frame : Assertion) X,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let checkpoint := os_int_exit_ready_checkpoint true state in
  let cached := replace_SchedS (sched_install_selected checkpoint.(SchedState)) checkpoint in
  let current := os_int_exit_wrapper_restored_state cached call.(os_sched_call_stack) in
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout waiting call state ->
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
     critical_region_inside critical sg call.(os_sched_call_invocation) acquired **
     (perr # UChar |->_ ** frame)))) before ->
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
      exists returned resumed_state,
        kernel_stack_call_same_call returned call /\
        (forall second second_final second_acquired second_heap,
          second.(kernel_save_return_word) = None -> valid_os_cpu_sr second.(kernel_save_cpsr) ->
          armv7a_irq_fiq_mask second.(kernel_save_cpsr) = mask ->
          armv7a_save_suffix_transition save (kernel_save_read_cpsr second) resumed_state after
            second_final second_acquired second_heap ->
          kernel_call_save_uninterrupted_execution arch second resumed_state after
            second_final second_acquired second_heap /\
          second_acquired = resumed_state /\
          exists resumed node branch_heap cleaned,
            sem_pend_resume_branch_fragment sg resumed eid original.(os_sched_call_stack).(stackLeaseSlot)
              node second_heap branch_heap /\
            sem_pend_cleanup_fragment sg perr
              (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend)))) branch_heap cleaned /\
            (forall final_start final_written final_middle final_exit final_heap,
              final_start.(kernel_restore_r0) = second_final.(kernel_save_r0) ->
              armv7a_irq_fiq_mask final_start.(kernel_restore_current_cpsr) = 192 ->
              armv7a_restore_prefix_transition restore final_start cleaned final_written final_middle ->
              armv7a_restore_suffix_transition restore final_written final_middle final_exit final_heap ->
              kernel_call_restore_uninterrupted_execution arch final_start cleaned final_exit final_heap /\
              (sem_pend_stack_call_post environment.(task_stack_call_external)
                environment.(task_stack_call_platform) (Some environment) critical sg original mask
                pevent timeout perr initial X **
               (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                 handler.(os_int_exit_handler_fragments) ** frame)) final_heap))).
Proof.
  intros environment critical arch save restore sg state handler call suspended saved acquired before original mask
    initial observed eid pevent timeout waiting perr frame X abi focus payload checkpoint cached current
    Hnonnull Haddress_event Hid Hslot Hlayout Hordered Hexec Hwait Hsaved Horigin Hbinding Hcall Hslice Hmask Hactive
    Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hpre.
  destruct (sem_pend_selected_irq_scheduler_phase_source environment critical arch restore sg state handler call
    suspended saved acquired before original mask initial observed eid timeout waiting state
    (perr # UChar |->_ ** frame) Hwait Hsaved Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hrunning Hswitch
    Hnonempty Hhigh Hhook Haddress Hpre)
    as [prepared [installed [selected [Hprefix [Hnone [Hhooked [Hinstall
      [Hnesting [Hlocks [Hcache Hreturn]]]]]]]]]].
  exists prepared, installed, selected.
  split; [exact Hprefix|]. split; [exact Hnone|]. split; [exact Hhooked|]. split; [exact Hinstall|].
  split; [exact Hnesting|]. split; [exact Hlocks|]. split; [exact Hcache|].
  intros irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix.
  destruct (Hreturn irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix)
    as [Hrun Hafter].
  split; [exact Hrun|].
  eapply (sem_pend_scheduler_phase_return_source environment critical arch save restore sg original mask initial observed
    eid pevent timeout waiting call state perr
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
    X after Hnonnull Haddress_event Hid Hslot Hlayout Hordered Hexec).
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hreorder : P |-- Q) by entailer! end end.
  exact (Hreorder after Hafter).
Qed.

(** The ordinary OS_Sched/OSCtxSw source family joins the SAME return tail.
    Its concrete switch execution and selected resources are consumed
    together; the caller does not supply a separate post-switch wait path. *)
Lemma sem_pend_switch_wait_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid timeout waiting call entry
  context old_sp cpsr registers lr outgoing incoming selected node focus selector_heap prefix before
  saved acquired cursor written middle final_cursor after (selected_frame frame : Assertion) pevent perr X,
  let current := os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      context.(os_sched_call_stack).(stackLeaseSlot) outgoing.(armv7a_continuation_sp)) in
  let returned := armv7a_continuation_resumed_call selected call in
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout waiting call entry ->
  os_sched_source_switch_prefix_execution sg selector_heap prefix ->
  os_sched_source_switch_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) task_abi sg (os_sched_prefix_state entry)
    context old_sp cpsr registers lr outgoing incoming selected prefix before ->
  incoming = original.(os_sched_call_stack) -> interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (os_sched_source_selected_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg focus incoming selected node current ** selected_frame) before ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
    (task_stack_call_active_key returned) returned saved acquired current ** (perr # UChar |->_ ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  exists resumed_call resumed_state,
    kernel_stack_call_same_call resumed_call call /\
    (forall second second_final second_acquired second_heap,
      second.(kernel_save_return_word) = None -> valid_os_cpu_sr second.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask second.(kernel_save_cpsr) = mask ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr second) resumed_state after
        second_final second_acquired second_heap ->
      kernel_call_save_uninterrupted_execution arch second resumed_state after second_final second_acquired second_heap /\
      second_acquired = resumed_state /\
      exists resumed node branch_heap cleaned,
        sem_pend_resume_branch_fragment sg resumed eid original.(os_sched_call_stack).(stackLeaseSlot)
          node second_heap branch_heap /\
        sem_pend_cleanup_fragment sg perr
          (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend)))) branch_heap cleaned /\
        (forall final_start final_written final_middle final_exit final_heap,
          final_start.(kernel_restore_r0) = second_final.(kernel_save_r0) ->
          armv7a_irq_fiq_mask final_start.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore final_start cleaned final_written final_middle ->
          armv7a_restore_suffix_transition restore final_written final_middle final_exit final_heap ->
          kernel_call_restore_uninterrupted_execution arch final_start cleaned final_exit final_heap /\
          (sem_pend_stack_call_post environment.(task_stack_call_external)
            environment.(task_stack_call_platform) (Some environment) critical sg original mask
            pevent timeout perr initial X ** frame) final_heap)).
Proof.
  intros environment critical arch task_abi save restore sg original mask initial observed eid timeout waiting
    call entry context old_sp cpsr registers lr outgoing incoming selected node focus selector_heap prefix before
    saved acquired cursor written middle final_cursor after selected_frame frame pevent perr X current returned
    Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec Hwait Hprefix Hswitch Hincoming Hsaved Hr0 Hmask Hselected
    Howned Hrestore Hsuffix.
  destruct (sem_pend_switch_scheduler_phase_return environment critical arch task_abi restore sg original mask initial
    observed eid timeout waiting call entry entry context old_sp cpsr registers lr outgoing incoming selected node focus
    selector_heap prefix before saved acquired cursor written middle final_cursor after selected_frame
    (perr # UChar |->_ ** frame) Hwait Hprefix Hswitch Hincoming Hsaved Hr0 Hmask Hselected Howned Hrestore Hsuffix)
    as [Hrun Hafter].
  split; [exact Hrun|].
  eapply (sem_pend_scheduler_phase_return_source environment critical arch save restore sg original mask initial observed
    eid pevent timeout waiting call entry perr frame X after Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec).
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hreorder : P |-- Q) by entailer! end end.
  exact (Hreorder after Hafter).
Qed.
