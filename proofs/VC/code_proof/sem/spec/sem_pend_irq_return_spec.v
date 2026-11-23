Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** An executable finite suffix, not the public OSSemPend contract.
    The selected continuation is already the original pending call.
    Its OS_Sched Restore and SemPend's second Save are adjacent actual
    transitions on one heap. Interrupts at either unmasked cut need their
    own source proof and are not absorbed by this local frame rule. *)
Definition sem_pend_selected_success_suffix environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original selected saved state eid tid node perr (frame : Assertion) restored : Prop :=
  forall cursor written middle returned_cursor returned_heap registers final_registers acquired after,
    cursor.(kernel_restore_r0) = saved ->
    cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
    registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
    armv7a_restore_prefix_transition restore cursor restored written middle ->
    armv7a_restore_suffix_transition restore written middle returned_cursor returned_heap ->
    armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state returned_heap
      final_registers acquired after ->
    kernel_call_restore_uninterrupted_execution arch cursor restored returned_cursor returned_heap /\
    kernel_call_save_uninterrupted_execution arch registers state returned_heap final_registers acquired after /\
    acquired = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
    final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
    exists cleaned,
      sem_pend_success_cleanup_fragment sg perr after cleaned /\
      sem_pend_resume_critical sg eid state OS_ERR_NONE (event_pend_cleanup_state sg false state tid node) /\
      (forall final_input final_written final_middle final_cursor final_heap,
        final_input.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
        armv7a_irq_fiq_mask final_input.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore final_input cleaned final_written final_middle ->
        armv7a_restore_suffix_transition restore final_written final_middle final_cursor final_heap ->
        kernel_call_restore_uninterrupted_execution arch final_input cleaned final_cursor final_heap /\
        final_cursor.(kernel_restore_return_word) = Some final_input.(kernel_restore_lr) /\
        (kernel_call_execution_owned environment.(task_stack_call_external)
           environment.(task_stack_call_platform) (armv7a_continuation_resumed_call selected original)
           (armv7a_irq_fiq_mask final_registers.(kernel_save_r0)) **
         UCOS2_inv sg (event_pend_cleanup_state sg false state tid node) **
         perr # UChar |-> 0 ** frame) final_heap).

Lemma sem_pend_selected_success_return : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original selected saved entry state eid tid node perr (frame : Assertion) restored,
  selected.(armv7a_continuation_call) = Some original ->
  armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 ->
  sem_pend_resume_entry sg state eid tid node -> node.(statPend) = PendOK ->
  (armv7a_task_restored_execution environment.(task_stack_call_external)
     environment.(task_stack_call_platform) environment.(task_stack_call_port)
     environment.(task_stack_call_continuations) selected **
   interrupt_platform_saved environment.(task_stack_call_platform)
     (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
   critical_region_inside critical sg original.(os_sched_call_invocation) entry **
   UCOS2_inv sg state ** perr # UChar |->_ ** frame) restored ->
  sem_pend_selected_success_suffix environment critical arch restore save
    sg original selected saved state eid tid node perr frame restored.
Proof.
  intros environment critical arch restore save sg original selected saved entry state eid tid node
    perr frame restored Hcall Hmask Hresume Hsuccess Hpre.
  intros cursor written middle returned_cursor returned_heap registers final_registers acquired after
    Hr0 Hcursor Hreturn Hvalid Hnextmask Hprefix Hsuffix Hsave.
  assert (Hmask_cursor : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    by (rewrite Hcursor; exact Hmask).
  match type of Hpre with ?P restored => assert (Hopen : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      (armv7a_continuation_resumed_call selected original).(os_sched_call_invocation)
      (armv7a_continuation_resumed_call selected original).(os_sched_call_origin) saved entry **
    os_sched_context_resources environment.(task_stack_call_external)
      (armv7a_continuation_resumed_call selected original) **
    (UCOS2_inv sg state ** perr # UChar |->_ ** frame)) end.
  { unfold armv7a_task_restored_execution; rewrite Hcall, Hmask.
    unfold critical_region_masked, kernel_call_execution_owned.
    cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg
    (armv7a_continuation_resumed_call selected original) saved entry cursor restored written middle
    returned_cursor returned_heap _ Hr0 Hmask_cursor (Hopen restored Hpre) Hprefix Hsuffix)
    as [Hrestore [Hlr [Hmemory Hclosed]]].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hvalid|reflexivity]. }
  rewrite <- Hnextmask in Hclosed.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg
    (armv7a_continuation_resumed_call selected original) (kernel_save_read_cpsr registers) state
    returned_heap final_registers acquired after _ Hsaved Hclosed Hsave)
    as [Hstate [Hmemory_after [Hreturned [Hvalue Hpost]]]].
  split; [exact Hrestore|]. split.
  - unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - split; [exact Hstate|]. split; [exact Hvalue|]. split; [exact Hreturned|].
    match type of Hpost with ?P after => assert (Horder : P |--
      critical_region_masked environment.(task_stack_call_platform) critical sg
        (armv7a_continuation_resumed_call selected original).(os_sched_call_invocation)
        (armv7a_continuation_resumed_call selected original).(os_sched_call_origin)
        final_registers.(kernel_save_r0) state **
      os_sched_context_resources environment.(task_stack_call_external)
        (armv7a_continuation_resumed_call selected original) **
      UCOS2_inv sg state ** perr # UChar |->_ ** frame) by entailer! end.
    exact (sem_pend_success_uninterrupted_return _ _ _ _ restore sg state eid tid node
      (armv7a_continuation_resumed_call selected original) final_registers.(kernel_save_r0) perr frame
      after Hresume Hsuccess (Horder after Hpost)).
Qed.

(** A consumer of the actual OSIntExit selector/install/frame-restore
    producer. The returning-original branch is explicit; selecting another
    ready task does not establish this suffix. The input is the existing
    handler view, NOT SemPost's API view. Joining those two views requires
    a separately proved paired handler/API call interpretation; the
    ordinary KernelSequentialCallABI does not supply such a rule. *)
Lemma sem_pend_irq_selected_success_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state retained original pc lr handler saved entry eid waiting perr (frame : Assertion) before,
  let focus := armv7a_call_focus original pc lr in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  waiting.(statPend) = PendOK ->
  state.(SchedState).(isRunning) = true -> os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  (forall slot node, (os_int_exit_ready_checkpoint true state).(SchedState).(highRdyTid) = Some slot ->
    state.(TskState).(inUsedTaskStates) slot = Some node ->
    (slot, node.(taskGeneration)) <> task_stack_key retained.(armv7a_continuation_stack)) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage state.(TskState) None ->
  kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true state) (os_int_exit_ready_checkpoint true state) ->
  (UCOS2_inv sg state ** unmap_table_rep sg **
   (armv7a_dormant_continuation environment.(task_stack_call_continuations) retained **
    armv7a_task_call_stacks environment.(task_stack_call_continuations) state.(TskState) focus
      (task_stack_take state.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
    (interrupt_platform_running environment.(task_stack_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) entry **
      perr # UChar |->_ ** frame)))) before ->
  exists prepared,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    (forall hooked, kernel_heap_execution [] prepared hooked ->
      exists transfer installed selected,
        transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true state /\
        os_int_exit_destination_binding environment.(task_stack_call_external) transfer /\
        sched_install_heap_fragment sg hooked installed
          (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        (forall restored,
          armv7a_restore_transition environment.(task_stack_call_continuations) handler selected installed restored ->
          os_int_exit_source_selected_execution environment.(task_stack_call_external)
            environment.(task_stack_call_platform) environment.(task_stack_call_port)
            environment.(task_stack_call_continuations) sg state handler transfer selected before restored /\
          (task_stack_key transfer.(os_int_exit_incoming_stack) = armv7a_call_focus_key focus ->
           armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 ->
           sem_pend_selected_success_suffix environment critical arch restore save sg original selected saved
             (os_int_exit_installed_state transfer) eid original.(os_sched_call_stack).(stackLeaseSlot)
             waiting perr
             (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
              armv7a_dormant_continuation environment.(task_stack_call_continuations) retained **
              armv7a_task_call_stacks environment.(task_stack_call_continuations)
                (os_int_exit_installed_state transfer).(TskState) focus
                (task_stack_take (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks)
                  retained.(armv7a_continuation_stack)) ** unmap_table_rep sg ** frame) restored))).
Proof.
  intros environment critical arch task_abi initial restore save sg state retained original pc lr handler
    saved entry eid waiting perr frame before focus Horigin Hwaiting Hwait Hsuccess Hrunning Hswitch
    Hnonempty Hdifferent Haddress Hcoverage Hhook Hpre.
  destruct (armv7a_irq_switch_source_preserves_pending_split _ _ _
    environment.(task_stack_call_continuations) task_abi initial sg state retained focus handler _ before
    Hrunning Hswitch Hnonempty Hdifferent Haddress Hcoverage Hhook Hpre)
    as [prepared [Hprefix Hselect]].
  exists prepared; split; [exact Hprefix|].
  intros hooked Hhook_run.
  destruct (Hselect hooked Hhook_run) as [transfer [installed [selected [node
    [Hcheckpoint [Hdestination [Hinstall [Hlease [Hfocus [Hready [Hgeneration
      [Hcovered [Hretained Hrestore]]]]]]]]]]]]].
  exists transfer, installed, selected.
  split; [exact Hcheckpoint|]. split; [exact Hdestination|]. split; [exact Hinstall|].
  intros restored Hrun; destruct (Hrestore restored Hrun) as [Hsource Hpost].
  split; [exact Hsource|]. intros Hselected Hmask.
  pose proof (Hfocus Hselected) as [Hcall [Hpc Hlr]].
  assert (Hslot : transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) =
    original.(os_sched_call_stack).(stackLeaseSlot)).
  { exact (f_equal (@fst TaskID nat) Hselected). }
  rewrite Hslot in Hready.
  destruct Hready as [Hnode [Hcurrent [Hpriority [Hmember Heffective]]]].
  assert (Hlookup : (os_int_exit_installed_state transfer).(TskState).(inUsedTaskStates)
    original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting).
  { change (transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates)
      original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting).
    rewrite Hcheckpoint; exact Hwaiting. }
  assert (node = waiting) by congruence; subst node.
  destruct (sem_pend_wait_ready_resume_registration eid
    original.(os_sched_call_stack).(stackLeaseGeneration) waiting Hwait Heffective) as [Hregistration Hgen].
  match type of Hpost with ?P restored => assert (Hexpose : P |--
    coq_prop (UCOS2_state_inv sg (os_int_exit_installed_state transfer)) && TT) end.
  { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
  assert (Hresume : sem_pend_resume_entry sg (os_int_exit_installed_state transfer) eid
    original.(os_sched_call_stack).(stackLeaseSlot) waiting).
  { split; [exact (proj1 (Hexpose restored Hpost))|].
    exact (conj Hcurrent (conj Hlookup (conj Hregistration Hmember))). }
  eapply sem_pend_selected_success_return; [exact Hcall|exact Hmask|exact Hresume|exact Hsuccess|].
  match type of Hpost with ?P restored => match goal with |- ?Q restored =>
    assert (Horder : P |-- Q) by entailer! end end.
  exact (Horder restored Hpost).
Qed.
