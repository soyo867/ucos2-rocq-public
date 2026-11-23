Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.event Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reuse the existing approved non-VFP SVC IRQ register observation.
    The indexed source event and its old Save transition share the SAME
    descriptor and heaps. MRS determines live R0; the already configured
    observation binds that value to the saved frame. No full-CPSR equality,
    new platform law or separate freely chosen snapshot is required.
    Actual platform membership retains the documented external boundary. *)
Lemma sem_pend_mrs_irq_saved_value : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (registers_source : Armv7aIRQRegisterSave external platform port abi)
  arch registers after_mrs state before irq_input handler suspended saved_heap,
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  kernel_call_save_instruction_step arch SaveReadCPSR registers state before
    after_mrs state irq_input ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
  armv7a_irq_register_save registers_source after_mrs.(kernel_save_r0) after_mrs.(kernel_save_lr)
    handler suspended irq_input saved_heap ->
  armv7a_save_transition abi handler suspended irq_input saved_heap /\
  armv7a_continuation_binding suspended /\
  interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (nth 0 suspended.(armv7a_continuation_registers) 0) /\
  nth 0 suspended.(armv7a_continuation_registers) 0 = registers.(kernel_save_cpsr).
Proof.
  intros external platform port abi registers_source arch registers after_mrs state before
    irq_input handler suspended saved_heap Hvalid Hmrs Hmask Hsource.
  inversion Hmrs; subst after_mrs.
  destruct (armv7a_irq_register_save_refinement _ _ _ _ registers_source _ _ _ _ _ _ Hsource)
    as [Hsave [Hr0 Hlr]].
  destruct (armv7a_save_transition_observations _ _ _ abi _ _ _ _ Hsave)
    as [_ [_ [Hbinding [Hsaved_mask _]]]].
  split; [exact Hsave|]. split; [exact Hbinding|]. split.
  - rewrite Hr0; split; [exact Hvalid|].
    cbn [kernel_save_read_cpsr kernel_save_r0]; congruence.
  - exact Hr0.
Qed.

(** The current pending frame is the same descriptor from the indexed
    IRQ save immediately after the actual MRS instruction.
    The existing Scheduler consumer identifies the selected words by actual
    SP/frame loads and then executes Restore and CPSID/DSB/BX. Its returned
    R0 is consequently the ORIGINAL MRS value, not a fresh current mask.

    The source history and Event projection in the final continuation are
    supplied by the same registered execution. They remain explicit until
    canonical first-Save integration; no future-return condition is placed
    in SemPend's public Require. The result includes the literal count cell
    and is suitable for either the positive-count or zero-count branch. *)
Lemma sem_pend_mrs_sched_restore_count : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (registers_source : Armv7aIRQRegisterSave environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg original registers after_mrs start before irq_input handler suspended saved_heap
  context outgoing hooked eid observed (frame : Assertion) heap,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  kernel_call_save_instruction_step arch SaveReadCPSR registers start before
    after_mrs start irq_input ->
  handler.(os_int_exit_interrupted_call) = original ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
  armv7a_irq_register_save registers_source after_mrs.(kernel_save_r0) after_mrs.(kernel_save_lr)
    handler suspended irq_input saved_heap ->
  armv7a_task_frame_slice suspended ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) hooked ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  mutex_query_lookup start eid observed -> observed.(eventType) = OS_EVENT_TYPE_SEM ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** frame)) heap ->
  let installed_state := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored cursor final_registers acquired after,
      let returned := armv7a_continuation_resumed_call selected original in
      armv7a_task_restore_transition task_abi context selected installed restored ->
      cursor.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      cursor.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      cursor.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      armv7a_save_suffix_transition suffix cursor installed_state restored final_registers acquired after ->
      kernel_call_save_history environment critical sg original start returned acquired ->
      sem_pend_save_event_trace critical sg original.(os_sched_call_invocation) start acquired ->
      acquired = installed_state /\
      final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
      kernel_save_after_mrs_execution arch cursor installed_state restored final_registers acquired after /\
      sem_pend_task_call_stage sg returned acquired /\
      task_stack_live_coverage acquired.(TskState) (Some (task_stack_key original.(os_sched_call_stack))) /\
      exists current,
        sem_pend_acquire_observation environment critical sg original returned
          (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0)
          start acquired eid observed current /\
        (critical_region_masked environment.(task_stack_call_platform) critical sg
           original.(os_sched_call_invocation) original.(os_sched_call_origin)
           final_registers.(kernel_save_r0) acquired **
         os_sched_context_resources environment.(task_stack_call_external) returned **
         (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
         sem_post_count_frame sg acquired eid current **
         armv7a_task_call_stacks abi acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks) **
         frame) after).
Proof.
  intros environment critical arch task_abi suffix registers_source sg original registers after_mrs start before
    irq_input handler suspended saved_heap context outgoing hooked eid observed frame heap abi
    focus Hvalid_registers Hmrs Hhandler Hpc Hmask Hcapture Hslice Horigin Hactive Hfields Hstack
    Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hprotocol Hlookup Htype Hpre installed_state.
  destruct (sem_pend_mrs_irq_saved_value _ _ _ abi registers_source arch registers after_mrs
    start before irq_input handler suspended saved_heap Hvalid_registers Hmrs Hmask Hcapture)
    as [Hsave [Hbinding [Hsaved Hword]]].
  destruct (armv7a_save_transition_observations _ _ _ abi _ _ _ _ Hsave)
    as [_ [Hcall [_ [_ [Hsaved_pc _]]]]].
  rewrite Hhandler in Hcall; rewrite Hpc in Hsaved_pc.
  destruct (sem_pend_sched_restore_first_save _ _ _ _ _ abi task_abi suffix sg context outgoing hooked
    original suspended frame heap Hbinding Hcall Hslice Hsaved_pc Hsaved Horigin Hactive Hfields
    Hstack Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads Hreturn]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored cursor final_registers acquired after returned Hrestore Hcursor_cpsr Hcursor_r0
    Hcursor_lr Hsuffix Hhistory Hevents.
  destruct (Hreturn restored cursor final_registers acquired after Hrestore Hcursor_cpsr Hcursor_r0
    Hcursor_lr Hsuffix) as [Hstate [Hlr [Hr0 [Hexecution [Hstage [Hcovered Howned]]]]]].
  assert (Horiginal_value : final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr))
    by (rewrite Hr0; exact Hword).
  assert (Horiginal_saved : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    final_registers.(kernel_save_r0)) by (rewrite Horiginal_value; split; [exact Hvalid_registers|reflexivity]).
  assert (Hvalid : UCOS2_state_inv sg acquired).
  { match type of Howned with ?P after => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg acquired) && TT) end.
    { unfold UCOS2_inv; entailer!. }
    exact (proj1 (Hobserve after Howned)). }
  destruct (sem_pend_source_acquire_observation environment critical sg original returned
    (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0)
    start acquired eid observed Hhistory Hevents Horiginal_saved Hvalid Hprotocol Hlookup Htype)
    as [current Hobservation].
  assert (Hreturned_stage : sem_pend_task_call_stage sg returned acquired).
  { destruct (kernel_call_save_history_same_call environment critical sg original start returned acquired Hhistory)
      as [Hinvocation [Hreturned_origin Hlease]].
    unfold sem_pend_task_call_stage, kernel_call_task_source in *.
    rewrite Hinvocation, Hreturned_origin, Hlease; exact Hstage. }
  split; [exact Hstate|]. split; [exact Horiginal_value|]. split; [exact Hexecution|].
  split; [exact Hreturned_stage|]. split; [exact Hcovered|]. exists current; split; [exact Hobservation|].
  match type of Howned with ?P after =>
    match goal with |- ?Q after => assert (Hsplit : P |-- Q) end
  end.
  { sep_apply_l_atomic (sem_pend_acquire_count_split environment critical sg original returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0)
      start acquired eid observed current Hobservation); entailer!. }
  exact (Hsplit after Howned).
Qed.
