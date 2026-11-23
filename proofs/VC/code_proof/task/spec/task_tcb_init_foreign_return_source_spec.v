Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_world_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Installing the original continuation changes the current-task cache
    and parked map. Its actual returned heap establishes validity. The
    original creation fragment, invocation registration and names are
    transported by the preceding registered execution, not inferred from
    the focused descriptor. *)
Lemma task_tcb_init_install_preserves_call :
  forall sg original released context outgoing hooked,
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released hooked ->
  UCOS2_state_inv sg current ->
  hooked.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
  (UCOS2_state_inv sg released ->
   task_tcb_init_stack_source_preserved original released current).
Proof.
  intros sg original released context outgoing hooked current Hhistory Hvalid Hselected.
  split.
  - intros Hreleased.
    destruct (Hhistory Hreleased) as [_ [Hframe [Hactive Hname]]].
    split; [exact Hvalid|]. split; [exact Hframe|]. split; assumption.
  - intros Hreleased [Horigin [Hactive Hcurrent]].
    destruct (Hhistory Hreleased) as [_ [_ [Hlive _]]].
    split; [exact Horigin|]. split.
    + apply Hlive; exact Hactive.
    + unfold task_execution_current; rewrite Horigin; exact Hselected.
Qed.

(** One actual ordinary-switch return, including the install stores,
    original frame loads, task restore and final MSR/BX. The history is
    supplied by the same registered source producer; it contains no
    future-selected endpoint. The retained frame may hold the private TCB
    or no-free stack buffer. The current world is obtained from the
    pending-call restore producer and cannot be replaced by an old world. *)
Lemma task_tcb_init_foreign_switch_return :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original released context outgoing hooked suspended saved acquired heap (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  UCOS2_state_inv sg released ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released hooked ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
     unmap_table_rep sg ** frame))) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
      armv7a_restore_prefix_transition restore cursor restored written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
      (task_tcb_init_stack_restore_output environment critical sg original saved released **
       unmap_table_rep sg ** frame) after /\
      (task_tcb_init_stack_call_return_post environment critical sg original
         (armv7a_irq_fiq_mask saved) released ** unmap_table_rep sg ** frame) after).
Proof.
  intros environment critical arch task_abi restore sg original released context outgoing hooked
    suspended saved acquired heap frame abi focus Hreleased Hhistory Horigin Hbinding Hcall Hslice
    Hmask Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre.
  destruct (task_create_sched_pending_return_source environment critical arch task_abi restore
    sg context outgoing hooked original suspended saved acquired heap frame
    Horigin Hbinding Hcall Hslice Hmask Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre)
    as [installed [selected [node [Hinstall [Hreads [Hsp [Hcpsr [Hregisters Hresume]]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hsp|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros restored Hrun cursor written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix.
  destruct (Hresume restored Hrun) as [Hsame [Hsource [Hselected [Hmasked Hreturn]]]].
  set (returned := armv7a_continuation_resumed_call selected original) in *.
  set (current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked) in *.
  assert (Hvalid : UCOS2_state_inv sg current).
  { match type of Hmasked with ?P restored =>
      assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
    { unfold kernel_stack_call_masked, kernel_stack_inv, kernel_program_inv, UCOS2_inv;
        entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve restored Hmasked)). }
  destruct (task_tcb_init_install_preserves_call sg original released context outgoing hooked
    Hhistory Hvalid (proj1 Hdestination)) as [Hpreserved Hordinary].
  assert (Hcursor_mask : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    by (rewrite Hcursor, Hcpsr; exact Hmask).
  match type of Hmasked with ?P restored => assert (Hopen : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) returned **
    (kernel_stack_inv abi kernel_program_inv sg (task_stack_call_active_key returned) current ** frame))
    by (unfold kernel_stack_call_masked; entailer!) end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg returned saved
    acquired cursor restored written middle final_cursor after _ Hr0 Hcursor_mask
    (Hopen restored Hmasked) Hprefix Hsuffix) as [Hexecution [Hlr [Hmemory Howned]]].
  assert (Houtput : (task_tcb_init_stack_restore_output environment critical sg original saved released **
    unmap_table_rep sg ** frame) after).
  { match type of Howned with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) end end.
    { unfold kernel_stack_inv; Intros.
      unfold task_tcb_init_stack_restore_output; Exists returned current.
      unfold task_tcb_init_stack_save_input, task_tcb_init_stack_capsules.
      rewrite kernel_program_inv_split_unmap.
      unfold critical_region_outside.
      rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
      unfold UCOS2_inv; entailer!. }
    exact (Hclose after Howned). }
  split; [exact Hexecution|]. split; [exact Houtput|].
  match type of Houtput with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold task_tcb_init_stack_restore_output; Intros last current_state.
    assert (Hobserved : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
      released current_state) by tauto.
    destruct (Hobserved Hreleased) as [_ [Hframe [Hactive Hname]]].
    unfold task_tcb_init_stack_call_return_post; Exists last current_state.
    unfold task_tcb_init_stack_return_preserved; entailer!; try tauto. }
  exact (Hclose after Houtput).
Qed.
