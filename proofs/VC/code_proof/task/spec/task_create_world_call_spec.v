Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_switch_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Consume the shared source-established MASKED world at the actual
    scheduler C entry. All three no-switch C guards are handled by the
    existing concrete prefix producer. The final MSR/BX produces the new
    source-rich return assertion used by TaskCreate's canonical which12.

    This theorem is the uninterrupted final-Restore branch, not a complete
    callee Ensure. Its acquired/current indices stay distinct, and no
    old erased interval or future bare architecture-save forall is used.
    The IRQ branch must use its actual deposited/registry/current world. *)
Lemma task_create_sched_masked_nonswitch_return :
  forall environment critical arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call saved acquired state before (frame : Assertion),
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv
     critical sg (task_stack_call_active_key call) call saved acquired state ** frame) before ->
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg before prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (os_sched_source_return_post environment critical sg call (armv7a_irq_fiq_mask saved)
         (os_sched_prefix_state state) ** frame) after).
Proof.
  intros environment critical arch restore sg call saved acquired state before frame
    Hnoswitch Hnonempty Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (UCOS2_inv sg state ** unmap_table_rep sg **
     (critical_region_masked environment.(task_stack_call_platform) critical sg
        call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
      task_tcb_init_stack_context environment call **
      task_tcb_init_stack_covered_capsules environment state ** frame))) end.
  { unfold kernel_stack_call_masked, kernel_stack_inv, task_tcb_init_stack_context,
      task_tcb_init_stack_covered_capsules.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (os_sched_source_nonswitch_prefix_resources sg state _ before Hnoswitch Hnonempty Howned)
    as [prefix_heap [Hprefix Hafter_prefix]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmask Hrestore_prefix Hrestore_suffix.
  match type of Hafter_prefix with ?P prefix_heap => assert (Hrestore_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment call ** UCOS2_inv sg (os_sched_prefix_state state) **
    task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state state) **
    unmap_table_rep sg ** frame) end.
  { change (task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state state)) with
      (task_tcb_init_stack_covered_capsules environment state); entailer!. }
  exact (os_sched_source_uninterrupted_return_post environment critical arch restore sg call saved
    acquired (os_sched_prefix_state state) cursor prefix_heap written middle final_cursor after frame
    Hcoverage Hr0 Hmask (Hrestore_input prefix_heap Hafter_prefix) Hrestore_prefix Hrestore_suffix).
Qed.

(** The actual ordinary task-switch destination is the pending original
    invocation. Its install/take proof recovers the original saved SP,
    CPSR and all thirteen registers. Only then do the original saved-mask
    token and region handle rejoin the newly restored running authority.

    This is the ordinary returning-destination / uninterrupted final
    Restore branch. A foreign destination is NOT a return of this call;
    the current map cannot be framed unchanged through that interval.
    The owned token/handle below are the original call's retained frame,
    not a duplicate running owner carried through context switching. *)
Lemma task_create_sched_pending_return_source :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg context outgoing hooked original suspended saved acquired heap (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
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
  exists installed selected node,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := armv7a_continuation_resumed_call selected original in
      task_tcb_init_stack_same_call returned original /\
      environment.(task_stack_call_external).(os_sched_arch_resume_source) original returned /\
      (os_sched_source_selected_post environment.(task_stack_call_external)
         environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
         sg focus original.(os_sched_call_stack) selected node current **
       (interrupt_platform_saved environment.(task_stack_call_platform)
          (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
        critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
        unmap_table_rep sg ** frame)) restored /\
      (kernel_stack_call_masked abi kernel_program_inv critical sg
         (task_stack_call_active_key returned) returned saved acquired current ** frame) restored /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        (os_sched_source_return_post environment critical sg returned
           (armv7a_irq_fiq_mask saved) current ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg context outgoing hooked original suspended
    saved acquired heap frame abi focus current Horigin Hbinding Hcall Hslice Hmask Hsaved
    Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre.
  destruct (task_create_sched_restore_pending_call _ _ _ abi task_abi sg context outgoing hooked
    original suspended _ heap Hbinding Hcall Hslice Hsaved Hdestination Hhigh Hnonempty
    Hpointer Haddress Hcoverage Hpre)
    as [installed [selected [node [Hinstall [Hreads [Hfocus [Hlease [Hsp [Hcpsr
      [Hregisters [Hcovered Hrestore]]]]]]]]]]].
  exists installed, selected, node.
  split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hsp|].
  split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros restored Hrun returned.
  destruct (Hrestore restored Hrun) as [Hmemory [Hsource [Hselected Hresources]]].
  rewrite Hmask in Hresources; fold returned in Hsource, Hresources.
  fold current focus abi in Hresources, Hselected, Hcovered.
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { unfold task_tcb_init_stack_same_call, returned, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; auto. }
  assert (Hactive : task_stack_call_active_key returned = Some (task_stack_key original.(os_sched_call_stack))).
  { unfold task_stack_call_active_key, returned, armv7a_continuation_resumed_call;
      cbn [os_sched_call_origin]; rewrite Horigin; reflexivity. }
  assert (Hmasked : (kernel_stack_call_masked abi kernel_program_inv critical sg
    (task_stack_call_active_key returned) returned saved acquired current ** frame) restored).
  { match type of Hresources with ?P restored => match goal with |- ?Q restored =>
      assert (Hclose : P |-- Q) end end.
    { sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ abi current.(TskState)
        focus current.(TskState).(parkedTaskStacks)).
      unfold kernel_stack_call_masked, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
      unfold kernel_call_execution_owned, critical_region_masked.
      rewrite Hactive; unfold returned, armv7a_continuation_resumed_call;
        cbn [os_sched_call_invocation os_sched_call_origin].
      entailer!. }
    exact (Hclose restored Hresources). }
  split; [exact Hsame|]. split; [exact Hsource|]. split; [exact Hselected|].
  split; [exact Hmasked|].
  intros cursor written middle final_cursor after Hr0 Hcursor Hprefix Hsuffix.
  assert (Hmask_cursor : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    by (rewrite Hcursor, Hcpsr; exact Hmask).
  assert (Hrestore_input : kernel_stack_call_masked abi kernel_program_inv critical sg
      (task_stack_call_active_key returned) returned saved acquired current ** frame |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment returned ** UCOS2_inv sg current **
    task_tcb_init_stack_covered_capsules environment current ** unmap_table_rep sg ** frame).
  { unfold kernel_stack_call_masked, kernel_stack_inv, task_tcb_init_stack_context,
      task_tcb_init_stack_covered_capsules.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  eapply os_sched_source_uninterrupted_return_post; try eassumption.
  - rewrite Hactive; exact Hcovered.
  - exact (Hrestore_input restored Hmasked).
Qed.

(** TCBInit's actual source return feeds the next Save on THIS heap and
    executing invocation. The shared generic suffix exposes its concrete
    masked endpoint, rather than asking this consumer to guess the state
    hidden by an existential post. The C prefix and final Restore then
    consume that same world. No old weak post is used to recreate it.

    This is the no-IRQ Save / no-switch C / no-IRQ final-Restore branch.
    The branch guards and observed registers concern this actual state;
    they are not a new forall over unrelated architecture source atoms. *)
Lemma task_create_tcb_return_sched_nonswitch_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original released returned mask state registers before
    final_registers acquired saved_heap (frame : Assertion),
  kernel_call_restore_history environment critical sg original released returned state ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv
     sg (task_stack_call_active_key returned) returned mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  task_tcb_init_stack_same_call returned original /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (os_sched_source_return_post environment critical sg returned mask
         (os_sched_prefix_state state) ** frame) after).
Proof.
  intros environment critical arch save restore sg original released returned mask state registers before
    final_registers acquired saved_heap frame Hhistory Hreturn Hvalid Hmask Hnoswitch Hnonempty Hpre Hsave.
  pose proof (kernel_call_restore_history_same_call environment critical sg original released returned state
    Hhistory) as Hsame.
  assert (Hsame_generic : kernel_stack_call_same_call returned original) by exact Hsame.
  assert (Hsaved : interrupt_saved_value mask (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hvalid|exact Hmask]. }
  assert (Hobserved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hvalid|reflexivity]. }
  assert (Hrun : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  assert (Hinput : (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    sg (task_stack_call_active_key returned) returned
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) state ** frame) before).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; exact Hpre. }
  destruct (kernel_stack_call_history_save_suffix _ _ _ _ _
    environment.(task_stack_call_continuations) save kernel_program_inv sg
    (task_stack_call_active_key returned) (kernel_call_restore_history environment critical sg)
    original returned mask released state (kernel_save_read_cpsr registers) before
    final_registers acquired saved_heap frame Hhistory Hsame_generic Hsaved Hobserved Hinput Hsave)
    as [Hstate [Hr0 [Hlr [Hmasked Hpost]]]].
  split; [exact Hsame|]. split; [exact Hrun|]. split; [exact Hstate|]. subst acquired.
  destruct (task_create_sched_masked_nonswitch_return environment critical arch restore sg returned
    final_registers.(kernel_save_r0) state state saved_heap frame Hnoswitch Hnonempty Hmasked)
    as [prefix_heap [Hprefix Hrestore]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hcursor Hcurrent Hprefix_run Hsuffix_run.
  destruct (Hrestore cursor written middle final_cursor after Hcursor Hcurrent Hprefix_run Hsuffix_run)
    as [Hexecution Hresources].
  split; [exact Hexecution|]. rewrite Hr0 in Hresources.
  cbn [kernel_save_read_cpsr kernel_save_r0] in Hresources; rewrite Hmask in Hresources; exact Hresources.
Qed.
