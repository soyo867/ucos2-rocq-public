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
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_switch_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_foreign_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_registered_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Resume an actual pending call with its original saved mask. The same
    install/frame-load proof covers a pending Save suffix and a pending
    Restore BX. Neither branch executes a second MRS or MSR. Historical
    creation resources come from the preceding concrete source trace;
    current resources come from the actual selected install/restore.
    [frame] can own a private TCB or the failed-create stack buffer. *)
Lemma task_tcb_init_pending_call_suffix_source :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original released context outgoing hooked suspended heap (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released hooked ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
  (task_tcb_init_switch_capture environment task_abi sg original suspended context outgoing hooked ** frame) heap ->
  exists installed selected,
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
      (exists node,
        sched_current_ready_at current.(TskState) current.(SchedState)
          original.(os_sched_call_stack).(stackLeaseSlot) node /\
        node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
        current.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None) /\
      (current.(SchedState).(isRunning) = true -> task_create_call_stage returned current) /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current) /\
      (task_tcb_init_stack_save_input environment critical sg returned
         (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) current **
       unmap_table_rep sg ** frame) restored /\
      (forall cursor final_registers acquired after,
        cursor.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
        cursor.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
        cursor.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
        interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
          (nth 0 suspended.(armv7a_continuation_registers) 0) ->
        armv7a_save_suffix_transition save cursor current restored final_registers acquired after ->
        kernel_save_after_mrs_execution arch cursor current restored final_registers acquired after /\
        acquired = current /\
        final_registers.(kernel_save_r0) = nth 0 suspended.(armv7a_continuation_registers) 0 /\
        final_registers.(kernel_save_return_word) = Some suspended.(armv7a_continuation_lr) /\
        (task_tcb_init_stack_save_output environment critical sg original
           (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) final_registers.(kernel_save_r0) released **
         unmap_table_rep sg ** frame) after) /\
      (forall saved written cursor final_cursor after,
        armv7a_irq_fiq_mask written = armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) ->
        armv7a_irq_fiq_mask saved = armv7a_irq_fiq_mask written ->
        cursor.(kernel_restore_msr_word) = Some written ->
        cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
        armv7a_restore_suffix_transition restore cursor restored final_cursor after ->
        final_cursor.(kernel_restore_return_word) = Some suspended.(armv7a_continuation_lr) /\
        (kernel_stack_call_closed abi kernel_program_inv sg (task_stack_call_active_key returned)
           returned (armv7a_irq_fiq_mask saved) current ** frame) after /\
        (task_tcb_init_stack_restore_output environment critical sg original saved released **
         unmap_table_rep sg ** frame) after)).
Proof.
  intros environment critical arch task_abi save restore sg original released context outgoing hooked suspended
    heap frame abi current Hhistory Horigin Hbinding Hcall Hslice Hpointer Haddress Hdestination Hpre.
  set (focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr)).
  match type of Hpre with ?P heap => assert (Hopen : P |--
    coq_prop (os_sched_saved_stack_binding context outgoing hooked /\
      sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) /\
      hooked.(SchedState).(readyList) <> [] /\
      task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack)))) &&
    (UCOS2_inv sg hooked **
     task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
     armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
       (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
     armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
     (armv7a_task_switch_control task_abi context ** (unmap_table_rep sg ** frame)))) end.
  { unfold task_tcb_init_switch_capture; fold abi focus; entailer!. }
  destruct (Hopen heap Hpre) as [[Hsaved [Hhigh [Hnonempty Hcoverage]]] Hinput].
  destruct (task_create_sched_restore_pending_call _ _ _ abi task_abi sg context outgoing hooked original
    suspended (unmap_table_rep sg ** frame) heap Hbinding Hcall Hslice Hsaved Hdestination Hhigh Hnonempty
    Hpointer Haddress Hcoverage Hinput)
    as [installed [selected [node [Hinstall [Hreads [Hfocus [Hlease [Hsp [Hcpsr [Hregisters [Hcovered Hrun]]]]]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hsp|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros restored Hrestore returned.
  destruct (Hrun restored Hrestore) as [Hmemory [Hsource [Hselected Howned]]].
  fold current returned focus in Howned, Hcovered.
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { unfold returned, task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; auto. }
  assert (Hactive_coverage : task_stack_live_coverage current.(TskState) (task_stack_call_active_key returned)).
  { unfold returned, armv7a_continuation_resumed_call, task_stack_call_active_key;
      cbn [os_sched_call_origin]; rewrite Horigin; exact Hcovered. }
  assert (Hvalid : UCOS2_state_inv sg current).
  { match type of Howned with ?P restored => assert (Hobserve : P |--
      coq_prop (UCOS2_state_inv sg current) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve restored Howned)). }
  destruct (task_tcb_init_install_preserves_call sg original released context outgoing hooked
    Hhistory Hvalid (proj1 Hdestination)) as [Hpreserved Hordinary].
  assert (Hselection : sched_current_ready_at current.(TskState) current.(SchedState)
    original.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration)).
  { match type of Hselected with ?P restored => assert (Hobserve : P |-- coq_prop
      (sched_current_ready_at current.(TskState) current.(SchedState)
         original.(os_sched_call_stack).(stackLeaseSlot) node /\
       node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration)) && TT) end.
    { unfold os_sched_source_selected_post; fold current; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve restored Hselected)). }
  destruct Hselection as [Hready Hgeneration].
  assert (Habsent : current.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None).
  { unfold current, os_sched_install_context.
    cbn [replace_SchedS replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_take_lookup. }
  assert (Hstage : current.(SchedState).(isRunning) = true -> task_create_call_stage returned current).
  { intro Hrunning.
    unfold task_create_call_stage, returned, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin os_sched_call_stack]; rewrite Horigin, Hlease.
    split.
    - unfold task_create_call_origin; split; [exact Hrunning|].
      split; [exact (proj1 (proj2 Hready))|].
      exists node; split; [exact (proj1 Hready)|exact Hgeneration].
    - split; [reflexivity|]. split; [reflexivity|]. split.
      + exact Habsent.
      + intro Henabled; exists node; split; assumption. }
  assert (Hclosed : (kernel_stack_call_closed abi kernel_program_inv sg
    (task_stack_call_active_key returned) returned
    (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) current ** frame) restored).
  { match type of Howned with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
    { unfold kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
      sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ abi current.(TskState) focus
        current.(TskState).(parkedTaskStacks)); entailer!. }
    exact (Hclose restored Howned). }
  set (history := fun previous before (actual : OsSchedCallContext) after =>
    task_tcb_init_call_preserved sg previous.(os_sched_call_invocation) before after /\
    (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved previous before after)).
  assert (Hhistory_current : history original released returned current) by (split; assumption).
  split; [exact Hsame|]. split; [exists node; auto|]. split; [exact Hstage|].
  split; [exact Hpreserved|]. split; [exact Hordinary|]. split.
  - match type of Hclosed with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
    { unfold abi; rewrite <- (task_tcb_init_stack_save_input_closed_world environment critical sg returned
        (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) current); entailer!. }
    exact (Hclose restored Hclosed).
  - split.
    + intros cursor final_registers acquired after Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsaved_value Hsuffix.
      assert (Hsaved_cursor : interrupt_saved_value
        (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) cursor.(kernel_save_r0)).
      { rewrite Hcursor_r0, Hregisters; exact Hsaved_value. }
      assert (Hsaved_current : interrupt_saved_value (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr))
        cursor.(kernel_save_r0)).
      { rewrite Hcursor_cpsr, Hcpsr; exact Hsaved_cursor. }
      assert (Hsuffix_input : (kernel_stack_call_closed abi kernel_program_inv sg
        (task_stack_call_active_key returned) returned (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr))
        current ** frame) restored).
      { rewrite Hcursor_cpsr, Hcpsr; exact Hclosed. }
      destruct (kernel_stack_call_history_save_suffix _ _ _ critical arch abi save kernel_program_inv sg
        (task_stack_call_active_key returned) history original returned
        (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) released current cursor restored
        final_registers acquired after frame Hhistory_current Hsame Hsaved_cursor Hsaved_current
        Hsuffix_input Hsuffix) as [Hstate [Hr0 [Hlr [Hmasked Hpost]]]].
      split; [exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsuffix)|].
      split; [exact Hstate|]. split; [rewrite Hr0, Hcursor_r0, Hregisters; reflexivity|].
      split; [rewrite Hlr, Hcursor_lr; f_equal; exact (proj2 (proj2 Hfocus))|].
      subst acquired.
      assert (Hsaved_final : interrupt_saved_value
        (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) final_registers.(kernel_save_r0))
        by (rewrite Hr0; exact Hsaved_cursor).
      match type of Hmasked with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
      { unfold kernel_stack_call_masked, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
        Intros. unfold task_tcb_init_stack_save_output; Exists returned current.
        unfold task_tcb_init_stack_context, task_tcb_init_stack_capsules; entailer!. }
      exact (Hclose after Hmasked).
    + intros saved written cursor final_cursor after Hwritten Hsaved_mask Hword Hcursor_lr Hsuffix.
      assert (Hsuffix_input : (kernel_stack_call_closed abi kernel_program_inv sg
        (task_stack_call_active_key returned) returned (armv7a_irq_fiq_mask written) current ** frame) restored).
      { rewrite Hwritten; exact Hclosed. }
      destruct (kernel_stack_call_history_restore_suffix _ _ _ critical arch abi restore kernel_program_inv sg
        (task_stack_call_active_key returned) history original released returned current written cursor restored
        final_cursor after frame Hhistory_current Hsame Hword Hsuffix_input Hsuffix)
        as [Hcursor [Hafter_memory [Hafter Hpost]]].
      split.
      * rewrite Hcursor; cbn [kernel_restore_branch_lr kernel_restore_return_word].
        rewrite Hcursor_lr; f_equal; exact (proj2 (proj2 Hfocus)).
      * split; [rewrite Hsaved_mask; exact Hafter|].
        match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
        { rewrite <- Hsaved_mask; unfold abi.
          rewrite <- (task_tcb_init_stack_save_input_closed_world environment critical sg returned
            (armv7a_irq_fiq_mask saved) current).
          unfold task_tcb_init_stack_restore_output; Exists returned current; entailer!. }
        exact (Hclose after Hafter).
Qed.
