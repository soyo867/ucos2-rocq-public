Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_switch_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A complete finite scheduler-call/second-Save chain on one heap. The
    actual enabled/equal-priority branch establishes readiness, using the
    current-cache binding retained by the wait/source prefix. The wait
    history and its intervening interval are past source facts, not a
    universal acquire-safety condition or an assumed callee Ensure.

    Post/Abort/Tick must establish the supplied wait continuation at STATE
    by their own source effects. Locked no-selection returns and IRQs in
    either Save/Restore are not covered by this explicitly guarded branch.
    The result is the same resume_origin and cells consumed at canonical
    which15 and the common cleanup, without changing the public result. *)
Lemma sem_pend_nonswitch_source_wait_save_return : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call original_mask original_state observed eid timeout waiting state mask old
  registers before final_registers acquired saved_heap (frame : Assertion),
  sem_pend_wait_history critical sg call original_mask original_state observed eid timeout waiting ->
  critical_region_interval critical sg call.(os_sched_call_invocation) waiting state ->
  kernel_call_task_source call state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  sem_pend_wait_continuation eid call.(os_sched_call_stack).(stackLeaseGeneration) old ->
  os_sched_selection_enabled state = true -> os_sched_requests_switch state = false ->
  state.(SchedState).(readyList) <> [] ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (task_tcb_init_stack_covered_save_input environment critical sg call mask state **
   unmap_table_rep sg ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\ exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor returned_heap,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor returned_heap ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor returned_heap /\
      forall second_registers second_final resumed after,
        second_registers.(kernel_save_return_word) = None ->
        valid_os_cpu_sr second_registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask second_registers.(kernel_save_cpsr) = mask ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr second_registers)
          (os_sched_prefix_state state) returned_heap second_final resumed after ->
        kernel_call_save_uninterrupted_execution arch second_registers (os_sched_prefix_state state)
          returned_heap second_final resumed after /\
        resumed = os_sched_prefix_state state /\
        sem_pend_resume_origin environment.(task_stack_call_external) critical sg call original_mask
          original_state observed eid timeout resumed call.(os_sched_call_stack).(stackLeaseSlot) old /\
        task_stack_live_coverage resumed.(TskState) (task_stack_call_active_key call) /\
        kernel_call_save_source environment.(task_stack_call_external) environment.(task_stack_call_port)
          critical sg call call mask second_final.(kernel_save_r0) (os_sched_prefix_state state) resumed /\
        (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
           call.(os_sched_call_origin) second_final.(kernel_save_r0) resumed **
         os_sched_context_resources environment.(task_stack_call_external) call **
         sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) **
         tcb_cell (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
           TCBStat (Some (encode_task_status old.(stat))) **
         tcb_cell (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
           TCBStatPend (Some (encode_pend_status old.(statPend))) **
         tcb_cell (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
           TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
         sem_pend_cleanup_frame sg resumed call.(os_sched_call_stack).(stackLeaseSlot) old **
         armv7a_task_stack_continuations environment.(task_stack_call_continuations)
           resumed.(TskState) resumed.(TskState).(parkedTaskStacks) **
         unmap_table_rep sg ** frame) after).
Proof.
  intros environment critical arch save restore sg call original_mask original_state observed eid timeout
    waiting state mask old registers before final_registers acquired saved_heap frame Hhistory Hinterval
    Hsource Hcache Hold Hwait Hen Hnoswitch Hnonempty Hreturn Hcpsr Hmask Hpre Hsave.
  assert (Hvalid : UCOS2_state_inv sg state).
  { assert (Hobserve : task_tcb_init_stack_covered_save_input environment critical sg call mask state **
        unmap_table_rep sg ** frame |-- coq_prop (UCOS2_state_inv sg state) && TT).
    { unfold task_tcb_init_stack_covered_save_input; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  destruct (os_sched_nonswitch_current_ready_at sg call state Hvalid Hsource Hcache Hen Hnoswitch Hnonempty)
    as [node [Hready Hgen]].
  assert (node = old) by (pose proof (proj1 Hready); change (state.(TskState).(inUsedTaskStates)
    call.(os_sched_call_stack).(stackLeaseSlot) = Some node) in H; congruence); subst node.
  assert (Hprefix_valid : UCOS2_state_inv sg (os_sched_prefix_state state))
    by (apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid).
  pose proof (os_sched_prefix_preserves_task_source call state Hsource) as Hprefix_source.
  assert (Horigin : sem_pend_resume_origin environment.(task_stack_call_external) critical sg call original_mask
    original_state observed eid timeout (os_sched_prefix_state state) call.(os_sched_call_stack).(stackLeaseSlot) old).
  { unfold sem_pend_resume_origin; split.
    - unfold sem_pend_resume_entry.
      destruct Hready as [Hlookup [Hcurrent [Hpriority [Hin Heffective]]]].
      split; [exact Hprefix_valid|]. split; [exact Hcurrent|]. split; [exact Hlookup|].
      split; [exact (proj1 (sem_pend_wait_ready_resume_registration _ _ _ Hwait Heffective))|exact Hin].
    - split; [rewrite Hgen; exact (proj1 Hsource)|].
      exists waiting, call; split; [exact Hhistory|].
      exists state, (os_sched_prefix_state state); split; [exact Hinterval|].
      split; [unfold os_sched_c_return; rewrite Hnoswitch; auto|constructor]. }
  destruct (os_sched_source_uninterrupted_nonswitch_call_resources environment critical arch save restore
    sg call mask state registers before final_registers acquired saved_heap frame
    Hreturn Hcpsr Hmask Hnoswitch (fun _ => Hnonempty) Hpre Hsave)
    as [Hsave_run [Hstate [prefix_heap [Hprefix Hrestore]]]].
  split; [exact Hsave_run|]. split; [exact Hstate|]. exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor returned_heap Hr0 Hmasked Hrestore_prefix Hrestore_suffix.
  destruct (Hrestore cursor written middle final_cursor returned_heap Hr0 Hmasked Hrestore_prefix Hrestore_suffix)
    as [Hrestore_run Hreturned].
  split; [exact Hrestore_run|].
  intros second_registers second_final resumed after Hsecond_return Hsecond_cpsr Hsecond_mask Hsecond_save.
  set (current := os_sched_prefix_state state).
  assert (Hopen : task_tcb_init_stack_covered_save_input environment critical sg call mask current **
      unmap_table_rep sg ** frame |--
    coq_prop (task_stack_live_coverage current.(TskState) (task_stack_call_active_key call)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      call (armv7a_irq_fiq_mask (kernel_save_read_cpsr second_registers).(kernel_save_cpsr)) **
    (kernel_stack_inv environment.(task_stack_call_continuations) UCOS2_inv sg
       (task_stack_call_active_key call) current ** unmap_table_rep sg ** frame))).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hsecond_mask.
    unfold task_tcb_init_stack_covered_save_input, task_tcb_init_stack_covered_capsules,
      kernel_stack_inv, critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  destruct (Hopen returned_heap Hreturned) as [Hcoverage Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr second_registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr second_registers).(kernel_save_r0))
    by (split; [exact Hsecond_cpsr|reflexivity]).
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr second_registers) current returned_heap second_final resumed after _
    Hsaved Howned Hsecond_save)
    as [Hresumed [Hmemory [Hlr [Hvalue Hpost]]]].
  assert (Hsecond_run : kernel_call_save_uninterrupted_execution arch second_registers current
    returned_heap second_final resumed after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hsecond_return|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsecond_save). }
  split; [exact Hsecond_run|]. split; [exact Hresumed|]. subst resumed.
  split; [exact Horigin|]. split; [exact Hcoverage|].
  assert (Hsecond_source : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call call mask second_final.(kernel_save_r0) current current).
  { rewrite Hvalue; split; [constructor|]. repeat (split; [reflexivity|]).
    split; [exact Hsecond_cpsr|exact Hsecond_mask]. }
  split; [exact Hsecond_source|].
  match type of Hpost with ?P after => assert (Hclose : P |--
    kernel_stack_call_masked environment.(task_stack_call_continuations) UCOS2_inv critical sg
      (task_stack_call_active_key call) call second_final.(kernel_save_r0) current current **
    unmap_table_rep sg ** frame) end.
  { unfold kernel_stack_call_masked; entailer!. }
  assert (Hcells : kernel_stack_call_masked environment.(task_stack_call_continuations) UCOS2_inv critical sg
      (task_stack_call_active_key call) call second_final.(kernel_save_r0) current current **
      unmap_table_rep sg ** frame |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) second_final.(kernel_save_r0) current **
    os_sched_context_resources environment.(task_stack_call_external) call **
    sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) **
    tcb_cell (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      TCBStat (Some (encode_task_status old.(stat))) **
    tcb_cell (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      TCBStatPend (Some (encode_pend_status old.(statPend))) **
    tcb_cell (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
    sem_pend_cleanup_frame sg current call.(os_sched_call_stack).(stackLeaseSlot) old **
    armv7a_task_stack_continuations environment.(task_stack_call_continuations)
      current.(TskState) current.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame).
  { sep_apply_l_atomic (sem_pend_save_stack_cleanup_cells _ _ _ environment.(task_stack_call_continuations)
      critical sg (task_stack_call_active_key call) call call mask second_final.(kernel_save_r0)
      current current Hprefix_valid Hprefix_source Hsecond_source); Intros selected.
    assert (Hselected : current.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some selected)
      by tauto.
    change (state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some selected) in Hselected.
    assert (selected = old) by congruence; subst selected; entailer!. }
  exact (Hcells after (Hclose after Hpost)).
Qed.

(** Consume the ACTUAL selected-source postcondition. The earlier client
    source transports invocation liveness and no-wait/non-idle fields;
    it need not preserve current/ready while another task runs. Those
    facts come from the actual selector and restore's selected lease.
    This is not yet the whole scheduler or first-Save C return. *)
Lemma sem_pend_selected_source_call_stage : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg original pc lr incoming selected node state,
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) state ->
  task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
  os_sched_source_selected_post external platform port abi sg
    (armv7a_call_focus original pc lr) incoming selected node state |--
  coq_prop (selected.(armv7a_continuation_call) = Some original /\
    selected.(armv7a_continuation_pc) = pc /\ selected.(armv7a_continuation_lr) = lr /\
    sem_pend_task_call_stage sg (armv7a_continuation_resumed_call selected original) state /\
    task_stack_live_coverage state.(TskState)
      (Some (task_stack_key (armv7a_continuation_resumed_call selected original).(os_sched_call_stack)))) &&
  (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call selected original)
     (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
   UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState)
     (armv7a_call_focus original pc lr) state.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg original pc lr incoming selected node state
    Horigin Hactive [Hrunning [observed [Hobserved Hfields]]] Hkey.
  unfold os_sched_source_selected_post; Intros.
  assert (Hlease : selected.(armv7a_continuation_stack) = incoming) by tauto.
  assert (Hfocused : armv7a_continuation_focus_binding (armv7a_call_focus original pc lr) selected).
  { assert (Hfocus_key : task_stack_key incoming = armv7a_call_focus_key (armv7a_call_focus original pc lr))
      by exact Hkey; tauto. }
  destruct Hfocused as [Hcall [Hpc Hlr]].
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) node)
    by tauto.
  assert (Hgen : node.(taskGeneration) = incoming.(stackLeaseGeneration)) by tauto.
  assert (Hcoverage : task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) by tauto.
  assert (Hslot : incoming.(stackLeaseSlot) = original.(os_sched_call_stack).(stackLeaseSlot))
    by exact (f_equal fst Hkey).
  assert (Hgeneration : incoming.(stackLeaseGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration))
    by exact (f_equal snd Hkey).
  assert (Hlookup : state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { rewrite <- Hslot; exact (proj1 Hready). }
  assert (observed = node) by congruence; subst observed.
  assert (Hstage : sem_pend_task_call_stage sg (armv7a_continuation_resumed_call selected original) state).
  { unfold sem_pend_task_call_stage, kernel_call_task_source.
    cbn [armv7a_continuation_resumed_call os_sched_call_origin os_sched_call_invocation os_sched_call_stack].
    rewrite Hlease; split.
    - split; [rewrite Hslot, Hgeneration; exact Horigin|]. split; [exact Hactive|].
      unfold task_execution_current; rewrite Horigin, <- Hslot; exact (proj1 (proj2 Hready)).
    - split; [exact Hrunning|]. exists node; split; [exact Hready|].
      split; [exact Hgen|exact Hfields]. }
  assert (Hcovered : task_stack_live_coverage state.(TskState)
    (Some (task_stack_key (armv7a_continuation_resumed_call selected original).(os_sched_call_stack)))).
  { cbn [armv7a_continuation_resumed_call os_sched_call_stack]; rewrite Hlease; exact Hcoverage. }
  unfold armv7a_task_restored_execution; cbn [armv7a_call_focus armv7a_focus_call] in Hcall.
  rewrite Hcall; entailer!.
Qed.


(** Finish the actual first-Save suffix after this selected original call.
    The PC/register joins concern the saved descriptor, not the entry state
    before interruption. The current stack map is retained on that same
    heap; an old pre-switch map is not framed across the transfer. *)
Lemma sem_pend_selected_source_save_return : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg original lr incoming selected node state registers before final_registers acquired after (frame : Assertion),
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) state ->
  task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
  registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
  registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
  registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  (os_sched_source_selected_post external platform port abi sg
    (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr) incoming selected node state ** frame) before ->
  armv7a_save_suffix_transition suffix registers state before final_registers acquired after ->
  let returned := armv7a_continuation_resumed_call selected original in
  acquired = state /\ selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
  final_registers.(kernel_save_return_word) = Some lr /\
  final_registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 /\
  kernel_save_after_mrs_execution arch registers state before final_registers acquired after /\
  sem_pend_task_call_stage sg returned acquired /\
  task_stack_live_coverage acquired.(TskState) (Some (task_stack_key returned.(os_sched_call_stack))) /\
  (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
     returned.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
   os_sched_context_resources external returned ** UCOS2_inv sg acquired **
   armv7a_task_call_stacks abi acquired.(TskState)
     (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
     acquired.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port critical arch abi suffix sg original lr incoming selected node state
    registers before final_registers acquired after frame Horigin Hactive Hfields Hkey Hcpsr Hr0 Hlr
    Hsaved Hpre Hrun returned.
  pose proof (sem_pend_selected_source_call_stage external platform port abi sg original
    (armv7a_save_entry_address suffix + 4) lr incoming selected node state Horigin Hactive Hfields Hkey) as Hstage_source.
  assert (Hopen : os_sched_source_selected_post external platform port abi sg
      (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr) incoming selected node state ** frame |--
    coq_prop (selected.(armv7a_continuation_call) = Some original /\
      selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
      selected.(armv7a_continuation_lr) = lr /\ sem_pend_task_call_stage sg returned state /\
      task_stack_live_coverage state.(TskState) (Some (task_stack_key returned.(os_sched_call_stack)))) &&
    (kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
     (UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState)
       (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
       state.(TskState).(parkedTaskStacks) ** frame))).
  { sep_apply_l_atomic Hstage_source; rewrite Hcpsr; entailer!. }
  destruct (Hopen before Hpre) as [[Hcall [Hpc [Hreturn_lr [Hstage Hcoverage]]]] Howned].
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg returned
    registers state before final_registers acquired after _ Hsaved Howned Hrun)
    as [Hstate [Hmemory [Hreturn [Hvalue Hpost]]]].
  subst acquired; split; [reflexivity|]. split; [exact Hpc|]. split.
  - rewrite Hreturn, Hlr, Hreturn_lr; reflexivity.
  - split; [rewrite Hvalue; exact Hr0|]. split.
    + exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hrun).
    + split; [exact Hstage|]. split; [exact Hcoverage|].
      match type of Hpost with ?P after => assert (Hclose : P |--
        critical_region_masked platform critical sg returned.(os_sched_call_invocation)
          returned.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
        os_sched_context_resources external returned ** UCOS2_inv sg state **
        armv7a_task_call_stacks abi state.(TskState)
          (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
          state.(TskState).(parkedTaskStacks) ** frame) by entailer!
      end.
      exact (Hclose after Hpost).
Qed.

(** The blocked call's second Save consumes an ACTUAL selected-source
    post. The wait observation is transported by the real client trace
    (sem_pend_client_trace_wait_resources), whereas readiness is supplied
    by scheduler selection. Neither fact is obtained from CPU authority.
    The real CPSID/DSB/BX suffix produces the masked heap and the exact
    current/Stat/StatPend/EventPtr cells subsequently read by os_sem.c.
    This is not a stronger declaration for an unproved OS_Sched callee. *)
Lemma sem_pend_selected_source_wait_save_return : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg original lr incoming selected node state eid registers before
  final_registers acquired after (frame : Assertion),
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) node ->
  task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
  registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
  registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
  registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  (os_sched_source_selected_post external platform port abi sg
    (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
    incoming selected node state ** frame) before ->
  armv7a_save_suffix_transition suffix registers state before final_registers acquired after ->
  acquired = state /\
  final_registers.(kernel_save_return_word) = Some lr /\
  final_registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 /\
  kernel_save_after_mrs_execution arch registers state before final_registers acquired after /\
  sem_pend_resume_entry sg acquired eid original.(os_sched_call_stack).(stackLeaseSlot) node /\
  task_stack_live_coverage acquired.(TskState) (Some (task_stack_key incoming)) /\
  (critical_region_masked platform critical sg original.(os_sched_call_invocation)
     original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
   os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
   sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) **
   tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
     TCBStat (Some (encode_task_status node.(stat))) **
   tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
     TCBStatPend (Some (encode_pend_status node.(statPend))) **
   tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
     TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
   sem_pend_cleanup_frame sg acquired original.(os_sched_call_stack).(stackLeaseSlot) node **
   armv7a_task_call_stacks abi acquired.(TskState)
     (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
     acquired.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port critical arch abi suffix sg original lr incoming selected node state
    eid registers before final_registers acquired after frame Hwait Hkey Hcpsr Hr0 Hlr Hsaved Hpre Hrun.
  assert (Hslot : incoming.(stackLeaseSlot) = original.(os_sched_call_stack).(stackLeaseSlot))
    by exact (f_equal fst Hkey).
  assert (Hopen : os_sched_source_selected_post external platform port abi sg
      (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
      incoming selected node state ** frame |--
    coq_prop (sem_pend_resume_entry sg state eid original.(os_sched_call_stack).(stackLeaseSlot) node /\
      selected.(armv7a_continuation_lr) = lr /\
      task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) &&
    (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call selected original)
       (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
     (UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState)
       (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
       state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold os_sched_source_selected_post; Intros.
    assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState)
      incoming.(stackLeaseSlot) node) by tauto.
    assert (Hfocused : armv7a_continuation_focus_binding
      (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr) selected).
    { assert (Hfocus_key : task_stack_key incoming = armv7a_call_focus_key
        (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)) by exact Hkey; tauto. }
    destruct Hfocused as [Hcall [Hpc Hreturn_lr]].
    cbn [armv7a_call_focus armv7a_focus_call] in Hcall.
    destruct Hready as [Hnode [Hcurrent [Hpriority [Hmember Heffective]]]].
    destruct (sem_pend_wait_ready_resume_registration eid
      original.(os_sched_call_stack).(stackLeaseGeneration) node Hwait Heffective)
      as [Hregistration Hgeneration].
    unfold armv7a_task_restored_execution; rewrite Hcall, Hcpsr.
    unfold UCOS2_inv; Intros.
    assert (Hvalid : UCOS2_state_inv sg state) by assumption.
    assert (Hresume : sem_pend_resume_entry sg state eid
      original.(os_sched_call_stack).(stackLeaseSlot) node).
    { unfold sem_pend_resume_entry; rewrite <- Hslot.
      exact (conj Hvalid (conj Hcurrent (conj Hnode (conj Hregistration Hmember)))). }
    entailer!. }
  destruct (Hopen before Hpre) as [[Hresume [Hreturn_lr Hcoverage]] Howned].
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg
    (armv7a_continuation_resumed_call selected original) registers state before
    final_registers acquired after _ Hsaved Howned Hrun)
    as [Hstate [Hmemory [Hreturn [Hvalue Hpost]]]].
  subst acquired; split; [reflexivity|]. split; [rewrite Hreturn, Hlr, Hreturn_lr; reflexivity|].
  split; [rewrite Hvalue; exact Hr0|]. split.
  - exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hrun).
  - split; [exact Hresume|]. split; [exact Hcoverage|].
    match type of Hpost with ?P after => assert (Hclose : P |--
      critical_region_masked platform critical sg original.(os_sched_call_invocation)
        original.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
      os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) **
      tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
        TCBStat (Some (encode_task_status node.(stat))) **
      tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
        TCBStatPend (Some (encode_pend_status node.(statPend))) **
      tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
        TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
      sem_pend_cleanup_frame sg state original.(os_sched_call_stack).(stackLeaseSlot) node **
      armv7a_task_call_stacks abi state.(TskState)
        (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
        state.(TskState).(parkedTaskStacks) ** frame) end.
    { destruct Hresume as [Hvalid [Hcurrent [Hnode _]]].
      sep_apply_l_atomic (sem_pend_cleanup_split sg state
        original.(os_sched_call_stack).(stackLeaseSlot) node Hvalid Hcurrent Hnode).
      cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
    exact (Hclose after Hpost).
Qed.

(** The actual ordinary scheduler return to a first-Save continuation.
    The installed TCB-SP and the same sixteen-word frame identify the
    original CPSR/registers. This removes a separate, unproved register
    preservation premise at the Sem consumer. The preceding registered
    client trace must still supply the current pointer, invocation and
    no-wait fields; readiness comes from this real scheduler selection.
    No claim is made that every selected destination returns this call. *)
Lemma sem_pend_sched_restore_first_save : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg context outgoing hooked original suspended (frame : Assertion) heap,
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  suspended.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
  interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (nth 0 suspended.(armv7a_continuation_registers) 0) ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) hooked ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack)
    suspended.(armv7a_continuation_fragments) ->
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
   (armv7a_task_switch_control task_abi context ** frame)) heap ->
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored registers final_registers acquired after,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      armv7a_save_suffix_transition suffix registers current restored final_registers acquired after ->
      acquired = current /\
      final_registers.(kernel_save_return_word) = Some suspended.(armv7a_continuation_lr) /\
      final_registers.(kernel_save_r0) = nth 0 suspended.(armv7a_continuation_registers) 0 /\
      kernel_save_after_mrs_execution arch registers current restored final_registers acquired after /\
      sem_pend_task_call_stage sg original acquired /\
      task_stack_live_coverage acquired.(TskState) (Some (task_stack_key original.(os_sched_call_stack))) /\
      (critical_region_masked platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
       os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
       UCOS2_inv sg acquired ** armv7a_task_call_stacks abi acquired.(TskState)
         focus acquired.(TskState).(parkedTaskStacks) ** frame) after).
Proof.
  intros external platform port critical arch abi task_abi suffix sg context outgoing hooked original
    suspended frame heap focus Hbinding Hcall Hslice Hpc Hsaved Horigin Hactive Hfields Hstack
    Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre current.
  destruct (task_create_sched_restore_pending_call external platform port abi task_abi sg context
    outgoing hooked original suspended frame heap Hbinding Hcall Hslice Hstack Hdestination Hhigh
    Hnonempty Hpointer Haddress Hcoverage Hpre)
    as [installed [selected [node [Hinstall [Hreads [Hfocus [Hlease [Hsp [Hcpsr [Hregisters
      [Hcovered Hrestore]]]]]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored registers final_registers acquired after Hrun Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsuffix.
  destruct (Hrestore restored Hrun) as [Hmemory [Hsource [Hselected Howned]]].
  assert (Hcurrent_active : task_invocation_active current.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) by exact Hactive.
  assert (Hcurrent_fields : sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot)
    current) by exact Hfields.
  assert (Hsaved_current : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    registers.(kernel_save_r0)).
  { rewrite Hcursor_cpsr, Hcursor_r0, Hcpsr, Hregisters; exact Hsaved. }
  rewrite Hpc in Hselected.
  destruct (sem_pend_selected_source_save_return external platform port critical arch abi suffix sg
    original suspended.(armv7a_continuation_lr) original.(os_sched_call_stack) selected node current
    registers restored final_registers acquired after frame Horigin Hcurrent_active Hcurrent_fields
    eq_refl Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsaved_current Hselected Hsuffix)
    as [Hstate [Hselected_pc [Hreturn [Hvalue [Hsource_return [Hstage [Hcovered_return Hpost]]]]]]].
  split; [exact Hstate|]. split; [exact Hreturn|].
  split; [rewrite Hvalue, Hregisters; reflexivity|].
  split; [exact Hsource_return|]. split.
  - unfold sem_pend_task_call_stage, kernel_call_task_source in Hstage |- *.
    cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin
      os_sched_call_stack] in Hstage.
    rewrite Hlease in Hstage; exact Hstage.
  - split.
    + change (task_stack_live_coverage acquired.(TskState)
        (Some (task_stack_key selected.(armv7a_continuation_stack)))) in Hcovered_return.
      rewrite Hlease in Hcovered_return; exact Hcovered_return.
    + unfold focus; rewrite Hpc; exact Hpost.
Qed.
