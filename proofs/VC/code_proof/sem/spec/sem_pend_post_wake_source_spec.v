Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_wait_return_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This finite ordinary-task branch starts at the REAL EventTaskRdy
    return inside SemPost. The waiting invocation can be a different
    waiter from the one this Post wakes. Its focused map, SP and active
    registration pass through the same wake mutation, not a separate
    abstract trace. Restore/Save below are actual uninterrupted events;
    the switch guard is tested in the actual woken state. *)
Lemma sem_pend_post_wake_sched_prefix : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg entry eid event tid old priority call saved original suspended waiting waiting_event
  before (frame : Assertion) cursor written middle final_cursor released
  registers final_registers acquired saved_heap,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  let selected := os_sched_prefix_state checkpoint in
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation waiting_event original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at entry original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  os_sched_requests_switch checkpoint = true -> checkpoint.(SchedState).(readyList) <> [] ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   os_sched_context_resources environment.(task_stack_call_external) call **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) before ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor released ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint released
    final_registers acquired saved_heap ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  kernel_call_save_uninterrupted_execution arch registers checkpoint released final_registers acquired saved_heap /\
  acquired = checkpoint /\
  exists prefix_heap current,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    sched_high_ready_consistency selected.(TskState) selected.(SchedState) /\
    selected.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
    sem_pend_wait_continuation waiting_event original.(os_sched_call_stack).(stackLeaseGeneration) current /\
    task_invocation_active selected.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
    task_saved_pointer_at selected original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) /\
    selected.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
      Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) /\
    (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
       environment.(task_stack_call_port) abi sg call focus selected ** unmap_table_rep sg **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) checkpoint ** frame)) prefix_heap.
Proof.
  intros environment critical arch restore save sg entry eid event tid old priority call saved original
    suspended waiting waiting_event before frame cursor written middle final_cursor released registers
    final_registers acquired saved_heap abi focus checkpoint selected Hvalid Hlookup Htype Hentry Hcoverage
    Hwaiting Hwait Hactive Hpointer Hparked Hswitch Hnonempty Hpre Hr0 Hmask Hprefix Hsuffix
    Hreturn Hcpsr Hnextmask Hsave.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hkind : event_type_to_pend_type event.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg entry eid event tid tail PendSem 0 PendOK Hvalid Hlookup Hkind Hlist)
    as [found [Hfound [Hstep Hrest]]].
  assert (found = old) by congruence; subst found.
  match type of Hpre with ?P before => assert (Hmerge : P |--
    EX current, coq_prop (
      task_stack_live_coverage checkpoint.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
      checkpoint.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
      sem_pend_wait_continuation waiting_event original.(os_sched_call_stack).(stackLeaseGeneration) current) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
     os_sched_context_resources environment.(task_stack_call_external) call **
     (kernel_program_inv sg checkpoint ** armv7a_task_call_stacks abi checkpoint.(TskState) focus
        checkpoint.(TskState).(parkedTaskStacks) ** frame))) end.
  { sep_apply_l_atomic (sem_post_wake_preserves_pending_call _ _ _ abi sg entry eid event tid old priority
      focus (Some (task_stack_key call.(os_sched_call_stack))) original.(os_sched_call_stack).(stackLeaseSlot)
      waiting waiting_event original.(os_sched_call_stack).(stackLeaseGeneration)
      Hvalid Hlookup Htype Hentry Hcoverage Hwaiting Hwait); Intros after current.
    assert (Heq : after = checkpoint).
    { assert (Hresult : sem_post_wake_result sg eid entry after priority) by tauto.
      unfold sem_post_wake_result in Hresult; rewrite Hstep in Hresult; unfold checkpoint; congruence. }
    subst after; Exists current; entailer!. }
  destruct (Hmerge before Hpre) as [current [[Hcovered [Hcurrent Hcontinuation]] Howned]].
  assert (Hactive_after : task_invocation_active checkpoint.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive]. }
  assert (Hpointer_after : task_saved_pointer_at checkpoint original.(os_sched_call_stack)
    suspended.(armv7a_continuation_sp)).
  { destruct Hpointer as [previous [Hprevious [Hg Hsp]]].
    unfold task_saved_pointer_at; change (exists node,
      (if Z.eqb original.(os_sched_call_stack).(stackLeaseSlot) tid then Some (task_event_wake_single old PendSem 0 PendOK)
       else entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot)) = Some node /\
      node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
      node.(tcbStkPtr) = suspended.(armv7a_continuation_sp)).
    destruct (Z.eqb original.(os_sched_call_stack).(stackLeaseSlot) tid) eqn:Heq.
    - apply Z.eqb_eq in Heq; rewrite Heq in Hprevious; assert (previous = old) by congruence; subst previous.
      exists (task_event_wake_single old PendSem 0 PendOK); auto.
    - exists previous; auto. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call saved entry
    cursor before written middle final_cursor released _ Hr0 Hmask Howned Hprefix Hsuffix)
    as [Hrestore [Hlr [Hmemory Hreleased]]].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  rewrite <- Hnextmask in Hreleased.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) checkpoint released final_registers acquired saved_heap _
    Hsaved Hreleased Hsave) as [Hstate [Hmemory_after [Hreturned [Hvalue Hsaved_owned]]]].
  split; [exact Hrestore|]. split.
  - unfold kernel_call_save_uninterrupted_execution; econstructor.
    + constructor; [exact Hreturn|reflexivity].
    + exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - split; [exact Hstate|]. subst acquired.
    match type of Hsaved_owned with ?P saved_heap => assert (Hswitch_input : P |--
      os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
        environment.(task_stack_call_port) abi sg call focus checkpoint ** unmap_table_rep sg **
      (interrupt_platform_saved environment.(task_stack_call_platform)
         (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
       critical_region_inside critical sg call.(os_sched_call_invocation) checkpoint ** frame)) end.
    { unfold os_sched_source_switch_pre, critical_region_masked, kernel_call_execution_owned.
      rewrite kernel_program_inv_split_unmap; entailer!. }
    destruct (os_sched_source_switch_prefix_resources _ _ _ abi sg checkpoint call focus _ saved_heap
      Hswitch Hnonempty (Hswitch_input saved_heap Hsaved_owned)) as [prefix_heap [Hrun [Hhigh Hafter]]].
    exists prefix_heap, current; split; [exact Hrun|]. split; [exact Hhigh|].
    split; [exact Hcurrent|]. split; [exact Hcontinuation|]. split; [exact Hactive_after|].
    split; [exact Hpointer_after|]. split; [exact Hparked|exact Hafter].
Qed.

(** The high-ready cache has already been produced by OS_SchedNew. A
    matching owned pending entry supplies the actual architecture restore
    source. In particular the caller does not supply destination_binding
    or fabricate the dormant CPU resource from its descriptor. *)
Lemma sem_pend_selected_pending_destination : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg context outgoing state original suspended node,
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  UCOS2_state_inv sg state ->
  state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  sched_high_ready_consistency state.(TskState) state.(SchedState) -> state.(SchedState).(readyList) <> [] ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) |--
  coq_prop (os_sched_destination_binding external context outgoing state original.(os_sched_call_stack)
    suspended.(armv7a_continuation_fragments)) && TT.
Proof.
  intros external platform port abi task_abi sg context outgoing state original suspended node focus
    Hvalid Hselected Hhigh Hnonempty Hnode Hgen Hnone Hparked.
  assert (Hother : task_stack_key original.(os_sched_call_stack) <> task_stack_key context.(os_sched_call_stack))
    by (intro Heq; rewrite Heq, Hnone in Hparked; discriminate).
  assert (Hlookup : (task_stack_park_fragments state.(TskState).(parkedTaskStacks)
    context.(os_sched_call_stack) outgoing) (task_stack_key original.(os_sched_call_stack)) =
      Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { rewrite task_stack_park_fragments_lookup_other by exact Hother; exact Hparked. }
  assert (Hpriority : state.(SchedState).(highRdyPrio) = Some node.(curPrio)).
  { destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    unfold sched_high_ready_consistency in Hhigh; rewrite Hlist in Hhigh.
    destruct Hhigh as [Hhead [found [Hfound Hprio]]].
    assert (head = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst head.
    assert (found = node) by congruence; subst found; exact Hprio. }
  assert (Hlive : task_stack_live_binding state.(TskState) original.(os_sched_call_stack)).
  { assert (Hconsistent : parked_stacks_consistent state.(TskState) state.(TskState).(parkedTaskStacks))
      by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
    destruct (Hconsistent _ _ _ _ Hparked) as [Hr [Hf [Hp Hmatch]]].
    exists node; split; [exact Hnode|apply Hmatch; assumption]. }
  unfold armv7a_task_call_stacks.
  sep_apply_l_atomic (store_parked_continuations_take (armv7a_task_call_stack_entry abi state.(TskState) focus)
    state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack)
    suspended.(armv7a_continuation_fragments) Hparked).
  unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec as [Heq|Hneq]; [|contradiction].
  Intros stored.
  assert (Hkey : task_stack_key stored.(armv7a_continuation_stack) = task_stack_key original.(os_sched_call_stack)) by tauto.
  assert (Hpayload : (stored.(armv7a_continuation_stack).(stackLeaseRegion), stored.(armv7a_continuation_fragments)) =
    (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))) by tauto.
  assert (Hlease : stored.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { unfold task_stack_key in Hkey; destruct stored.(armv7a_continuation_stack), original.(os_sched_call_stack);
      cbn in *; congruence. }
  assert (Hfragments : stored.(armv7a_continuation_fragments) = suspended.(armv7a_continuation_fragments)) by congruence.
  assert (Hsp : node.(tcbStkPtr) = stored.(armv7a_continuation_sp)).
  { assert (Hpointer : task_stack_live_sp state.(TskState) (task_stack_key original.(os_sched_call_stack))
      stored.(armv7a_continuation_sp)) by tauto; apply Hpointer; assumption. }
  sep_apply_l_atomic (armv7a_task_dormant_restore_source _ _ _ abi task_abi stored); Intros.
  assert (Hsource : external.(os_sched_arch_restore_source) original.(os_sched_call_stack)
    node.(tcbStkPtr) suspended.(armv7a_continuation_fragments)).
  { rewrite Hsp, <- Hlease, <- Hfragments; assumption. }
  assert (Hdestination : os_sched_destination_binding external context outgoing state original.(os_sched_call_stack)
    suspended.(armv7a_continuation_fragments)).
  { unfold os_sched_destination_binding; split; [exact Hselected|].
    split; [exists node; tauto|]. split; assumption. }
  entailer!; intros ? ?; exact I.
Qed.

(** One actual foreign save/capture/hook/install followed by the original
    SemPend continuation. The post includes linear runtime resources and
    the all-arms cleanup consumer; it is not merely a trace-shaped tag.
    The original active registration is separately retained as a source
    fact, rather than inferred from the focused dormant owner. *)
Definition sem_pend_live_switch_stack_return environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state context old_sp cpsr registers lr fragments original original_saved eid waiting perr before
  (frame : Assertion) : Prop :=
  let saved := armv7a_task_save_image context old_sp cpsr registers lr fragments in
  let hooked := os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments original.(os_sched_call_stack) hooked in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured heap,
      armv7a_task_capture_transition task_abi context saved stored captured ->
      kernel_heap_execution [] captured heap ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg hooked hooked ->
      task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
      exists installed selected,
        sched_install_heap_fragment sg heap installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored cursor restore_written middle final_cursor returned_heap next_registers final_registers acquired after,
          armv7a_task_restore_transition task_abi context selected installed restored ->
          cursor.(kernel_restore_r0) = original_saved ->
          cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
          next_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr next_registers.(kernel_save_cpsr) ->
          armv7a_irq_fiq_mask next_registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask original_saved ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor returned_heap ->
          armv7a_save_suffix_transition save (kernel_save_read_cpsr next_registers) current returned_heap
            final_registers acquired after ->
          os_sched_source_switch_execution environment.(task_stack_call_external) environment.(task_stack_call_platform)
            environment.(task_stack_call_port) environment.(task_stack_call_continuations) task_abi sg state
            context old_sp cpsr registers lr saved original.(os_sched_call_stack) selected before restored /\
          kernel_call_task_source (armv7a_continuation_resumed_call selected original) current /\
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor returned_heap /\
          kernel_call_save_uninterrupted_execution arch next_registers current returned_heap final_registers acquired after /\
          acquired = current /\
          kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original /\
          final_registers.(kernel_save_r0) = next_registers.(kernel_save_cpsr) /\
          (sem_pend_resume_stack_resources environment critical sg (armv7a_continuation_resumed_call selected original)
             final_registers.(kernel_save_r0) acquired eid original.(os_sched_call_stack).(stackLeaseSlot) waiting **
           (perr # UChar |->_ ** frame)) after /\
          sem_pend_resume_stack_return environment critical arch restore sg (armv7a_continuation_resumed_call selected original)
            final_registers.(kernel_save_r0) acquired eid original.(os_sched_call_stack).(stackLeaseSlot) waiting perr after frame)).

Lemma sem_pend_live_switch_pending_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state node context old_sp cpsr registers lr prefix suffix first old_words publication
  original suspended original_saved entry eid waiting perr before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  os_sched_source_live_save_input sg state node context old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  event_object_layout_prop sg eid ->
  (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg context focus state **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) entry ** unmap_table_rep sg **
    (perr # UChar |->_ ** frame))) before ->
  sem_pend_live_switch_stack_return environment critical arch task_abi restore save sg state context old_sp cpsr
    registers lr fragments original original_saved eid waiting perr before frame.
Proof.
  intros environment critical arch task_abi restore save sg state node context old_sp cpsr registers lr
    prefix suffix first old_words publication original suspended original_saved entry eid waiting perr before
    frame abi focus fragments Hinput Horigin Hbinding Hcall Hslice Hmask Hwaiting Hwait Hactive Hpointer
    Hparked Hselected Hlayout Hpre.
  destruct Hinput as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments [Hregion
    [Hgeometry [Hsp_range [Hhistory [Hlength [Hcpsr [Hlr [Hranges [Hsave_mask [Hsp32 [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  assert (Hwaiting_gen : waiting.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration)).
  { destruct Hpointer as [found [Hfound [Hg Hp]]]; assert (found = waiting) by congruence; congruence. }
  assert (Hother : original.(os_sched_call_stack).(stackLeaseSlot) <> context.(os_sched_call_stack).(stackLeaseSlot)).
  { intro Heq; rewrite Heq in Hwaiting; assert (waiting = node) by congruence; subst waiting.
    assert (Hkey : task_stack_key original.(os_sched_call_stack) = task_stack_key context.(os_sched_call_stack))
      by (unfold task_stack_key; congruence).
    rewrite Hkey, Hnone in Hparked; discriminate. }
  assert (Horiginal_lease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (task_stack_live_coverage state.(TskState) (Some (task_stack_key context.(os_sched_call_stack)))) &&
    (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform) context 192 **
     UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) entry ** unmap_table_rep sg **
      (perr # UChar |->_ ** frame)))) end.
  { unfold os_sched_source_switch_pre; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (armv7a_task_save_global_call _ _ _ abi task_abi sg state node context old_sp cpsr registers lr
    prefix suffix first old_words focus _ before Hcurrent Hnode Hid Hgen Hnone Hcoverage Hfocus Hfragments
    Hlength Hcpsr Hlr Hranges Hsave_mask Hsp32 Hsp (Haddress _) Howned)
    as [written [stored [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]].
  set (saved := armv7a_task_save_image context old_sp cpsr registers lr fragments) in *.
  set (hooked := os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp)) in *.
  fold fragments saved hooked in Hstore, Hcovered, Hcapture.
  assert (Hwaiting_after : hooked.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting).
  { unfold hooked, os_sched_save_current_sp; rewrite Hnode; cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq _ _) Hother); exact Hwaiting. }
  assert (Hpointer_after : task_saved_pointer_at hooked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)).
  { rewrite Horiginal_lease; destruct Hpointer as [found [Hfound [Hg Hp]]].
    assert (found = waiting) by congruence; subst found; exists waiting; auto. }
  assert (Hactive_after : task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { unfold hooked, os_sched_save_current_sp; rewrite Hnode.
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive]. }
  assert (Hparked_after : hooked.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { unfold hooked, os_sched_save_current_sp; rewrite Hnode; exact Hparked. }
  assert (Hselected_after : hooked.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold hooked, os_sched_save_current_sp; rewrite Hnode; exact Hselected. }
  assert (Hhigh_after : sched_high_ready_consistency hooked.(TskState) hooked.(SchedState)).
  { unfold sched_high_ready_consistency in *.
    destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    destruct Hhigh as [Hhead [found [Hfound Hprio]]].
    assert (head = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst head.
    assert (found = waiting) by congruence; subst found.
    unfold hooked, os_sched_save_current_sp; rewrite Hnode; cbn [replace_TskS SchedState TskState]; rewrite Hlist.
    split; [exact Hhead|]. exists waiting; split; [|exact Hprio].
    unfold hooked, os_sched_save_current_sp in Hwaiting_after; rewrite Hnode in Hwaiting_after; exact Hwaiting_after. }
  assert (Hsaved : os_sched_saved_stack_binding context fragments hooked).
  { apply task_create_saved_context_binding with (node := node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hnonempty_after : hooked.(SchedState).(readyList) <> []).
  { unfold hooked, os_sched_save_current_sp; rewrite Hnode; exact Hnonempty. }
  unfold sem_pend_live_switch_stack_return; fold saved hooked.
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured heap Hcaptured Hhook_heap Hhook_step.
  assert (Hunchanged : heap = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|]. split; [constructor|]; split; reflexivity. }
  subst heap; destruct (Hcapture captured Hcaptured) as [Hmemory [Hsource Hcaptured_owned]].
  assert (Hdestination : os_sched_destination_binding environment.(task_stack_call_external) context fragments hooked
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments)).
  { match type of Hcaptured_owned with ?P captured => assert (Hobserve : P |-- coq_prop
      (os_sched_destination_binding environment.(task_stack_call_external) context fragments hooked
        original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments)) && TT) end.
    { unfold UCOS2_inv; Intros.
      pose proof (sem_pend_selected_pending_destination _ _ _ abi task_abi sg context fragments hooked
        original suspended waiting ltac:(assumption) Hselected_after Hhigh_after Hnonempty_after Hwaiting_after Hwaiting_gen
        (proj2 (proj2 (proj2 (proj2 Hsaved)))) Hparked_after) as Hdestination_from_entry.
      fold focus in Hdestination_from_entry.
      sep_apply_l_atomic Hdestination_from_entry; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve captured Hcaptured_owned)). }
  match type of Hcaptured_owned with ?P captured => assert (Horder : P |--
    UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) fragments **
    armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) entry ** unmap_table_rep sg **
      (perr # UChar |->_ ** frame)))) by entailer! end.
  destruct (sem_pend_sched_pending_resume_source environment critical arch task_abi restore save sg context fragments
    hooked original suspended original_saved entry eid waiting perr captured frame Horigin Hbinding Hcall Hslice Hmask
    Hwaiting_after Hwait Hlayout Hsaved Hdestination Hhigh_after Hnonempty_after Hpointer_after (Haddress _) Hcovered
    (Horder captured Hcaptured_owned)) as [installed [selected [Hinstall [Hreads Hreturn]]]].
  split; [exact Hactive_after|]. exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored cursor restore_written middle final_cursor returned_heap next_registers final_registers acquired after
    Hrestore Hr0 Hcursor Hreg Hvalid Hnextmask Hprefix_run Hsuffix_run Hsave.
  destruct (Hreturn restored cursor restore_written middle final_cursor returned_heap next_registers final_registers acquired after
    Hrestore Hr0 Hcursor Hreg Hvalid Hnextmask Hprefix_run Hsuffix_run Hsave)
    as [Hrestore_run [Hsave_run [Hacquired [Hvalue [Hword [Hresources [Hcleanup Hsame]]]]]]].
  split.
  - exists written, stored, captured, captured, installed; tauto.
  - split.
    + pose proof Hsame as [Hinvocation [Hsameorigin Hstack]].
      unfold kernel_call_task_source; rewrite Hinvocation, Hsameorigin, Hstack.
      split; [exact Horigin|]. split; [exact Hactive_after|].
      unfold task_execution_current; rewrite Horigin; exact Hselected_after.
    + split; [exact Hrestore_run|]. split; [exact Hsave_run|]. split; [exact Hacquired|].
      split; [exact Hsame|]. split; [exact Hvalue|]. split; [exact Hresources|exact Hcleanup].
Qed.

(** The actual Post-woken waiter is the scheduler's actual ready head.
    Consume EventTaskRdy's established post, then SemPost's Restore, the
    following scheduler Save/C prefix, the foreign task's literal stack
    save, and the already checked original-call/second-Save/cleanup tail.

    [live_save_input] describes this one outgoing physical stack frame,
    not every endpoint of an opaque future Save. The no-write hook and
    uninterrupted CPU suffixes remain explicit finite-source branches.
    The posting call is suspended: its saved mask/inside handle are still
    owned in the final caller frame, not discarded when SemPend returns.
    This does not claim that every Post immediately selects this waiter,
    or that every possible IRQ/first switch has been accounted for. *)
Lemma sem_pend_post_wake_original_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg entry eid event tid old priority call saved original suspended waiting original_saved original_entry perr
  before (frame : Assertion) cursor written middle final_cursor released registers final_registers acquired saved_heap
  node old_sp cpsr task_registers lr prefix suffix first old_words publication,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  let selected := os_sched_prefix_state checkpoint in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: task_registers ++ [lr; lr]))] ++ suffix in
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at entry original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tid = original.(os_sched_call_stack).(stackLeaseSlot) ->
  os_sched_requests_switch checkpoint = true ->
  hd_error checkpoint.(SchedState).(readyList) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  os_sched_source_live_save_input sg selected node call old_sp cpsr task_registers lr
    prefix suffix first old_words focus publication ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  event_object_layout_prop sg eid ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   os_sched_context_resources environment.(task_stack_call_external) call **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry **
    (perr # UChar |->_ ** frame))) before ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor released ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint released
    final_registers acquired saved_heap ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  kernel_call_save_uninterrupted_execution arch registers checkpoint released final_registers acquired saved_heap /\
  acquired = checkpoint /\
  exists prefix_heap current,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\ current.(statPend) = PendOK /\
    sem_pend_live_switch_stack_return environment critical arch task_abi restore save sg selected call old_sp cpsr
      task_registers lr fragments original original_saved eid current perr prefix_heap
      (interrupt_platform_saved environment.(task_stack_call_platform)
         (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
       critical_region_inside critical sg call.(os_sched_call_invocation) checkpoint ** frame).
Proof.
  intros environment critical arch task_abi restore save sg entry eid event tid old priority call saved original
    suspended waiting original_saved original_entry perr before frame cursor written middle final_cursor released
    registers final_registers acquired saved_heap node old_sp cpsr task_registers lr prefix suffix first old_words
    publication abi focus checkpoint selected fragments Hvalid Hlookup Htype Hentry Hcoverage Hwaiting Hwait
    Hactive Hpointer Hparked Hwoken Hswitch Hhead Hlive Horigin Hbinding Hcall Hslice Hmask Hlayout Hpre
    Hr0 Hif Hprefix Hsuffix Hreg Hcpsr Hnextmask Hsave.
  assert (Hnonempty : checkpoint.(SchedState).(readyList) <> []) by (intro Heq; rewrite Heq in Hhead; discriminate).
  destruct (sem_pend_post_wake_sched_prefix environment critical arch restore save sg entry eid event tid old priority
    call saved original suspended waiting eid before _ cursor written middle final_cursor released registers
    final_registers acquired saved_heap Hvalid Hlookup Htype Hentry Hcoverage Hwaiting Hwait Hactive Hpointer Hparked
    Hswitch Hnonempty Hpre Hr0 Hif Hprefix Hsuffix Hreg Hcpsr Hnextmask Hsave)
    as [Hrestore_run [Hsave_run [Hacquired [prefix_heap [current [Hprefix_run [Hhigh [Hcurrent [Hcont
      [Hactive_current [Hpointer_current [Hparked_current Hresources]]]]]]]]]]]].
  assert (Hselected : selected.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
  { assert (Hreadylist : selected.(SchedState).(readyList) = checkpoint.(SchedState).(readyList))
      by exact (proj1 (os_sched_ready_checkpoint_frame checkpoint)).
    fold checkpoint selected in Hhigh; unfold sched_high_ready_consistency in Hhigh.
    rewrite Hreadylist in Hhigh.
    destruct checkpoint.(SchedState).(readyList) as [|head tail]; [contradiction|].
    cbn in Hhead; injection Hhead as Hhead; subst head; exact (proj1 Hhigh). }
  assert (Hstatus : current.(statPend) = PendOK).
  { change ((if Z.eqb original.(os_sched_call_stack).(stackLeaseSlot) tid then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot)) = Some current) in Hcurrent.
    rewrite Hwoken, Z.eqb_refl in Hcurrent; injection Hcurrent as Hcurrent; subst current; reflexivity. }
  split; [exact Hrestore_run|]. split; [exact Hsave_run|]. split; [exact Hacquired|].
  exists prefix_heap, current; split; [exact Hprefix_run|]. split; [exact Hstatus|].
  eapply sem_pend_live_switch_pending_return_source with (node := node) (old_words := old_words)
    (publication := publication) (suspended := suspended) (entry := original_entry); try eassumption.
  match type of Hresources with ?P prefix_heap => match goal with |- ?Q prefix_heap =>
    assert (Horder : P |-- Q) by entailer! end end.
  exact (Horder prefix_heap Hresources).
Qed.
