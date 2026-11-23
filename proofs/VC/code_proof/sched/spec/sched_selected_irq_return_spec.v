Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_pending_irq_switch_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Execute the final OSIntExit selection/install and original-call restore
    after an actual registry has returned its current world. Extra resources
    are indexed by that world; the caller proves their transport through THIS
    selector/cache/take tail only. Nothing is framed across foreign execution.
    This is the observed return branch, with the existing platform and hook
    contracts; no eventual return or arbitrary-handler law is introduced. *)
Lemma sched_selected_irq_return_resources : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (extra : StableGlobVars -> UCOS2_Verify_State -> Assertion)
  sg state handler original suspended saved acquired before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  let checkpoint := os_int_exit_ready_checkpoint true state in
  let cached := replace_SchedS (sched_install_selected checkpoint.(SchedState)) checkpoint in
  let current := os_int_exit_wrapper_restored_state cached original.(os_sched_call_stack) in
  (extra sg state |-- extra sg current) ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  state.(SchedState).(isRunning) = true ->
  os_int_exit_requests_switch true state = true ->
  state.(SchedState).(readyList) <> [] ->
  checkpoint.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg checkpoint checkpoint ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_client_call_stack_world abi sg focus payload state **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) acquired **
     (extra sg state ** frame)))) before ->
  exists prepared installed selected,
    os_int_exit_source_switch_prefix_execution sg before prepared /\
    kernel_heap_execution [] prepared prepared /\
    kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg checkpoint checkpoint /\
    sched_install_heap_fragment sg prepared installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original /\
    task_invocation_active checkpoint.(TskState) original.(os_sched_call_invocation)
      original.(os_sched_call_origin) /\
    (exists node, current.(TskState).(inUsedTaskStates)
       original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
       is_effectively_ready node.(stat) node.(dly) = true) /\
    (forall irq_return cursor written middle final_cursor after,
      armv7a_restore_transition abi handler selected installed irq_return ->
      cursor.(kernel_restore_r0) = saved ->
      cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
      armv7a_restore_prefix_transition restore cursor irq_return written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor irq_return final_cursor after /\
      kernel_call_task_source (armv7a_continuation_resumed_call selected original) current /\
      (kernel_stack_call_closed abi
         (fun sg state => kernel_program_inv sg state ** extra sg state)
         sg (task_stack_call_active_key original)
         (armv7a_continuation_resumed_call selected original)
         (armv7a_irq_fiq_mask saved) current **
       (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) after).

Proof.
  intros environment critical arch restore extra sg state handler original suspended saved acquired
    before frame abi focus payload checkpoint cached current Htransport Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hrunning Hswitch Hnonempty Hhigh Hhook Haddress Hpre.
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  destruct Hpointer as [node [Hnode [Hgen Hsp]]].
  rewrite Hlease in Hnode, Hgen.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (kernel_client_call_stack_facts focus payload state) &&
    (UCOS2_inv sg state ** unmap_table_rep sg **
     (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running environment.(task_stack_call_platform)
         handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources environment.(task_stack_call_port) handler **
       (interrupt_platform_saved environment.(task_stack_call_platform)
          (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
        critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** (extra sg state ** frame)))))) end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [Hfacts Howned].
  destruct (os_int_exit_source_switch_prefix_frame_post sg state _ before Hrunning Hswitch Hnonempty Howned)
    as [prepared [Hprefix [Hconsistent Hprepared]]].
  fold checkpoint in Hprepared, Hconsistent.
  assert (Hvalid : UCOS2_state_inv sg checkpoint).
  { match type of Hprepared with ?P prepared => assert (Hexpose : P |--
      coq_prop (UCOS2_state_inv sg checkpoint) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose prepared Hprepared)). }
  assert (Hready : is_effectively_ready node.(stat) node.(dly) = true).
  { pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hmembers.
    pose proof Hconsistent as Hselected.
    unfold sched_high_ready_consistency in Hselected.
    destruct checkpoint.(SchedState).(readyList) as [|slot tail] eqn:Hlist.
    - destruct Hselected as [Hnone _]; congruence.
    - destruct Hselected as [Hslot [head [Hhead Hpriority]]].
      assert (slot = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst slot.
      destruct (Hmembers _ (or_introl eq_refl)) as [found [Hfound [_ Hready]]].
      change (state.(TskState).(inUsedTaskStates)
        original.(os_sched_call_stack).(stackLeaseSlot) = Some found) in Hfound.
      assert (found = node) by congruence; subst found; exact Hready. }
  assert (Hindex : forall p, checkpoint.(SchedState).(highRdyPrio) = Some p -> task_priority_in_range sg p).
  { intros p Hp.
    unfold sched_high_ready_consistency in Hconsistent.
    destruct checkpoint.(SchedState).(readyList) as [|slot tail] eqn:Hlist.
    - destruct Hconsistent as [Hnone _]; congruence.
    - destruct Hconsistent as [Hslot [selected_node [Hselected_node Hpriority]]].
      assert (slot = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst slot.
      assert (selected_node = node) by
        (change (state.(TskState).(inUsedTaskStates)
          original.(os_sched_call_stack).(stackLeaseSlot) = Some selected_node) in Hselected_node; congruence).
      subst selected_node; assert (p = node.(curPrio)) by congruence; subst p.
      pose proof (proj1 (proj2 Hvalid)) as Htasks.
      assert (Hrange : forall tid t, checkpoint.(TskState).(inUsedTaskStates) tid = Some t ->
        task_priority_in_range sg t.(curPrio)) by (unfold task_in_range in Htasks; tauto).
      apply (Hrange _ _ Hnode). }
  match type of Hprepared with ?P prepared => assert (Hraw : P |--
    UCOS2_raw_rep sg checkpoint **
    (unmap_table_rep sg ** armv7a_task_call_stacks abi checkpoint.(TskState) focus
       checkpoint.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(task_stack_call_platform)
        handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources environment.(task_stack_call_port) handler **
      (interrupt_platform_saved environment.(task_stack_call_platform)
         (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
       critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** (extra sg state ** frame))))) end.
  { unfold UCOS2_inv; entailer!. }
  destruct (sched_install_heap_raw_frame_post sg checkpoint original.(os_sched_call_stack).(stackLeaseSlot)
    node _ prepared Hhigh Hnode Haddress (Hraw prepared Hprepared)) as [installed [Hinstall Hinstalled]].
  assert (Hcached_valid : UCOS2_state_inv sg cached)
    by (apply os_int_exit_install_cache_preserves_validity; assumption).
  match type of Hinstalled with ?P installed => assert (Hclose : P |--
    kernel_client_call_stack_world abi sg focus payload cached **
    (interrupt_platform_running environment.(task_stack_call_platform)
       handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources environment.(task_stack_call_port) handler **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired ** (extra sg state ** frame)))) end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap.
    unfold UCOS2_inv; entailer!. }
  assert (Hcached_pointer : task_saved_pointer_at cached suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { exists node; rewrite Hlease; auto. }
  destruct (task_create_pending_call_stack_restore _ _ _ abi sg original suspended Hbinding Hcall Hslice
    cached installed handler _ Hcached_pointer Hhigh Haddress (Hclose installed Hinstalled))
    as [selected [Hpointers [Hfocused [Hselected_lease [Hselected_sp [Hcpsr [Hregisters [Hcoverage Hresume]]]]]]]].
  assert (Hsame : kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original).
  { unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  assert (Hordinary : kernel_call_task_source (armv7a_continuation_resumed_call selected original) current).
  { unfold kernel_call_task_source, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin os_sched_call_stack os_sched_call_invocation].
    split; [rewrite Hselected_lease; exact Horigin|]. split; [exact Hactive|].
    unfold task_execution_current; rewrite Horigin; exact Hhigh. }
  exists prepared, installed, selected; split; [exact Hprefix|].
  split; [split; [constructor|auto]|].
  split; [exact Hhook|].
  split; [rewrite Hselected_sp, <- Hsp; exact Hinstall|].
  split; [exact Hcpsr|]. split; [exact Hregisters|]. split; [exact Hsame|]. split; [exact Hactive|].
  split; [exists node; split; assumption|].
  intros irq_return cursor written middle final_cursor after Hirq Hr0 Hcursor Hrestore Hsuffix.
  destruct (Hresume irq_return Hirq) as [Hmemory Hrestored].
  rewrite Hmask in Hrestored.
  set (returned := armv7a_continuation_resumed_call selected original) in *.
  assert (Hcursor_mask : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    by (rewrite Hcursor, Hcpsr; exact Hmask).
  match type of Hrestored with ?P irq_return => assert (Hmasked : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) returned **
    (kernel_stack_inv abi (fun sg state => kernel_program_inv sg state ** extra sg state)
       sg (task_stack_call_active_key returned) current **
     (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame))) end.
  { unfold kernel_call_execution_owned, critical_region_masked, kernel_stack_inv.
    rewrite kernel_program_inv_split_unmap.
    unfold task_stack_call_active_key, returned, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin os_sched_call_invocation]; rewrite Horigin.
    sep_apply_l_atomic Htransport; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg returned saved
    acquired cursor irq_return written middle final_cursor after _ Hr0 Hcursor_mask
    (Hmasked irq_return Hrestored) Hrestore Hsuffix) as [Hexecution [Hlr [Hafter_memory Hafter]]].
  split; [exact Hexecution|]. split; [exact Hordinary|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hpost : P |-- Q) end end.
  { unfold kernel_stack_call_closed.
    assert (Hkey : task_stack_call_active_key original = task_stack_call_active_key returned)
      by (unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity).
    rewrite Hkey; entailer!. }
  exact (Hpost after Hafter).
Qed.
