Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_saved_continuation_history_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A current-call source establishes identity and a live generation.
    Absence and conditional readiness come from the actual source cut;
    neither is inferred from the CPU owner or coverage exemption. In
    particular an ISR or scheduler-locked stage need not be ready. *)
Lemma task_create_call_stage_from_current_source : forall call state,
  kernel_call_task_source call state ->
  state.(SchedState).(isRunning) = true ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  (os_sched_selection_enabled state = true ->
    exists node,
      sched_current_ready_at state.(TskState) state.(SchedState)
        call.(os_sched_call_stack).(stackLeaseSlot) node /\
      node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration)) ->
  task_create_call_stage call state.
Proof.
  intros call state Hsource Hrunning Habsent Hready.
  pose proof (kernel_call_task_source_current_at call state Hsource) as Hcurrent.
  pose proof (proj1 Hsource) as Horigin.
  unfold task_create_call_stage; rewrite Horigin.
  split.
  - unfold task_create_call_origin; exact (conj Hrunning Hcurrent).
  - split; [reflexivity|]. split; [reflexivity|].
    exact (conj Habsent Hready).
Qed.

(** The same high-cache binding used by the actual install names a ready
    node when the current selector cache is refreshed. No nonempty-ready
    premise is added: a Some destination and the refreshed cache already
    exclude an empty list. The install copies those caches and takes the
    selected stack without changing its TCB or ready-list membership. *)
Lemma task_create_install_selected_ready :
  forall external sg context outgoing hooked incoming resumed,
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_destination_binding external context outgoing hooked incoming resumed ->
  exists node,
    sched_current_ready_at (os_sched_install_context context outgoing incoming hooked).(TskState)
      (os_sched_install_context context outgoing incoming hooked).(SchedState)
      incoming.(stackLeaseSlot) node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration).
Proof.
  intros external sg context outgoing hooked incoming resumed Hvalid Hhigh Hdestination.
  destruct Hdestination as [Hselected [[node [Hnode [Hgeneration [Hpriority Hsource]]]] Hrest]].
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hready.
  unfold sched_high_ready_consistency in Hhigh.
  destruct hooked.(SchedState).(readyList) as [|slot tail] eqn:Hlist.
  - destruct Hhigh as [Hnone Hnone_priority]; congruence.
  - destruct Hhigh as [Hhead Hhead_node].
    assert (Hslot : slot = incoming.(stackLeaseSlot)) by congruence.
    destruct (Hready incoming.(stackLeaseSlot) (or_introl Hslot))
      as [ready_node [Hready_node [Hrange Heffective]]].
    assert (ready_node = node) by congruence; subst ready_node.
    assert (Hin : In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList)).
    { rewrite Hlist; left; exact Hslot. }
    exists node; split; [|exact Hgeneration].
    unfold sched_current_ready_at.
    change (hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
      hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
      hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) /\
      is_effectively_ready node.(stat) node.(dly) = true).
    exact (conj Hnode (conj Hselected (conj Hpriority (conj Hin Heffective)))).
Qed.

(** The install's take establishes absence for this actual selected key.
    Only when the source's two scheduling guards are enabled do we use
    its refreshed high-ready cache. A locked or ISR stage therefore keeps
    the original conditional-ready protocol. OSRunning is a current
    source observation and is not supplied by the architecture ABI. *)
Lemma task_create_installed_call_stage :
  forall external sg context outgoing hooked incoming resumed returned,
  UCOS2_state_inv sg hooked ->
  hooked.(SchedState).(isRunning) = true ->
  (os_sched_selection_enabled hooked = true ->
    sched_high_ready_consistency hooked.(TskState) hooked.(SchedState)) ->
  os_sched_destination_binding external context outgoing hooked incoming resumed ->
  returned.(os_sched_call_stack) = incoming ->
  kernel_call_task_source returned (os_sched_install_context context outgoing incoming hooked) ->
  task_create_call_stage returned (os_sched_install_context context outgoing incoming hooked).
Proof.
  intros external sg context outgoing hooked incoming resumed returned
    Hvalid Hrunning Hhigh Hdestination Hstack Hsource.
  apply task_create_call_stage_from_current_source; [exact Hsource|exact Hrunning| |].
  - rewrite Hstack; apply task_stack_take_lookup.
  - intros Henabled.
    destruct (task_create_install_selected_ready external sg context outgoing hooked incoming resumed
      Hvalid (Hhigh Henabled) Hdestination) as [node [Hready Hgeneration]].
    exists node; rewrite Hstack; exact (conj Hready Hgeneration).
Qed.

(** The actual history-indexed local is transported at the selected key,
    then the existing install/TaskRestore/C-Restore source proof is used
    unchanged. Its exact returned/current resource endpoint is retained
    beside the public post. The two heap assertions are alternative views
    of the SAME owned heap, never a separating duplication of that world.

    Keeping the exact endpoint matters: an unrelated stage outside an
    existential public post would not identify that post's witnesses and
    could not feed the next sequential entry. Here the stage and closed
    world use the same returned/current pair throughout. Other entries'
    local resources are retained, including historical inactive entries.

    Scope: an actually selected saved Scheduler call, followed by its
    uninterrupted C Restore. The current running/selector observations
    and active registration must come from the completed source chain;
    this statement does not promise eventual selection or cover an
    arbitrary interrupt between the two C Restore source steps. *)
Lemma task_create_saved_continuation_return_stage_source :
  forall environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg context outgoing hooked source_tasks original saved acquired saved_local resumed before
    region args task_return lower old_frame upper (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let local := kernel_sched_saved_local_at environment.(task_stack_call_platform)
    critical sg source_tasks original saved acquired (task_create_continuation_local saved_local) in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  hooked.(SchedState).(isRunning) = true ->
  (os_sched_selection_enabled hooked = true ->
    sched_high_ready_consistency hooked.(TskState) hooked.(SchedState)) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some original /\
      kernel_call_task_source returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
        after.(ConAssertion.s_mem) = restored.(ConAssertion.s_mem) /\
        task_create_call_stage returned current /\
        (kernel_continuation_call_closed abi kernel_program_inv
           (task_create_continuation_local saved_local) sg (task_stack_call_active_key returned)
           returned (armv7a_irq_fiq_mask saved) current ** frame) after /\
        (task_create_continuation_post environment critical saved_local sg region args task_return
           lower old_frame upper original (armv7a_irq_fiq_mask saved) 0 ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg context outgoing hooked source_tasks original saved acquired
    saved_local resumed before region args task_return lower old_frame upper frame abi local resource current
    Hactive Hrunning Hhigh Hsaved Hdestination Haddress Hcoverage Hpre.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { match type of Hpre with ?P before =>
      assert (Hexpose : P |-- coq_prop (UCOS2_state_inv sg hooked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hpre)). }
  set (current_local := kernel_sched_saved_local_at environment.(task_stack_call_platform)
    critical sg hooked.(TskState) original saved acquired (task_create_continuation_local saved_local)).
  set (current_resource := kernel_saved_continuation_entry abi hooked.(TskState) current_local).
  assert (Hentry : forall key payload, resource key payload |-- current_resource key payload).
  { intros key payload; unfold resource, local, current_resource, current_local.
    apply kernel_saved_continuation_entry_current_registration; exact Hactive. }
  assert (Hmap : store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) |--
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks)).
  { unfold resource, local, current_resource, current_local.
    apply kernel_saved_continuation_map_current_registration; exact Hactive. }
  match type of Hpre with ?P before => assert (Hconvert : P |--
    UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
    current_resource (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) end.
  { sep_apply_l_atomic (Hentry (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing)).
    sep_apply_l_atomic Hmap; entailer!. }
  destruct (kernel_saved_sched_continuation_return_source _ _ _ abi critical arch task_abi restore
    sg context outgoing hooked original saved acquired (task_create_continuation_local saved_local)
    resumed before frame Hsaved Hdestination Haddress Hcoverage (Hconvert before Hpre))
    as [installed [selected [Hinstall [Hreads [Hlease Hrestore]]]]].
  fold current current_local in Hrestore.
  assert (Hcoverage_current : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key original.(os_sched_call_stack)))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing))
      original.(os_sched_call_stack)
      (task_stack_park_covers_active hooked.(TskState) context.(os_sched_call_stack) outgoing Hcoverage)). }
  assert (Habsent : current.(TskState).(parkedTaskStacks)
    (task_stack_key original.(os_sched_call_stack)) = None) by apply task_stack_take_lookup.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hcall [Hsource Htail]].
  fold returned in Hsource, Htail.
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { unfold returned, kernel_selected_call; rewrite Hcall.
    unfold armv7a_continuation_resumed_call, task_tcb_init_stack_same_call; cbn; auto. }
  assert (Hstack : returned.(os_sched_call_stack) = original.(os_sched_call_stack))
    by exact (proj2 (proj2 Hsame)).
  assert (Hstage : task_create_call_stage returned current).
  { exact (task_create_installed_call_stage environment.(task_stack_call_external) sg context outgoing
      hooked original.(os_sched_call_stack) resumed returned Hvalid Hrunning Hhigh Hdestination Hstack Hsource). }
  assert (Hcoverage_returned : task_stack_live_coverage current.(TskState)
    (task_stack_call_active_key returned)).
  { pose proof (proj1 Hsource) as Horigin.
    unfold task_stack_call_active_key; rewrite Horigin, Hstack; exact Hcoverage_current. }
  split; [exact Hcall|]. split; [exact Hsource|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Htail cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix)
    as [Hrun [Hlr [Hmemory Howned]]].
  split; [exact Hrun|]. split; [exact Hlr|]. split; [exact Hmemory|]. split; [exact Hstage|].
  match type of Howned with ?P after => assert (Hclose : P |--
    kernel_continuation_call_closed abi kernel_program_inv (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key returned) returned (armv7a_irq_fiq_mask saved) current ** frame) end.
  { unfold current_local.
    sep_apply_l_atomic (kernel_saved_continuation_map_unfocus_absent _ _ _ abi critical sg hooked.(TskState)
      current.(TskState) original saved acquired (task_create_continuation_local saved_local)
      current.(TskState).(parkedTaskStacks) Habsent).
    unfold kernel_continuation_call_closed, kernel_continuation_inv; entailer!. }
  pose proof (Hclose after Howned) as Hclosed.
  split; [exact Hclosed|].
  match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
  { unfold abi; sepcon_assoc_change.
    sep_apply_l_atomic (task_create_continuation_closed_returns_success environment critical saved_local sg
      original returned (armv7a_irq_fiq_mask saved) current region args task_return lower old_frame upper Hsame).
    entailer!. }
  exact (Hpost after Hclosed).
Qed.
