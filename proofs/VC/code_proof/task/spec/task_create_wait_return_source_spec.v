Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Ordinary foreign OSSemPend's literal three stores and EventTaskWait
    retain an EARLIER pending invocation. Reindex the existing focused map
    through the real TCB update: every generation/SP is unchanged. Neither
    the world nor its focus is treated as a frame across an arbitrary call.
    Only the disjoint execution/token handles and caller frame accompany
    these proved local C writes. *)
Lemma task_create_foreign_wait_preserves_pending_call : forall environment critical sg
  context saved entry eid event tid old timeout original suspended (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  sem_pend_wait_entry sg entry eid event tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  0 <= timeout < 4294967296 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) saved entry **
   os_sched_context_resources environment.(task_stack_call_external) context ** kernel_program_inv sg entry **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) ** frame) before ->
  exists waited,
    sem_pend_wait_fragment sg entry eid event tid old timeout before waited /\
    kernel_call_task_source context waiting /\
    sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
    task_stack_live_coverage waiting.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) /\
    task_invocation_active waiting.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
    task_saved_pointer_at waiting suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) /\
    (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
       context.(os_sched_call_origin) saved entry **
     os_sched_context_resources environment.(task_stack_call_external) context ** kernel_program_inv sg waiting **
     armv7a_task_call_stacks abi waiting.(TskState) focus waiting.(TskState).(parkedTaskStacks) ** frame) waited.
Proof.
  intros environment critical sg context saved entry eid event tid old timeout original suspended frame before
    abi focus waiting Hentry Hsource Hcache Hcoverage Hactive Hpointer Htimeout Hpre.
  pose proof Hentry as [Hvalid [_ [Hcurrent [Hold _]]]].
  set (rest := critical_region_masked environment.(task_stack_call_platform) critical sg
    context.(os_sched_call_invocation) context.(os_sched_call_origin) saved entry **
    os_sched_context_resources environment.(task_stack_call_external) context **
    armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
    unmap_table_rep sg ** frame).
  match type of Hpre with ?P before => assert (Hcells : P |--
    sem_pend_wait_prefix_cells sg entry tid old (encode_task_status old.(stat))
      (encode_pend_status old.(statPend)) old.(dly) ** rest) end.
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (sem_pend_wait_prefix_split sg entry tid old Hvalid Hcurrent Hold).
    unfold sem_pend_wait_prefix_cells, rest; entailer!. }
  destruct (sem_pend_wait_stores_source sg entry eid event tid old timeout rest before Hentry Htimeout
    (Hcells before Hpre)) as [waited [Hstores Hafter]].
  assert (Hnodes : forall slot node, waiting.(TskState).(inUsedTaskStates) slot = Some node ->
    exists previous, entry.(TskState).(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode.
    change ((if Z.eqb slot tid then
      Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
      else entry.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
      exists old; repeat split; assumption || reflexivity.
    - exists node; repeat split; assumption || reflexivity. }
  assert (Hcovered : task_stack_live_coverage waiting.(TskState)
    (Some (task_stack_key context.(os_sched_call_stack)))).
  { eapply task_stack_live_coverage_used_map_frame with (before := entry.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; auto. }
  assert (Hstacks : armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_call_stacks abi waiting.(TskState) focus waiting.(TskState).(parkedTaskStacks)).
  { change (armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
      armv7a_task_call_stacks abi waiting.(TskState) focus entry.(TskState).(parkedTaskStacks)).
    apply armv7a_task_call_stacks_reindex.
    intros key payload node Hpayload Hnode Hgen; apply Hnodes; exact Hnode. }
  assert (Hwaiting_active : task_invocation_active waiting.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { unfold waiting; cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState].
    eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hold|reflexivity|exact Hactive]. }
  assert (Hwaiting_pointer : task_saved_pointer_at waiting suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { destruct Hpointer as [node [Hnode [Hgen Hsp]]].
    destruct (Z.eq_dec suspended.(armv7a_continuation_stack).(stackLeaseSlot) tid) as [Heq|Hneq].
    - assert (node = old) by (rewrite Heq in Hnode; congruence); subst node.
      exists (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)).
      split; [|split; assumption].
      change ((if Z.eqb suspended.(armv7a_continuation_stack).(stackLeaseSlot) tid then
        Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
        else entry.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot)) =
        Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))).
      rewrite Heq, Z.eqb_refl; reflexivity.
    - exists node; split; [|auto].
      change ((if Z.eqb suspended.(armv7a_continuation_stack).(stackLeaseSlot) tid then
        Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
        else entry.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot)) = Some node).
      destruct (Z.eqb _ _) eqn:Htest; [apply Z.eqb_eq in Htest; contradiction|exact Hnode]. }
  destruct (sem_pend_wait_preserves_call_source sg context entry eid event tid old timeout
    Hentry Hsource Hcache) as [Hwaiting_valid [Hwaiting_source Hwaiting_cache]].
  exists waited; split; [exact Hstores|]. split; [exact Hwaiting_source|].
  split; [exact Hwaiting_cache|]. split; [exact Hcovered|].
  split; [exact Hwaiting_active|]. split; [exact Hwaiting_pointer|].
  match type of Hafter with ?P waited => match goal with |- ?Q waited => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (sem_pend_wait_call_merge sg entry eid event tid old timeout Hentry).
    unfold rest; sep_apply_l_atomic Hstacks.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  exact (Hclose waited Hafter).
Qed.

(** A concrete returning branch: before the foreign task blocks, it is
    the first ready task and the original pending task is next. The real
    removal selects the original; this is not a termination assertion or
    a future high-ready premise. *)
Lemma task_create_foreign_wait_selects_pending : forall sg entry eid event tid old timeout
  pending tail,
  sem_pend_wait_entry sg entry eid event tid old ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) = tid :: pending :: tail -> pending <> tid ->
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  waiting.(SchedState).(readyList) = pending :: remove_Z_eqb tid tail /\
  os_sched_requests_switch waiting = true /\
  (os_sched_prefix_state waiting).(SchedState).(highRdyTid) = Some pending.
Proof.
  intros sg entry eid event tid old timeout pending tail Hentry Hcache Henabled Hlist Hne waiting.
  pose proof Hentry as [Hvalid [_ [Hcurrent [Hold _]]]].
  pose proof (sem_pend_wait_entry_preserves_validity sg entry eid event tid old timeout Hentry)
    as Hwaiting_valid.
  fold waiting in Hwaiting_valid.
  assert (Hneq : Z.eqb pending tid = false) by (apply Z.eqb_neq; exact Hne).
  assert (Hready : waiting.(SchedState).(readyList) = pending :: remove_Z_eqb tid tail).
  { change (remove_Z_eqb tid entry.(SchedState).(readyList) = pending :: remove_Z_eqb tid tail).
    rewrite Hlist; apply remove_Z_eqb_x_then_ne_cons; exact Hneq. }
  assert (Hwaiting_enabled : os_sched_selection_enabled waiting = true) by exact Henabled.
  pose proof (proj1 (proj1 (proj2 (proj2 Hwaiting_valid)))) as Hrdy.
  assert (Hin : In pending waiting.(SchedState).(readyList)) by (rewrite Hready; left; reflexivity).
  destruct (proj1 Hrdy pending Hin) as [node [Hnode _]].
  assert (Hentry_node : entry.(TskState).(inUsedTaskStates) pending = Some node).
  { change ((if Z.eqb pending tid then
      Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
      else entry.(TskState).(inUsedTaskStates) pending) = Some node) in Hnode.
    rewrite Hneq in Hnode; exact Hnode. }
  assert (Hpriority : entry.(SchedState).(curSchedPrio) = Some old.(curPrio)).
  { unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
    destruct Hcache as [current [Hlookup Hprio]]; rewrite Hold in Hlookup;
      injection Hlookup as Heq; subst current; exact Hprio. }
  assert (Hunique : task_priority_unique entry.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hswitch : os_sched_requests_switch waiting = true).
  { apply (proj2 (os_sched_requests_switch_iff waiting)); split; [exact Hwaiting_enabled|].
    rewrite (sched_selected_priority_eq_head sg _ _ _ _ _ (proj1 (proj1 Hvalid)) Hrdy Hready Hnode).
    change (node.(curPrio) <> sched_priority_byte entry.(SchedState).(curSchedPrio)).
    rewrite Hpriority; cbn [sched_priority_byte]; intro Heq; apply Hne.
    exact (Hunique pending tid node old Hentry_node Hold Heq). }
  split; [exact Hready|]. split; [exact Hswitch|].
  pose proof (os_sched_ready_checkpoint_high_consistency sg waiting Hrdy Hwaiting_enabled) as Hhigh.
  unfold sched_high_ready_consistency in Hhigh.
  rewrite (proj1 (os_sched_ready_checkpoint_frame waiting)), Hready in Hhigh.
  exact (proj1 Hhigh).
Qed.

(** The original destination is a saved ordinary call, not a fresh task
    entry. Its EXISTING focused dormant owner supplies the architecture
    source fact; no initial-entry ABI or newly assumed restore relation is
    needed. This observation is consumed by the actual return below. *)
Lemma task_create_pending_entry_destination : forall environment
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  context outgoing state original pc lr fragments node,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original pc lr in
  state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(highRdyPrio) = Some node.(curPrio) ->
  task_stack_live_binding state.(TskState) original.(os_sched_call_stack) ->
  (task_stack_park_fragments state.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing)
    (task_stack_key original.(os_sched_call_stack)) =
      Some (original.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  armv7a_task_call_stack_entry abi state.(TskState) focus (task_stack_key original.(os_sched_call_stack))
    (original.(os_sched_call_stack).(stackLeaseRegion), fragments) |--
  coq_prop (os_sched_destination_binding environment.(task_stack_call_external) context outgoing state
    original.(os_sched_call_stack) fragments) && TT.
Proof.
  intros environment task_abi context outgoing state original pc lr fragments node abi focus
    Hhigh Hnode Hgen Hprio Hlive Hparked.
  unfold armv7a_task_call_stack_entry.
  destruct task_stack_key_eq_dec as [Heq|Hne]; [|exfalso; apply Hne; reflexivity].
  Intros suspended.
  assert (Hkey : task_stack_key suspended.(armv7a_continuation_stack) =
    task_stack_key original.(os_sched_call_stack)) by tauto.
  assert (Hpayload : (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) = (original.(os_sched_call_stack).(stackLeaseRegion), fragments))
    by tauto.
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { unfold task_stack_key in Hkey.
    destruct suspended.(armv7a_continuation_stack), original.(os_sched_call_stack); cbn in *; congruence. }
  assert (Hfragments : suspended.(armv7a_continuation_fragments) = fragments) by congruence.
  assert (Hsp : node.(tcbStkPtr) = suspended.(armv7a_continuation_sp)).
  { assert (Hlive_sp : task_stack_live_sp state.(TskState)
      (task_stack_key original.(os_sched_call_stack)) suspended.(armv7a_continuation_sp)) by tauto.
    apply Hlive_sp; assumption. }
  sep_apply_l_atomic (armv7a_task_dormant_restore_source _ _ _ abi task_abi suspended).
  Intros.
  assert (Harch : environment.(task_stack_call_external).(os_sched_arch_restore_source)
    original.(os_sched_call_stack) node.(tcbStkPtr) fragments).
  { rewrite Hsp, <- Hlease, <- Hfragments; assumption. }
  assert (Hdestination : os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing state original.(os_sched_call_stack) fragments).
  { unfold os_sched_destination_binding; split; [exact Hhigh|].
    split; [exists node; tauto|]. split; assumption. }
  entailer!; intros ? ?; exact I.
Qed.

(** Returning ordinary-task branch. Real SemPend stores remove the current
    foreign task from the ready list. After its actual Restore and the
    scheduler's actual Save, the C selector chooses the original pending
    task from the resulting list. Sixteen stack stores, TCB-SP store and
    capture preserve the OLD focus; the existing pending-return producer
    then installs/takes that exact owner and executes the final Restore.

    The ready-list prefix is a present-state branch of the linked program,
    not a guarantee that every application blocks or eventually returns.
    The reference hook is explicitly the existing no-write/source step.
    IRQ-interrupted Save/Restore paths retain their separate producers. *)
Lemma task_create_foreign_wait_return_resources : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg context foreign_mask entry eid event tid old timeout tail original suspended saved original_entry
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  let checkpoint := os_sched_prefix_state waiting in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let foreign_saved := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  sem_pend_wait_entry sg entry eid event tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) = tid :: original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  0 <= timeout < 4294967296 ->
  context.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region context.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    context.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range context.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened entry.(TskState) publication context.(os_sched_call_stack).(stackLeaseSlot)
    context.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) foreign_mask entry **
   os_sched_context_resources environment.(task_stack_call_external) context ** kernel_program_inv sg entry **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame)) before ->
  exists waited,
    sem_pend_wait_fragment sg entry eid event tid old timeout before waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = foreign_mask ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask foreign_mask ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers acquired saved_heap /\
        acquired = waiting /\
        exists prefix_heap stack_written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap stack_written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi context foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed selected,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi context selected installed restored ->
                forall return_cursor return_written return_middle return_final after,
                return_cursor.(kernel_restore_r0) = saved ->
                return_cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
                armv7a_restore_prefix_transition restore return_cursor restored return_written return_middle ->
                armv7a_restore_suffix_transition restore return_written return_middle return_final after ->
                let retained := interrupt_platform_saved environment.(task_stack_call_platform)
                  (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation)
                    context.(os_sched_call_origin)) **
                  critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame in
                os_sched_source_switch_execution environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi
                  sg checkpoint context old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  selected prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final after /\
                kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original /\
                kernel_call_task_source (armv7a_continuation_resumed_call selected original)
                  (os_sched_install_context context fragments original.(os_sched_call_stack) updated) /\
                (exists node,
                  (os_sched_install_context context fragments original.(os_sched_call_stack) updated).(TskState).(inUsedTaskStates)
                    original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
                  is_effectively_ready node.(stat) node.(dly) = true) /\
                (kernel_stack_call_closed abi kernel_program_inv sg
                   (task_stack_call_active_key (armv7a_continuation_resumed_call selected original))
                   (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask saved)
                   (os_sched_install_context context fragments original.(os_sched_call_stack) updated) ** retained) after)))).
Proof.
  intros environment critical arch save restore task_abi sg context foreign_mask entry eid event tid old timeout tail
    original suspended saved original_entry old_sp cpsr values
    lr prefix suffix first old_words publication frame before abi focus waiting checkpoint fragments foreign_saved updated
    Hentry Hsource Hcache Henabled Hlist Habsent Hcoverage Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hparked
    Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre.
  pose proof Hentry as [Hvalid [_ [Hcurrent [Hold _]]]].
  assert (Hcontext_origin : context.(os_sched_call_origin) = RunningInvocation
    context.(os_sched_call_stack).(stackLeaseSlot) context.(os_sched_call_stack).(stackLeaseGeneration))
    by exact (proj1 Hsource).
  assert (Htid : context.(os_sched_call_stack).(stackLeaseSlot) = tid).
  { pose proof (proj2 (proj2 Hsource)) as Hcur.
    unfold task_execution_current in Hcur; rewrite Hcontext_origin in Hcur; congruence. }
  assert (Hdifferent : original.(os_sched_call_stack).(stackLeaseSlot) <> tid).
  { pose proof (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 (proj2 Hvalid))))))) as Hnodup.
    rewrite Hlist in Hnodup; inversion Hnodup as [|? ? Hnot _].
    intro Heq; apply Hnot; left; exact Heq. }
  assert (Hkey_ne : task_stack_key original.(os_sched_call_stack) <> task_stack_key context.(os_sched_call_stack)).
  { unfold task_stack_key; intro Heq; injection Heq; rewrite Htid; congruence. }
  assert (Hlease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { destruct Hbinding as [_ Hbound]; rewrite Hcall in Hbound; symmetry; exact Hbound. }
  set (original_handles := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame).
  destruct (task_create_foreign_wait_preserves_pending_call environment critical sg context foreign_mask entry
    eid event tid old timeout original suspended original_handles before Hentry Hsource Hcache Hcoverage Hactive
    Hpointer Htimeout Hpre) as [waited [Hstores [Hwaiting_source [Hwaiting_cache [Hcovered
      [Hwaiting_active [Hwaiting_pointer Hwaiting]]]]]]].
  fold abi focus waiting in Hwaiting_source, Hwaiting_cache, Hcovered, Hwaiting_active, Hwaiting_pointer, Hwaiting.
  destruct (task_create_foreign_wait_selects_pending sg entry eid event tid old timeout
    original.(os_sched_call_stack).(stackLeaseSlot) tail Hentry Hcache Henabled Hlist Hdifferent)
    as [Hready [Hswitch Hselected_tid]].
  fold waiting checkpoint in Hready, Hswitch, Hselected_tid.
  assert (Hnonempty : waiting.(SchedState).(readyList) <> []) by (rewrite Hready; discriminate).
  exists waited; split; [exact Hstores|].
  intros cursor written middle final_cursor released Hr0 Hcursor_mask Hrestore_prefix Hrestore_suffix.
  match type of Hwaiting with ?P waited => assert (Hrestore_order : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) foreign_mask entry **
    os_sched_context_resources environment.(task_stack_call_external) context **
    (kernel_program_inv sg waiting ** armv7a_task_call_stacks abi waiting.(TskState) focus
      waiting.(TskState).(parkedTaskStacks) ** original_handles)) by entailer! end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg context foreign_mask entry
    cursor waited written middle final_cursor released _ Hr0 Hcursor_mask (Hrestore_order waited Hwaiting)
    Hrestore_prefix Hrestore_suffix) as [Hrestore_execution [Hreturn_word [Hreleased_memory Hreleased]]].
  split; [exact Hrestore_execution|].
  intros registers final_registers acquired saved_heap Hreturn Hvalid_sr Hsave_mask Hsave.
  assert (Hobserved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid_sr|reflexivity]).
  rewrite <- Hsave_mask in Hreleased.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg context (kernel_save_read_cpsr registers)
    waiting released final_registers acquired saved_heap _ Hobserved Hreleased Hsave)
    as [Hacquired [Hsaved_memory [Hsaved_return [Hsaved_r0 Hmasked]]]].
  split.
  { unfold kernel_call_save_uninterrupted_execution; econstructor.
    - constructor; [exact Hreturn|reflexivity].
    - exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  split; [exact Hacquired|]. subst acquired.
  set (retained := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
    critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame).
  set (rest := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** retained).
  match type of Hmasked with ?P saved_heap => assert (Hprefix_order : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg context focus waiting ** unmap_table_rep sg ** rest) end.
  { unfold os_sched_source_switch_pre, kernel_call_execution_owned, critical_region_masked,
      rest, retained, original_handles.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (os_sched_source_switch_prefix_resources _ _ _ abi sg waiting context focus rest saved_heap
    Hswitch Hnonempty (Hprefix_order saved_heap Hmasked)) as [prefix_heap [Hprefix [Hhigh Hprefix_owned]]].
  fold checkpoint in Hhigh, Hprefix_owned.
  set (waiting_node := task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)).
  assert (Hnode : checkpoint.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot) = Some waiting_node).
  { change ((if Z.eqb context.(os_sched_call_stack).(stackLeaseSlot) tid then Some waiting_node
      else entry.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot)) = Some waiting_node).
    rewrite Htid, Z.eqb_refl; reflexivity. }
  assert (Hid : waiting_node.(taskID) = context.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hlinks.
    destruct Hlinks as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    change (old.(taskID) = context.(os_sched_call_stack).(stackLeaseSlot)); rewrite Htid.
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hold]. apply Hdomain; eauto. }
  assert (Hgen : waiting_node.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration)).
  { pose proof (proj2 (proj2 (proj1 (proj2 Hsource)))) as Hlive.
    unfold task_invocation_origin_live in Hlive; rewrite Hcontext_origin in Hlive.
    destruct Hlive as [node [Hlookup Hgeneration]]; rewrite Htid, Hold in Hlookup;
      injection Hlookup as Heq; subst node; exact Hgeneration. }
  assert (Hcur : checkpoint.(SchedState).(curTaskID) = Some context.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj2 (proj2 Hwaiting_source)) as Hcur.
    unfold task_execution_current in Hcur; rewrite Hcontext_origin in Hcur.
    change ((os_sched_ready_checkpoint waiting).(curTaskID) = Some context.(os_sched_call_stack).(stackLeaseSlot)).
    rewrite (proj1 (proj2 (os_sched_ready_checkpoint_frame waiting))); exact Hcur. }
  assert (Hfocus : task_stack_key context.(os_sched_call_stack) = armv7a_call_focus_key focus ->
    focus = armv7a_call_focus context lr lr).
  { intro Heq; exfalso; apply Hkey_ne; symmetry; exact Heq. }
  match type of Hprefix_owned with ?P prefix_heap => assert (Hsave_order : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      context 192 ** UCOS2_inv sg checkpoint **
    armv7a_task_call_stacks abi checkpoint.(TskState) focus checkpoint.(TskState).(parkedTaskStacks) **
    (unmap_table_rep sg ** rest))
    by (unfold os_sched_source_switch_pre; entailer!) end.
  destruct (armv7a_task_save_global_call _ _ _ abi task_abi sg checkpoint waiting_node context old_sp cpsr values
    lr prefix suffix first old_words focus (unmap_table_rep sg ** rest) prefix_heap Hcur Hnode Hid Hgen Habsent Hcovered Hfocus Hfragments
    Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp (Haddress _) (Hsave_order prefix_heap Hprefix_owned))
    as [stack_written [stored [Hwrites [Hload [Hstore [Hcoverage_updated Hcapture]]]]]].
  fold fragments foreign_saved updated in Hstore, Hcoverage_updated, Hcapture.
  assert (Hsaved_binding : os_sched_saved_stack_binding context fragments updated).
  { apply task_create_saved_context_binding with (node := waiting_node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hlookup_other : forall slot, slot <> context.(os_sched_call_stack).(stackLeaseSlot) ->
    updated.(TskState).(inUsedTaskStates) slot = waiting.(TskState).(inUsedTaskStates) slot).
  { intros slot Hne; unfold updated, os_sched_save_current_sp; rewrite Hnode.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb slot context.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq;
      [apply Z.eqb_eq in Heq; contradiction|reflexivity]. }
  assert (Hwaiting_original : exists node, waiting.(TskState).(inUsedTaskStates)
    original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
    node.(tcbStkPtr) = suspended.(armv7a_continuation_sp)).
  { rewrite <- Hlease; exact Hwaiting_pointer. }
  destruct Hwaiting_original as [original_node [Horiginal_node [Horiginal_gen Horiginal_sp]]].
  assert (Horiginal_updated : updated.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) =
    Some original_node) by (rewrite Hlookup_other; [exact Horiginal_node|rewrite Htid; exact Hdifferent]).
  assert (Hpointer_updated : task_saved_pointer_at updated suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { rewrite Hlease; exists original_node; auto. }
  assert (Hactive_updated : task_invocation_active updated.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hwaiting_active]. }
  assert (Hready_checkpoint : checkpoint.(SchedState).(readyList) =
    original.(os_sched_call_stack).(stackLeaseSlot) :: remove_Z_eqb tid tail).
  { change ((os_sched_ready_checkpoint waiting).(readyList) =
      original.(os_sched_call_stack).(stackLeaseSlot) :: remove_Z_eqb tid tail).
    rewrite (proj1 (os_sched_ready_checkpoint_frame waiting)); exact Hready. }
  assert (Hready_updated : updated.(SchedState).(readyList) = checkpoint.(SchedState).(readyList)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; reflexivity. }
  assert (Hhigh_updated : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold sched_high_ready_consistency in *; rewrite Hready_updated, Hready_checkpoint.
    rewrite Hready_checkpoint in Hhigh; destruct Hhigh as [Hhigh_tid [node [Hlookup Hpriority]]].
    change (waiting.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node) in Hlookup.
    rewrite Horiginal_node in Hlookup; injection Hlookup as Heq; subst node.
    split; [|exists original_node; split; [exact Horiginal_updated|]].
    all: unfold updated, os_sched_save_current_sp; rewrite Hnode; assumption. }
  exists prefix_heap, stack_written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
  split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  assert (Hhook_eq : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|]. split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture captured Hcaptured) as [Hcapture_memory [Harch Hcaptured_owned]].
  assert (Hupdated_valid : UCOS2_state_inv sg updated).
  { match type of Hcaptured_owned with ?P captured => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg updated) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve captured Hcaptured_owned)). }
  assert (Hparked_updated : updated.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; exact Hparked. }
  assert (Hparked_effective : (task_stack_park_fragments updated.(TskState).(parkedTaskStacks)
    context.(os_sched_call_stack) fragments) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { rewrite task_stack_park_fragments_lookup_other; assumption. }
  assert (Hlive : task_stack_live_binding updated.(TskState) original.(os_sched_call_stack)).
  { assert (Hconsistent : parked_stacks_consistent updated.(TskState) updated.(TskState).(parkedTaskStacks))
      by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hupdated_valid; tauto).
    exists original_node; split; [exact Horiginal_updated|].
    pose proof (proj2 (proj2 (proj2 (Hconsistent _ _ _ _ Hparked_updated))) original_node
      Horiginal_updated Horiginal_gen) as Hmatches.
    destruct original.(os_sched_call_stack); exact Hmatches. }
  assert (Hdestination : os_sched_destination_binding environment.(task_stack_call_external) context fragments updated
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments)).
  { assert (Hnone : updated.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None)
      by (unfold updated, os_sched_save_current_sp; rewrite Hnode; exact Habsent).
    assert (Hhigh_original : updated.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) /\
      updated.(SchedState).(highRdyPrio) = Some original_node.(curPrio)).
    { unfold sched_high_ready_consistency in Hhigh_updated; rewrite Hready_updated, Hready_checkpoint in Hhigh_updated.
      destruct Hhigh_updated as [Hhigh_tid [node [Hlookup Hpriority]]].
      rewrite Horiginal_updated in Hlookup; injection Hlookup as Heq; subst node; auto. }
    match type of Hcaptured_owned with ?P captured => assert (Hobserve : P |-- coq_prop
      (os_sched_destination_binding environment.(task_stack_call_external) context fragments updated
        original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments)) && TT) end.
    { eapply derivable1_trans with (y :=
        (armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key context.(os_sched_call_stack))
          (context.(os_sched_call_stack).(stackLeaseRegion), fragments) **
         armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks)) ** TT).
      { entailer!; intros ? ?; exact I. }
      unfold armv7a_task_call_stacks.
      eapply derivable1_trans.
      { apply derivable1_sepcon_mono; [|reflexivity].
        exact (store_parked_continuations_switch (armv7a_task_call_stack_entry abi updated.(TskState) focus)
          updated.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) original.(os_sched_call_stack) fragments
          suspended.(armv7a_continuation_fragments) Hnone Hparked_effective). }
      pose proof (task_create_pending_entry_destination environment task_abi context fragments updated original
        suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) suspended.(armv7a_continuation_fragments)
        original_node (proj1 Hhigh_original) Horiginal_updated Horiginal_gen (proj2 Hhigh_original) Hlive Hparked_effective)
        as Hfrom_entry.
      fold abi focus in Hfrom_entry; sep_apply_l_atomic Hfrom_entry.
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve captured Hcaptured_owned)). }
  match type of Hcaptured_owned with ?P captured => assert (Hreturn_order : P |--
    UCOS2_inv sg updated ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) fragments **
    armv7a_task_call_stack_entry abi updated.(TskState) focus (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** unmap_table_rep sg ** retained)))
    by (unfold rest; entailer!) end.
  destruct (task_create_sched_pending_return_resources environment critical arch task_abi restore sg context fragments updated
    original suspended saved original_entry captured retained
    Horigin Hbinding Hcall Hslice Hmask Hsaved_binding Hdestination Hhigh_updated
    ltac:(rewrite Hready_updated, Hready_checkpoint; discriminate) Hpointer_updated (Haddress _) Hcoverage_updated
    Hactive_updated (Hreturn_order captured Hcaptured_owned))
    as [installed [selected [Hinstall [Hreads [Hselected_sp [Hselected_cpsr [Hregisters Hfinal]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hselected_sp|]. split; [exact Hselected_cpsr|]. split; [exact Hregisters|].
  intros restored Htask_restore return_cursor return_written return_middle return_final after
    Hreturn_r0 Hreturn_cpsr Hreturn_prefix Hreturn_suffix; cbv zeta.
  split.
  - exists stack_written, stored, captured, captured, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcaptured
      (conj Hhook_heap (conj Hhook_step (conj Hinstall Htask_restore))))))).
  - exact (Hfinal restored Htask_restore return_cursor return_written return_middle return_final after
      Hreturn_r0 Hreturn_cpsr Hreturn_prefix Hreturn_suffix).
Qed.

(** Preserve the established Task interface as a projection. *)
Lemma task_create_foreign_wait_return_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg context foreign_mask entry eid event tid old timeout tail original suspended saved original_entry
  call_before region args task_return lower old_frame upper
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  let checkpoint := os_sched_prefix_state waiting in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let foreign_saved := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  sem_pend_wait_entry sg entry eid event tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  entry.(SchedState).(readyList) = tid :: original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  0 <= timeout < 4294967296 ->
  context.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region context.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    context.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range context.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened entry.(TskState) publication context.(os_sched_call_stack).(stackLeaseSlot)
    context.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) foreign_mask entry **
   os_sched_context_resources environment.(task_stack_call_external) context ** kernel_program_inv sg entry **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame)) before ->
  exists waited,
    sem_pend_wait_fragment sg entry eid event tid old timeout before waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = foreign_mask ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask foreign_mask ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers acquired saved_heap /\
        acquired = waiting /\
        exists prefix_heap stack_written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap stack_written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi context foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed selected,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi context selected installed restored ->
                forall return_cursor return_written return_middle return_final after,
                return_cursor.(kernel_restore_r0) = saved ->
                return_cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
                armv7a_restore_prefix_transition restore return_cursor restored return_written return_middle ->
                armv7a_restore_suffix_transition restore return_written return_middle return_final after ->
                let retained := interrupt_platform_saved environment.(task_stack_call_platform)
                  (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation)
                    context.(os_sched_call_origin)) **
                  critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame in
                os_sched_source_switch_execution environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi
                  sg checkpoint context old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  selected prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final after /\
                (os_sched_stack_return_post environment kernel_program_inv sg original
                  (armv7a_irq_fiq_mask saved) call_before ** retained) after /\
                (task_create_stack_post environment critical sg region args task_return lower old_frame upper
                  original (armv7a_irq_fiq_mask saved) 0 ** retained) after)))).
Proof.
  intros environment critical arch save restore task_abi sg context foreign_mask entry eid event tid old timeout tail
    original suspended saved original_entry call_before region args task_return lower old_frame upper old_sp cpsr values
    lr prefix suffix first old_words publication frame before abi focus waiting checkpoint fragments foreign_saved updated
    Hentry Hsource Hcache Henabled Hlist Habsent Hcoverage Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hparked
    Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre.
  destruct (task_create_foreign_wait_return_resources environment critical arch save restore task_abi
    sg context foreign_mask entry eid event tid old timeout tail original suspended saved original_entry
    old_sp cpsr values lr prefix suffix first old_words
    publication frame before Hentry Hsource Hcache Henabled Hlist Habsent Hcoverage Horigin Hbinding Hcall Hslice
    Hmask Hactive Hpointer Hparked Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr
    Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre) as [waited [Hstores Hreturn]].
  exists waited; split; [exact Hstores|].
  intros cursor written middle final_cursor released Hr0 Hcursor Hprefix Hsuffix.
  destruct (Hreturn cursor written middle final_cursor released Hr0 Hcursor Hprefix Hsuffix)
    as [Hrestore_execution Hafter_restore].
  split; [exact Hrestore_execution|].
  intros registers final_registers acquired saved_heap Hreturn_word Hvalid_sr Hsave_mask Hsave.
  destruct (Hafter_restore registers final_registers acquired saved_heap Hreturn_word Hvalid_sr Hsave_mask Hsave)
    as [Hsave_execution [Hacquired [prefix_heap [stack_written [stored [Hprefix_execution [Hwrites
      [Hload [Hstore Hafter_save]]]]]]]]].
  split; [exact Hsave_execution|]. split; [exact Hacquired|].
  exists prefix_heap, stack_written, stored; split; [exact Hprefix_execution|].
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hafter_save captured hooked Hcapture Hhook_heap Hhook_step)
    as [installed [selected [Hinstall [Hreads [Hselected_sp [Hselected_cpsr [Hregisters Hfinal]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hselected_sp|]. split; [exact Hselected_cpsr|]. split; [exact Hregisters|].
  intros restored Htask_restore return_cursor return_written return_middle return_final after
    Hreturn_r0 Hreturn_cpsr Hreturn_prefix Hreturn_suffix; cbv zeta.
  destruct (Hfinal restored Htask_restore return_cursor return_written return_middle return_final after
    Hreturn_r0 Hreturn_cpsr Hreturn_prefix Hreturn_suffix)
    as [Hswitch_execution [Hrestore_return [Hsame [Hsource_return [Hready_return Howned]]]]].
  set (returned := armv7a_continuation_resumed_call selected original) in *.
  set (current := os_sched_install_context context fragments original.(os_sched_call_stack) updated) in *.
  fold waiting checkpoint fragments foreign_saved updated current in Howned, Hsource_return, Hready_return.
  set (retained := interrupt_platform_saved environment.(task_stack_call_platform)
    (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
    critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame) in *.
  fold retained in Howned.
  assert (Hpost : (os_sched_stack_return_post environment kernel_program_inv sg original
    (armv7a_irq_fiq_mask saved) call_before ** retained) after).
  { match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { assert (Hactive_key : task_stack_call_active_key original = task_stack_call_active_key returned).
      { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
      unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post.
      Exists returned current; rewrite Hactive_key; entailer!. }
    exact (Hclose after Howned). }
  split; [exact Hswitch_execution|]. split; [exact Hrestore_return|]. split; [exact Hpost|].
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (os_sched_stack_return_post_returns_create environment critical sg original original
      (armv7a_irq_fiq_mask saved) call_before region args task_return lower old_frame upper
      ltac:(unfold task_tcb_init_stack_same_call; auto)); entailer!. }
  exact (Hclose after Hpost).
Qed.
