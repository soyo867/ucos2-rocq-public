Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_nonswitch_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The EventTaskRdy return cut inside SemPost. The retained descriptor is
    the exact IRQ save, separately owned alongside the map for an earlier
    pending call. All parked bytes stay in the kernel invariant. A wake
    changes neither that map nor any task's saved SP/generation. *)
Lemma sem_post_wake_merge_pending_split : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry eid event tid old priority retained focus active,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) active ->
  let after := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  sem_post_wake_frame sg entry eid tid **
  armv7a_dormant_continuation abi retained **
  armv7a_task_call_stacks abi entry.(TskState) focus
    (task_stack_take entry.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) |--
  coq_prop (sem_post_wake_result sg eid entry after priority /\
    task_stack_live_coverage after.(TskState) active) &&
  (kernel_program_inv sg after ** armv7a_dormant_continuation abi retained **
   armv7a_task_call_stacks abi after.(TskState) focus
     (task_stack_take after.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack))).
Proof.
  intros external platform port abi sg entry eid event tid old priority retained focus active
    Hvalid Hlookup Htype Hentry Hcoverage after.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hkind : event_type_to_pend_type event.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg entry eid event tid tail PendSem 0 PendOK
    Hvalid Hlookup Hkind Hlist) as [found [Hfound [Hstep Hrest]]].
  assert (found = old) by congruence; subst found.
  assert (Hnodes : forall slot node, after.(TskState).(inUsedTaskStates) slot = Some node ->
    exists previous, entry.(TskState).(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode.
    change ((if Z.eqb slot tid then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
      exists old; repeat split; assumption || reflexivity.
    - exists node; repeat split; assumption || reflexivity. }
  assert (Hcovered : task_stack_live_coverage after.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := entry.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; auto. }
  assert (Htransport : armv7a_task_call_stacks abi entry.(TskState) focus
      (task_stack_take entry.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) |--
    armv7a_task_call_stacks abi after.(TskState) focus
      (task_stack_take after.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack))).
  { change (armv7a_task_call_stacks abi entry.(TskState) focus
      (task_stack_take entry.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) |--
      armv7a_task_call_stacks abi after.(TskState) focus
      (task_stack_take entry.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack))).
    apply armv7a_task_call_stacks_reindex.
    intros key payload node Hpayload Hnode Hgen; apply Hnodes; exact Hnode. }
  sep_apply_l_atomic (sem_post_wake_merge_full sg entry eid event tid old priority
    Hvalid Hlookup Htype Hentry); Intros returned.
  assert (Hresult : sem_post_wake_result sg eid entry returned priority) by tauto.
  unfold sem_post_wake_result in Hresult; rewrite Hstep in Hresult.
  injection Hresult as Hpriority Hreturned; subst returned.
  sep_apply_l_atomic Htransport.
  rewrite kernel_program_inv_split_unmap; unfold sem_post_wake_result, after; entailer!.
Qed.

(** Wake keeps the current task's cache identity and priority. If the
    current slot is the updated slot, the canonical wake still preserves
    its generation and effective readiness. No "different waiter" premise
    is required. *)
Lemma sem_post_wake_preserves_current_ready : forall sg entry eid event tid old slot caller,
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sched_current_ready_at entry.(TskState) entry.(SchedState) slot caller ->
  let after := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  exists current,
    sched_current_ready_at after.(TskState) after.(SchedState) slot current /\
    current.(taskGeneration) = caller.(taskGeneration).
Proof.
  intros sg entry eid event tid old slot caller Hold
    [Hcaller [Hcurrent [Hpriority [Hin Hready]]]] after.
  assert (Hcurrent_after : after.(SchedState).(curTaskID) = Some slot).
  { change ((sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
      (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat))).(curTaskID) = Some slot).
    unfold sched_wake_by_status; destruct task_status_is_suspended; exact Hcurrent. }
  assert (Hpriority_after : after.(SchedState).(curSchedPrio) = Some caller.(curPrio)).
  { change ((sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
      (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat))).(curSchedPrio) =
      Some caller.(curPrio)).
    unfold sched_wake_by_status; destruct task_status_is_suspended; exact Hpriority. }
  assert (Hin_after : In slot after.(SchedState).(readyList)).
  { apply sched_wake_by_status_membership; left; exact Hin. }
  destruct (Z.eq_dec slot tid) as [Hequal|Hother].
  - subst slot; assert (caller = old) by congruence; subst caller.
    exists (task_event_wake_single old PendSem 0 PendOK); split; [|reflexivity].
    unfold sched_current_ready_at; split.
    + change ((if Z.eqb tid tid then Some (task_event_wake_single old PendSem 0 PendOK)
        else entry.(TskState).(inUsedTaskStates) tid) =
        Some (task_event_wake_single old PendSem 0 PendOK)); rewrite Z.eqb_refl; reflexivity.
    + split; [exact Hcurrent_after|]. split; [exact Hpriority_after|].
      split; [exact Hin_after|apply task_event_wake_single_keeps_ready_task_ready; exact Hready].
  - exists caller; split; [|reflexivity].
    unfold sched_current_ready_at; split.
    + change ((if Z.eqb slot tid then Some (task_event_wake_single old PendSem 0 PendOK)
        else entry.(TskState).(inUsedTaskStates) slot) = Some caller).
      apply Z.eqb_neq in Hother; rewrite Hother; exact Hcaller.
    + exact (conj Hcurrent_after (conj Hpriority_after (conj Hin_after Hready))).
Qed.

(** Actual SemPost success suffix, starting immediately after the
    EventTaskRdy return. Preserve both pending descriptors through
    OS_EXIT_CRITICAL and the following OS_Sched Save/guard/Restore.
    Nonzero interrupt nesting derives the no-switch branch. The named
    uninterrupted instruction transitions are local source evidence;
    nested IRQs and the enclosing handler's return have separate joins. *)
Lemma sem_post_wake_isr_uninterrupted_return : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg entry eid event tid old priority call saved retained focus caller before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) None ->
  sched_current_ready_at entry.(TskState) entry.(SchedState)
    retained.(armv7a_continuation_stack).(stackLeaseSlot) caller ->
  entry.(IntrState).(intNesting) <> 0 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   os_sched_context_resources environment.(task_stack_call_external) call **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid **
   armv7a_dormant_continuation abi retained **
   armv7a_task_call_stacks abi entry.(TskState) focus
     (task_stack_take entry.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
   frame) before ->
  forall cursor written middle final_cursor released_heap,
    cursor.(kernel_restore_r0) = saved ->
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
    armv7a_restore_prefix_transition restore cursor before written middle ->
    armv7a_restore_suffix_transition restore written middle final_cursor released_heap ->
    kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released_heap /\
    exists current,
      sched_current_ready_at checkpoint.(TskState) checkpoint.(SchedState)
        retained.(armv7a_continuation_stack).(stackLeaseSlot) current /\
      current.(taskGeneration) = caller.(taskGeneration) /\
      (forall registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None ->
        valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint released_heap
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers checkpoint released_heap
          final_registers acquired saved_heap /\ acquired = checkpoint /\
        exists prefix_heap,
          os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
          (forall sched_cursor sched_written sched_middle sched_final final_heap,
            sched_cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
            armv7a_irq_fiq_mask sched_cursor.(kernel_restore_current_cpsr) = 192 ->
            armv7a_restore_prefix_transition restore sched_cursor prefix_heap sched_written sched_middle ->
            armv7a_restore_suffix_transition restore sched_written sched_middle sched_final final_heap ->
            kernel_call_restore_uninterrupted_execution arch sched_cursor prefix_heap sched_final final_heap /\
            task_stack_live_coverage checkpoint.(TskState) None /\
            (kernel_call_execution_owned environment.(task_stack_call_external)
               environment.(task_stack_call_platform) call (armv7a_irq_fiq_mask saved) **
             kernel_program_inv sg checkpoint **
             armv7a_dormant_continuation abi retained **
             armv7a_task_call_stacks abi checkpoint.(TskState) focus
               (task_stack_take checkpoint.(TskState).(parkedTaskStacks)
                 retained.(armv7a_continuation_stack)) ** frame) final_heap)).
Proof.
  intros environment critical arch save restore sg entry eid event tid old priority call saved retained focus
    caller before frame abi checkpoint Hvalid Hlookup Htype Hentry Hcoverage Hready Hnesting Hpre
    cursor written middle final_cursor released_heap Hcursor Hmask Hprefix Hsuffix.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  destruct (sem_post_wake_preserves_current_ready sg entry eid event tid old
    retained.(armv7a_continuation_stack).(stackLeaseSlot) caller Hold Hready)
    as [current [Hcurrent Hgeneration]].
  pose proof (sem_post_wake_merge_pending_split _ _ _ abi sg entry eid event tid old priority
    retained focus None Hvalid Hlookup Htype Hentry Hcoverage) as Hmerge; cbv zeta in Hmerge.
  match type of Hpre with ?P before => assert (Hrestore_input : P |--
    coq_prop (task_stack_live_coverage checkpoint.(TskState) None) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
     os_sched_context_resources environment.(task_stack_call_external) call **
     (kernel_program_inv sg checkpoint ** armv7a_dormant_continuation abi retained **
      armv7a_task_call_stacks abi checkpoint.(TskState) focus
        (task_stack_take checkpoint.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
      frame))) end.
  { sep_apply_l_atomic Hmerge; Intros; entailer!. }
  destruct (Hrestore_input before Hpre) as [Hcovered Howned].
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call
    saved entry cursor before written middle final_cursor released_heap _ Hcursor Hmask Howned Hprefix Hsuffix)
    as [Hrestore_run [Hreturn [Hmemory Hreleased]]].
  split; [exact Hrestore_run|].
  exists current; split; [exact Hcurrent|]. split; [exact Hgeneration|].
  intros registers final_registers acquired saved_heap Hregisters Hcpsr Hsaved_mask Hsave.
  assert (Hselection : os_sched_selection_enabled checkpoint = false).
  { unfold os_sched_selection_enabled; change
      ((Z.eqb entry.(IntrState).(intNesting) 0 && Z.eqb entry.(IntrState).(lockNesting) 0)%bool = false).
    apply Z.eqb_neq in Hnesting; rewrite Hnesting; reflexivity. }
  assert (Hnoswitch : os_sched_requests_switch checkpoint = false).
  { unfold os_sched_requests_switch; rewrite Hselection; reflexivity. }
  assert (Hnonempty : os_sched_selection_enabled checkpoint = true ->
    checkpoint.(SchedState).(readyList) <> []) by (rewrite Hselection; discriminate).
  assert (Hcheckpoint : os_sched_prefix_state checkpoint = checkpoint).
  { unfold os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Hselection.
    destruct checkpoint; reflexivity. }
  match type of Hreleased with ?P released_heap => assert (Hsave_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call (armv7a_irq_fiq_mask saved) **
    kernel_program_inv sg checkpoint **
    (armv7a_dormant_continuation abi retained **
     armv7a_task_call_stacks abi checkpoint.(TskState) focus
       (task_stack_take checkpoint.(TskState).(parkedTaskStacks) retained.(armv7a_continuation_stack)) **
     frame)) by entailer! end.
  destruct (os_sched_uninterrupted_nonswitch_frame _ _ _ _ save restore sg call
    (armv7a_irq_fiq_mask saved) checkpoint registers released_heap final_registers acquired saved_heap _
    Hregisters Hcpsr Hsaved_mask Hnoswitch Hnonempty (Hsave_input released_heap Hreleased) Hsave)
    as [Hsave_run [Hacquired [prefix_heap [Hprefix_run Hcontinue]]]].
  split; [exact Hsave_run|]. split; [exact Hacquired|].
  exists prefix_heap; split; [exact Hprefix_run|].
  intros sched_cursor sched_written sched_middle sched_final final_heap Hr0 Hif Hrp Hrs.
  destruct (Hcontinue sched_cursor sched_written sched_middle sched_final final_heap Hr0 Hif Hrp Hrs)
    as [Hrun Hpost].
  rewrite Hcheckpoint in Hpost; split; [exact Hrun|]. split; [exact Hcovered|].
  match type of Hpost with ?P final_heap => match goal with |- ?Q final_heap =>
    assert (Hclose : P |-- Q) by entailer! end end.
  exact (Hclose final_heap Hpost).
Qed.

