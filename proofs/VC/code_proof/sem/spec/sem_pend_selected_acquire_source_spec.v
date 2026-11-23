Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Saving an outgoing stack changes its SP only.  The pending SemPend
    invocation may be another task; no current/ready preservation is used. *)
Lemma sem_pend_save_current_sp_preserves_call_fields : forall sg state slot node sp tid,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  sem_pend_call_fields sg tid state ->
  sem_pend_call_fields sg tid (os_sched_save_current_sp state slot sp).
Proof.
  intros sg state slot node sp tid Hnode [Hrunning [observed [Hobserved Hfields]]].
  unfold os_sched_save_current_sp; rewrite Hnode.
  split; [exact Hrunning|].
  destruct (Z.eqb tid slot) eqn:Hsame.
  - apply Z.eqb_eq in Hsame; subst tid.
    assert (observed = node) by congruence; subst observed.
    exists (task_set_saved_sp node sp); split.
    + cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + exact Hfields.
  - exists observed; split; [|exact Hfields].
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite Hsame; exact Hobserved.
Qed.

(** The next count-cell consumer uses the selected current owner. At this
    local scheduling cut EventState is unchanged, so the observed object
    and its generation are preserved exactly. Earlier client activity
    must separately establish the handle at [entry]. *)
Lemma sem_pend_selected_acquire_count_resources : forall external platform port critical
  (abi : Armv7aContinuationABI external platform port)
  sg returned focus saved entry acquired eid event (frame : Assertion),
  acquired.(EventState) = entry.(EventState) ->
  mutex_query_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_pend_task_call_stage sg returned acquired ->
  critical_region_masked platform critical sg returned.(os_sched_call_invocation)
    returned.(os_sched_call_origin) saved acquired **
  os_sched_context_resources external returned ** UCOS2_inv sg acquired **
  armv7a_task_call_stacks abi acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks) ** frame |--
  coq_prop (UCOS2_state_inv sg acquired /\ mutex_query_lookup acquired eid event /\
    0 <= encode_event_cnt_value event <= 65535 /\
    (encode_event_cnt_value event = 0 -> event_object_layout_prop sg eid ->
      exists node, sem_pend_wait_entry sg acquired eid event
        returned.(os_sched_call_stack).(stackLeaseSlot) node /\
        kernel_call_task_source returned acquired /\
        sched_current_consistency acquired.(TskState) acquired.(SchedState))) &&
  (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
     returned.(os_sched_call_origin) saved acquired **
   os_sched_context_resources external returned **
   (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event **
   sem_post_count_frame sg acquired eid event **
   armv7a_task_call_stacks abi acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks) ** frame).
Proof.
  intros external platform port critical abi sg returned focus saved entry acquired eid event frame
    Hevent Hlookup Htype Hstage.
  assert (Hcurrent : mutex_query_lookup acquired eid event).
  { unfold mutex_query_lookup in *; rewrite Hevent; exact Hlookup. }
  sep_apply_l_atomic (sem_post_count_split_full sg acquired eid event Hcurrent Htype).
  Intros.
  assert (Hwait : encode_event_cnt_value event = 0 -> event_object_layout_prop sg eid ->
    exists node, sem_pend_wait_entry sg acquired eid event
      returned.(os_sched_call_stack).(stackLeaseSlot) node /\
      kernel_call_task_source returned acquired /\
      sched_current_consistency acquired.(TskState) acquired.(SchedState)).
  { intros Hzero Hlayout.
    destruct (sem_pend_task_stage_wait_entry sg returned acquired eid event
      Hstage ltac:(tauto) Hcurrent Htype Hzero Hlayout)
      as [node [Hentry [Horigin [Hsource Hcache]]]].
    exists node; auto. }
  entailer!.
Qed.

(** A concrete returning branch of an interrupted first CPU Save.
    At this cut another task executes OS_Sched and the original invocation
    is the actual ready-list head.  The C selector, outgoing frame/SP writes,
    reference no-write hook, destination install and frame restore produce
    the selected source post; the existing CPSID/DSB/BX consumer immediately
    establishes SemPend's acquired task stage on that SAME heap.

    Only invocation liveness and unregistered/non-idle fields arrive from
    the earlier client trace.  Selection supplies current/ready/generation.
    [live_save_input] concerns the actual outgoing frame at the C checkpoint;
    it does not assert that every opaque platform endpoint is safe.  Earlier
    IRQ deposit/client transport and other hook/interrupt branches retain
    their separate source obligations.  No public Require is strengthened. *)
Lemma sem_pend_scheduler_selected_acquire_source : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  (save_suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg entry outgoing node old_sp cpsr registers lr prefix suffix first old_words
  original original_lr publication tail (frame : Assertion) before,
  let focus := armv7a_call_focus original (armv7a_save_entry_address save_suffix + 4) original_lr in
  let state := os_sched_prefix_state entry in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image outgoing old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state outgoing.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) entry ->
  entry.(SchedState).(readyList) = original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  os_sched_requests_switch entry = true ->
  os_sched_source_live_save_input sg state node outgoing old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  (os_sched_source_switch_pre external platform port abi sg outgoing focus entry **
   unmap_table_rep sg ** frame) before ->
  exists checkpoint written stored,
    os_sched_source_switch_prefix_execution sg before checkpoint /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) checkpoint written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg outgoing.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg outgoing.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi outgoing saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected current,
        os_sched_destination_binding external outgoing fragments updated incoming resumed /\
        task_stack_key incoming = task_stack_key original.(os_sched_call_stack) /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored, armv7a_task_restore_transition task_abi outgoing selected installed restored ->
          os_sched_source_switch_execution external platform port abi task_abi sg state outgoing old_sp cpsr
            registers lr saved incoming selected checkpoint restored /\
          (os_sched_source_selected_post external platform port abi sg focus incoming selected current
             (os_sched_install_context outgoing fragments incoming updated) ** unmap_table_rep sg ** frame) restored /\
          (forall cursor final_cursor acquired after,
            cursor.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
            cursor.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
            cursor.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
            interrupt_saved_value (armv7a_irq_fiq_mask cursor.(kernel_save_cpsr)) cursor.(kernel_save_r0) ->
            armv7a_save_suffix_transition save_suffix cursor
              (os_sched_install_context outgoing fragments incoming updated) restored final_cursor acquired after ->
            let returned := armv7a_continuation_resumed_call selected original in
            acquired = os_sched_install_context outgoing fragments incoming updated /\
            selected.(armv7a_continuation_pc) = armv7a_save_entry_address save_suffix + 4 /\
            final_cursor.(kernel_save_return_word) = Some original_lr /\
            final_cursor.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 /\
            kernel_save_after_mrs_execution arch cursor
              (os_sched_install_context outgoing fragments incoming updated) restored final_cursor acquired after /\
            sem_pend_task_call_stage sg returned acquired /\
            task_stack_live_coverage acquired.(TskState) (Some (task_stack_key returned.(os_sched_call_stack))) /\
            acquired.(EventState) = entry.(EventState) /\
            (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
               returned.(os_sched_call_origin) final_cursor.(kernel_save_r0) acquired **
             os_sched_context_resources external returned ** UCOS2_inv sg acquired **
             armv7a_task_call_stacks abi acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks) **
             unmap_table_rep sg ** frame) after /\
            (forall eid event, mutex_query_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
              (coq_prop (UCOS2_state_inv sg acquired /\ mutex_query_lookup acquired eid event /\
                0 <= encode_event_cnt_value event <= 65535 /\
                (encode_event_cnt_value event = 0 -> event_object_layout_prop sg eid ->
                  exists node, sem_pend_wait_entry sg acquired eid event
                    returned.(os_sched_call_stack).(stackLeaseSlot) node /\
                    kernel_call_task_source returned acquired /\
                    sched_current_consistency acquired.(TskState) acquired.(SchedState))) &&
               (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
                  returned.(os_sched_call_origin) final_cursor.(kernel_save_r0) acquired **
                os_sched_context_resources external returned **
                (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event **
                sem_post_count_frame sg acquired eid event **
                armv7a_task_call_stacks abi acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks) **
                (unmap_table_rep sg ** frame))) after)))).
Proof.
  intros external platform port critical arch abi task_abi initial save_suffix
    sg entry outgoing node old_sp cpsr registers lr prefix suffix first old_words
    original original_lr publication tail frame before focus state fragments saved updated
    Horigin Hactive Hfields Hhead Hswitch Hinput Hpre.
  assert (Hnonempty : entry.(SchedState).(readyList) <> []) by (rewrite Hhead; discriminate).
  destruct (os_sched_source_switch_prefix_resources external platform port abi sg entry outgoing focus
    frame before Hswitch Hnonempty Hpre) as [checkpoint [Hprefix [Hhigh Hcheckpoint]]].
  fold state in Hhigh, Hcheckpoint.
  assert (Hnode : state.(TskState).(inUsedTaskStates) outgoing.(os_sched_call_stack).(stackLeaseSlot) = Some node)
    by exact (proj1 (proj2 Hinput)).
  assert (Hselection : os_sched_selection_enabled entry = true)
    by exact (proj1 (proj1 (os_sched_requests_switch_iff entry) Hswitch)).
  assert (Hrunning : state.(SchedState).(isRunning) = entry.(SchedState).(isRunning)).
  { unfold state, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Hselection, Hswitch; reflexivity. }
  assert (Hready_list : state.(SchedState).(readyList) = entry.(SchedState).(readyList)).
  { unfold state, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Hselection, Hswitch; reflexivity. }
  assert (Hfields_state : sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) state).
  { destruct Hfields as [Hr Hnodes]; split; [rewrite Hrunning; exact Hr|exact Hnodes]. }
  assert (Hfields_updated : sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) updated).
  { eapply sem_pend_save_current_sp_preserves_call_fields; [exact Hnode|exact Hfields_state]. }
  assert (Hactive_updated : task_invocation_active updated.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive]. }
  assert (Hselected_slot : updated.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    change (state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot)).
    unfold sched_high_ready_consistency in Hhigh; rewrite Hready_list, Hhead in Hhigh; exact (proj1 Hhigh). }
  assert (Hswitch_pre : (os_sched_source_switch_pre external platform port abi sg outgoing focus state **
    (unmap_table_rep sg ** frame)) checkpoint).
  { match type of Hcheckpoint with ?P checkpoint => assert (Horder : P |--
      os_sched_source_switch_pre external platform port abi sg outgoing focus state **
      (unmap_table_rep sg ** frame)) by entailer! end; exact (Horder checkpoint Hcheckpoint). }
  destruct (os_sched_source_live_switch_destination_resources external platform port abi task_abi initial
    sg state node outgoing old_sp cpsr registers lr prefix suffix first old_words focus publication
    (unmap_table_rep sg ** frame) checkpoint Hinput Hswitch_pre)
    as [written [stored [Hwrites [Hload [Hstore Hcapture]]]]].
  fold fragments saved updated in Hstore, Hcapture.
  exists checkpoint, written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
  split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  destruct (Hcapture captured hooked Hcaptured Hhook_heap Hhook_step)
    as [incoming [resumed [installed [selected [current [Hsave [Hdestination [Hfragments
      [Hinstall [Hreads [Hpending Hrestore]]]]]]]]]]].
  assert (Hkey : task_stack_key incoming = task_stack_key original.(os_sched_call_stack)).
  { destruct Hdestination as [Hselected [[found [Hfound [Hgeneration Hrest]]] Hremaining]].
    assert (Hslot : incoming.(stackLeaseSlot) = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
    pose proof (proj2 (proj2 Hactive_updated)) as Hlive.
    rewrite Horigin in Hlive; destruct Hlive as [observed [Hobserved Hg]].
    rewrite Hslot in Hfound; assert (found = observed) by congruence; subst found.
    unfold task_stack_key; f_equal; [exact Hslot|congruence]. }
  assert (Hactive_installed : task_invocation_active
    (os_sched_install_context outgoing fragments incoming updated).(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)) by exact Hactive_updated.
  assert (Hfields_installed : sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot)
    (os_sched_install_context outgoing fragments incoming updated)) by exact Hfields_updated.
  exists incoming, resumed, installed, selected, current.
  split; [exact Hdestination|]. split; [exact Hkey|]. split; [exact Hfragments|].
  split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored Hrun; destruct (Hrestore restored Hrun) as [Hexecution [Hrestored_source Hrestored]].
  assert (Hselected : (os_sched_source_selected_post external platform port abi sg focus incoming selected current
    (os_sched_install_context outgoing fragments incoming updated) ** unmap_table_rep sg ** frame) restored).
  { match type of Hrestored with ?P restored => assert (Horder : P |--
      os_sched_source_selected_post external platform port abi sg focus incoming selected current
        (os_sched_install_context outgoing fragments incoming updated) ** unmap_table_rep sg ** frame)
      by entailer! end; exact (Horder restored Hrestored). }
  split; [exact Hexecution|]. split; [exact Hselected|].
  intros cursor final_cursor acquired after Hcpsr Hr0 Hlr Hsaved Hsuffix returned.
  pose proof (sem_pend_selected_source_save_return external platform port critical arch abi save_suffix
    sg original original_lr incoming selected current (os_sched_install_context outgoing fragments incoming updated)
    cursor restored final_cursor acquired after (unmap_table_rep sg ** frame)
    Horigin Hactive_installed Hfields_installed Hkey Hcpsr Hr0 Hlr Hsaved Hrestored Hsuffix) as Hreturn.
  destruct Hreturn as [Hacquired [Hpc [Hword [Hvalue [Hsave_source [Hstage [Hcoverage Howned]]]]]]].
  fold returned focus in Howned, Hstage, Hcoverage.
  split; [exact Hacquired|]. split; [exact Hpc|]. split; [exact Hword|]. split; [exact Hvalue|].
  split; [exact Hsave_source|]. split; [exact Hstage|]. split; [exact Hcoverage|].
  assert (Hevents : acquired.(EventState) = entry.(EventState)).
  { rewrite Hacquired; unfold os_sched_install_context, updated, os_sched_save_current_sp.
    rewrite Hnode; reflexivity. }
  split; [exact Hevents|]. split.
  - match type of Howned with ?P after => assert (Horder : P |--
      critical_region_masked platform critical sg returned.(os_sched_call_invocation)
        returned.(os_sched_call_origin) final_cursor.(kernel_save_r0) acquired **
      os_sched_context_resources external returned ** UCOS2_inv sg acquired **
      armv7a_task_call_stacks abi acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks) **
      unmap_table_rep sg ** frame) by entailer! end.
    exact (Horder after Howned).
  - intros eid event Hlookup Htype.
    exact (sem_pend_selected_acquire_count_resources external platform port critical abi sg returned focus
      final_cursor.(kernel_save_r0) entry acquired eid event (unmap_table_rep sg ** frame)
      Hevents Hlookup Htype Hstage after Howned).
Qed.
