Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_status Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The LAST task-level selection of an interrupted first-Save caller.
    Source clients must already have transported its live invocation and
    non-Idle/no-registration fields to the actual post-hook cut. They do
    not supply current or ready there: another task can be executing.

    Those two missing facts are established by the actual selector and
    current-cache writes. The focused strong entry, not an equal TCB key
    alone, supplies the original invocation/PC/LR and running authority.
    This is an end-of-transfer consumer; it is not a proof of the earlier
    handler/client prefix, of arbitrary hooks, or of the whole Save call. *)
Lemma sem_pend_task_restore_call_stage : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg outgoing_call outgoing hooked original pc lr (frame : Assertion) heap,
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  hooked.(SchedState).(isRunning) = true ->
  (forall node, hooked.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(curPrio) <> sg.(osLowestPrio) /\ node.(eventPtr) = None /\
    node.(eventMultiWaitEvents) = [] /\ node.(tcbFlagNode) = 0) ->
  os_sched_saved_stack_binding outgoing_call outgoing hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  (forall slot node, hooked.(TskState).(inUsedTaskStates) slot = Some node ->
    tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key outgoing_call.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep outgoing_call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) (armv7a_call_focus original pc lr)
     (task_stack_key outgoing_call.(os_sched_call_stack))
     (outgoing_call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) (armv7a_call_focus original pc lr)
     hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi outgoing_call ** frame)) heap ->
  exists incoming installed selected,
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = incoming /\
    (forall restored,
      armv7a_task_restore_transition task_abi outgoing_call selected installed restored ->
      task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
      let resumed := armv7a_continuation_resumed_call selected original in
      let state := os_sched_install_context outgoing_call outgoing incoming hooked in
      selected.(armv7a_continuation_call) = Some original /\
      selected.(armv7a_continuation_pc) = pc /\ selected.(armv7a_continuation_lr) = lr /\
      sem_pend_task_call_stage sg resumed state /\
      task_stack_live_coverage state.(TskState) (Some (task_stack_key resumed.(os_sched_call_stack))) /\
      (kernel_call_execution_owned external platform resumed
         (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
       UCOS2_inv sg state **
       armv7a_task_call_stacks abi state.(TskState) (armv7a_call_focus original pc lr)
         state.(TskState).(parkedTaskStacks) ** frame) restored).
Proof.
  intros external platform port abi task_abi initial sg outgoing_call outgoing hooked original pc lr
    frame heap Horigin Hactive Hrunning Hfields Hsaved Hhigh Hnonempty Haddress Hcoverage Hpre.
  destruct (armv7a_task_restore_selected_call external platform port abi task_abi initial
    sg outgoing_call outgoing hooked (armv7a_call_focus original pc lr) frame heap
    Hsaved Hhigh Hnonempty Haddress Hcoverage Hpre)
    as [incoming [installed [selected [node [Hrun [Hlease [Hfocus [Hready [Hgen
      [Hcovered [Hother Hrestore]]]]]]]]]]].
  exists incoming, installed, selected; split; [exact Hrun|]. split; [exact Hlease|].
  intros restored Hrun_restore Hkey; cbv zeta.
  destruct (Hrestore restored Hrun_restore) as [Hmemory [Hsource [Hexecution Hfocused]]].
  pose proof (Hfocus Hkey) as Hbinding.
  destruct Hbinding as [Hcall [Hpc Hlr]].
  assert (Hslot : incoming.(stackLeaseSlot) = original.(os_sched_call_stack).(stackLeaseSlot))
    by (exact (f_equal fst Hkey)).
  assert (Hgeneration : incoming.(stackLeaseGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration))
    by (exact (f_equal snd Hkey)).
  assert (Hnode : hooked.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { rewrite <- Hslot; exact (proj1 Hready). }
  assert (Hstage : sem_pend_task_call_stage sg (armv7a_continuation_resumed_call selected original)
    (os_sched_install_context outgoing_call outgoing incoming hooked)).
  { unfold sem_pend_task_call_stage, kernel_call_task_source.
    cbn [armv7a_continuation_resumed_call os_sched_call_origin os_sched_call_invocation os_sched_call_stack].
    rewrite Hlease.
    split.
    - split; [rewrite Hslot, Hgeneration; exact Horigin|]. split; [exact Hactive|].
      unfold task_execution_current; rewrite Horigin, <- Hslot; exact (proj1 (proj2 Hready)).
    - split; [exact Hrunning|]. exists node; split; [exact Hready|].
      split; [exact Hgen|exact (Hfields node Hnode)]. }
  split; [exact Hcall|]. split; [exact Hpc|]. split; [exact Hlr|]. split; [exact Hstage|]. split.
  - cbn [armv7a_continuation_resumed_call os_sched_call_stack]; rewrite Hlease; exact Hcovered.
  - exact (Hfocused Hkey).
Qed.

(** The prefix, unlike the cleanup tail, owns Dly as its third mutable
    cell. Split the actual current TCB and keep all other modules and
    TCB fields in the existing prefix residual. *)
Lemma sem_pend_wait_prefix_split : forall sg state tid old,
  UCOS2_state_inv sg state -> state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_inv sg state |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some old.(dly)) **
  sem_pend_prefix_frame sg state tid old.
Proof.
  intros * Hvalid Hcurrent Hnode.
  sep_apply_l_atomic (sem_pend_full_task_split sg state tid old Hvalid Hnode).
  sep_apply_l_atomic (sem_pend_tcb_three_fields_split (task_slot_addr sg tid)
    (task_tcb64_image sg old) TCBDly ltac:(discriminate) ltac:(discriminate)).
  unfold sem_pend_full_task_frame, sem_pend_prefix_frame, sem_pend_sched_without_current,
    sched_raw_rep, sched_physical_rep.
  cbn [task_tcb64_image]; rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

(** This is the source-facing zero-count consumer. Its inputs are exactly
    the observations produced with the protected count cell; the Save
    history is deliberately not used to manufacture a flat interval. *)
Lemma sem_pend_acquired_wait_prefix : forall sg context entry eid current,
  sem_pend_task_call_stage sg context entry ->
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  encode_event_cnt_value current = 0 -> event_object_layout_prop sg eid ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
    sem_post_count_frame sg entry eid current |--
  EX node,
    coq_prop (sem_pend_wait_entry sg entry eid current context.(os_sched_call_stack).(stackLeaseSlot) node /\
      context.(os_sched_call_origin) = RunningInvocation
        context.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration) /\
      kernel_call_task_source context entry /\
      sched_current_consistency entry.(TskState) entry.(SchedState) /\
      0 <= encode_task_status node.(stat) <= 255) &&
    (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
       TCBStat (Some (encode_task_status node.(stat))) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
       TCBStatPend (Some (encode_pend_status node.(statPend))) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) TCBDly (Some node.(dly)) **
     sem_pend_prefix_frame sg entry context.(os_sched_call_stack).(stackLeaseSlot) node).
Proof.
  intros sg context entry eid current Hstage Hvalid Hlookup Htype Hzero Hlayout.
  destruct (sem_pend_task_stage_wait_entry sg context entry eid current
    Hstage Hvalid Hlookup Htype Hzero Hlayout) as [node [Hentry [Horigin [Hsource Hcache]]]].
  pose proof Hentry as [_ [_ [Hcurrent [Hnode _]]]].
  sep_apply_l_atomic (sem_pend_count_merge_unchanged sg entry eid current Hvalid Hlookup Htype).
  sep_apply_l_atomic (sem_pend_wait_prefix_split sg entry context.(os_sched_call_stack).(stackLeaseSlot)
    node Hvalid Hcurrent Hnode).
  pose proof (encode_task_status_in_range node.(stat)) as Hrange.
  Exists node; entailer!; unfold task.encode_task_status; lia.
Qed.

(** The older annotation additionally frames its first-acquisition
    relation into wait_origin. The literal field split is the same
    source-facing consumer, not a second proof relying on that history. *)
Lemma sem_pend_acquired_task_wait_prefix : forall critical sg context mask saved
  before observed entry eid current,
  sem_pend_task_call_stage sg context entry ->
  sem_query_acquire_facts critical sg context.(os_sched_call_invocation) eid mask saved
    before entry observed current ->
  encode_event_cnt_value current = 0 -> event_object_layout_prop sg eid ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
    sem_post_count_frame sg entry eid current |--
  EX node,
    coq_prop (sem_pend_wait_origin critical sg context mask saved before observed entry eid current
      context.(os_sched_call_stack).(stackLeaseSlot) node /\
      0 <= encode_task_status node.(stat) <= 255) &&
    (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
       TCBStat (Some (encode_task_status node.(stat))) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
       TCBStatPend (Some (encode_pend_status node.(statPend))) **
     tcb_cell (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) TCBDly (Some node.(dly)) **
     sem_pend_prefix_frame sg entry context.(os_sched_call_stack).(stackLeaseSlot) node).
Proof.
  intros critical sg context mask saved before observed entry eid current Hstage Hacquire Hzero Hlayout.
  pose proof Hacquire as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  sep_apply_l_atomic (sem_pend_acquired_wait_prefix sg context entry eid current
    Hstage Hvalid Hlookup Htype Hzero Hlayout).
  Intros node; Exists node; unfold sem_pend_wait_origin; entailer!.
Qed.

(** Waiting preserves the current invocation and priority cache, not its
    ready bit. These facts depend on the acquired entry, not on a flat
    trace from the public call's earlier pre-Save snapshot. *)
Lemma sem_pend_wait_preserves_call_source : forall sg context entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  let waiting := event_pend_state sg entry eid current tid old PendSem timeout in
  UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
  sched_current_consistency waiting.(TskState) waiting.(SchedState).
Proof.
  intros sg context entry eid current tid old timeout Hentry Hsource Hcache waiting.
  pose proof Hentry as [_ [_ [Hcurrent [Hnode _]]]].
  split; [apply sem_pend_wait_entry_preserves_validity; exact Hentry|].
  split.
  - destruct Hsource as [Hlease [Hactive Hcur]].
    split; [exact Hlease|]. split.
    + unfold waiting; cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState].
      eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Hnode|reflexivity|exact Hactive].
    + exact Hcur.
  - unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
    destruct Hcache as [node [Hlookup Hpriority]].
    assert (node = old) by congruence; subst node.
    unfold sched_current_consistency.
    change (match entry.(SchedState).(curTaskID) with
      | None => entry.(SchedState).(curSchedPrio) = None
      | Some selected => exists node,
          (if Z.eqb selected tid then
             Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
           else entry.(TskState).(inUsedTaskStates) selected) = Some node /\
          entry.(SchedState).(curSchedPrio) = Some node.(curPrio)
      end).
    rewrite Hcurrent; exists (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)).
    split; [rewrite Z.eqb_refl; reflexivity|exact Hpriority].
Qed.

(** The actual OS_EventTaskWait return reconstructs the SAME masked
    world. The outer Save history can be retained by its caller without
    being collapsed to a critical_region_interval. *)
Lemma sem_pend_wait_call_stack_merge_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  critical sg active context saved entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  task_stack_live_coverage entry.(TskState) active ->
  critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved entry ** os_sched_context_resources external context **
  sem_pend_wait_call_post sg entry eid current tid old timeout **
  armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) |--
  coq_prop (let waiting := event_pend_state sg entry eid current tid old PendSem timeout in
    UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
    sched_current_consistency waiting.(TskState) waiting.(SchedState)) &&
  kernel_stack_call_masked abi UCOS2_inv critical sg active context saved entry
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros external platform port abi critical sg active context saved entry
    eid current tid old timeout Hentry Hsource Hcache Hcoverage.
  pose proof Hentry as [_ [_ [_ [Hold _]]]].
  set (waiting := event_pend_state sg entry eid current tid old PendSem timeout).
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
  assert (Hcovered : task_stack_live_coverage waiting.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := entry.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; auto. }
  assert (Hstacks : armv7a_task_stack_continuations abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi waiting.(TskState) waiting.(TskState).(parkedTaskStacks)).
  { change (armv7a_task_stack_continuations abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi waiting.(TskState) entry.(TskState).(parkedTaskStacks)).
    apply armv7a_task_stack_continuations_reindex.
    intros key payload node Hpayload Hnode Hgen; apply Hnodes; exact Hnode. }
  pose proof (sem_pend_wait_preserves_call_source sg context entry eid current tid old timeout
    Hentry Hsource Hcache) as Hwaiting.
  sep_apply_l_atomic (sem_pend_wait_call_merge sg entry eid current tid old timeout Hentry).
  sep_apply_l_atomic Hstacks.
  unfold kernel_stack_call_masked, kernel_stack_inv; fold waiting; entailer!.
Qed.

(** Legacy annotation projection. Its historical acquisition relation is
    not used to establish any write effect or reconstruct stack ownership. *)
Lemma sem_pend_wait_call_stack_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  critical sg active context mask saved before observed entry eid current tid old timeout,
  sem_pend_wait_origin critical sg context mask saved before observed entry eid current tid old ->
  task_stack_live_coverage entry.(TskState) active ->
  critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved entry ** os_sched_context_resources external context **
  sem_pend_wait_call_post sg entry eid current tid old timeout **
  armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) |--
  coq_prop (sem_pend_wait_history critical sg context mask before observed eid timeout
    (event_pend_state sg entry eid current tid old PendSem timeout)) &&
  kernel_stack_call_masked abi UCOS2_inv critical sg active context saved entry
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros external platform port abi critical sg active context mask saved before observed entry
    eid current tid old timeout Horigin Hcoverage.
  pose proof Horigin as [_ [Hentry [_ [Hsource Hcache]]]].
  pose proof (sem_pend_wait_origin_history critical sg context mask saved before observed entry
    eid current tid old timeout Horigin) as Hhistory.
  sep_apply_l_atomic (sem_pend_wait_call_stack_merge_source external platform port abi critical sg active
    context saved entry eid current tid old timeout Hentry Hsource Hcache Hcoverage).
  entailer!.
Qed.

(** A concrete foreign TaskCreate publication during this wait. The
    published slot is private, hence cannot replace the live waiter;
    updating the previous list head changes only its links. Consume the
    actual publication storage producer and retain the wait observation
    in its new strong runtime world. This does not classify arbitrary
    registered clients or assert that the active-list order is unchanged. *)
Lemma sem_pend_task_publication_stack_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg publication entry active tid old eid generation,
  UCOS2_state_inv sg entry -> task_create_stack_publication_input sg publication entry ->
  task_stack_live_coverage entry.(TskState) active ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  let after := task_create_stack_publication_state sg publication entry in
  task_create_publication_storage sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_acquired)
    entry publication.(stack_publication_slot) publication.(stack_publication_image) **
  task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
  armv7a_task_stack_continuations abi entry.(TskState) entry.(TskState).(parkedTaskStacks) |--
  EX current,
    coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg entry after /\
      after.(TskState).(inUsedTaskStates) tid = Some current /\
      sem_pend_wait_continuation eid generation current) &&
    kernel_stack_inv abi UCOS2_inv sg active after.
Proof.
  intros external platform port abi sg publication entry active tid old eid generation
    Hvalid Hinput Hcoverage Hold Hwait after.
  pose proof Hinput as [_ [_ [Hcommit _]]].
  set (args := task_create_stack_publication_args publication).
  set (published := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity entry.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) published).
  { apply task_tcb_init_commit_binding_identity with
      (origin := publication.(stack_publication_origin)); exact Hcommit. }
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  destruct (task_private_excludes_public sg entry.(TskState) published.(taskID)
    (proj1 (proj1 (proj2 Hvalid))) Hprivate) as [Hnone Hfree].
  destruct (task_commit_transports_old_fields entry.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) published tid old Hnone Hold)
    as [current [Hcurrent Hfields]].
  assert (Hwaitfields : sem_pend_wait_fields_equal old current).
  { unfold sem_pend_wait_fields_equal.
    repeat split; match goal with |- ?field current = ?field old =>
      exact (f_equal field Hfields) end. }
  pose proof (sem_pend_wait_fields_equal_preserves_continuation eid generation old current
    Hwaitfields Hwait) as Hwaiting.
  assert (Hlookup : after.(TskState).(inUsedTaskStates) tid = Some current) by exact Hcurrent.
  pose proof (task_create_publication_covered_stack_merge external platform port abi
    sg publication entry active Hvalid Hinput Hcoverage) as Hmerge.
  cbv zeta in Hmerge; eapply derivable1_trans; [exact Hmerge|]; Intros.
  Exists current; unfold kernel_stack_inv; entailer!.
Qed.

(** The exact source-return cut of SECOND Save. Keeping returned/acquired
    explicit allows the selector's observations to refer to this SAME
    world, before the public existential post hides those witnesses. *)
Lemma sem_pend_save_stack_cleanup_cells : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  critical sg active original returned mask saved before acquired,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  kernel_call_save_source external port critical sg original returned mask saved before acquired ->
  kernel_stack_call_masked abi UCOS2_inv critical sg active returned saved acquired acquired |--
  EX node,
    coq_prop (kernel_call_task_source returned acquired /\
      task_stack_live_coverage acquired.(TskState) active /\
      acquired.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
      node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration)) &&
    (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBStat (Some (encode_task_status node.(stat))) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBStatPend (Some (encode_pend_status node.(statPend))) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
     sem_pend_cleanup_frame sg acquired returned.(os_sched_call_stack).(stackLeaseSlot) node **
     armv7a_task_stack_continuations abi acquired.(TskState) acquired.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi critical sg active original returned mask saved before acquired
    Hvalid Hcaller Hsource.
  unfold kernel_stack_call_masked, kernel_stack_inv; Intros.
  pose proof (kernel_call_save_source_preserves_task_source external port critical sg original returned
    mask saved before acquired Hvalid Hcaller Hsource) as Hreturned.
  destruct (kernel_call_task_source_current_at returned acquired Hreturned) as [Hcurrent [node [Hnode Hgen]]].
  unfold UCOS2_inv at 1; Intros.
  assert (Hacquired : UCOS2_state_inv sg acquired) by assumption.
  assert (Hsplit : UCOS2_raw_rep sg acquired |--
    sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot) **
    tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
      TCBStat (Some (encode_task_status node.(stat))) **
    tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
      TCBStatPend (Some (encode_pend_status node.(statPend))) **
    tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
      TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
    sem_pend_cleanup_frame sg acquired returned.(os_sched_call_stack).(stackLeaseSlot) node).
  { eapply derivable1_trans; [|apply sem_pend_cleanup_split; eassumption].
    unfold UCOS2_inv; entailer!. }
  sep_apply_l_atomic Hsplit.
  Exists node; entailer!.
Qed.

(** Consumer of the common source-bound SECOND Save post. Its exact
    source-cut consumer above is also used by concrete source suffixes;
    opening this existential post never invents readiness/registration or
    identifies its hidden world with an unrelated source endpoint. *)
Lemma sem_pend_save_stack_cleanup_split : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  critical sg active original mask saved before,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  kernel_stack_call_save_post abi UCOS2_inv critical sg active original mask saved before |--
  EX returned acquired node,
    coq_prop (kernel_call_save_source external port critical sg original returned mask saved before acquired /\
      kernel_call_task_source returned acquired /\
      task_stack_live_coverage acquired.(TskState) active /\
      acquired.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
      node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration)) &&
    (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBStat (Some (encode_task_status node.(stat))) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBStatPend (Some (encode_pend_status node.(statPend))) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
     sem_pend_cleanup_frame sg acquired returned.(os_sched_call_stack).(stackLeaseSlot) node **
     armv7a_task_stack_continuations abi acquired.(TskState) acquired.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi critical sg active original mask saved before Hvalid Hcaller.
  unfold kernel_stack_call_save_post; Intros returned acquired.
  assert (Hsource : kernel_call_save_source external port critical sg original returned mask saved before acquired)
    by assumption.
  sep_apply_l_atomic (sem_pend_save_stack_cleanup_cells external platform port abi critical sg active
    original returned mask saved before acquired Hvalid Hcaller Hsource); Intros node.
  Exists returned acquired node; entailer!.
Qed.

(** Finish the actual post-MRS Save after the last TASK-level restore.
    The focused PC is the real CPSID address; R0/LR/CPSR are joined to the
    frame just consumed. The suffix changes CPU/CSL resources, not the OS
    state or kernel bytes, and retains the current whole stack map. This
    does not equate the pre-interruption snapshot with the acquired state. *)
Lemma sem_pend_task_selected_save_return : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg outgoing_call outgoing hooked original lr (frame : Assertion) heap,
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  hooked.(SchedState).(isRunning) = true ->
  (forall node, hooked.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    node.(curPrio) <> sg.(osLowestPrio) /\ node.(eventPtr) = None /\
    node.(eventMultiWaitEvents) = [] /\ node.(tcbFlagNode) = 0) ->
  os_sched_saved_stack_binding outgoing_call outgoing hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  (forall slot node, hooked.(TskState).(inUsedTaskStates) slot = Some node ->
    tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key outgoing_call.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep outgoing_call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState)
     (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
     (task_stack_key outgoing_call.(os_sched_call_stack))
     (outgoing_call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState)
     (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
     hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi outgoing_call ** frame)) heap ->
  exists incoming installed selected,
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = incoming /\
    (forall restored registers final_registers acquired after,
      armv7a_task_restore_transition task_abi outgoing_call selected installed restored ->
      task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
      armv7a_save_suffix_transition suffix registers
        (os_sched_install_context outgoing_call outgoing incoming hooked) restored final_registers acquired after ->
      let returned := armv7a_continuation_resumed_call selected original in
      acquired = os_sched_install_context outgoing_call outgoing incoming hooked /\
      selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
      final_registers.(kernel_save_return_word) = Some lr /\
      final_registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 /\
      kernel_save_after_mrs_execution arch registers
        (os_sched_install_context outgoing_call outgoing incoming hooked) restored final_registers acquired after /\
      sem_pend_task_call_stage sg returned acquired /\
      task_stack_live_coverage acquired.(TskState) (Some (task_stack_key returned.(os_sched_call_stack))) /\
      (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
         returned.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
       os_sched_context_resources external returned ** UCOS2_inv sg acquired **
       armv7a_task_call_stacks abi acquired.(TskState)
         (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
         acquired.(TskState).(parkedTaskStacks) ** frame) after).
Proof.
  intros external platform port critical arch abi task_abi initial suffix sg outgoing_call outgoing
    hooked original lr frame heap Horigin Hactive Hrunning Hfields Hsaved Hhigh Hnonempty Haddress Hcoverage Hpre.
  destruct (sem_pend_task_restore_call_stage external platform port abi task_abi initial sg outgoing_call
    outgoing hooked original (armv7a_save_entry_address suffix + 4) lr frame heap Horigin Hactive Hrunning
    Hfields Hsaved Hhigh Hnonempty Haddress Hcoverage Hpre)
    as [incoming [installed [selected [Hinstall [Hlease Hrestore]]]]].
  exists incoming, installed, selected; split; [exact Hinstall|]. split; [exact Hlease|].
  intros restored registers final_registers acquired after Hrun_restore Hkey Hcpsr Hr0 Hlr Hsaved_value Hsuffix;
    cbv zeta.
  destruct (Hrestore restored Hrun_restore Hkey)
    as [Hcall [Hpc [Hreturn_lr [Hstage [Hcovered Howned]]]]].
  set (state := os_sched_install_context outgoing_call outgoing incoming hooked) in *.
  set (returned := armv7a_continuation_resumed_call selected original) in *.
  match type of Howned with ?P restored =>
    assert (Horder : P |-- kernel_call_execution_owned external platform returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
      (UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState)
        (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
        state.(TskState).(parkedTaskStacks) ** frame))
  end.
  { rewrite Hcpsr; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg returned
    registers state restored final_registers acquired after _ Hsaved_value (Horder restored Howned) Hsuffix)
    as [Hstate [Hmemory [Hreturn [Hvalue Hpost]]]].
  subst acquired; split; [reflexivity|]. split; [exact Hpc|]. split.
  - rewrite Hreturn, Hlr, Hreturn_lr; reflexivity.
  - split; [rewrite Hvalue; exact Hr0|]. split.
    + exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hsuffix).
    + split; [exact Hstage|]. split; [exact Hcovered|].
      match type of Hpost with ?P after =>
        assert (Hclose : P |-- critical_region_masked platform critical sg returned.(os_sched_call_invocation)
          returned.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
          os_sched_context_resources external returned ** UCOS2_inv sg state **
          armv7a_task_call_stacks abi state.(TskState)
            (armv7a_call_focus original (armv7a_save_entry_address suffix + 4) lr)
            state.(TskState).(parkedTaskStacks) ** frame)
      end.
      { entailer!. }
      exact (Hclose after Hpost).
Qed.

Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.

(** The current C caller retains the same descriptor-local resources
    across its actual OS_EventTaskWait post. The legacy stack lemma above
    remains an empty-local compatibility interface. *)
Lemma sem_pend_wait_call_continuation_merge_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local
  critical sg active context saved entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  kernel_call_task_source context entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  task_stack_live_coverage entry.(TskState) active ->
  critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved entry ** os_sched_context_resources external context **
  sem_pend_wait_call_post sg entry eid current tid old timeout **
  store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local) entry.(TskState).(parkedTaskStacks) |--
  coq_prop (let waiting := event_pend_state sg entry eid current tid old PendSem timeout in
    UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
    sched_current_consistency waiting.(TskState) waiting.(SchedState)) &&
  kernel_continuation_call_masked abi UCOS2_inv local critical sg active context saved entry
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros external platform port abi local critical sg active context saved entry
    eid current tid old timeout Hentry Hsource Hcache Hcoverage.
  pose proof Hentry as [_ [_ [_ [Hold _]]]].
  set (waiting := event_pend_state sg entry eid current tid old PendSem timeout).
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
  assert (Hcovered : task_stack_live_coverage waiting.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := entry.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; auto. }
  assert (Hstacks : store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi waiting.(TskState) local) waiting.(TskState).(parkedTaskStacks)).
  { change (store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi waiting.(TskState) local) entry.(TskState).(parkedTaskStacks)).
    apply kernel_saved_continuation_map_reindex.
    intros key payload node Hpayload Hnode Hgen; apply Hnodes; exact Hnode. }
  pose proof (sem_pend_wait_preserves_call_source sg context entry eid current tid old timeout
    Hentry Hsource Hcache) as Hwaiting.
  sep_apply_l_atomic (sem_pend_wait_call_merge sg entry eid current tid old timeout Hentry).
  sep_apply_l_atomic Hstacks.
  unfold kernel_continuation_call_masked, kernel_continuation_inv; fold waiting; entailer!.
Qed.
