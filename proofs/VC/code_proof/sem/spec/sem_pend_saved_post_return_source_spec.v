Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_wake_selection_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_post_wait_history_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Import KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Current and ready are facts from the actual selector/install, while
    registration comes from the SAME old wait's source history. Neither
    component alone establishes the resumed Pend branch. *)
Lemma sem_pend_wait_selected_from_ready_current : forall environment critical sg original mask initial
  observed eid timeout waiting call current,
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call current ->
  UCOS2_state_inv sg current ->
  current.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  In original.(os_sched_call_stack).(stackLeaseSlot) current.(SchedState).(readyList) ->
  sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call current.
Proof.
  intros * Hwait Hvalid Hcurrent Hmember; split; [exact Hwait|].
  destruct Hwait as [owned [Howned [Hsame [Hinitial Hpath]]]].
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hinitial)
    as [first [Hfirst Hcontinuation]].
  destruct (sem_pend_wait_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath
    first Hfirst Hcontinuation) as [last [Hlast Hlast_wait]].
  pose proof Hvalid as [_ [_ [[Hready _] _]]].
  destruct (proj1 Hready _ Hmember) as [node [Hnode [Hpriority Heffective]]].
  assert (node = last) by congruence; subst node.
  destruct (sem_pend_wait_ready_resume_registration _ _ _ Hlast_wait Heffective)
    as [Hregistration Hgeneration].
  exists last; unfold sem_pend_resume_entry; auto.
Qed.

(** The present-state highest, unsuspended Post-waiter family. The input
    is the real EventTaskRdy return cut with an EXACT parked saved-call
    entry, previously produced by Save/capture/park. The old original
    saved-token/inside pair is not supplied as a separate frame premise.

    EventTaskRdy/Post -> real C selector -> physical switch/install/take
    recovers that pair. The same wait history then reaches OS_Sched's own
    Restore, SemPend's second Save, existing result/cleanup and public
    post on one heap sequence. No eventual selection premise or fresh
    platform law is introduced. Other priorities/suspension/IRQ paths
    and production of this earlier EventTaskRdy/exact-map cut remain
    their own source families; this is not full API coverage. *)
Lemma sem_pend_saved_post_public_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg entry eid event tid old priority context node poster_saved call saved acquired descriptor focus
  old_sp cpsr values lr prefix suffix first old_words publication before (frame : Assertion)
  cursor restore_written middle final_cursor released registers final_registers next_acquired saved_heap
  public_call mask initial observed pevent timeout waiting perr X,
  let abi := environment.(task_stack_call_continuations) in
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  let selected := os_sched_prefix_state checkpoint in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let outgoing := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp selected context.(os_sched_call_stack).(stackLeaseSlot)
    outgoing.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments call.(os_sched_call_stack) updated in
  let returned := kernel_selected_call descriptor current in
  let retained := interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
    critical_region_inside critical sg context.(os_sched_call_invocation) checkpoint ** frame in
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  interrupt_saved_value mask saved ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (Some environment) critical sg public_call pevent timeout))
      sem_query_observe_error) X ->
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    waiting call entry ->
  critical.(critical_region_clients) (sem_pend_post_source_client context.(os_sched_call_invocation) eid) ->
  context.(os_sched_call_invocation) <> public_call.(os_sched_call_invocation) ->
  sem_post_group entry event <> 0 ->
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  task_status_is_suspended
    (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)) = false ->
  (forall slot ready, In slot entry.(SchedState).(readyList) ->
    entry.(TskState).(inUsedTaskStates) slot = Some ready -> old.(curPrio) < ready.(curPrio)) ->
  sched_current_ready_at entry.(TskState) entry.(SchedState) context.(os_sched_call_stack).(stackLeaseSlot) node ->
  entry.(IntrState).(intNesting) = 0 -> entry.(IntrState).(lockNesting) = 0 ->
  tid = call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  node.(taskID) = context.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  (task_stack_key context.(os_sched_call_stack) = armv7a_call_focus_key focus ->
    focus = armv7a_call_focus context lr lr) ->
  context.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region context.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    context.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range context.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened entry.(TskState) publication
    context.(os_sched_call_stack).(stackLeaseSlot) context.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) poster_saved entry **
   os_sched_context_resources environment.(task_stack_call_external) context **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
     entry.(TskState).(parkedTaskStacks) ** (perr # UChar |->_ ** frame)) before ->
  cursor.(kernel_restore_r0) = poster_saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before restore_written middle ->
  armv7a_restore_suffix_transition restore restore_written middle final_cursor released ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask poster_saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint released
    final_registers next_acquired saved_heap ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  kernel_call_save_uninterrupted_execution arch registers checkpoint released final_registers next_acquired saved_heap /\
  next_acquired = checkpoint /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    selected.(SchedState).(highRdyTid) = Some tid /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      outgoing.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi context outgoing stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      exists installed,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
          descriptor.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads descriptor installed /\
        (forall restored restore_start restore_word restore_middle restore_exit return_heap
          next_registers second_registers second_acquired second_heap,
          armv7a_task_restore_transition task_abi context descriptor installed restored ->
          restore_start.(kernel_restore_r0) = saved ->
          armv7a_irq_fiq_mask restore_start.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore restore_start restored restore_word restore_middle ->
          armv7a_restore_suffix_transition restore restore_word restore_middle restore_exit return_heap ->
          next_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr next_registers.(kernel_save_cpsr) ->
          armv7a_irq_fiq_mask next_registers.(kernel_save_cpsr) = mask ->
          armv7a_save_suffix_transition save (kernel_save_read_cpsr next_registers) current return_heap
            second_registers second_acquired second_heap ->
          kernel_stack_call_same_call returned public_call /\
          sem_pend_wait_selected_at (Some environment) critical sg public_call mask initial observed eid timeout
            waiting returned current /\
          current.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old PendSem 0 PendOK) /\
          kernel_call_restore_uninterrupted_execution arch restore_start restored restore_exit return_heap /\
          kernel_call_save_uninterrupted_execution arch next_registers current return_heap
            second_registers second_acquired second_heap /\ second_acquired = current /\
          exists resumed result_node branch_heap cleaned,
            sem_pend_resume_branch_fragment sg resumed eid public_call.(os_sched_call_stack).(stackLeaseSlot)
              result_node second_heap branch_heap /\
            result_node.(statPend) = PendOK /\
            sem_pend_cleanup_fragment sg perr 0 branch_heap cleaned /\
            (forall last_start last_word last_middle last_exit last_heap,
              last_start.(kernel_restore_r0) = second_registers.(kernel_save_r0) ->
              armv7a_irq_fiq_mask last_start.(kernel_restore_current_cpsr) = 192 ->
              armv7a_restore_prefix_transition restore last_start cleaned last_word last_middle ->
              armv7a_restore_suffix_transition restore last_word last_middle last_exit last_heap ->
              kernel_call_restore_uninterrupted_execution arch last_start cleaned last_exit last_heap /\
              (sem_pend_stack_call_post environment.(task_stack_call_external)
                environment.(task_stack_call_platform) (Some environment) critical sg public_call mask
                pevent timeout perr initial X ** retained) last_heap))).
Proof.
  intros environment critical arch task_abi restore save sg entry eid event tid old priority context node
    poster_saved call saved acquired descriptor focus old_sp cpsr values lr prefix suffix first old_words
    publication before frame cursor restore_written middle final_cursor released registers final_registers
    next_acquired saved_heap public_call mask initial observed pevent timeout waiting perr X abi checkpoint
    selected fragments outgoing updated current returned retained Hnonnull Haddress_event Heid Hslot Hlayout
    Hordered Hsaved Hexec Hwait Hin Hforeign Hgroup Hvalid Hlookup Htype Hentry Hcoverage Hunsuspended
    Hhighest Hcurrent Hnest Hlock Htid Hparked Hid Hgeneration Hnone Hfocus Hfragments Hregion Hgeometry
    Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hsaved_mask Hsp32 Hsp Haddress Hpre
    Hr0 Hmask Hrestore_prefix Hrestore_suffix Hreturn Hregisters_cpsr Hnextmask Hsave.
  assert (Hwake_facts : sem_post_wake_result sg eid entry checkpoint priority /\
    task_stack_live_coverage checkpoint.(TskState) (Some (task_stack_key context.(os_sched_call_stack)))).
  { match type of Hpre with ?P before => assert (Hfacts : P |-- coq_prop
      (sem_post_wake_result sg eid entry checkpoint priority /\
       task_stack_live_coverage checkpoint.(TskState) (Some (task_stack_key context.(os_sched_call_stack)))) && TT) end.
    { pose proof (kernel_saved_sched_call_wake_merge _ _ _ abi critical sg call saved acquired descriptor
        entry eid event tid old priority focus (Some (task_stack_key context.(os_sched_call_stack)))
        Hvalid Hlookup Htype Hentry Hcoverage) as Hmerge.
      cbv zeta in Hmerge; fold checkpoint in Hmerge.
      sep_apply_l_atomic Hmerge; Intros; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hfacts before Hpre)). }
  pose proof (sem_pend_registered_post_wait_source environment critical sg public_call call mask initial observed
    eid timeout waiting entry context.(os_sched_call_invocation) eid event tid old priority Hwait Hin Hforeign
    Hlookup Hgroup (proj1 Hwake_facts)) as Hwake_wait.
  fold checkpoint in Hwake_wait.
  destruct (sem_post_wake_selects_highest_waiter sg entry eid event tid old
    context.(os_sched_call_stack).(stackLeaseSlot) node Hvalid Hlookup Htype Hentry
    Hunsuspended Hhighest Hcurrent Hnest Hlock) as [Hready [Hwoken [Hswitch [Hhigh Hpriority]]]].
  fold checkpoint selected in Hready, Hwoken, Hswitch, Hhigh, Hpriority.
  pose proof Hcurrent as [Hnode [Hcurrent_id [Hcurrent_priority [Hcurrent_ready Hcurrent_effective]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [Hwait_head Hold]]]]]].
  assert (Hdifferent : context.(os_sched_call_stack).(stackLeaseSlot) <> tid).
  { pose proof (Hhighest _ node Hcurrent_ready Hnode).
    intro Heq; rewrite Heq in Hnode; assert (node = old) by congruence; subst node; lia. }
  assert (Hnode_selected : selected.(TskState).(inUsedTaskStates)
    context.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { change ((if Z.eqb context.(os_sched_call_stack).(stackLeaseSlot) tid
      then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot)) = Some node).
    rewrite (proj2 (Z.eqb_neq _ _) Hdifferent); exact Hnode. }
  assert (Hcovered_current : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { assert (Hupdated : task_stack_live_coverage updated.(TskState)
      (Some (task_stack_key context.(os_sched_call_stack)))).
    { unfold updated, os_sched_save_current_sp; rewrite Hnode_selected.
      apply task_stack_save_sp_preserves_coverage with (node := node);
        [exact Hnode_selected|exact (proj2 Hwake_facts)]. }
    pose proof (task_stack_park_covers_active updated.(TskState) context.(os_sched_call_stack)
      fragments Hupdated) as Hparked_coverage.
    pose proof (task_stack_take_covers_selected
      (glob_task_set_parked_stacks updated.(TskState)
        (task_stack_park_fragments updated.(TskState).(parkedTaskStacks)
          context.(os_sched_call_stack) fragments)) call.(os_sched_call_stack)
      Hparked_coverage) as Htaken_coverage.
    exact Htaken_coverage. }
  assert (Hwoken_current : current.(TskState).(inUsedTaskStates) tid =
    Some (task_event_wake_single old PendSem 0 PendOK)).
  { change (updated.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old PendSem 0 PendOK)).
    unfold updated, os_sched_save_current_sp; rewrite Hnode_selected.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    rewrite (proj2 (Z.eqb_neq tid context.(os_sched_call_stack).(stackLeaseSlot))
      ltac:(congruence)); exact Hwoken. }
  assert (Hselected_ready : selected.(SchedState).(readyList) = checkpoint.(SchedState).(readyList)).
  { unfold selected, os_sched_prefix_state; cbn [replace_SchedS SchedState].
    unfold os_sched_ready_checkpoint; destruct (os_sched_selection_enabled checkpoint);
      destruct (os_sched_requests_switch checkpoint); reflexivity. }
  assert (Hcurrent_ready_member : In tid current.(SchedState).(readyList)).
  { change (In tid selected.(SchedState).(readyList)); rewrite Hselected_ready, Hready; left; reflexivity. }
  assert (Hcurrent_id_woken : current.(SchedState).(curTaskID) = Some tid).
  { change (selected.(SchedState).(highRdyTid) = Some tid); exact Hhigh. }
  destruct (kernel_saved_sched_call_wake_resume_source _ _ _ abi critical arch task_abi restore save
    sg entry eid event tid old priority context node poster_saved call saved acquired descriptor focus
    old_sp cpsr values lr prefix suffix first old_words publication before (perr # UChar |->_ ** frame)
    cursor restore_written middle final_cursor released registers final_registers next_acquired saved_heap
    Hvalid Hlookup Htype Hentry Hcoverage Hunsuspended Hhighest Hcurrent Hnest Hlock Htid Hparked
    Hid Hgeneration Hnone Hfocus Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr
    Hranges Hsaved_mask Hsp32 Hsp Haddress Hpre Hr0 Hmask Hrestore_prefix Hrestore_suffix Hreturn
    Hregisters_cpsr Hnextmask Hsave)
    as [Hrestore_run [Hsave_run [Hacquired [prefix_heap [written [stored
      [Hprefix [Hselected [Hwrites [Hload [Hstore Hcontinue]]]]]]]]]]].
  split; [exact Hrestore_run|]. split; [exact Hsave_run|]. split; [exact Hacquired|].
  exists prefix_heap, written, stored; split; [exact Hprefix|]. split; [exact Hselected|].
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook.
  destruct (Hcontinue captured hooked Hcapture Hhook_heap Hhook)
    as (installed & Hinstall & Hreads & Hdescriptor_call & Hsource & Hresume).
  assert (Hsource_returned : kernel_call_task_source returned current) by exact Hsource.
  exists installed; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored restore_start restore_word restore_middle restore_exit return_heap next_registers
    second_registers second_acquired second_heap Hrestore Hsecond_r0 Hsecond_mask Hsecond_prefix
    Hsecond_suffix Hsecond_return Hsecond_cpsr Hsecond_saved_mask Hsecond_save.
  destruct (Hresume restored Hrestore) as [Harch [Hpc [Hdescriptor_mask [Hmemory Hrestored]]]].
  assert (Hrestored_current :
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
     os_sched_context_resources environment.(task_stack_call_external) returned **
     kernel_program_inv sg current **
     armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
      critical_region_inside critical sg context.(os_sched_call_invocation) checkpoint **
      (perr # UChar |->_ ** frame))) restored) by exact Hrestored.
  clear Hrestored; rename Hrestored_current into Hrestored.
  assert (Hswitch_run : os_sched_source_switch_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi sg selected
    context old_sp cpsr values lr outgoing call.(os_sched_call_stack) descriptor prefix_heap restored).
  { exists written, stored, captured, hooked, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcapture
      (conj Hhook_heap (conj Hhook (conj Hinstall Hrestore))))))). }
  pose proof (sem_pend_wait_phase_switch_source environment critical sg public_call mask initial observed
    eid timeout waiting call checkpoint task_abi context old_sp cpsr values lr outgoing call.(os_sched_call_stack)
    descriptor saved_heap prefix_heap restored Hwake_wait Hprefix Hswitch_run) as Hcurrent_wait.
  fold current in Hcurrent_wait.
  assert (Hcall_same : kernel_stack_call_same_call returned call).
  { pose proof (proj1 Hreads) as [_ Hbinding]; rewrite Hdescriptor_call in Hbinding.
    unfold returned, kernel_selected_call; rewrite Hdescriptor_call.
    unfold kernel_stack_call_same_call; cbn [armv7a_continuation_resumed_call]; auto. }
  pose proof Hwait as [owned [Henv [Hpublic_same Hhistory]]].
  assert (Hreturned_same : kernel_stack_call_same_call returned public_call).
  { unfold kernel_stack_call_same_call in *; intuition congruence. }
  assert (Hreturned_wait : sem_pend_wait_at (Some environment) critical sg public_call mask initial observed
    eid timeout waiting returned current).
  { destruct Hcurrent_wait as [owned' [Henv' [Hsame' Hrest]]].
    exists owned'; split; [exact Henv'|]. split; [exact Hreturned_same|exact Hrest]. }
  assert (Hslot_same : tid = public_call.(os_sched_call_stack).(stackLeaseSlot)).
  { rewrite Htid, (proj2 (proj2 Hpublic_same)); reflexivity. }
  assert (Hvalid_current : UCOS2_state_inv sg current).
  { match type of Hrestored with ?P restored => assert (Hfacts : P |-- coq_prop (UCOS2_state_inv sg current) && TT)
      by (unfold kernel_program_inv, UCOS2_inv; entailer!; intros ? ?; exact I) end.
    exact (proj1 (Hfacts restored Hrestored)). }
  assert (Hwait_selected : sem_pend_wait_selected_at (Some environment) critical sg public_call mask initial
    observed eid timeout waiting returned current).
  { eapply sem_pend_wait_selected_from_ready_current; [exact Hreturned_wait|exact Hvalid_current| |];
      rewrite <- Hslot_same; assumption. }
  assert (Hactive : task_stack_call_active_key call = Some (task_stack_key call.(os_sched_call_stack))).
  { pose proof (proj1 Hsource_returned) as Horigin.
    unfold task_stack_call_active_key; rewrite <- (proj1 (proj2 Hcall_same)), Horigin.
    rewrite (proj2 (proj2 Hcall_same)); reflexivity. }
  assert (Hmasked : (kernel_stack_call_masked abi kernel_program_inv critical sg
    (task_stack_call_active_key call) returned saved acquired current ** (perr # UChar |->_ ** retained)) restored).
  { match type of Hrestored with ?P restored => match goal with |- ?Q restored => assert (Hpack : P |-- Q) end end.
    { sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ abi current.(TskState) focus
        current.(TskState).(parkedTaskStacks)).
      unfold kernel_stack_call_masked, kernel_stack_inv, retained; rewrite Hactive; entailer!. }
    exact (Hpack restored Hrestored). }
  destruct (kernel_saved_sched_call_return_source environment kernel_program_inv critical arch restore
    sg call returned entry saved acquired current restore_start restored restore_word restore_middle
    restore_exit return_heap (perr # UChar |->_ ** retained) Hcall_same Hsource_returned Hsecond_r0 Hsecond_mask
    Hmasked Hsecond_prefix Hsecond_suffix) as [Hreturn_run [Hreturn_word [Hclosed Hpublic_sched]]].
  assert (Hpend_return : uchar_load (tcb_field_address (task_slot_addr sg tid) TCBStatPend) 0 return_heap).
  { match type of Hclosed with ?P return_heap => assert (Hcell : P |--
      tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> 0 ** TT) end.
    { unfold kernel_stack_call_closed, kernel_stack_inv.
      rewrite kernel_program_inv_split_unmap; Intros.
      sep_apply_l_atomic (sem_pend_cleanup_split sg current tid
        (task_event_wake_single old PendSem 0 PendOK) Hvalid_current Hcurrent_id_woken Hwoken_current).
      cbn [tcb_cell].
      change (encode_pend_status (task_event_wake_single old PendSem 0 PendOK).(statPend)) with 0.
      entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hcell return_heap Hclosed). }
  pose proof (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsecond_save) as Hsave_source.
  destruct (kernel_call_save_instructions_preserve_kernel _ _ _ _ _ _ _ _ Hsave_source)
    as [Hsave_state Hsave_memory].
  assert (Hpend_second : uchar_load
    (tcb_field_address (task_slot_addr sg public_call.(os_sched_call_stack).(stackLeaseSlot)) TCBStatPend)
    0 second_heap).
  { unfold uchar_load; rewrite Hsave_memory, <- Hslot_same; exact Hpend_return. }
  assert (Hsave_input : (sem_pend_stack_save_input environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg returned mask current **
    unmap_table_rep sg ** perr # UChar |->_ ** retained) return_heap).
  { assert (Hactive_same : task_stack_call_active_key call = task_stack_call_active_key returned).
    { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hcall_same)); reflexivity. }
    rewrite Hactive_same, (proj2 Hsaved) in Hclosed.
    match type of Hclosed with ?P return_heap => match goal with |- ?Q return_heap => assert (Hpack : P |-- Q) end end.
    { rewrite sem_pend_stack_save_input_owned, task_tcb_init_stack_save_input_closed_world; entailer!. }
    exact (Hpack return_heap Hclosed). }
  destruct (sem_pend_second_save_return_source environment critical arch save restore sg public_call mask initial
    observed eid pevent timeout waiting returned current perr retained X next_registers return_heap
    second_registers second_acquired second_heap Hnonnull Haddress_event Heid Hslot Hlayout Hordered Hexec
    Hwait_selected Hsecond_return Hsecond_cpsr Hsecond_saved_mask Hsave_input Hsecond_save)
    as [Hsecond_run [Hsecond_acquired Htail]].
  split; [exact Hreturned_same|]. split; [exact Hwait_selected|]. split; [exact Hwoken_current|].
  split; [exact Hreturn_run|]. split; [exact Hsecond_run|]. split; [exact Hsecond_acquired|].
  destruct Htail as (resumed & result_node & branch_heap & cleaned & Hbranch & Hcleanup & Hfinal).
  pose proof (uchar_load_deterministic _ _ _ _ Hpend_second (proj1 (proj2 Hbranch))) as Hstatus_code.
  assert (Hstatus : result_node.(statPend) = PendOK).
  { destruct result_node.(statPend); cbn [encode_pend_status] in Hstatus_code; congruence. }
  rewrite Hstatus in Hcleanup; cbn [encode_pend_status sem_pend_resume_error encode_os_err_code] in Hcleanup.
  exists resumed, result_node, branch_heap, cleaned; auto.
Qed.
