Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.event Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_switch_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_scheduled_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_mrs_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Join the actual first-Save path at its existing source cuts. The IRQ
    descriptor comes from the MRS register observation, the registered trace
    starts on the heap produced by its deposit, and Scheduler's real writes
    restore that same pending frame. The history and Event projection are
    derived here; neither is an unexplained continuation premise.

    The source-stage facts/owned world are outputs of the preceding registry
    and Scheduler producers. The existing non-VFP SVC register observation,
    capture and restore contracts remain explicit external boundaries. This
    returning-source theorem does not assert that an arbitrary schedule must
    return, or give a fresh platform law or public future-safety premise. *)
Lemma sem_pend_scheduled_first_acquire_source : forall environment critical arch Extra
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (registers_source : Armv7aIRQRegisterSave environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
    KernelClientHeapCut Extra -> model -> Prop)
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
  sg original start first_registers before irq_input handler suspended saved_heap registry_heap
  payload (parked_frame : Assertion) entry_heap entry stopped returned_origin checkpoint
  context old_sp cpsr task_registers lr saved written stored captured hooked_heap
  eid observed (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original (armv7a_save_entry_address save + 4)
    suspended.(armv7a_continuation_lr) in
  let parked := armv7a_irq_live_parked_state start original suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let hooked := os_sched_save_current_sp (os_sched_prefix_state entry)
    context.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp) in
  valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  kernel_call_save_instruction_step arch SaveReadCPSR first_registers start before
    (kernel_save_read_cpsr first_registers) start irq_input ->
  handler.(os_int_exit_interrupted_call) = original ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address save + 4 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) ->
  armv7a_irq_register_save registers_source
    (kernel_save_read_cpsr first_registers).(kernel_save_r0)
    (kernel_save_read_cpsr first_registers).(kernel_save_lr)
    handler suspended irq_input saved_heap ->
  armv7a_task_frame_slice suspended ->
  kernel_heap_execution (armv7a_irq_live_entry_writes sg start
    original.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
    saved_heap registry_heap ->
  (kernel_client_call_stack_world abi sg focus payload parked ** parked_frame) registry_heap ->
  kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
    KernelClientHeapClosed entry_heap ->
  kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
    KernelClientHeapClosed entry ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    parked stopped returned_origin entry ->
  os_sched_source_switch_prefix_execution sg entry_heap checkpoint ->
  kernel_heap_execution (armv7a_task_save_writes old_sp cpsr task_registers lr) checkpoint written ->
  pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written ->
  kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
    saved.(armv7a_continuation_sp)) written stored ->
  armv7a_task_capture_transition task_abi context saved stored captured ->
  kernel_heap_execution [] captured hooked_heap ->
  kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg hooked hooked ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) hooked ->
  os_sched_saved_stack_binding context saved.(armv7a_continuation_fragments) hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context
    saved.(armv7a_continuation_fragments) hooked original.(os_sched_call_stack)
    suspended.(armv7a_continuation_fragments) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  mutex_query_lookup start eid observed -> observed.(eventType) = OS_EVENT_TYPE_SEM ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved.(armv7a_continuation_fragments) **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** frame)) hooked_heap ->
  let current := os_sched_install_context context saved.(armv7a_continuation_fragments)
    original.(os_sched_call_stack) hooked in
  exists installed selected,
    sched_install_heap_fragment sg hooked_heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored registers final_registers acquired after,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      armv7a_save_suffix_transition save registers current restored final_registers acquired after ->
      let returned := armv7a_continuation_resumed_call selected original in
      acquired = current /\
      final_registers.(kernel_save_r0) = first_registers.(kernel_save_cpsr) /\
      kernel_save_after_mrs_execution arch registers current restored final_registers acquired after /\
      exists event,
        (coq_prop (sem_pend_acquire_observation environment critical sg original returned
           (armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0)
           start acquired eid observed event /\
         sem_pend_task_call_stage sg returned acquired /\
         task_stack_live_coverage acquired.(TskState) (Some (task_stack_key returned.(os_sched_call_stack))) /\
         0 <= encode_event_cnt_value event <= 65535 /\
         (encode_event_cnt_value event = 0 -> event_object_layout_prop sg eid ->
           exists waiting, sem_pend_wait_entry sg acquired eid event
             returned.(os_sched_call_stack).(stackLeaseSlot) waiting /\
             kernel_call_task_source returned acquired /\
             sched_current_consistency acquired.(TskState) acquired.(SchedState))) &&
         (critical_region_masked environment.(task_stack_call_platform) critical sg
            returned.(os_sched_call_invocation) returned.(os_sched_call_origin)
            final_registers.(kernel_save_r0) acquired **
          os_sched_context_resources environment.(task_stack_call_external) returned **
          (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event **
          sem_post_count_frame sg acquired eid event **
          armv7a_task_call_stacks abi acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks) **
          frame)) after).
Proof.
  intros environment critical arch Extra save task_abi registers_source extra_step extra_effect
    sg original start first_registers before irq_input handler suspended saved_heap registry_heap
    payload parked_frame entry_heap entry stopped returned_origin checkpoint context old_sp cpsr
    task_registers lr saved written stored captured hooked_heap eid observed frame abi focus parked hooked
    Hvalid_registers Hmrs Hhandler Hhandler_pc Hhandler_mask Hcapture_irq Hslice Hentry Hworld
    Hheap_trace Hstate_trace Hsource_trace Hprefix Hwrites Hload Hstore Hcapture Hhook_heap Hhook
    Horigin Hactive Hfields Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage
    Hprotocol Hlookup Htype Hpre current.
  destruct (sem_pend_mrs_irq_saved_value _ _ _ abi registers_source arch first_registers
    (kernel_save_read_cpsr first_registers) start before irq_input handler suspended saved_heap
    Hvalid_registers Hmrs Hhandler_mask Hcapture_irq)
    as [Hdeposit [Hbinding [Hsaved_value Hword]]].
  destruct (armv7a_save_transition_observations _ _ _ abi _ _ _ _ Hdeposit)
    as [_ [Hcall [_ [_ [Hpc _]]]]].
  rewrite Hhandler in Hcall; rewrite Hhandler_pc in Hpc.
  pose proof (sem_pend_scheduled_save_event_trace environment critical sg original start
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments)
    focus payload registry_heap parked_frame stopped returned_origin entry entry
    Hworld Hsource_trace eq_refl) as Hevents.
  destruct (sem_pend_save_event_trace_preserves_handle critical sg original.(os_sched_call_invocation)
    start entry eid observed Hevents Hprotocol Hlookup)
    as [event [Hevent_lookup [Hevent_generation Hevent_type]]].
  assert (Hsem : event.(eventType) = OS_EVENT_TYPE_SEM) by congruence.
  unfold focus in Hpre; rewrite <- Hpc in Hpre.
  destruct (task_create_sched_restore_pending_call _ _ _ abi task_abi sg context
    saved.(armv7a_continuation_fragments) hooked original suspended frame hooked_heap
    Hbinding Hcall Hslice Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre)
    as [installed [selected [node [Hinstall [Hreads [Hfocused [Hlease [Hsp [Hcpsr [Hregisters
      [Hcovered Hrestore]]]]]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored registers final_registers acquired after Hrun Hcursor_cpsr Hcursor_r0 Hcursor_lr Hsuffix returned.
  destruct (Hrestore restored Hrun) as [Hmemory [Hsource [Hselected Howned]]].
  rewrite Hpc in Hselected.
  assert (Hswitch : os_sched_source_switch_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi sg
    (os_sched_prefix_state entry) context old_sp cpsr task_registers lr saved original.(os_sched_call_stack)
    selected checkpoint restored).
  { exists written, stored, captured, hooked_heap, installed.
    exact (conj Hwrites (conj Hload (conj Hstore (conj Hcapture
      (conj Hhook_heap (conj Hhook (conj Hinstall Hrun))))))). }
  assert (Hcursor_saved : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    registers.(kernel_save_r0)).
  { rewrite Hcursor_cpsr, Hcursor_r0, Hcpsr, Hregisters; exact Hsaved_value. }
  destruct (sem_pend_scheduled_save_history_count environment critical arch Extra save task_abi
    extra_step extra_effect sg original start handler suspended selected first_registers before irq_input
    saved_heap registry_heap entry_heap entry stopped returned_origin checkpoint context old_sp cpsr
    task_registers lr saved original.(os_sched_call_stack) restored registers final_registers acquired after
    node eid event frame Hhandler Hmrs Hpc Hdeposit Hentry Hheap_trace Hstate_trace Hsource_trace
    Hprefix Hswitch (proj1 Hreads) Horigin Hactive Hfields eq_refl Hcursor_cpsr Hcursor_r0 Hcursor_lr
    Hcursor_saved Hevent_lookup Hsem Hselected Hsuffix)
    as [Hstate [Hexecution [Hfacts Hcount]]].
  destruct Hfacts as [Hhistory [Hsame [Hstage [Hcovered_now [Hvalid [Hcurrent_lookup [Hrange Hzero]]]]]]].
  destruct (kernel_save_after_mrs_return_values _ _ _ _ _ _ _ Hexecution) as [Hr0 _].
  assert (Horiginal_value : final_registers.(kernel_save_r0) = first_registers.(kernel_save_cpsr)).
  { rewrite Hr0, Hcursor_r0, Hregisters; exact Hword. }
  assert (Horiginal_saved : interrupt_saved_value (armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr))
    final_registers.(kernel_save_r0)).
  { rewrite Horiginal_value; split; [exact Hvalid_registers|reflexivity]. }
  assert (Hobservation : sem_pend_acquire_observation environment critical sg original returned
    (armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0)
    start acquired eid observed event).
  { exact (conj (or_introl Hhistory) (conj Hsame (conj Horiginal_saved (conj Hvalid
      (conj Hlookup (conj Hcurrent_lookup (conj Htype (conj Hsem Hevent_generation)))))))). }
  split; [exact Hstate|]. split; [exact Horiginal_value|]. split; [exact Hexecution|].
  exists event; split.
  - exact (conj Hobservation (conj Hstage (conj Hcovered_now (conj Hrange Hzero)))).
  - exact Hcount.
Qed.
