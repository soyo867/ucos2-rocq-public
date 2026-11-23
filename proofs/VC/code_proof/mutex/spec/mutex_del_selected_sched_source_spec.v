Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.mutex_query_spec Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.task.spec.task_create_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_foreign_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_wait_entry_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Consume the actual Scheduler-selected initial task, then the existing
    ordinary API-entry source to register the distinct SemPend invocation.
    Type/nesting/count facts come from byte reads. Its actual first Save
    creates the foreign token; the original Del token stays separate.
    Blocking removes the ready head and makes the next original task
    selected. This is a returning source family, not whole-API coverage. *)
Lemma mutex_del_selected_foreign_wait_source : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform))
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (initial_entry : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  sg selected_state incoming first_selected first_node eid event timeout tail original suspended saved original_entry
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion)
  before entered first_registers first_final acquired after,
  let previous := kernel_selected_call first_selected selected_state in
  let state := kernel_selected_call_state first_selected selected_state in
  let mask := armv7a_irq_fiq_mask first_selected.(armv7a_continuation_cpsr) in
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  first_selected.(armv7a_continuation_call) = None ->
  armv7a_initial_frame_binding first_selected ->
  task_stack_fragments_in_range first_selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 first_selected.(armv7a_continuation_fragments) ->
  mutex_program_selected_reachable sg selected_state ->
  mutex_del_private_types_non_mutex selected_state.(EventState) ->
  task_holds_no_mutex state.(EventState) previous.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(SchedState).(isRunning) = true ->
  first_node.(curPrio) <> sg.(osLowestPrio) -> first_node.(eventPtr) = None ->
  first_node.(eventMultiWaitEvents) = [] -> first_node.(tcbFlagNode) = 0 ->
  state.(SchedState).(readyList) = previous.(os_sched_call_stack).(stackLeaseSlot) ::
    original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  state.(TskState).(parkedTaskStacks) (task_stack_key previous.(os_sched_call_stack)) = None ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  task_invocation_active selected_state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at selected_state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  selected_state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  mutex_query_lookup state eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  0 <= timeout < 4294967296 ->
  previous.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region previous.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range previous.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    previous.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range previous.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication previous.(os_sched_call_stack).(stackLeaseSlot)
    previous.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = previous.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (os_sched_source_selected_post environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
     environment.(mutex_del_call_port) abi sg focus incoming first_selected first_node selected_state **
   unmap_table_rep sg ** event_private_pool_rep sg selected_state.(EventState) **
   (interrupt_platform_saved environment.(mutex_del_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame)) before ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered ->
  uchar_load sg.(g_OSIntNesting) 0 entered -> uchar_load sg.(g_OSLockNesting) 0 entered ->
  first_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr first_registers) entry entered
    first_final acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after ->
  uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  kernel_call_save_uninterrupted_execution arch first_registers entry entered first_final acquired after /\
  acquired = entry /\
  exists old waited,
    let waiting := event_pend_state sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old PendSem timeout in
    let checkpoint := os_sched_prefix_state waiting in
    let fragments := prefix ++ [(first, first + 16,
      map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
    let foreign_saved := armv7a_task_save_image call old_sp cpsr values lr fragments in
    let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
      foreign_saved.(armv7a_continuation_sp) in
    sem_pend_wait_fragment sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old timeout after waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = first_final.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers sched_acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask first_final.(kernel_save_r0) ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers sched_acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers sched_acquired saved_heap /\
        sched_acquired = waiting /\
        exists prefix_heap stack_written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap stack_written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi call foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed selected,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi call selected installed restored ->
                forall return_cursor return_written return_middle return_final final_heap,
                return_cursor.(kernel_restore_r0) = saved ->
                return_cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
                armv7a_restore_prefix_transition restore return_cursor restored return_written return_middle ->
                armv7a_restore_suffix_transition restore return_written return_middle return_final final_heap ->
                let retained := interrupt_platform_saved environment.(mutex_del_call_platform)
                  (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation)
                    call.(os_sched_call_origin)) **
                  critical_region_inside critical sg call.(os_sched_call_invocation) waiting ** frame in
                os_sched_source_switch_execution environment.(mutex_del_call_external)
                  environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi
                  sg checkpoint call old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  selected prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final final_heap /\
                (mutex_del_source_return environment environment.(mutex_del_call_external)
                   environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved) **
                 retained) final_heap)))).
Proof.
  intros environment critical arch boundary save restore task_abi initial_entry sg selected_state incoming
    first_selected first_node eid event timeout tail original suspended saved original_entry
    old_sp cpsr values lr prefix suffix first old_words publication frame before entered
    first_registers first_final acquired after previous state mask abi focus call entry
    Hnone Hinitial Hinitial_geometry Hreachable Htypes Hno_mutex Hrunning Hnot_idle Hevent_none Hmulti_none Hflag_none
    Hlist Habsent Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hparked Hlookup Hnonnull Hlayout
    Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask
    Hsp32 Hsp Haddress Hpre Hboundary Htype_read Hint_read Hlock_read Hreturn Hvalid_sr Hsave_mask
    Hsave Hlow Hhigh.
  assert (Hvalid : UCOS2_state_inv sg selected_state).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg selected_state) && TT) end.
    { unfold os_sched_source_selected_post, UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  assert (Hpending : selected_state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)))
    by exact Hparked.
  pose proof (kernel_selected_call_resources _ _ _ abi initial_entry sg focus
    (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))
    incoming first_selected first_node selected_state ltac:(intros; exact Hinitial)
    ltac:(intros; exact Hinitial_geometry) Hpending) as Hselected.
  cbv zeta in Hselected; fold previous state mask in Hselected.
  match type of Hpre with ?P before => assert (Hentry_order : P |--
    coq_prop (previous.(os_sched_call_stack) = incoming /\
      sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) first_node /\
      first_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
      (first_selected.(armv7a_continuation_call) = None -> kernel_call_task_source previous state)) &&
    (kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
       previous mask **
     kernel_pending_call_world abi sg focus
       (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))
       (Some (task_stack_key incoming)) state **
     (event_private_pool_rep sg selected_state.(EventState) **
      interrupt_platform_saved environment.(mutex_del_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame))) end.
  { sepcon_assoc_change; sep_apply_l_atomic Hselected; entailer!. }
  destruct (Hentry_order before Hpre) as [[Hforeign_stack [Hready [Hgeneration Hsource]]] Howned].
  specialize (Hsource Hnone).
  assert (Hstage : sem_pend_task_call_stage sg previous state).
  { split; [exact Hsource|]. split; [exact Hrunning|].
    exists first_node; rewrite Hforeign_stack.
    exact (conj Hready (conj Hgeneration (conj Hnot_idle (conj Hevent_none (conj Hmulti_none Hflag_none))))). }
  assert (Hcoverage : task_stack_live_coverage state.(TskState)
    (Some (task_stack_key previous.(os_sched_call_stack)))).
  { match type of Howned with ?P before => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) && TT) end.
    { unfold kernel_pending_call_world; entailer!; intros ? ?; exact I. }
    rewrite Hforeign_stack; exact (proj1 (Hobserve before Howned)). }
  destruct (kernel_selected_call_preserves_pending_fields sg first_selected selected_state original
    suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) Hvalid Hactive Hpointer)
    as [Hactive_state Hpointer_state].
  fold state in Hactive_state, Hpointer_state.
  assert (Hreach_state : mutex_program_selected_reachable sg state).
  { eapply mutex_program_source_step_reachable; [exact Hreachable|].
    unfold state, kernel_selected_call_state; rewrite Hnone; apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hreach_entry : mutex_program_selected_reachable sg entry).
  { eapply mutex_program_source_step_reachable; [exact Hreach_state|].
    apply MutexOwnerSourceFrame; reflexivity. }
  assert (Htypes_entry : mutex_del_private_types_non_mutex entry.(EventState)).
  { unfold entry, state, kernel_selected_call_state; rewrite Hnone; exact Htypes. }
  assert (Hpool : event_private_pool_rep sg selected_state.(EventState) = event_private_pool_rep sg entry.(EventState)).
  { unfold entry, state, kernel_selected_call_state; rewrite Hnone; reflexivity. }
  assert (Hparked_entry : entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { unfold entry, state, kernel_selected_call_state; rewrite Hnone; exact Hparked. }
  set (retained := interrupt_platform_saved environment.(mutex_del_call_platform)
    (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry **
    (event_private_pool_rep sg entry.(EventState) ** frame)).
  match type of Howned with ?P before => assert (Hapi_order : P |--
    kernel_call_execution_owned environment.(mutex_del_call_external) environment.(mutex_del_call_platform)
      previous mask ** kernel_program_inv sg state **
    armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** retained) end.
  { unfold kernel_pending_call_world, retained; rewrite Hpool; entailer!. }
  destruct (task_create_foreign_wait_entry_source (mutex_del_runtime_sched_environment environment)
    critical arch boundary save sg previous original suspended mask state eid event before entered
    first_registers first_final acquired after retained Hstage Hcoverage Hactive_state Hpointer_state
    Hlookup Hnonnull Hlayout (Hapi_order before Howned) Hboundary Htype_read Hint_read Hlock_read
    Hreturn Hvalid_sr Hsave_mask Hsave Hlow Hhigh)
    as [Hsave_execution [Hacquired [Herror [Henabled [Hactive_entry [Hpointer_entry [Hcovered
      [old [Hentry [Hcall_source [Hcache Hmasked]]]]]]]]]]].
  fold abi focus call entry in Hentry, Hcall_source, Hcache, Hmasked, Hactive_entry, Hpointer_entry, Hcovered.
  split; [exact Hsave_execution|]. split; [exact Hacquired|].
  match type of Hmasked with ?P after => assert (Hwait_order : P |--
    critical_region_masked environment.(mutex_del_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) first_final.(kernel_save_r0) entry **
    os_sched_context_resources environment.(mutex_del_call_external) call ** kernel_program_inv sg entry **
    armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) original_entry **
     event_private_pool_rep sg entry.(EventState) ** frame)) by (unfold retained; entailer!) end.
  destruct (mutex_del_foreign_wait_return_source environment critical arch save restore task_abi sg call
    first_final.(kernel_save_r0) entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old timeout tail
    original suspended saved original_entry old_sp cpsr values lr prefix suffix first old_words publication
    frame after Hreach_entry Htypes_entry Hno_mutex Hentry Hcall_source Hcache Henabled Hlist Habsent Hcovered
    Horigin Hbinding Hcall Hslice Hmask Hactive_entry Hpointer_entry Hparked_entry Htimeout Hfragments Hregion
    Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress (Hwait_order after Hmasked))
    as [waited Hwait].
  exists old, waited; exact Hwait.
Qed.
