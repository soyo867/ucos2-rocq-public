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

Require Import Ucos2Verify.VC.code.task.spec.task_create_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_focus_spec.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_saved_wait_source_spec.

(** Consume the exact pending TaskCreate entry after another task reaches
    the real zero-count SemPend cut. Its own saved/inside resources and
    descriptor facts come from that one owned entry; they are not supplied
    independently by the caller. The actual wait removes the current ready
    head and selects the original task, then the established physical return
    supplies TaskCreate's existing public success post. The remaining
    guards describe this observed path, not future selection or termination.
    The Timer first-entry consumer below supplies the real preceding cut. *)
Lemma task_create_saved_wait_return_source : forall environment critical arch
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
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved original_entry suspended entry.(TskState) focus)
     entry.(TskState).(parkedTaskStacks) ** frame) before ->
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
    Hentry Hsource Hcache Henabled Hlist Habsent Hcoverage Hparked Htimeout Hfragments Hregion Hgeometry Hsp_range
    Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (armv7a_continuation_binding suspended /\ suspended.(armv7a_continuation_call) = Some original /\
      armv7a_task_frame_slice suspended /\ armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 /\
      original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
        original.(os_sched_call_stack).(stackLeaseGeneration) /\
      task_invocation_active entry.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
      task_saved_pointer_at entry suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
       context.(os_sched_call_origin) foreign_mask entry **
     os_sched_context_resources environment.(task_stack_call_external) context ** kernel_program_inv sg entry **
     armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) original_entry ** frame))) end.
  { unfold focus.
    sep_apply_l_atomic (kernel_saved_sched_call_focus_resources environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port) abi critical sg original saved
      original_entry suspended entry Hparked).
    entailer!; tauto. }
  destruct (Hopen before Hpre) as
    [[Hbinding [Hcall [Hslice [Hmask [Horigin [Hactive Hpointer]]]]]] Howned].
  exact (task_create_foreign_wait_return_source environment critical arch save restore task_abi
    sg context foreign_mask entry eid event tid old timeout tail original suspended saved original_entry
    call_before region args task_return lower old_frame upper old_sp cpsr values lr prefix suffix first old_words
    publication frame before Hentry Hsource Hcache Henabled Hlist Habsent Hcoverage Horigin Hbinding Hcall Hslice
    Hmask Hactive Hpointer Hparked Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr
    Hranges Hswitch_mask Hsp32 Hsp Haddress Howned).
Qed.

(** The real Timer task's first zero-count Pend supplies the preceding
    source cut of the exact-map consumer above. Only the no-effect argument
    assignment precedes this call in OSTmr_Task. Initial entry, local err
    storage and the signal pointer are consumed by the shared Timer source;
    no completed previous API or SequentialCall boundary is assumed.
    The concrete wait and physical return reach TaskCreate's existing
    success post. This is one initial-task/uninterrupted/no-write-hook path,
    not all foreign task histories or a proof that this call must return. *)
Lemma task_create_timer_first_wait_return_source : forall environment critical arch
  (initial : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg state selected node timer_entry timer_lower value timer_upper perr
  original saved original_entry descriptor eid event before first_registers first_final acquired after
  tail old_sp cpsr values lr prefix suffix first old_words publication
  call_before region args task_return lower old_frame upper (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let timer_region := selected.(armv7a_continuation_stack).(stackLeaseRegion) in
  let call_fragments := tmr_task_local_stack_fragments timer_region timer_lower timer_upper in
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation) call_fragments in
  let entry := armv7a_initial_call_registered selected state in
  let focus := armv7a_call_focus original descriptor.(armv7a_continuation_pc) descriptor.(armv7a_continuation_lr) in
  armv7a_initial_frame_binding selected ->
  selected.(armv7a_continuation_pc) = task_stack_init_entry_pc timer_entry ->
  hd_error selected.(armv7a_continuation_registers) = Some 0 ->
  state.(TimerState).(timerTask) = Some (task_stack_key selected.(armv7a_continuation_stack)) ->
  selected.(armv7a_continuation_fragments) =
    task_stack_complete_fragments timer_region (timer_lower ++ [Some value] ++ timer_upper) ->
  timer_region.(stackRegionWords) = Zlength timer_lower + 1 + Zlength timer_upper ->
  0 < Zlength timer_lower -> 0 < Zlength timer_upper ->
  perr = timer_region.(stackRegionBase) + Zlength timer_lower * 4 ->
  sched_current_ready_at state.(TskState) state.(SchedState)
    selected.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  node.(curPrio) = sg.(osLowestPrio) - 2 ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  state.(SchedState).(isRunning) = true ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key selected.(armv7a_continuation_stack))) ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState) ->
  state.(TimerState).(timerSignalSem) = event_addr sg eid ->
  mutex_query_lookup state eid event -> event_addr sg eid <> 0 -> event_object_layout_prop sg eid ->
  (armv7a_task_restored_execution environment.(task_stack_call_external)
     environment.(task_stack_call_platform) environment.(task_stack_call_port) abi selected **
   kernel_program_inv sg state **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved original_entry descriptor state.(TskState) focus)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 before ->
  uchar_load sg.(g_OSIntNesting) 0 before -> uchar_load sg.(g_OSLockNesting) 0 before ->
  first_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr first_registers) entry before
    first_final acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after ->
  uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  state.(SchedState).(readyList) = selected.(armv7a_continuation_stack).(stackLeaseSlot) ::
    original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  state.(TskState).(parkedTaskStacks) (task_stack_key selected.(armv7a_continuation_stack)) = None ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  call_fragments = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  task_stack_saved_pointer_in_range timer_region (old_sp - 64) ->
  task_publication_happened state.(TskState) publication selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = timer_region.(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  pointer_load sg.(g_OSTmrSemSignal) (event_addr sg eid) before /\
  kernel_call_save_uninterrupted_execution arch first_registers entry before first_final acquired after /\
  acquired = entry /\
  exists old,
    let waiting := event_pend_state sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old PendSem 0 in
    let checkpoint := os_sched_prefix_state waiting in
    let fragments := prefix ++ [(first, first + 16,
      map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
    let foreign_saved := armv7a_task_save_image call old_sp cpsr values lr fragments in
    let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
      foreign_saved.(armv7a_continuation_sp) in
  exists waited,
    sem_pend_wait_fragment sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old 0 after waited /\
    (forall cursor written middle final_cursor released,
      cursor.(kernel_restore_r0) = first_final.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor released ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor released /\
      (forall registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask first_final.(kernel_save_r0) ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting released
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting released final_registers acquired saved_heap /\
        acquired = waiting /\
        exists prefix_heap stack_written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap stack_written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi call foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed selected,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              selected.(armv7a_continuation_sp) = descriptor.(armv7a_continuation_sp) /\
              selected.(armv7a_continuation_cpsr) = descriptor.(armv7a_continuation_cpsr) /\
              selected.(armv7a_continuation_registers) = descriptor.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi call selected installed restored ->
                forall return_cursor return_written return_middle return_final final_heap,
                return_cursor.(kernel_restore_r0) = saved ->
                return_cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
                armv7a_restore_prefix_transition restore return_cursor restored return_written return_middle ->
                armv7a_restore_suffix_transition restore return_written return_middle return_final final_heap ->
                let retained := interrupt_platform_saved environment.(task_stack_call_platform)
                  (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation)
                    call.(os_sched_call_origin)) **
                  critical_region_inside critical sg call.(os_sched_call_invocation) waiting ** (perr # UChar |->_ ** tmr_task_local_padding perr ** frame) in
                os_sched_source_switch_execution environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi
                  sg checkpoint call old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  selected prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final final_heap /\
                (os_sched_stack_return_post environment kernel_program_inv sg original
                  (armv7a_irq_fiq_mask saved) call_before ** retained) final_heap /\
                (task_create_stack_post environment critical sg region args task_return lower old_frame upper
                  original (armv7a_irq_fiq_mask saved) 0 ** retained) final_heap)))).
Proof.
  intros environment critical arch initial save restore task_abi sg state selected node timer_entry timer_lower value
    timer_upper perr original saved original_entry descriptor eid event before first_registers first_final acquired after
    tail old_sp cpsr values lr prefix suffix first old_words publication call_before region args task_return lower
    old_frame upper frame abi timer_region call_fragments call entry focus
    Hbinding Hpc Hargument Htimer_task Hinitial_fragments Hsize Hlower Hupper Hperr Hready Hgen Hpriority
    Hevent Hmulti Hflag Hrunning Hcoverage Henabled Hinitialized Hsignal Hlookup Hnonnull Hlayout
    Hpre Htype_read Hint_read Hlock_read Hreturn Hcpsr Hmask Hsave Hlow Hhigh
    Hlist Habsent Hparked Hfragments Hsp_range Hpublication Hlength Hswitch_cpsr Hlr Hranges Hswitch_mask
    Hsp32 Hsp Haddress.
  destruct (tmr_task_saved_wait_entry_source environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) abi initial critical arch save
    sg state selected node timer_entry timer_lower value timer_upper perr original saved original_entry descriptor focus
    eid event before first_registers first_final acquired after frame Hbinding Hpc Hargument Htimer_task
    Hinitial_fragments Hsize Hlower Hupper Hperr Hready Hgen Hpriority Hevent Hmulti Hflag Hrunning Hcoverage
    Henabled Hinitialized Hsignal Hlookup Hnonnull Hlayout Hpre Htype_read Hint_read Hlock_read Hreturn
    Hcpsr Hmask Hsave Hlow Hhigh)
    as [Hread [Hfirst [Hacquired [Hclear [Hsched [Hcovered [old [Hwait [Hsource [Hcache Howned]]]]]]]]]].
  assert (Hregion : valid_task_stack_region timer_region).
  { unfold timer_region.
    pose proof Hbinding as [top [task_entry [argument [task_ret [lo [up [Heq [Hvalid Hrest]]]]]]]].
    rewrite Heq; exact Hvalid. }
  assert (Hgeometry : task_stack_fragments_in_range timer_region.(stackRegionWords) 0 call_fragments).
  { unfold call_fragments; apply tmr_task_local_stack_fragments_in_range; assumption. }
  split; [exact Hread|]. split; [exact Hfirst|]. split; [exact Hacquired|].
  exists old; cbv zeta.
  exact (task_create_saved_wait_return_source environment critical arch save restore task_abi
    sg call first_final.(kernel_save_r0) entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old 0 tail
    original descriptor saved original_entry call_before region args task_return lower old_frame upper old_sp
    cpsr values lr prefix suffix first old_words publication
    (perr # UChar |->_ ** tmr_task_local_padding perr ** frame) after
    Hwait Hsource Hcache Hsched Hlist Habsent Hcovered Hparked ltac:(lia) Hfragments Hregion Hgeometry
    Hsp_range Hpublication Hlength Hswitch_cpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Howned).
Qed.
