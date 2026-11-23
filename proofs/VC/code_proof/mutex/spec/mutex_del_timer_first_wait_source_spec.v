Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.interrupt Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_saved_foreign_wait_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_saved_wait_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The initial Timer owner is the None result of the already proved
    foreign install/TaskRestore. OSTmr_Task's real first OSSemPend loads
    OSTmrSemSignal, uses timeout zero and borrows err from this same stack.
    Its registration changes only the invocation map; Del's source history,
    private ECB pool and exact saved entry are retained.

    On the concrete ready prefix Timer::original::tail, the real wait
    removes Timer and selects original. The existing source consumer then
    performs its own Save/capture, the explicit no-write Hook branch,
    original TaskRestore and the distinct later C Restore, reaching Del's
    source_return. No arbitrary first API or Timer-loop return is asserted.
    Actual uninterrupted Save/Restore and frame-layout conditions remain
    explicit; the saved OSCtxSw LR is never identified with a later BL LR. *)
Lemma mutex_del_timer_first_wait_return_source : forall environment critical arch
  (initial : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  sg state selected node timer_entry lower value upper perr
  original suspended saved original_entry eid event tail before
  first_registers first_final first_acquired first_after
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let region := selected.(armv7a_continuation_stack).(stackLeaseRegion) in
  let context := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    (tmr_task_local_stack_fragments region lower upper) in
  let entry := armv7a_initial_call_registered selected state in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let waiting := event_pend_state sg entry eid event context.(os_sched_call_stack).(stackLeaseSlot) node PendSem 0 in
  let checkpoint := os_sched_prefix_state waiting in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let foreign_saved := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  armv7a_initial_frame_binding selected ->
  selected.(armv7a_continuation_pc) = task_stack_init_entry_pc timer_entry ->
  hd_error selected.(armv7a_continuation_registers) = Some 0 ->
  state.(TimerState).(timerTask) = Some (task_stack_key selected.(armv7a_continuation_stack)) ->
  selected.(armv7a_continuation_fragments) =
    task_stack_complete_fragments region (lower ++ [Some value] ++ upper) ->
  region.(stackRegionWords) = Zlength lower + 1 + Zlength upper ->
  0 < Zlength lower -> 0 < Zlength upper ->
  perr = region.(stackRegionBase) + Zlength lower * 4 ->
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
  task_holds_no_mutex state.(EventState) selected.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(SchedState).(readyList) = selected.(armv7a_continuation_stack).(stackLeaseSlot) ::
    original.(os_sched_call_stack).(stackLeaseSlot) :: tail ->
  state.(TskState).(parkedTaskStacks) (task_stack_key selected.(armv7a_continuation_stack)) = None ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  context.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  task_stack_saved_pointer_in_range region (old_sp - 64) ->
  task_publication_happened state.(TskState) publication selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun word => 0 <= word < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 -> old_sp - 64 = region.(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (armv7a_task_restored_execution environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi selected **
   mutex_del_stack_resources sg state ** store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved original_entry suspended state.(TskState) focus)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 before ->
  uchar_load sg.(g_OSIntNesting) 0 before -> uchar_load sg.(g_OSLockNesting) 0 before ->
  first_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) =
    armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr first_registers) entry before
    first_final first_acquired first_after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 first_after ->
  uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 first_after ->
  pointer_load sg.(g_OSTmrSemSignal) (event_addr sg eid) before /\
  kernel_call_save_uninterrupted_execution arch first_registers entry before first_final first_acquired first_after /\
  first_acquired = entry /\
  exists waited,
    sem_pend_wait_fragment sg entry eid event context.(os_sched_call_stack).(stackLeaseSlot) node 0 first_after waited /\
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
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) stack_written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
            foreign_saved.(armv7a_continuation_sp)) stack_written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi context foreign_saved stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg updated updated ->
            exists installed resumed,
              sched_install_heap_fragment sg hooked installed
                (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) resumed.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads resumed installed /\
              resumed.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
              resumed.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
              resumed.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
              (forall restored,
                armv7a_task_restore_transition task_abi context resumed installed restored ->
                forall return_cursor return_written return_middle return_final after,
                return_cursor.(kernel_restore_r0) = saved ->
                return_cursor.(kernel_restore_current_cpsr) = resumed.(armv7a_continuation_cpsr) ->
                armv7a_restore_prefix_transition restore return_cursor restored return_written return_middle ->
                armv7a_restore_suffix_transition restore return_written return_middle return_final after ->
                let retained := interrupt_platform_saved environment.(mutex_del_call_platform)
                  (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation)
                    context.(os_sched_call_origin)) **
                  critical_region_inside critical sg context.(os_sched_call_invocation) waiting **
                  (perr # UChar |->_ ** tmr_task_local_padding perr ** frame) in
                os_sched_source_switch_execution environment.(mutex_del_call_external)
                  environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi
                  sg checkpoint context old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  resumed prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final after /\
                (mutex_del_source_return environment environment.(mutex_del_call_external)
                   environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved) **
                 retained) after)))).
Proof.
  intros environment critical arch initial save restore task_abi sg state selected node timer_entry lower value upper perr
    original suspended saved original_entry eid event tail before first_registers first_final first_acquired first_after
    old_sp cpsr values lr prefix suffix first old_words publication frame
    abi region context entry focus waiting checkpoint fragments foreign_saved updated
    Hbinding Hpc Hargument Htimer_task Hcomplete Hsize Hlower Hupper Hperr Hready Hgen Hpriority
    Hevent Hmulti Hflag Hrunning Hcoverage Htimer_enabled Hinitialized Hsignal Hlookup Hnonnull Hlayout
    Hno_mutex Hlist Habsent Hparked Hfragments Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hmask
    Hsp32 Hsp Haddress Hpre Htype_read Hint_read Hlock_read Hreturn Hfirst_cpsr Hfirst_mask Hsave Hlow Hhigh.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState)) &&
    (armv7a_task_restored_execution environment.(mutex_del_call_external)
       environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi selected **
     kernel_program_inv sg state ** store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg original saved original_entry suspended state.(TskState) focus)
       state.(TskState).(parkedTaskStacks) ** (event_private_pool_rep sg state.(EventState) ** frame))) end.
  { unfold mutex_del_stack_resources; entailer!. }
  destruct (Hopen before Hpre) as [[Hreachable Htypes] Howned].
  destruct (tmr_task_saved_wait_entry_source environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi initial critical arch save
    sg state selected node timer_entry lower value upper perr original saved original_entry suspended focus eid event
    before first_registers first_final first_acquired first_after (event_private_pool_rep sg state.(EventState) ** frame)
    Hbinding Hpc Hargument Htimer_task Hcomplete Hsize Hlower Hupper Hperr Hready Hgen Hpriority Hevent Hmulti Hflag
    Hrunning Hcoverage Htimer_enabled Hinitialized Hsignal Hlookup Hnonnull Hlayout Howned
    Htype_read Hint_read Hlock_read Hreturn Hfirst_cpsr Hfirst_mask Hsave Hlow Hhigh)
    as [Hsignal_read [Hfirst_execution [Hacquired [_ [Henabled [Hlive [old [Hwait [Hsource [Hcache Hafter]]]]]]]]]].
  assert (Hold : old = node).
  { pose proof (proj1 (proj2 (proj2 (proj2 Hwait)))) as Hnode.
    change (state.(TskState).(inUsedTaskStates) selected.(armv7a_continuation_stack).(stackLeaseSlot) = Some old) in Hnode.
    rewrite (proj1 Hready) in Hnode; congruence. }
  subst old.
  assert (Hreachable_entry : mutex_program_selected_reachable sg entry).
  { eapply mutex_program_source_step_reachable; [exact Hreachable|].
    apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hregion : valid_task_stack_region region).
  { destruct Hbinding as [top [task_entry [argument [task_return [lo [hi [Heq [Hvalid Hrest]]]]]]]].
    unfold region; rewrite Heq; exact Hvalid. }
  assert (Hgeometry : task_stack_fragments_in_range region.(stackRegionWords) 0 context.(os_sched_call_fragments)).
  { apply tmr_task_local_stack_fragments_in_range; assumption. }
  assert (Htypes_entry : mutex_del_private_types_non_mutex entry.(EventState)) by exact Htypes.
  fold region context entry abi in Hafter.
  change (event_private_pool_rep sg state.(EventState)) with
    (event_private_pool_rep sg entry.(EventState)) in Hafter.
  match type of Hafter with ?P first_after => assert (Hclose : P |--
    critical_region_masked environment.(mutex_del_call_platform) critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) first_final.(kernel_save_r0) entry **
    os_sched_context_resources environment.(mutex_del_call_external) context ** mutex_del_stack_resources sg entry **
    store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg original saved original_entry suspended entry.(TskState) focus)
      entry.(TskState).(parkedTaskStacks) **
    (perr # UChar |->_ ** tmr_task_local_padding perr ** frame)) end.
  { unfold mutex_del_stack_resources; entailer!. }
  split; [exact Hsignal_read|]. split; [exact Hfirst_execution|]. split; [exact Hacquired|].
  exact (mutex_del_saved_foreign_wait_return_source environment critical arch save restore task_abi
    sg context first_final.(kernel_save_r0) entry eid event context.(os_sched_call_stack).(stackLeaseSlot) node 0 tail
    original suspended saved original_entry old_sp cpsr values lr prefix suffix first old_words publication
    (perr # UChar |->_ ** tmr_task_local_padding perr ** frame) first_after
    Hno_mutex Hwait Hsource Hcache Henabled Hlist Habsent Hlive Hparked ltac:(lia) Hfragments
    Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress
    (Hclose first_after Hafter)).
Qed.
