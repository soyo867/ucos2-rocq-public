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
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** An actual foreign blocking call supplies progress to the pending Del:
    its three TCB stores and EventTaskWait remove the current task from the
    ready list. The present prefix [foreign; original; ...] makes the
    selector choose the original, without a future selected-original
    premise. The existing no-blocking-while-owning-Mutex application
    protocol remains explicit in [task_holds_no_mutex]. *)
Lemma mutex_del_foreign_wait_return_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  sg context foreign_mask entry eid event tid old timeout tail original suspended saved original_entry
  old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion) before,
  let abi := environment.(mutex_del_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let waiting := event_pend_state sg entry eid event tid old PendSem timeout in
  let checkpoint := os_sched_prefix_state waiting in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let foreign_saved := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint context.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  mutex_program_selected_reachable sg entry ->
  mutex_del_private_types_non_mutex entry.(EventState) ->
  task_holds_no_mutex entry.(EventState) tid ->
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
  (critical_region_masked environment.(mutex_del_call_platform) critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) foreign_mask entry **
   os_sched_context_resources environment.(mutex_del_call_external) context ** kernel_program_inv sg entry **
   armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
   (interrupt_platform_saved environment.(mutex_del_call_platform)
      (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) original_entry **
    event_private_pool_rep sg entry.(EventState) ** frame)) before ->
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
            kernel_client_step environment.(mutex_del_call_external).(os_sched_hook_action) sg updated updated ->
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
                let retained := interrupt_platform_saved environment.(mutex_del_call_platform)
                  (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation)
                    context.(os_sched_call_origin)) **
                  critical_region_inside critical sg context.(os_sched_call_invocation) waiting ** frame in
                os_sched_source_switch_execution environment.(mutex_del_call_external)
                  environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi task_abi
                  sg checkpoint context old_sp cpsr values lr foreign_saved original.(os_sched_call_stack)
                  selected prefix_heap restored /\
                kernel_call_restore_uninterrupted_execution arch return_cursor restored return_final after /\
                (mutex_del_source_return environment environment.(mutex_del_call_external)
                   environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved) **
                 retained) after)))).
Proof.
  intros environment critical arch save restore task_abi sg context foreign_mask entry eid event tid old timeout tail
    original suspended saved original_entry old_sp cpsr values lr prefix suffix first old_words publication frame before
    abi focus waiting checkpoint fragments foreign_saved updated Hreachable Htypes Hno_mutex
    Hentry Hsource Hcache Henabled Hlist Habsent Hcoverage Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hparked
    Htimeout Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre.
  assert (Hwaiting_reachable : mutex_program_selected_reachable sg waiting).
  { eapply mutex_program_source_step_reachable; [exact Hreachable|].
    apply MutexOwnerSourceWait; [|exact Hno_mutex].
    unfold sem_pend_wait_entry, mutex_query_lookup in Hentry; tauto. }
  assert (Hcheckpoint_reachable : mutex_program_selected_reachable sg checkpoint).
  { eapply mutex_program_source_step_reachable; [exact Hwaiting_reachable|].
    apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hupdated_reachable : mutex_program_selected_reachable sg updated).
  { eapply mutex_program_source_history_reachable; [exact Hcheckpoint_reachable|].
    eapply mutex_program_saved_sp_source with (actor := context.(os_sched_call_invocation)); reflexivity. }
  assert (Hcurrent_reachable : mutex_program_selected_reachable sg
    (os_sched_install_context context fragments original.(os_sched_call_stack) updated)).
  { eapply mutex_program_source_step_reachable; [exact Hupdated_reachable|].
    apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hcurrent_types : mutex_del_private_types_non_mutex
    (os_sched_install_context context fragments original.(os_sched_call_stack) updated).(EventState)).
  { exact Htypes. }
  assert (Hpool : event_private_pool_rep sg entry.(EventState) =
    event_private_pool_rep sg
      (os_sched_install_context context fragments original.(os_sched_call_stack) updated).(EventState)).
  { reflexivity. }
  match type of Hpre with ?P before => assert (Hpre_order : P |--
    critical_region_masked environment.(mutex_del_call_platform) critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) foreign_mask entry **
    os_sched_context_resources environment.(mutex_del_call_external) context ** kernel_program_inv sg entry **
    armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
    (interrupt_platform_saved environment.(mutex_del_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) original_entry **
     (event_private_pool_rep sg entry.(EventState) ** frame))) by entailer! end.
  destruct (task_create_foreign_wait_return_resources (mutex_del_runtime_sched_environment environment)
    critical arch save restore task_abi sg context foreign_mask entry eid event tid old timeout tail
    original suspended saved original_entry old_sp cpsr values lr prefix suffix first old_words publication
    (event_private_pool_rep sg entry.(EventState) ** frame) before Hentry Hsource Hcache Henabled Hlist Habsent
    Hcoverage Horigin Hbinding Hcall Hslice Hmask Hactive Hpointer Hparked Htimeout Hfragments Hregion Hgeometry
    Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress (Hpre_order before Hpre))
    as [waited [Hstores Hreturn]].
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
  assert (Hstage : mutex_del_call_stage returned current).
  { unfold mutex_del_call_stage; rewrite (proj1 (proj2 Hsame)), Horigin.
    split; [exact Hsource_return|]. intros _; rewrite (proj2 (proj2 Hsame)); exact Hready_return. }
  split; [exact Hswitch_execution|]. split; [exact Hrestore_return|].
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { assert (Hactive_key : task_stack_call_active_key original = task_stack_call_active_key returned).
    { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
    unfold mutex_del_source_return, mutex_del_source_return_at, mutex_del_runtime_return_at.
    Exists returned current environment.
    unfold kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources, mutex_del_callsite_environment.
    rewrite Hactive_key, Hpool; entailer!. }
  exact (Hclose after Howned).
Qed.
