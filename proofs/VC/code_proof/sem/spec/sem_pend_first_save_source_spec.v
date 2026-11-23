Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_stage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_switch_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** IRQ entry changes saved SP, nesting and the existing parked map.
    None of those writes registers a Sem wait. The task has not executed
    the zero-count body yet; its stage is transported from the actual
    interrupted call, not asserted at an arbitrary acquired state. *)
Lemma sem_pend_irq_parked_call_stage : forall sg call entry sp fragments,
  sem_pend_task_call_stage sg call entry ->
  sem_pend_task_call_stage sg call (armv7a_irq_live_parked_state entry call sp fragments).
Proof.
  intros sg call entry sp fragments Hstage.
  pose proof (sem_pend_irq_entry_same_priority_call_stage sg call entry sp fragments Hstage) as Hparked.
  change (sem_pend_task_call_stage sg call
    (armv7a_irq_live_parked_state entry call sp fragments)) in Hparked.
  exact Hparked.
Qed.

(** The actual first-Save IRQ entry supplies the SAME focused owner used
    by the concrete client registry. The port save is the existing ABI
    boundary; the kernel nesting/TCB-SP stores are the proved source
    fragment, with a precise heap endpoint. The current strong map comes
    from the source-established world, never from a weak-map upgrade.

    This is the entry half of an interrupted Save. The registry, actual
    last selector/restore and CPSID/DSB/BX suffix must still be composed;
    the theorem does not pretend every interrupt returns to this caller. *)
Lemma sem_pend_first_save_irq_source : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg entry node handler saved publication (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc)
    saved.(armv7a_continuation_lr) in
  let payload := (call.(os_sched_call_stack).(stackLeaseRegion),
    saved.(armv7a_continuation_fragments)) in
  let parked := armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  sem_pend_task_call_stage sg call entry -> entry.(IntrState).(intNesting) = 0 ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) -> armv7a_task_frame_slice saved ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
  (os_int_exit_frame_save_pre external platform handler **
    (kernel_stack_inv abi kernel_program_inv sg
      (Some (task_stack_key call.(os_sched_call_stack))) entry ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists entry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) saved_heap entry_heap /\
    saved.(armv7a_continuation_call) = Some call /\
    saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
    armv7a_continuation_binding saved /\
    sem_pend_task_call_stage sg call parked /\
    task_saved_pointer_at parked call.(os_sched_call_stack) saved.(armv7a_continuation_sp) /\
    (kernel_client_call_stack_world abi sg focus payload parked **
      (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) entry_heap.
Proof.
  intros external platform port critical arch abi suffix sg entry node handler saved publication
    frame before saved_heap call focus payload parked Hstage Hnesting Hnode Hid Habsent
    Haddress Hregion Hgeometry Hpublication Hsp Hslice Hcursor Hpre Hsave.
  pose proof Hstage as [_ [Hrunning [old [Hready [Hgeneration Hfields]]]]].
  assert (old = node) by (destruct Hready; congruence); subst old.
  pose proof (proj1 (proj2 Hready)) as Hcurrent.
  match type of Hpre with ?P before =>
    assert (Hopen : P |-- coq_prop (task_stack_live_coverage entry.(TskState)
      (Some (task_stack_key call.(os_sched_call_stack)))) &&
      (os_int_exit_frame_save_pre external platform handler **
       (UCOS2_inv sg entry ** armv7a_task_stack_continuations abi entry.(TskState)
         entry.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))))
  end.
  { unfold kernel_stack_inv; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (armv7a_irq_source_save_parks_call external platform port abi sg entry node handler saved
    publication (unmap_table_rep sg ** frame) before saved_heap Hslice Hrunning Hnesting
    Hcurrent Hnode Hid Hgeneration Habsent Haddress Hregion Hgeometry Hpublication Hsp
    Hcoverage Howned Hsave) as [entry_heap [Hwrites [Hentry [Hcovered Hparked]]]].
  destruct (armv7a_save_transition_observations _ _ _ abi handler saved before saved_heap Hsave)
    as [Hentry_source [Hcall [Hbinding [Hmask [Hpc [Hsaved_sp Hsaved_fragments]]]]]].
  assert (Hlookup : parked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { unfold parked, armv7a_irq_live_parked_state, focus, payload.
    apply task_stack_park_fragments_lookup. }
  assert (Hpointer : task_saved_pointer_at parked call.(os_sched_call_stack) saved.(armv7a_continuation_sp)).
  { exists (task_set_saved_sp node saved.(armv7a_continuation_sp)).
    unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode.
    split.
    - change ((if Z.eqb call.(os_sched_call_stack).(stackLeaseSlot)
        call.(os_sched_call_stack).(stackLeaseSlot) then Some (task_set_saved_sp node
        saved.(armv7a_continuation_sp)) else entry.(TskState).(inUsedTaskStates)
        call.(os_sched_call_stack).(stackLeaseSlot)) = Some (task_set_saved_sp node saved.(armv7a_continuation_sp))).
      rewrite Z.eqb_refl; reflexivity.
    - exact (conj Hgeneration eq_refl). }
  exists entry_heap; split; [exact Hwrites|]. split; [exact Hentry|].
  split; [exact Hcall|]. split; [congruence|]. split; [exact Hbinding|].
  split; [apply sem_pend_irq_parked_call_stage; exact Hstage|]. split; [exact Hpointer|].
  match type of Hparked with ?P entry_heap => assert (Hclose : P |--
    kernel_client_call_stack_world abi sg focus payload parked **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame))
  end.
  { unfold kernel_client_call_stack_world, kernel_client_call_stack_facts.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  exact (Hclose entry_heap Hparked).
Qed.

(** Continue the actual IRQ entry through one registered heap/state/source
    trace, load the original frame and execute the restored Save suffix.
    Stage transport uses that SAME trace, not a second possible interval.
    Extra clients here must prove the no-switch stage law. A path selecting
    another task is handled by the separate actual selector/switch chain;
    no public Sem premise excludes it. *)
Lemma sem_pend_registered_first_save_return : forall external platform port critical arch Extra
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  extra_resources extra_step extra_effect clients sg original suspended,
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original -> armv7a_task_frame_slice suspended ->
  suspended.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
  interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (nth 0 suspended.(armv7a_continuation_registers) 0) ->
  @kernel_client_call_stack_extension_valid external platform port Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sem_pend_task_call_stage sg original state ->
    UCOS2_state_inv sg returned /\ sem_pend_task_call_stage sg original returned) ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg
    original.(os_sched_call_invocation) None extra_effect ->
  forall cut before closed_heap state handler (frame : Assertion),
  UCOS2_state_inv sg state -> sem_pend_task_call_stage sg original state ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  kernel_client_heap_trace extra_step sg cut before KernelClientHeapClosed closed_heap ->
  kernel_client_heap_observer_cut original.(os_sched_call_invocation) cut ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg cut state KernelClientHeapClosed returned /\
    kernel_resumption_task_source_trace external port clients sg original.(os_sched_call_invocation)
      None original.(os_sched_call_origin) state stopped returned_origin returned /\
    (returned.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
     tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
       task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
     let resumed := os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack) in
     exists selected,
       armv7a_irq_restore_pointer_reads sg closed_heap
         (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
         selected.(armv7a_continuation_sp) /\
       armv7a_continuation_focus_binding focus selected /\
       selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
       selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
       selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
       (forall registers restored final_registers acquired after,
         registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
         registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
         registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
         armv7a_restore_transition abi handler selected closed_heap restored ->
         armv7a_save_suffix_transition suffix registers resumed restored final_registers acquired after ->
         acquired = resumed /\
         kernel_save_after_mrs_execution arch registers resumed restored final_registers acquired after /\
         final_registers.(kernel_save_return_word) = Some suspended.(armv7a_continuation_lr) /\
         sem_pend_task_call_stage sg (armv7a_continuation_resumed_call selected original) acquired /\
         (critical_region_masked platform critical sg original.(os_sched_call_invocation)
            original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
          os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
          kernel_stack_inv abi UCOS2_inv sg (Some (task_stack_key original.(os_sched_call_stack))) acquired **
          (unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
            handler.(os_int_exit_handler_fragments) ** frame)) after)).
Proof.
  intros external platform port critical arch Extra abi suffix extra_resources extra_step extra_effect
    clients sg original suspended focus payload Hbinding Hcall Hslice Hpc Hsaved
    Hextension Hpointer_step Hstage_step Henter Hexit Hpublish Hsource
    cut before closed_heap state handler frame Hvalid Hstage Hpointer Htrace Hcut Hpre.
  destruct (task_create_registered_call_stack_restore external platform port Extra abi extra_resources
    extra_step extra_effect clients sg original suspended Hbinding Hcall Hslice Hextension
    Hpointer_step Henter Hexit Hpublish Hsource cut before closed_heap state handler frame
    Hvalid Hpointer Htrace Hcut Hpre)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  destruct (sem_pend_client_trace_preserves_call_stage Extra extra_effect sg original Hstage_step
    cut state KernelClientHeapClosed returned Hstates Hvalid Hstage) as [Hvalid_returned Hstage_returned].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hcurrent Haddress resumed.
  destruct (Hreturn Hcurrent Haddress)
    as [selected [Hloads [Hfocus [Hlease [Hselected_sp [Hcpsr [Hregisters [Hcovered Hresume]]]]]]]].
  exists selected; split; [exact Hloads|]. split; [exact Hfocus|].
  split; [exact Hlease|]. split; [exact Hcpsr|]. split; [exact Hregisters|].
  intros registers restored final_registers acquired after Hregister_cpsr Hr0 Hlr Hrestore Hsuffix.
  destruct (Hresume restored Hrestore) as [Hmemory Hrestored].
  assert (Hresumed_stage : sem_pend_task_call_stage sg
    (armv7a_continuation_resumed_call selected original) resumed).
  { unfold sem_pend_task_call_stage, kernel_call_task_source, armv7a_continuation_resumed_call.
    cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    rewrite Hlease; exact Hstage_returned. }
  assert (Hactive_key : task_stack_key
    (armv7a_continuation_resumed_call selected original).(os_sched_call_stack) =
      task_stack_key original.(os_sched_call_stack)).
  { cbn [armv7a_continuation_resumed_call os_sched_call_stack]; rewrite Hlease; reflexivity. }
  assert (Hcovered_resumed : task_stack_live_coverage resumed.(TskState)
    (Some (task_stack_key (armv7a_continuation_resumed_call selected original).(os_sched_call_stack)))).
  { rewrite Hactive_key; exact Hcovered. }
  assert (Hsaved_registers : interrupt_saved_value
    (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0)).
  { rewrite Hregister_cpsr, Hr0, Hcpsr, Hregisters; exact Hsaved. }
  match type of Hrestored with ?P restored => assert (Horder : P |--
    sem_pend_task_stack_resources abi UCOS2_inv sg
      (armv7a_continuation_resumed_call selected original)
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) resumed **
    (unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame))
  end.
  { rewrite Hregister_cpsr, Hcpsr.
    unfold sem_pend_task_stack_resources, kernel_stack_inv; entailer!. }
  destruct (sem_pend_save_suffix_keeps_stack_resources external platform port critical arch abi suffix
    UCOS2_inv sg (armv7a_continuation_resumed_call selected original) resumed registers restored
    final_registers acquired after _ Hsaved_registers (Horder restored Hrestored) Hsuffix)
    as [Hacquired [Hunchanged [Hexecution [Hreturn_word [Hsaved_word [Hstage_after Hafter]]]]]].
  split; [exact Hacquired|]. split; [exact Hexecution|]. split.
  - rewrite Hreturn_word, Hlr; f_equal; exact (proj2 (proj2 Hfocus)).
  - split; [exact Hstage_after|]. rewrite Hactive_key in Hafter; exact Hafter.
Qed.

(** The handle protocol is applied only to the registered middle trace.
    Its stopped flag is retained, not forced to false merely to obtain an
    old critical-region interval. Entry deposit and final stack take leave
    the Event module unchanged and are handled separately below. *)
Lemma sem_pend_client_trace_preserves_handle : forall critical sg invocation event_observer
  eid before stopped after observed,
  mutex_query_handle_protocol critical sg invocation eid ->
  kernel_client_resource_trace critical.(critical_region_clients) sg invocation event_observer
    before stopped after ->
  UCOS2_state_inv sg before -> mutex_query_lookup before eid observed ->
  exists current, mutex_query_lookup after eid current /\
    current.(eventGeneration) = observed.(eventGeneration) /\
    current.(eventType) = observed.(eventType).
Proof.
  intros critical sg invocation event_observer eid before stopped after observed Hprotocol Htrace.
  revert observed.
  induction Htrace as
    [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros previous Hvalid Hlookup.
  - exists previous; repeat split; assumption || reflexivity.
  - destruct (Hprotocol action before middle previous Hin Hforeign Hvalid Hstep Hlookup)
      as [next [Hnext [Hgen Htype]]].
    pose proof (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action Hin)
      sg before middle Hvalid Hstep) as Hmiddle.
    destruct (IH next Hmiddle Hnext) as [current [Hcurrent [Hgen' Htype']]].
    exists current; split; [exact Hcurrent|]; split; congruence.
Qed.

Lemma sem_pend_parked_source_preserves_handle : forall external port critical sg original
  before sp fragments stopped returned_origin returned eid observed,
  let parked := armv7a_irq_live_parked_state before original sp fragments in
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  UCOS2_state_inv sg parked -> mutex_query_lookup before eid observed ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    parked stopped returned_origin returned ->
  exists current,
    mutex_query_lookup (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) eid current /\
    current.(eventGeneration) = observed.(eventGeneration) /\
    current.(eventType) = observed.(eventType).
Proof.
  intros external port critical sg original before sp fragments stopped returned_origin returned
    eid observed parked Hprotocol Hvalid Hlookup Hsource.
  destruct (kernel_resumption_task_source_trace_erases external port critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None original.(os_sched_call_origin) parked stopped
    returned_origin returned Hsource) as [Hresources Hcontrol].
  pose proof (kernel_resumption_resource_trace_erases _ _ _ _ _ _ _ Hresources) as Hraw.
  assert (Hparked_lookup : mutex_query_lookup parked eid observed).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state, mutex_query_lookup in *.
    destruct before.(SchedState).(isRunning);
      cbn [replace_IntrS TskState replace_TskS EventState];
      destruct (before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot));
      exact Hlookup. }
  destruct (sem_pend_client_trace_preserves_handle critical sg original.(os_sched_call_invocation)
    None eid parked stopped returned observed Hprotocol Hraw Hvalid Hparked_lookup)
    as [current [Hcurrent [Hgeneration Htype]]].
  exists current; split; [exact Hcurrent|]; split; assumption.
Qed.

(** The actual registered first-Save return feeds the literal protected
    semaphore-count read. The earlier IRQ entry owner is the output of
    [sem_pend_first_save_irq_source]; its actual MRS/save/deposit edges are
    retained here in the shared segmented history. The registered source,
    selected frame and final CPSID/DSB/BX are exactly those used to produce
    the returned heap, full acquired task stage and current strong world.

    At the literal zero-count guard the SAME acquired owner supplies the
    Stat/StatPend/Dly write cells, then the actual three stores and full
    EventWait body produce the first Restore input. An actual uninterrupted
    Restore returns the same context and complete current strong world.
    This consumes acquired observations and segmented Save history, not
    a flat acquisition interval. The returned strong owner also supplies
    the actual first Scheduler switch and the selected task's guarded
    ordinary Post-entry/wake/return continuation; no wake post is assumed
    at this first-Save entry.

    This is the explicit +4/no-switch registered branch. The extension's
    source, saved-SP and task-stage laws remain visible branch conditions,
    not new public requirements on all kernel clients or all Save calls. *)
Lemma sem_pend_registered_first_save_count_return : forall external platform port critical arch Extra
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  extra_resources extra_step extra_effect sg original suspended,
  let environment := {| task_stack_call_external := external;
    task_stack_call_platform := platform; task_stack_call_port := port;
    task_stack_call_continuations := abi |} in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original -> armv7a_task_frame_slice suspended ->
  suspended.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
  interrupt_saved_value (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
    (nth 0 suspended.(armv7a_continuation_registers) 0) ->
  @kernel_client_call_stack_extension_valid external platform port Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sem_pend_task_call_stage sg original state ->
    UCOS2_state_inv sg returned /\ sem_pend_task_call_stage sg original returned) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None extra_effect ->
  forall entry handler initial_registers initial_heap irq_input saved_heap registry_heap closed_heap
    eid observed (frame : Assertion),
  let parked := armv7a_irq_live_parked_state entry original suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  handler.(os_int_exit_interrupted_call) = original ->
  kernel_call_save_instruction_step arch SaveReadCPSR initial_registers entry initial_heap
    (kernel_save_read_cpsr initial_registers) entry irq_input ->
  armv7a_save_transition abi handler suspended irq_input saved_heap ->
  kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
    original.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap ->
  UCOS2_state_inv sg parked -> sem_pend_task_call_stage sg original parked ->
  task_saved_pointer_at parked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  mutex_query_lookup entry eid observed -> observed.(eventType) = OS_EVENT_TYPE_SEM ->
  kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload KernelClientHeapClosed parked **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) registry_heap ->
  exists returned stopped returned_origin current,
    kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked KernelClientHeapClosed returned /\
    kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      parked stopped returned_origin returned /\
    mutex_query_lookup (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) eid current /\
    current.(eventGeneration) = observed.(eventGeneration) /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
    (returned.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
     tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
       task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
     exists selected,
       armv7a_irq_restore_pointer_reads sg closed_heap
         (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
       (forall registers restored final_registers acquired after,
         registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
         registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
         registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
         armv7a_restore_transition abi handler selected closed_heap restored ->
         armv7a_save_suffix_transition suffix registers
           (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) restored
           final_registers acquired after ->
         kernel_call_save_history environment critical sg original entry
           (armv7a_continuation_resumed_call selected original) acquired /\
         sem_pend_task_call_stage sg (armv7a_continuation_resumed_call selected original) acquired /\
         (coq_prop (UCOS2_state_inv sg acquired /\ 0 <= encode_event_cnt_value current <= 65535 /\
            task_stack_live_coverage acquired.(TskState) (Some (task_stack_key original.(os_sched_call_stack)))) &&
          (critical_region_masked platform critical sg original.(os_sched_call_invocation)
             original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
           os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
           (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
           sem_post_count_frame sg acquired eid current **
           armv7a_task_stack_continuations abi acquired.(TskState) acquired.(TskState).(parkedTaskStacks) **
           unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
             handler.(os_int_exit_handler_fragments) ** frame)) after /\
         (encode_event_cnt_value current = 0 -> event_object_layout_prop sg eid ->
          (EX node,
            coq_prop (sem_pend_wait_entry sg acquired eid current
                original.(os_sched_call_stack).(stackLeaseSlot) node /\
              original.(os_sched_call_origin) = RunningInvocation
                original.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration) /\
              kernel_call_task_source (armv7a_continuation_resumed_call selected original) acquired /\
              sched_current_consistency acquired.(TskState) acquired.(SchedState) /\
              0 <= encode_task_status node.(stat) <= 255 /\
              task_stack_live_coverage acquired.(TskState)
                (Some (task_stack_key original.(os_sched_call_stack)))) &&
            (critical_region_masked platform critical sg original.(os_sched_call_invocation)
               original.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
             os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
             sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) **
             tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
               TCBStat (Some (encode_task_status node.(stat))) **
             tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
               TCBStatPend (Some (encode_pend_status node.(statPend))) **
             tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBDly (Some node.(dly)) **
             sem_pend_prefix_frame sg acquired original.(os_sched_call_stack).(stackLeaseSlot) node **
             armv7a_task_stack_continuations abi acquired.(TskState) acquired.(TskState).(parkedTaskStacks) **
             unmap_table_rep sg ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
               handler.(os_int_exit_handler_fragments) ** frame)) after /\
          forall timeout, 0 <= timeout < 4294967296 ->
          exists node waited,
            let context := armv7a_continuation_resumed_call selected original in
            let waiting := event_pend_state sg acquired eid current
              original.(os_sched_call_stack).(stackLeaseSlot) node PendSem timeout in
            sem_pend_wait_fragment sg acquired eid current original.(os_sched_call_stack).(stackLeaseSlot)
              node timeout after waited /\
            kernel_call_save_history environment critical sg original entry context acquired /\
            sem_pend_first_critical sg eid timeout acquired
              (SemPendWaiting original.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration)) waiting /\
            kernel_call_task_source context waiting /\
            sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
            (task_tcb_init_stack_restore_input environment critical sg context final_registers.(kernel_save_r0)
               acquired waiting ** unmap_table_rep sg **
             task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) waited /\
            (forall restore_arch
              (restore_cpu : Armv7aRestoreResourceABI external platform critical restore_arch)
              cursor written middle final_cursor final_heap,
              cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
              armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
              armv7a_restore_prefix_transition restore_cpu cursor waited written middle ->
              armv7a_restore_suffix_transition restore_cpu written middle final_cursor final_heap ->
              kernel_call_restore_uninterrupted_execution restore_arch cursor waited final_cursor final_heap /\
              final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
              kernel_call_restore_history environment critical sg context waiting context waiting /\
              (kernel_stack_call_closed abi kernel_program_inv sg (task_stack_call_active_key context)
                 context (armv7a_irq_fiq_mask final_registers.(kernel_save_r0)) waiting **
               task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
                final_heap /\
              sem_pend_wait_sched_switch_continuation environment critical sg context
                (armv7a_irq_fiq_mask final_registers.(kernel_save_r0)) waiting eid
                (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid))
                final_heap (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
                  handler.(os_int_exit_handler_fragments) ** frame))))).
Proof.
  intros external platform port critical arch Extra abi suffix extra_resources extra_step extra_effect
    sg original suspended environment focus payload Hbinding Hcall Hslice Hpc Hsaved Hextension
    Hpointer_step Hstage_step Henter Hexit Hpublish Hsource entry handler initial_registers
    initial_heap irq_input saved_heap registry_heap closed_heap eid observed frame parked Hhandler
    Hmrs Hsave Hdeposit Hvalid Hstage Hpointer Hprotocol Hlookup Htype Htrace Hpre.
  destruct (sem_pend_registered_first_save_return external platform port critical arch Extra abi suffix
    extra_resources extra_step extra_effect critical.(critical_region_clients) sg original suspended
    Hbinding Hcall Hslice Hpc Hsaved Hextension Hpointer_step Hstage_step Henter Hexit Hpublish Hsource
    KernelClientHeapClosed registry_heap closed_heap parked handler frame Hvalid Hstage Hpointer
    Htrace ltac:(exact I) Hpre)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  destruct (sem_pend_parked_source_preserves_handle external port critical sg original entry
    suspended.(armv7a_continuation_sp) suspended.(armv7a_continuation_fragments) stopped returned_origin
    returned eid observed Hprotocol Hvalid Hlookup Hsources)
    as [current [Hcurrent [Hgeneration Hcurrent_type]]].
  assert (Hsem : current.(eventType) = OS_EVENT_TYPE_SEM) by congruence.
  exists returned, stopped, returned_origin, current.
  split; [exact Hstates|]. split; [exact Hsources|]. split; [exact Hcurrent|].
  split; [exact Hgeneration|]. split; [exact Hsem|].
  intros Hcur Haddress.
  destruct (Hreturn Hcur Haddress)
    as [selected [Hloads [Hfocus [Hlease [Hcpsr [Hregisters Hresume]]]]]].
  exists selected; split; [exact Hloads|].
  intros registers restored final_registers acquired after Hregister_cpsr Hr0 Hlr Hrestore Hsuffix.
  destruct (Hresume registers restored final_registers acquired after
    Hregister_cpsr Hr0 Hlr Hrestore Hsuffix)
    as [Hacquired [Hexecution [Hreturn_word [Hacquired_stage Hafter]]]].
  subst acquired.
  assert (Hsave_history : kernel_call_save_history environment critical sg original entry
    (armv7a_continuation_resumed_call selected original)
    (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack))).
  { unfold environment.
    eapply KernelCallSaveIRQ with (extra_step := extra_step) (extra_effect := extra_effect)
      (registers := initial_registers) (before := initial_heap) (irq_input := irq_input)
      (saved_heap := saved_heap) (registry_heap := registry_heap) (closed_heap := closed_heap)
      (stopped := stopped) (returned_origin := returned_origin) (resume_registers := registers)
      (final_registers := final_registers); eassumption. }
  split; [exact Hsave_history|].
  - split; [exact Hacquired_stage|].
    split.
    + match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hcount : P |-- Q) end end.
      { unfold kernel_stack_inv; Intros.
        sep_apply_l_atomic (sem_post_count_split_full sg
          (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) eid current Hcurrent Hsem).
        Intros; entailer!. }
      exact (Hcount after Hafter).
    + intros Hzero Hlayout.
      match goal with |- ?P /\ _ => assert (Hwait : P) end.
      { match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hfields : P |-- Q) end end.
        { unfold kernel_stack_inv; Intros.
        sep_apply_l_atomic (sem_post_count_split_full sg
          (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) eid current Hcurrent Hsem).
        Intros.
        sep_apply_l_atomic (sem_pend_acquired_wait_prefix sg
          (armv7a_continuation_resumed_call selected original)
          (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) eid current
          Hacquired_stage ltac:(tauto) Hcurrent Hsem Hzero Hlayout).
        Intros node; Exists node.
        cbn [armv7a_continuation_resumed_call os_sched_call_stack os_sched_call_origin] in *.
          rewrite Hlease in *; entailer!. }
        exact (Hfields after Hafter). }
      split; [exact Hwait|].
      intros timeout Htimeout.
      destruct Hwait as [node [[Hentry [Horigin [Htask_source [Hcache [Hrange Hcoverage]]]]] Hfields]].
      assert (Hcovered : task_stack_live_coverage
        (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)).(TskState)
        (task_stack_call_active_key (armv7a_continuation_resumed_call selected original))).
      { unfold task_stack_call_active_key; rewrite (proj1 Htask_source).
        cbn [armv7a_continuation_resumed_call os_sched_call_stack]; rewrite Hlease; exact Hcoverage. }
      match type of Hfields with ?P after => assert (Horder : P |--
        critical_region_masked platform critical sg original.(os_sched_call_invocation)
          original.(os_sched_call_origin) final_registers.(kernel_save_r0)
          (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) **
        os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
        sem_pend_wait_prefix_cells sg (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack))
          original.(os_sched_call_stack).(stackLeaseSlot) node (encode_task_status node.(stat))
          (encode_pend_status node.(statPend)) node.(dly) **
        armv7a_task_stack_continuations abi
          (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)).(TskState)
          (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)).(TskState).(parkedTaskStacks) **
        unmap_table_rep sg ** (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame))
        by (unfold sem_pend_wait_prefix_cells; entailer!) end.
      destruct (sem_pend_wait_first_restore_input environment critical sg original entry
        (armv7a_continuation_resumed_call selected original) final_registers.(kernel_save_r0)
        (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) eid current
        original.(os_sched_call_stack).(stackLeaseSlot) node timeout
        (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)
        after Hsave_history Hentry Htask_source Hcache Hcovered Htimeout (Horder after Hfields))
        as [waited [Hrun [Hhistory [Hfirst [Hwaiting_source [Hwaiting_cache Hinput]]]]]].
      exists node, waited; cbv zeta.
      split; [exact Hrun|]. split; [exact Hhistory|]. split; [exact Hfirst|].
      split; [exact Hwaiting_source|]. split; [exact Hwaiting_cache|].
      split.
      * match type of Hinput with ?P waited => match goal with |- ?Q waited => assert (Hclose : P |-- Q) by entailer! end end.
        exact (Hclose waited Hinput).
      * intros restore_arch restore_cpu cursor written middle final_cursor final_heap Hr0_restore Hmask_restore Hprefix Hsuffix_restore.
        pose proof (sem_pend_wait_first_restore_source environment critical restore_arch restore_cpu sg
          (armv7a_continuation_resumed_call selected original) final_registers.(kernel_save_r0)
          (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack))
          (event_pend_state sg (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) eid current
            original.(os_sched_call_stack).(stackLeaseSlot) node PendSem timeout)
          cursor waited written middle final_cursor final_heap _ Hr0_restore Hmask_restore Hinput Hprefix Hsuffix_restore)
          as [Hrestore_source [Hrestore_return [Hrestore_history Hfinal]]].
        split; [exact Hrestore_source|]. split; [exact Hrestore_return|]. split; [exact Hrestore_history|].
        split.
        -- match type of Hfinal with ?P final_heap => match goal with |- ?Q final_heap => assert (Hclose : P |-- Q) by entailer! end end.
           exact (Hclose final_heap Hfinal).
        -- pose proof (sem_pend_wait_task_observations sg
             (os_int_exit_wrapper_restored_state returned original.(os_sched_call_stack)) eid current
             original.(os_sched_call_stack).(stackLeaseSlot) node timeout) as [Hwaited_lookup [Hblocked Hrest]].
           assert (Hcontinuation : sem_pend_wait_continuation eid
             (armv7a_continuation_resumed_call selected original).(os_sched_call_stack).(stackLeaseGeneration)
             (task_set_event_ptr (task_prepare_event_wait node PendSem timeout) (Some eid))).
           { pose proof Hacquired_stage as [_ [_ [ready_node [Hready [Hready_generation Hfields_before]]]]].
             pose proof Hentry as [_ [_ [_ [Hnode_before Hrest_entry]]]].
             cbn [armv7a_continuation_resumed_call os_sched_call_stack] in Hready, Hready_generation |- *.
             rewrite Hlease in Hready, Hready_generation |- *.
             assert (ready_node = node) by (destruct Hready; congruence); subst ready_node.
             rewrite <- Hready_generation; apply sem_pend_wait_establishes_continuation;
               [exact (proj2 (proj2 (proj2 (proj2 Hready))))|tauto|tauto]. }
           eapply sem_pend_wait_sched_switch_continuation_from_owned.
           ++ exact Hwaiting_source.
           ++ cbn [armv7a_continuation_resumed_call os_sched_call_stack]; rewrite Hlease; exact Hwaited_lookup.
           ++ exact Hcontinuation.
           ++ cbn [armv7a_continuation_resumed_call os_sched_call_stack]; rewrite Hlease; exact Hblocked.
           ++ cbn [armv7a_continuation_resumed_call os_sched_call_stack]; rewrite Hlease.
              change (task_stack_take returned.(TskState).(parkedTaskStacks) original.(os_sched_call_stack)
                (task_stack_key original.(os_sched_call_stack)) = None).
              apply task_stack_take_lookup.
           ++ unfold os_sched_stack_pre.
              match type of Hfinal with ?P final_heap => match goal with |- ?Q final_heap =>
                assert (Hclose : P |-- Q) by entailer! end end.
              exact (Hclose final_heap Hfinal).
Qed.
