Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.interrupt Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.timer Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_entry_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_wait_entry_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTmr_Task's actual first call is OSSemPend(OSTmrSemSignal, 0, &err).
    There is only the no-effect p_arg=p_arg statement before this call.
    The initial descriptor is bound to that task's entry/R0 and initialized
    TCB. [timer_entry] and [perr] are the existing linked C symbol/local
    layout bindings: they are not inferred from a task ID or fresh label.

    The owned restored buffer supplies the borrowed err byte and padding;
    registration uses its remaining real fragments. No SequentialCall
    event or previous completed API is needed. The exact pending Scheduler
    map survives on the same heap. Type/nesting/count are the actual read
    observations of this successful zero-count branch; all other public
    SemPend branches retain their existing separate source proofs.
    This prefix ends before the three wait stores, not at Timer-loop return. *)
Lemma tmr_task_saved_wait_entry_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (initial : Armv7aInitialCallABI external platform port abi)
  critical arch (save : Armv7aSaveSuffixABI external platform critical arch)
  sg state selected node timer_entry lower value upper perr
  original saved original_entry descriptor focus eid event before registers final_registers acquired after
  (frame : Assertion),
  let region := selected.(armv7a_continuation_stack).(stackLeaseRegion) in
  let fragments := tmr_task_local_stack_fragments region lower upper in
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  let entry := armv7a_initial_call_registered selected state in
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
  (armv7a_task_restored_execution external platform port abi selected ** kernel_program_inv sg state **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved original_entry descriptor state.(TskState) focus)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 before ->
  uchar_load sg.(g_OSIntNesting) 0 before -> uchar_load sg.(g_OSLockNesting) 0 before ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry before
    final_registers acquired after ->
  uchar_load (event_addr sg eid + OSEventCnt_off) 0 after ->
  uchar_load (event_addr sg eid + OSEventCnt_off + 1) 0 after ->
  pointer_load sg.(g_OSTmrSemSignal) (event_addr sg eid) before /\
  kernel_call_save_uninterrupted_execution arch registers entry before final_registers acquired after /\
  acquired = entry /\ sem_pend_precritical_error (event_addr sg eid) 3 0 0 = None /\
  os_sched_selection_enabled entry = true /\
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
  exists old,
    sem_pend_wait_entry sg entry eid event call.(os_sched_call_stack).(stackLeaseSlot) old /\
    kernel_call_task_source call entry /\ sched_current_consistency entry.(TskState) entry.(SchedState) /\
    (critical_region_masked platform critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
       final_registers.(kernel_save_r0) entry ** os_sched_context_resources external call **
     kernel_program_inv sg entry ** store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg original saved original_entry descriptor entry.(TskState) focus)
       entry.(TskState).(parkedTaskStacks) **
     (perr # UChar |->_ ** tmr_task_local_padding perr ** frame)) after.
Proof.
  intros external platform port abi initial critical arch save sg state selected node timer_entry lower value upper perr
    original saved original_entry descriptor focus eid event before registers final_registers acquired after frame
    region fragments call entry Hbinding Hpc Hargument Htimer_task Hfragments Hsize Hlower Hupper Hperr
    Hready Hgen Hpriority Hevent Hmulti Hflag Hrunning Hcoverage Henabled Hinitialized Hsignal
    Hlookup Hnonnull Hlayout Hpre Htype_read Hint_read Hlock_read Hreturn Hcpsr Hmask Hsave Hlow Hhigh.
  assert (Hnone : selected.(armv7a_continuation_call) = None)
    by (apply armv7a_initial_frame_no_call; exact Hbinding).
  assert (Hcurrent : task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { split; [exact (proj1 (proj2 Hready))|]. exists node; exact (conj (proj1 Hready) Hgen). }
  assert (Hgeometry : task_stack_fragments_in_range region.(stackRegionWords) 0 fragments).
  { unfold fragments; apply tmr_task_local_stack_fragments_in_range; assumption. }
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (kernel_call_task_source call entry) &&
    (kernel_call_execution_owned external platform call
       (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) ** kernel_program_inv sg entry **
     store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg original saved original_entry descriptor entry.(TskState) focus)
       entry.(TskState).(parkedTaskStacks) **
     (perr # UChar |->_ ** tmr_task_local_padding perr ** frame))) end.
  { unfold armv7a_task_restored_execution; rewrite Hnone, Hfragments; fold region.
    rewrite task_stack_fragments_rep_complete, kernel_program_inv_split_unmap, Hperr.
    sep_apply_l_atomic (tmr_task_stack_local_byte region lower value upper Hsize Hlower Hupper).
    pose proof (kernel_saved_sched_call_initial_entry_resources external platform port abi initial critical
      sg state selected fragments original saved original_entry descriptor focus Hbinding Hgeometry Hcurrent) as Hregister.
    cbv zeta in Hregister; fold region fragments call entry in Hregister.
    fold fragments.
    match type of Hregister with ?P |-- ?Q =>
      eapply derivable1_trans with (P ** (unmap_table_rep sg **
        (region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
        tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4) ** frame)); [entailer!|] end.
    sep_apply_l_atomic Hregister; Intros; fold call entry; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [Hsource Howned].
  assert (Hvalid : UCOS2_state_inv sg entry).
  { match type of Howned with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg entry) && TT) end.
    { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Howned)). }
  assert (Hstage : sem_pend_task_call_stage sg call entry).
  { unfold sem_pend_task_call_stage; split; [exact Hsource|]. split; [exact Hrunning|].
    exists node; split; [exact Hready|]. split; [exact Hgen|].
    split; [rewrite Hpriority; lia|]. exact (conj Hevent (conj Hmulti Hflag)). }
  assert (Hsignal_read : pointer_load sg.(g_OSTmrSemSignal) (event_addr sg eid) before).
  { match type of Howned with ?P before => assert (Hobserve : P |-- UCOS2_inv sg entry ** TT) end.
    { rewrite kernel_program_inv_split_unmap; entailer!; intros ? ?; exact I. }
    pose proof (tmr_task_signal_pointer_read sg entry (TT) before Henabled Hinitialized
      (Hobserve before Howned)) as Hread.
    change entry.(TimerState).(timerSignalSem) with state.(TimerState).(timerSignalSem) in Hread.
    rewrite Hsignal in Hread; exact Hread. }
  assert (Htype : event.(eventType) = OS_EVENT_TYPE_SEM).
  { match type of Howned with ?P before => assert (Hcell : P |--
      (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type event.(eventType) ** TT) end.
    { rewrite kernel_program_inv_split_unmap.
      sep_apply_l_atomic (sem_post_field_split_full sg entry eid event EventTypeField Hlookup ltac:(simpl; tauto)).
      cbn [event_cell event_image event_field_offset]; unfold OSEventType_off; entailer!; intros ? ?; exact I. }
    pose proof (uchar_load_deterministic _ _ _ _
      (framed_uchar_store_load _ _ _ _ (Hcell before Howned)) Htype_read) as Hencoded.
    destruct event.(eventType); cbn [encode_event_type] in Hencoded; congruence. }
  assert (Hnesting : entry.(IntrState).(intNesting) = 0 /\ entry.(IntrState).(lockNesting) = 0).
  { assert (Hcells : kernel_program_inv sg entry |--
      sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) **
      sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) ** TT).
    { rewrite kernel_program_inv_split_unmap, UCOS2_inv_split_interrupt.
      unfold interrupt_inv, store_int_state; entailer!; intros ? ?; exact I. }
    match type of Howned with ?P before => assert (Hint : P |--
      sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) ** TT) end.
    { sep_apply_l_atomic Hcells; entailer!; intros ? ?; exact I. }
    match type of Howned with ?P before => assert (Hlock : P |--
      sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) ** TT) end.
    { sep_apply_l_atomic Hcells; entailer!; intros ? ?; exact I. }
    split; eapply uchar_load_deterministic; [|exact Hint_read| |exact Hlock_read];
      eapply framed_uchar_store_load; [exact (Hint before Howned)|exact (Hlock before Howned)]. }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  match type of Howned with ?P before => assert (Horder : P |--
    kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
    (kernel_program_inv sg entry ** store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg original saved original_entry descriptor entry.(TskState) focus)
       entry.(TskState).(parkedTaskStacks) **
     (perr # UChar |->_ ** tmr_task_local_padding perr ** frame))) by entailer! end.
  pose proof (Horder before Howned) as Hfirst; rewrite <- Hmask in Hfirst.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) entry before final_registers acquired after _ Hsaved Hfirst Hsave)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  assert (Hzero : encode_event_cnt_value event = 0).
  { match type of Hafter with ?P after => assert (Hcell : P |--
      (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event ** TT) end.
    { rewrite kernel_program_inv_split_unmap.
      sep_apply_l_atomic (sem_post_count_split_full sg entry eid event Hlookup Htype).
      entailer!; intros ? ?; exact I. }
    exact (task_create_wait_count_read_zero _ _ _ _ (Hcell after Hafter) Hlow Hhigh). }
  split; [exact Hsignal_read|]. split.
  - unfold kernel_call_save_uninterrupted_execution; econstructor.
    + constructor; [exact Hreturn|reflexivity].
    + exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - split; [exact Hstate|]. split; [apply sem_pend_precritical_clear; exact Hnonnull|].
    split.
    + unfold os_sched_selection_enabled; rewrite (proj1 Hnesting), (proj2 Hnesting); reflexivity.
    + split; [exact Hcoverage|].
      destruct (sem_pend_task_stage_wait_entry sg call entry eid event Hstage Hvalid Hlookup Htype Hzero Hlayout)
        as [old [Hwait [_ [Hcall Hcache]]]].
      exists old; split; [exact Hwait|]. split; [exact Hcall|]. split; [exact Hcache|].
      match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) by entailer! end end.
      exact (Hclose after Hafter).
Qed.
