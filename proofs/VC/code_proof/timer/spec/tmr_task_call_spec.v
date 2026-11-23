Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_start.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_stack_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_start_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reference-only binding: the pinned Template App_TaskSwHook is empty;
    the selected port OSTaskSwHook calls it and has empty trace/debug
    branches. Canonical source obligations for BOTH actual bodies are
    checked separately with arbitrary spatial frame. This is not the
    generic application-hook relation or a default profile change. *)
Definition tmr_task_reference_switch_hook : KernelClientAction :=
  {| kernel_client_actor := None; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun _ before after => after = before |}.

Lemma tmr_task_reference_switch_hook_certificate :
  KernelClientCertificate tmr_task_reference_switch_hook.
Proof.
  constructor; cbn; intros; subst; assumption || reflexivity.
Qed.

(** The real STRB OSRunning,1 at the post-hook cut. The caller still
    supplies the existing idle/timer obligations of starting this kernel;
    they are not synthesized by the CPU resource or the store. *)
Lemma tmr_task_start_running_store : forall sg state (frame : Assertion) heap,
  task_idle_tail sg state.(TskState) ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState)) ->
  (UCOS2_inv sg state ** frame) heap ->
  exists after,
    kernel_heap_execution [(sg.(g_OSRunning), 1)] heap after /\
    (UCOS2_inv sg (kernel_running_store state) ** frame) after.
Proof.
  intros sg state frame heap Hidle Htimer Hpre.
  assert (Hsplit : UCOS2_inv sg state ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (sg.(g_OSRunning) # UChar |-> (if state.(SchedState).(isRunning) then 1 else 0) **
     (UCOS2_raw_rep_missing_running sg state ** frame))).
  { rewrite UCOS2_inv_split_running; entailer!. }
  destruct (Hsplit heap Hpre) as [Hvalid Howned].
  destruct (kernel_heap_framed_uchar_store _ _ 1 _ heap ltac:(lia) Howned)
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : sg.(g_OSRunning) # UChar |-> 1 **
      (UCOS2_raw_rep_missing_running sg state ** frame) |--
    UCOS2_inv sg (kernel_running_store state) ** frame).
  { unfold UCOS2_inv; rewrite UCOS2_raw_rep_split_running.
    assert (Hnew : UCOS2_state_inv sg (kernel_running_store state))
      by (apply kernel_running_store_preserves_validity; assumption).
    change (UCOS2_raw_rep_missing_running sg (kernel_running_store state))
      with (UCOS2_raw_rep_missing_running sg state).
    change ((kernel_running_store state).(SchedState).(isRunning)) with true; entailer!. }
  exact (Hmerge after Hafter).
Qed.

Definition tmr_task_reference_external (external : OsSchedExternalResources)
  : OsSchedExternalResources :=
  {| os_sched_arch_running := external.(os_sched_arch_running);
     os_sched_arch_save_source := external.(os_sched_arch_save_source);
     os_sched_arch_restore_source := external.(os_sched_arch_restore_source);
     os_sched_arch_resume_source := external.(os_sched_arch_resume_source);
     os_sched_hook_action := tmr_task_reference_switch_hook;
     os_sched_hook_certificate := tmr_task_reference_switch_hook_certificate |}.

(** This uses the real source CreateExt arguments and initialized TCB
    fields. The lemma applies at the completed publication cut; it does
    not elide the earlier priority-table publication/hook interval. *)
Lemma tmr_task_initialized_wait_fields : forall sg pc stack_pointer initial_name acquired slot image
  previous next,
  let node := task_set_links (task_tcb_init_commit_node
    (task_create_tcb_args (kernel_boot_timer_args sg pc) stack_pointer initial_name)
    acquired slot image) previous next in
  node.(curPrio) = sg.(osLowestPrio) - 2 /\
  node.(curPrio) <> sg.(osLowestPrio) /\
  node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [] /\
  node.(tcbFlagNode) = 0 /\ is_effectively_ready node.(stat) node.(dly) = true.
Proof. intros; repeat split; try reflexivity; cbn; lia. Qed.

(** These are the actual selected initial-frame PC/R0/LR values. Binding
    [entry] to OSTmr_Task is the reference link input, not a fact inferred
    from a task slot or from an arbitrary running token. *)
Lemma tmr_task_initial_frame_entry : forall sg entry task_return lease lower upper,
  let saved := armv7a_initial_continuation lease
    (kernel_boot_timer_args sg entry).(createStackTop) entry 0 task_return lower upper in
  saved.(armv7a_continuation_call) = None /\
  saved.(armv7a_continuation_pc) = task_stack_init_entry_pc entry /\
  hd_error saved.(armv7a_continuation_registers) = Some 0 /\
  saved.(armv7a_continuation_lr) = task_return.
Proof. intros; repeat split; reflexivity. Qed.

(** OSStart's actual selected/current stores and OSRunning store establish
    the ready call stage on the no-kernel-write reference-hook branch.
    The ready head comes from the owned initialized OS world, never from
    the architecture ABI. Other tasks and their complete state remain in
    that world. This is a source cut, not a whole OSInit/Create proof. *)
Lemma tmr_task_selected_current_ready : forall sg state slot rest node,
  UCOS2_state_inv sg state -> state.(SchedState).(readyList) = slot :: rest ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  sched_current_ready_at
    (kernel_running_store (kernel_start_ready_state state)).(TskState)
    (kernel_running_store (kernel_start_ready_state state)).(SchedState) slot node.
Proof.
  intros sg state slot rest node Hvalid Hready Hlookup.
  destruct (kernel_start_running_task_boundary sg state Hvalid
    ltac:(rewrite Hready; discriminate)) as [_ [current [selected Hboundary]]].
  assert (Hcur : (kernel_running_store (kernel_start_ready_state state)).(SchedState).(curTaskID)
    = Some slot).
  { unfold kernel_running_store, kernel_start_ready_state, sched_set_running,
      sched_install_selected, sched_refresh_high; cbn; rewrite Hready; reflexivity. }
  destruct Hboundary as [Hselected [Hcurrent Hrest]].
  assert (current = slot) by congruence; subst current.
  assert (selected = node) by (change (state.(TskState).(inUsedTaskStates) slot = Some selected)
    in Hselected; congruence).
  subst selected; split; [exact Hlookup|]. split; [exact Hcur|exact Hrest].
Qed.

Definition tmr_task_local_stack_fragments (region : TaskStackRegion)
  (lower upper : list (option Z)) : TaskStackFragments :=
  [(0, Zlength lower, lower);
   (Zlength lower + 1, region.(stackRegionWords), upper)].

Definition tmr_task_local_padding (address : addr) : Assertion :=
  (address + 1) # UChar |->_ ** (address + 2) # UChar |->_ ** (address + 3) # UChar |->_ .

(** A typed local byte is obtained from an actually owned interior word.
    [address] will be the C entry-layout binding for &err. The three other
    bytes are retained, and neither fragment owns the borrowed word. The
    layout constraints belong to the selected C stack ABI; the lemma does
    not establish a compiler/local-object address by numeric arithmetic. *)
Lemma tmr_task_stack_local_byte : forall region lower value upper,
  region.(stackRegionWords) = Zlength lower + 1 + Zlength upper ->
  0 < Zlength lower -> 0 < Zlength upper ->
  task_stack_storage region (lower ++ [Some value] ++ upper) |--
  (region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
  tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4) **
  task_stack_fragments_rep region (tmr_task_local_stack_fragments region lower upper).
Proof.
  intros region lower value upper Hsize Hlower Hupper.
  pose proof (task_stack_storage_split_region region lower [Some value] upper) as Hsplit.
  change (Zlength [Some value]) with 1 in Hsplit.
  specialize (Hsplit Hsize); sep_apply_l_atomic Hsplit.
  sep_apply_l_atomic (armv7a_uint_single_cell
    (region.(stackRegionBase) + Zlength lower * sizeof(UINT)) value).
  sep_apply_l_atomic (store_uint_undef_store_uint
    (region.(stackRegionBase) + Zlength lower * sizeof(UINT)) value).
  sep_apply_l_atomic (proj1 (kernel_undef_store_uint_uchar_equiv
    (region.(stackRegionBase) + Zlength lower * sizeof(UINT)))).
  unfold task_stack_storage_without_region, tmr_task_local_padding,
    task_stack_fragments_rep, tmr_task_local_stack_fragments.
  cbn [map]. sep_apply_r_atomic (derivable1_iter_sepcon_r
    [task_stack_fragment_rep region (0, Zlength lower, lower);
     task_stack_fragment_rep region (Zlength lower + 1, region.(stackRegionWords), upper)]).
  cbn [fold_left task_stack_fragment_rep].
  rewrite (UIntArray.mixed_seg_0_shift region.(stackRegionBase)
    (Zlength lower + 1) region.(stackRegionWords) upper).
  rewrite Hsize; replace (Zlength lower + 1 + Zlength upper - (Zlength lower + 1))
    with (Zlength upper) by lia.
  change StoreUIntAsElement.sizeA with (sizeof(UINT)).
  change (UIntArray.mixed_seg region.(stackRegionBase) 0 (Zlength lower) lower)
    with (UIntArray.mixed_full region.(stackRegionBase) (Zlength lower) lower).
  change (UIntArray.mixed_seg
    (region.(stackRegionBase) + (Zlength lower + 1) * sizeof(UINT)) 0 (Zlength upper) upper)
    with (UIntArray.mixed_full
      (region.(stackRegionBase) + (Zlength lower + 1) * sizeof(UINT)) (Zlength upper) upper).
  rewrite sizeof_uint; entailer!.
Qed.

Lemma tmr_task_local_stack_fragments_in_range : forall region lower upper,
  region.(stackRegionWords) = Zlength lower + 1 + Zlength upper ->
  0 < Zlength lower -> 0 < Zlength upper ->
  task_stack_fragments_in_range region.(stackRegionWords) 0
    (tmr_task_local_stack_fragments region lower upper).
Proof.
  intros; unfold tmr_task_local_stack_fragments; cbn [task_stack_fragments_in_range];
    repeat split; lia.
Qed.

(** Actual resource consumer at the first C-entry cut. Its input stack is
    the SAME restored buffer, not a fresh err allocation. The source-level
    PC/layout binding remains explicit; ready/non-Idle/registration facts
    are supplied below by the source selection/initialization path, not by
    Armv7aInitialCallABI. No blanket SemPend Require is introduced here. *)
Lemma tmr_task_entry_call_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (entry_abi : Armv7aInitialCallABI external platform port abi)
  critical sg state saved lower value upper,
  armv7a_initial_frame_binding saved ->
  task_current_at state saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
    Zlength lower + 1 + Zlength upper ->
  0 < Zlength lower -> 0 < Zlength upper ->
  let region := saved.(armv7a_continuation_stack).(stackLeaseRegion) in
  let call := armv7a_initial_call saved state.(TskState).(taskLifecycle).(taskNextInvocation)
    (tmr_task_local_stack_fragments region lower upper) in
  UCOS2_inv sg state ** armv7a_initial_execution abi saved **
    task_stack_storage region (lower ++ [Some value] ++ upper) |--
  coq_prop (kernel_call_task_source call (armv7a_initial_call_registered saved state)) &&
    (mutex_query_closed platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr))
       (armv7a_initial_call_registered saved state) **
     os_sched_context_resources external call **
     (region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
     tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4)).
Proof.
  intros external platform port abi entry_abi critical sg state saved lower value upper
    Hbinding Hcurrent Hsize Hlower Hupper region call.
  sep_apply_l_atomic (tmr_task_stack_local_byte region lower value upper Hsize Hlower Hupper).
  pose proof (armv7a_initial_call_register_resources external platform port abi entry_abi
    sg state saved (tmr_task_local_stack_fragments region lower upper) Hbinding
    (tmr_task_local_stack_fragments_in_range region lower upper Hsize Hlower Hupper) Hcurrent)
    as Hregister.
  cbv zeta in Hregister; unfold region in *; sep_apply_l_atomic Hregister.
  Intros.
  rewrite mutex_query_closed_equiv.
  unfold kernel_call_execution_owned, call; entailer!.
Qed.

(** Both reloads use the current owned heap and the SAME selected node.
    This does not infer an SP from a slot address or from a CPU token. *)
Lemma tmr_task_start_selected_reads : forall sg state slot node (frame : Assertion) heap,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  (UCOS2_inv sg state ** frame) heap ->
  pointer_load sg.(g_OSTCBHighRdy) (task_slot_addr sg slot) heap /\
  pointer_load (task_slot_addr sg slot) node.(tcbStkPtr) heap.
Proof.
  intros sg state slot node frame heap Hhigh Hnode Haddress
    [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  assert (Hfocus : UCOS2_raw_rep sg state |--
    sg.(g_OSTCBHighRdy) # Ptr |-> task_slot_addr sg slot ** TT).
  { rewrite (UCOS2_raw_rep_split_module sg state SchedModule).
    cbn [UCOS2_module_rep]; unfold sched_raw_rep, sched_physical_rep.
    rewrite Hhigh; cbn [encode_task_link]; entailer!; intros ? ?; exact I. }
  split.
  - eapply pointer_load_frame; [|exact Hjoin].
    exact (framed_pointer_store_load _ _ _ owned (Hfocus owned Hraw)).
  - eapply pointer_load_frame; [|exact Hjoin].
    exact (armv7a_irq_raw_live_stack_pointer_load sg state slot node owned
      Hnode Haddress Hraw).
Qed.

(** The first OSSemPend argument is loaded from the real service-global
    cell. Its event-handle/lifetime protocol is a separate obligation; a
    loaded pointer is not by itself a live semaphore object. *)
Lemma tmr_task_signal_pointer_read : forall sg state (frame : Assertion) heap,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized state.(TimerState) ->
  (UCOS2_inv sg state ** frame) heap ->
  pointer_load sg.(g_OSTmrSemSignal) state.(TimerState).(timerSignalSem) heap.
Proof.
  intros sg state frame heap Henabled Hinitialized Howned.
  assert (Hfocus : UCOS2_inv sg state ** frame |--
    sg.(g_OSTmrSemSignal) # Ptr |-> state.(TimerState).(timerSignalSem) ** TT).
  { unfold UCOS2_inv; rewrite (UCOS2_raw_rep_split_module sg state TimerModule).
    cbn [UCOS2_module_rep].
    rewrite (timer_initialized_configured_rep_eq sg state.(TimerState) Henabled Hinitialized).
    unfold timer_raw_rep, timer_globals_rep; entailer!; intros ? ?; exact I. }
  exact (framed_pointer_store_load _ _ _ heap (Hfocus heap Howned)).
Qed.

(** Actual first-start consumer, from the post-hook source cut. It
    performs STRB OSRunning,1, takes the existing selected initial buffer,
    and on that SAME intermediate heap consumes the approved non-VFP
    restore transition. The normal C owner and err byte are then obtained
    from that restored buffer. No IRQ handler owner occurs in this chain.

    OSStart's earlier C selection and the initialized TCB fields are
    explicit source inputs; this is NOT an assertion that OSInit/OSStart
    has already executed those actions on an arbitrary public state. *)
Lemma tmr_task_start_first_save : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (start_abi : Armv7aStartRestoreABI external platform port abi)
  (entry_abi : Armv7aInitialCallABI external platform port abi)
  critical arch (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg state boot saved node lower value upper (frame : Assertion) heap,
  boot.(os_sched_call_origin) = BootInvocation ->
  armv7a_initial_frame_binding saved ->
  sched_current_ready_at state.(TskState) state.(SchedState)
    saved.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  state.(SchedState).(highRdyTid) = Some saved.(armv7a_continuation_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  node.(tcbStkPtr) = saved.(armv7a_continuation_sp) ->
  node.(curPrio) <> sg.(osLowestPrio) -> node.(eventPtr) = None ->
  node.(eventMultiWaitEvents) = [] -> node.(tcbFlagNode) = 0 ->
  tcb_field_address (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key saved.(armv7a_continuation_stack)) =
    Some (saved.(armv7a_continuation_stack).(stackLeaseRegion),
      saved.(armv7a_continuation_fragments)) ->
  saved.(armv7a_continuation_fragments) =
    task_stack_complete_fragments saved.(armv7a_continuation_stack).(stackLeaseRegion)
      (lower ++ [Some value] ++ upper) ->
  saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
    Zlength lower + 1 + Zlength upper ->
  0 < Zlength lower -> 0 < Zlength upper ->
  task_idle_tail sg state.(TskState) ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState)) ->
  let selected := kernel_start_take_stack_state (kernel_running_store state)
    saved.(armv7a_continuation_stack) in
  let registered := armv7a_initial_call_registered saved selected in
  let region := saved.(armv7a_continuation_stack).(stackLeaseRegion) in
  let call := armv7a_initial_call saved selected.(TskState).(taskLifecycle).(taskNextInvocation)
    (tmr_task_local_stack_fragments region lower upper) in
  (UCOS2_inv sg state ** (kernel_call_execution_owned external platform boot 192 ** frame)) heap ->
  exists restore_heap,
    kernel_heap_execution [(sg.(g_OSRunning), 1)] heap restore_heap /\
    pointer_load sg.(g_OSTCBHighRdy) (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot))
      restore_heap /\
    pointer_load (task_slot_addr sg saved.(armv7a_continuation_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp) restore_heap /\
    armv7a_continuation_restore_reads saved restore_heap /\
    (forall after,
      armv7a_start_restore_transition start_abi boot sg.(g_OSTCBHighRdy) saved restore_heap after ->
      armv7a_start_restore_execution sg.(g_OSTCBHighRdy) saved restore_heap after /\
      pointer_load sg.(g_OSTmrSemSignal) registered.(TimerState).(timerSignalSem) after /\
      (coq_prop (sem_pend_task_call_stage sg call registered /\
        forall eid, sem_pend_call_admission critical sg call
          registered.(TimerState).(timerSignalSem) registered eid) &&
       (mutex_query_closed platform critical sg call.(os_sched_call_invocation)
          call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) registered **
        os_sched_context_resources external call **
        (region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
        tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4) **
        task_stack_fragments_rep boot.(os_sched_call_stack).(stackLeaseRegion)
          boot.(os_sched_call_fragments) ** frame)) after /\
      (forall registers final_registers final_state final_heap,
        registers.(kernel_save_return_word) = None ->
        valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) =
          armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) ->
        armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers)
          registered after final_registers final_state final_heap ->
        kernel_call_save_uninterrupted_execution arch registers registered after
          final_registers final_state final_heap /\
        sem_pend_save_facts critical sg call.(os_sched_call_invocation)
          (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr))
          final_registers.(kernel_save_r0) registered final_state /\
        sem_pend_task_call_stage sg call final_state /\
        (critical_region_masked platform critical sg call.(os_sched_call_invocation)
           call.(os_sched_call_origin) final_registers.(kernel_save_r0) final_state **
         UCOS2_inv sg final_state ** os_sched_context_resources external call **
         ((region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
          tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4) **
          task_stack_fragments_rep boot.(os_sched_call_stack).(stackLeaseRegion)
            boot.(os_sched_call_fragments) ** frame)) final_heap)).
Proof.
  intros external platform port abi start_abi entry_abi critical arch suffix sg state boot saved node
    lower value upper frame heap Hboot Hbinding Hready Hhigh Hgeneration Hsp
    Hnonidle Hevent Hmulti Hflag Haddress Hparked
    Hfragments Hsize Hlower Hupper Hidle Henabled Htimer selected registered region call Hpre.
  destruct (tmr_task_start_running_store sg state _ heap Hidle Htimer Hpre)
    as [restore_heap [Hstore Hwritten]].
  destruct (tmr_task_start_selected_reads sg (kernel_running_store state)
    saved.(armv7a_continuation_stack).(stackLeaseSlot) node _ restore_heap
    Hhigh (proj1 Hready) Haddress Hwritten) as [Hload_high Hload_sp].
  rewrite Hsp in Hload_sp.
  pose proof (kernel_start_take_stack_resources sg (kernel_running_store state)
    saved.(armv7a_continuation_stack) (lower ++ [Some value] ++ upper) node
    Hready eq_refl Hhigh Hgeneration ltac:(rewrite <- Hfragments; exact Hparked)) as Htake.
  assert (Hprepare : UCOS2_inv sg (kernel_running_store state) **
      (kernel_call_execution_owned external platform boot 192 ** frame) |--
    kernel_call_execution_owned external platform boot 192 **
    task_stack_fragments_rep region saved.(armv7a_continuation_fragments) **
      (UCOS2_inv sg selected ** frame)).
  { sep_apply_l_atomic Htake; Intros.
    unfold selected, region.
    rewrite Hfragments, task_stack_fragments_rep_complete; entailer!. }
  pose proof (Hprepare restore_heap Hwritten) as Hprepared.
  assert (Hread_order : kernel_call_execution_owned external platform boot 192 **
      task_stack_fragments_rep region saved.(armv7a_continuation_fragments) **
        (UCOS2_inv sg selected ** frame) |--
    task_stack_fragments_rep region saved.(armv7a_continuation_fragments) **
      (kernel_call_execution_owned external platform boot 192 ** UCOS2_inv sg selected ** frame))
    by entailer!.
  pose proof (armv7a_initial_frame_restore_reads saved _ restore_heap Hbinding
    (Hread_order restore_heap Hprepared)) as Hreads.
  assert (Hcurrent : task_current_at selected
    saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { split; [exact (proj1 (proj2 Hready))|]. exists node; split; [exact (proj1 Hready)|exact Hgeneration]. }
  assert (Hready_registered : sched_current_ready_at registered.(TskState) registered.(SchedState)
    saved.(armv7a_continuation_stack).(stackLeaseSlot) node) by exact Hready.
  exists restore_heap; split; [exact Hstore|]. split; [exact Hload_high|].
  split; [exact Hload_sp|]. split; [exact Hreads|]. intros after Hrestore.
  split; [exact (armv7a_start_restore_source _ _ _ abi start_abi _ _ _ _ _ Hrestore)|].
  destruct (armv7a_start_restore_resources _ _ _ abi start_abi boot sg.(g_OSTCBHighRdy)
    saved (UCOS2_inv sg selected ** frame) restore_heap after Hboot Hbinding Hreads Hprepared Hrestore)
    as [Hmemory Hrestored].
  split.
  - pose proof (tmr_task_signal_pointer_read sg (kernel_running_store state) _
      restore_heap Henabled (Htimer Henabled) Hwritten) as Hsignal.
    unfold pointer_load in *; rewrite Hmemory; exact Hsignal.
  -
  assert (Hfinish : armv7a_initial_execution abi saved **
      task_stack_fragments_rep region saved.(armv7a_continuation_fragments) **
      task_stack_fragments_rep boot.(os_sched_call_stack).(stackLeaseRegion)
        boot.(os_sched_call_fragments) ** (UCOS2_inv sg selected ** frame) |--
    coq_prop (sem_pend_task_call_stage sg call registered /\
      forall eid, sem_pend_call_admission critical sg call
        registered.(TimerState).(timerSignalSem) registered eid) &&
    (mutex_query_closed platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) registered **
     os_sched_context_resources external call **
     (region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
     tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4) **
     task_stack_fragments_rep boot.(os_sched_call_stack).(stackLeaseRegion)
       boot.(os_sched_call_fragments) ** frame)).
  { unfold region; rewrite Hfragments, task_stack_fragments_rep_complete.
    pose proof (tmr_task_entry_call_resources external platform port abi entry_abi critical sg
      selected saved lower value upper Hbinding Hcurrent Hsize Hlower Hupper) as Hentry.
    cbv zeta in Hentry; unfold region in *; sep_apply_l_atomic Hentry.
    Intros.
    assert (Hstage : sem_pend_task_call_stage sg call registered).
    { split; [assumption|]. split; [reflexivity|]. exists node.
      split; [exact Hready_registered|].
      cbn [call armv7a_initial_call os_sched_call_stack].
      repeat first [assumption | split]. }
    assert (Hadmission : forall eid, sem_pend_call_admission critical sg call
      registered.(TimerState).(timerSignalSem) registered eid).
    { intro eid; apply sem_pend_call_admission_task_entry; exact Hstage. }
    unfold call, registered; entailer!. }
  pose proof (Hfinish after Hrestored) as Hentry_owned.
  split; [exact Hentry_owned|].
  intros registers final_registers final_state final_heap Hreturn Hcpsr Hmask Hsave.
  destruct Hentry_owned as [[Hstage Hadmission] Hresources].
  assert (Hcall_owned :
    (mutex_query_closed platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) registered **
     os_sched_context_resources external call **
     ((region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
      tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4) **
      task_stack_fragments_rep boot.(os_sched_call_stack).(stackLeaseRegion)
        boot.(os_sched_call_fragments) ** frame)) after).
  { assert (Horder :
      mutex_query_closed platform critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) registered **
      os_sched_context_resources external call **
      (region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
      tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4) **
      task_stack_fragments_rep boot.(os_sched_call_stack).(stackLeaseRegion)
        boot.(os_sched_call_fragments) ** frame |--
      mutex_query_closed platform critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) registered **
      os_sched_context_resources external call **
      ((region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
       tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4) **
       task_stack_fragments_rep boot.(os_sched_call_stack).(stackLeaseRegion)
         boot.(os_sched_call_fragments) ** frame)) by entailer!.
    exact (Horder after Hresources). }
  eapply sem_pend_uninterrupted_first_save_resources; eassumption.
Qed.

(** Reference-hook consumer of the interrupted first Save. The focused
    capsule is taken from the SAME actual post-hook heap, then the actual
    restore and CPSID/DSB/BX suffix consume its resources. The source-indexed
    prefix and final transfer establish the acquired call stage; no stage
    at acquisition is assumed. Only the selected ordinary-return branch is
    claimed, with all other dormant entries and caller bytes framed.

    This cut still requires production of the post-hook heap, registration
    of the concrete source clients, and the actual frame-load dataflow.
    It does not solve publication/parked coverage or a generic application
    hook, and it does not claim that a deleted/suspended call must return. *)
Lemma tmr_task_interrupted_first_save_resources :
  forall configured platform port critical arch
    (continuations : Armv7aContinuationABI (tmr_task_reference_external configured) platform port)
    (suffix : Armv7aSaveSuffixABI (tmr_task_reference_external configured) platform critical arch)
    clients sg original mask before origin irq_entry handler transfer action return_pc
    (frame : Assertion) heap,
  let external := tmr_task_reference_external configured in
  let focus := armv7a_call_focus original (armv7a_save_entry_address suffix + 4) return_pc in
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg original before ->
  (forall client, clients client -> critical.(critical_region_clients) client) ->
  (forall client, clients client -> sem_pend_projected_source_client client) ->
  kernel_resumption_task_source_trace external port clients sg original.(os_sched_call_invocation) None
    original.(os_sched_call_origin) before false origin irq_entry ->
  critical.(critical_region_clients) action ->
  kernel_client_actor action <> Some original.(os_sched_call_invocation) ->
  kernel_client_stops action original.(os_sched_call_invocation) = false ->
  kernel_client_step action sg irq_entry (os_int_exit_installed_state transfer) ->
  timer_public_trace sg irq_entry.(TimerState) (os_int_exit_installed_state transfer).(TimerState) ->
  os_int_exit_transfer_source external port sg handler irq_entry transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) = task_stack_key original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (armv7a_continuation_world continuations focus (UCOS2_inv sg)
      transfer.(os_int_exit_hooked_state) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) heap ->
  exists installed saved,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    saved.(armv7a_continuation_call) = Some original /\
    saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
    saved.(armv7a_continuation_lr) = return_pc /\
    (forall registers restored final_registers resumed after,
      saved.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
      registers.(kernel_save_cpsr) = saved.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 saved.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = saved.(armv7a_continuation_lr) ->
      interrupt_saved_value mask registers.(kernel_save_r0) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
      armv7a_continuation_restore_reads saved installed ->
      armv7a_restore_transition continuations handler saved installed restored ->
      armv7a_save_suffix_transition suffix registers (os_int_exit_installed_state transfer)
        restored final_registers resumed after ->
      resumed = os_int_exit_installed_state transfer /\
      final_registers.(kernel_save_return_word) = Some return_pc /\
      kernel_call_save_source external port critical sg original
        (armv7a_continuation_resumed_call saved original) mask final_registers.(kernel_save_r0)
        before resumed /\
      sem_pend_save_facts critical sg original.(os_sched_call_invocation) mask
        final_registers.(kernel_save_r0) before resumed /\
      sem_pend_task_call_stage sg (armv7a_continuation_resumed_call saved original) resumed /\
      (critical_region_masked platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) final_registers.(kernel_save_r0) resumed **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
       UCOS2_inv sg resumed **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) **
       (armv7a_parked_continuations continuations focus resumed ** frame)) after).
Proof.
  intros configured platform port critical arch continuations suffix clients sg original mask before
    origin irq_entry handler transfer action return_pc frame heap external focus Hvalid Hstage
    Hregistered Hclients Hprefix Hin Hforeign Hstop Hstep Htimer Htransfer Hkey Haddress Hpre.
  pose proof Htransfer as [_ [_ [_ [Hhook [Hdestination Hreturn]]]]].
  change (transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true irq_entry) in Hhook.
  destruct (armv7a_install_take_continuation external platform port continuations
    focus sg transfer _ heap Hdestination Hkey Haddress Hpre)
    as [installed [saved [Hinstall [Hbinding [Hfocused [Hstack [Hfragments [Hcurrent Howned]]]]]]]].
  destruct Hfocused as [Hcall [Hcursor Hlr]].
  change (saved.(armv7a_continuation_call) = Some original) in Hcall.
  change (saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4) in Hcursor.
  change (saved.(armv7a_continuation_lr) = return_pc) in Hlr.
  destruct Hbinding as [Hlength HcallStack]; rewrite Hcall in HcallStack.
  assert (Hselected : transfer.(os_int_exit_incoming_stack) = original.(os_sched_call_stack))
    by congruence.
  exists installed, saved; split; [exact Hinstall|]. split; [exact Hcall|].
  split; [exact Hcursor|]. split; [exact Hlr|].
  intros registers restored final_registers resumed after Hsp Hcpsr Hr0 Hregisterlr
    Hsaved HsavedRegister Hreads Hrestore Hsuffix.
  destruct (sem_pend_interrupt_transfer_acquires_call_stage external port critical clients sg original
    mask registers.(kernel_save_r0) before origin irq_entry handler transfer action Hvalid Hstage
    Hregistered Hclients Hprefix Hin Hforeign Hstop Hstep Htimer Htransfer Hhook Hselected Hsaved)
    as [Hsource Hacquired].
  assert (HresumedSource : kernel_call_save_source external port critical sg original
    (armv7a_continuation_resumed_call saved original) mask registers.(kernel_save_r0)
    before (os_int_exit_installed_state transfer)).
  { unfold kernel_call_save_source in *.
    cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    rewrite <- HcallStack; exact Hsource. }
  assert (Horder : armv7a_continuation_world continuations focus (UCOS2_inv sg)
      (os_int_exit_installed_state transfer) **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation continuations saved **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation continuations saved **
    (UCOS2_inv sg (os_int_exit_installed_state transfer) **
      (armv7a_parked_continuations continuations focus (os_int_exit_installed_state transfer) ** frame))).
  { unfold armv7a_continuation_world; entailer!. }
  destruct (armv7a_restored_save_returns_owned_source external platform port critical arch
    continuations suffix sg handler saved original mask before (os_int_exit_installed_state transfer)
    registers installed restored final_registers resumed after _ Hvalid (proj1 Hstage)
    Hcall Hcursor Hcpsr Hr0 Hregisterlr HsavedRegister HresumedSource Hreads
    (Horder installed Howned) Hrestore Hsuffix)
    as [Hstate [Hreturned [HsourceAfter [HcallerAfter Hafter]]]].
  subst resumed; split; [reflexivity|]. split; [rewrite Hlr in Hreturned; exact Hreturned|].
  split; [exact HsourceAfter|]. split.
  - unfold sem_pend_save_facts; split; [exact Hvalid|].
    pose proof (kernel_call_save_source_region_interval external port critical sg original
      (armv7a_continuation_resumed_call saved original) mask final_registers.(kernel_save_r0)
      before (os_int_exit_installed_state transfer) HsourceAfter) as Hinterval.
    split; [exact Hinterval|]. split.
    + exact (proj2 (proj2 (proj2 (proj2 HsourceAfter)))).
    + exact (proj1 (critical_region_interval_transports_resources critical sg
        original.(os_sched_call_invocation) before (os_int_exit_installed_state transfer) Hinterval Hvalid)).
  - split; [|exact Hafter].
    unfold sem_pend_task_call_stage in *.
    split; [exact HcallerAfter|].
    cbn [armv7a_continuation_resumed_call os_sched_call_stack].
    rewrite <- HcallStack; exact (proj2 Hacquired).
Qed.
