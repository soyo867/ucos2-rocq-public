Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_call_resource_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_heap_observation.
From AUXLib Require Import ListLib.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations KernelHeapObservation.
Local Open Scope Z_scope.

Module TmrTaskEntryOld.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** Only the actual used-object and parked-continuation maps determine
    these resources.  Other task fields may change.  This consequence
    reuses the current capsule-owner theorem and live-coverage theorem;
    it supplies no claim that an arbitrary callee preserves either map. *)
Lemma optional_continuations_maps_reindex : forall external platform environment
  saved_local context before after,
  before.(TskState).(inUsedTaskStates) = after.(TskState).(inUsedTaskStates) ->
  before.(TskState).(parkedTaskStacks) = after.(TskState).(parkedTaskStacks) ->
  sem_pend_optional_continuation_resources external platform (Some environment)
    saved_local context before |--
  sem_pend_optional_continuation_resources external platform (Some environment)
    saved_local context after.
Proof.
  intros external platform environment saved_local context before after Hused Hparked
    heap [[Hexternal [Hplatform Hcoverage]] Hcapsules].
  split.
  - split; [exact Hexternal|]. split; [exact Hplatform|].
    eapply task_stack_live_coverage_used_map_frame; [|symmetry; exact Hparked|exact Hcoverage].
    intros slot node Hnode; exists node; split; [rewrite Hused; exact Hnode|reflexivity].
  - exact (task_tcb_init_continuation_capsules_used_map_eq environment saved_local before after
      Hused Hparked heap Hcapsules).
Qed.
End TmrTaskEntryOld.

(** The initial err byte/padding/stack fragments come from the existing
    checked owner, not from an invented address token.  This rule merely
    lifts that entailment and preserves the actual callback environment
    and arbitrary product-rule frame. *)
Lemma tmr_task_call_initial_local_byte : forall region lower value upper frame,
  region.(stackRegionWords) = Zlength lower + 1 + Zlength upper ->
  0 < Zlength lower -> 0 < Zlength upper ->
  TmrTaskRules.derivable1
    (TmrTaskRules.sepcon
      (TmrTaskRules.lift (task_stack_storage region (lower ++ [Some value] ++ upper))) frame)
    (TmrTaskRules.sepcon
      (TmrTaskRules.lift
        (UCOS2_C_Rules.sepcon
          (UCOS2_C_Rules.sepcon
            (UCOS2_C_Rules.undef_store_uchar (region.(stackRegionBase) + Zlength lower * 4))
            (tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4)))
          (task_stack_fragments_rep region (tmr_task_local_stack_fragments region lower upper)))) frame).
Proof.
  intros region lower value upper frame Hsize Hlower Hupper.
  apply TimerCalleeLift.framed_lift_entailment.
  exact (tmr_task_stack_local_byte region lower value upper Hsize Hlower Hupper).
Qed.

Section EntryResources.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

Lemma tmr_task_call_initial_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (entry_abi : Armv7aInitialCallABI external platform port abi)
  critical sg state saved lower value upper (frame : TmrTaskRules.expr),
  armv7a_initial_frame_binding saved ->
  task_current_at state saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
    Zlength lower + 1 + Zlength upper ->
  0 < Zlength lower -> 0 < Zlength upper ->
  let region := saved.(armv7a_continuation_stack).(stackLeaseRegion) in
  let call := armv7a_initial_call saved state.(TskState).(taskLifecycle).(taskNextInvocation)
    (tmr_task_local_stack_fragments region lower upper) in
  TmrTaskRules.derivable1
    (TmrTaskRules.sepcon (TmrTaskRules.lift
      (UCOS2_inv sg state ** armv7a_initial_execution abi saved **
        task_stack_storage region (lower ++ [Some value] ++ upper))) frame)
    (TmrTaskRules.sepcon (TmrTaskRules.lift
      (coq_prop (kernel_call_task_source call (armv7a_initial_call_registered saved state)) &&
       (mutex_query_closed platform critical sg call.(os_sched_call_invocation)
         call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr))
         (armv7a_initial_call_registered saved state) **
        os_sched_context_resources external call **
        (region.(stackRegionBase) + Zlength lower * 4) # UChar |->_ **
        tmr_task_local_padding (region.(stackRegionBase) + Zlength lower * 4)))) frame).
Proof.
  intros external platform port abi entry_abi critical sg state saved lower value upper
    frame Hbinding Hcurrent Hsize Hlower Hupper region call.
  apply TimerCalleeLift.framed_lift_entailment.
  exact (tmr_task_entry_call_resources external platform port abi entry_abi critical sg
    state saved lower value upper Hbinding Hcurrent Hsize Hlower Hupper).
Qed.

Lemma tmr_task_call_signal_pointer_read : forall sg state (frame : Assertion) heap,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized state.(TimerState) ->
  TmrTaskRules.lift (UCOS2_inv sg state ** frame) heap ->
  pointer_load sg.(g_OSTmrSemSignal) state.(TimerState).(timerSignalSem) (fst heap).
Proof.
  intros sg state frame heap Henabled Hinitialized Howned.
  exact (tmr_task_signal_pointer_read sg state frame (fst heap) Henabled Hinitialized Howned).
Qed.
End EntryResources.

Lemma tmr_task_call_locals_maps_reindex : forall Application
  (AppRep : Application -> TmrTaskRules.expr) external platform environment
  saved_local perr context before after application,
  before.(TskState).(inUsedTaskStates) = after.(TskState).(inUsedTaskStates) ->
  before.(TskState).(parkedTaskStacks) = after.(TskState).(parkedTaskStacks) ->
  TmrTaskRules.derivable1
    (tmr_task_call_locals AppRep external platform environment saved_local perr
      context before application)
    (tmr_task_call_locals AppRep external platform environment saved_local perr
      context after application).
Proof.
  intros Application AppRep external platform environment saved_local perr context
    before after application Hused Hparked heap
    [error_heap [rest [Hwhole [Herror [capsule_heap [app_heap [Hrest [Hcapsules Happ]]]]]]]].
  exists error_heap, rest; split; [exact Hwhole|]. split; [exact Herror|].
  exists capsule_heap, app_heap; split; [exact Hrest|]. split; [|exact Happ].
  exact (TmrTaskEntryOld.optional_continuations_maps_reindex external platform environment
    saved_local context before after Hused Hparked (fst capsule_heap) Hcapsules).
Qed.
