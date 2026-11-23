Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The action begins after the hook. Reusing the whole-Scheduler
    transfer constructor here would execute the prefix/SP/hook twice;
    ClientFrame would incorrectly require OSTCBCur to be unchanged.
    The concrete installation constructor instead has exactly this edge. *)
Lemma os_sched_install_client_task_source :
  forall external port context outgoing incoming resumed sg before after,
  kernel_client_step (os_sched_install_client external context outgoing incoming resumed)
    sg before after ->
  task_execution_source_step external port sg
    context.(os_sched_call_origin) before
    (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)) after.
Proof.
  intros external port context outgoing incoming resumed sg before after
    [Hsaved [Hdestination [_ ->]]].
  eapply TaskExecutionSchedulerInstall; eassumption.
Qed.

(** Registration, actor identity and control transfer refer to one actual
    action on one state edge. The Timer projection is a literal frame of
    this installation, so the existing resumption trace follows without
    another relation or a new environment/ABI preservation law. *)
Lemma os_sched_install_client_registered_source :
  forall external port context outgoing incoming resumed clients sg observer event_observer before after,
  clients (os_sched_install_client external context outgoing incoming resumed) ->
  context.(os_sched_call_invocation) <> observer ->
  kernel_client_step (os_sched_install_client external context outgoing incoming resumed)
    sg before after ->
  kernel_client_task_source_trace external port clients sg observer event_observer
    context.(os_sched_call_origin) before false
    (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)) after /\
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    context.(os_sched_call_origin) before false
    (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)) after.
Proof.
  intros external port context outgoing incoming resumed clients sg observer event_observer before after
    Hregistered Hforeign Hstep.
  assert (Hsource : kernel_client_task_source_trace external port clients sg observer event_observer
    context.(os_sched_call_origin) before false
    (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)) after).
  { eapply KernelClientTaskSourceStep with
      (action := os_sched_install_client external context outgoing incoming resumed)
      (middle := RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration))
      (transient := after) (stopped := false).
    - exact Hregistered.
    - cbn; congruence.
    - intros invocation Hobserver; cbn; discriminate.
    - exact Hstep.
    - eapply os_sched_install_client_task_source; exact Hstep.
    - constructor. }
  split; [exact Hsource|].
  eapply KernelResumptionTaskSourceSegment with
    (middle := RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration))
    (transient := after) (stopped1 := false) (stopped2 := false).
  - exact Hsource.
  - pose proof (os_sched_install_client_state_frame external context outgoing incoming resumed
      sg before after Hstep) as [_ [_ [_ [_ [_ [_ Htimer]]]]]].
    rewrite Htimer; constructor.
  - constructor.
Qed.

(** This is the actual consumer, not a free-standing trace wrapper: use
    the cache-store/SP-read execution and the owned generic map to obtain
    both traces and the successor resources at the SAME heap endpoint.
    Every descriptor retains its local cut. Reindexing to current is
    definitional because install changes only the parked map and current
    caches, leaving the used TCBs (including live SPs) unchanged.

    A caller may put its physically owned private-pool bytes in [frame]
    for this masked install cut. No frame across a hook, a foreign call or
    a future switch is inferred here. Registration is the existing trace
    membership obligation; no public function gains a future-return input. *)
Lemma os_sched_install_continuation_source_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    clients sg observer event_observer context outgoing state incoming resumed
    (local : Armv7aContinuation -> Assertion) (frame : Assertion) before after sp,
  clients (os_sched_install_client external context outgoing incoming resumed) ->
  context.(os_sched_call_invocation) <> observer ->
  os_sched_saved_stack_binding context outgoing state ->
  os_sched_destination_binding external context outgoing state incoming resumed ->
  sched_high_ready_consistency state.(TskState) state.(SchedState) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (UCOS2_inv sg state **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   kernel_saved_continuation_entry abi state.(TskState) local
     (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  sched_install_heap_fragment sg before after (task_slot_addr sg incoming.(stackLeaseSlot)) sp ->
  let current := os_sched_install_context context outgoing incoming state in
  kernel_client_task_source_trace external port clients sg observer event_observer
    context.(os_sched_call_origin) state false
    (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)) current /\
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    context.(os_sched_call_origin) state false
    (RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)) current /\
  task_current_at current incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
  external.(os_sched_arch_restore_source) incoming sp resumed /\
  (UCOS2_inv sg current ** task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
   kernel_saved_continuation_entry abi current.(TskState) local
     (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
   store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
     current.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi clients sg observer event_observer context outgoing state incoming resumed
    local frame before after sp Hregistered Hforeign Hsaved Hdestination Hhigh Haddress Hpre Hactual current.
  destruct (os_sched_install_client_resources external sg context outgoing state incoming resumed
    (kernel_saved_continuation_entry abi state.(TskState) local) frame before after sp
    Hsaved Hdestination Hhigh Haddress Hpre Hactual)
    as [Hstep [Hcurrent [Hrestore Hpost]]].
  destruct (os_sched_install_client_registered_source external port context outgoing incoming resumed
    clients sg observer event_observer state current Hregistered Hforeign Hstep) as [Hsource Hresumption].
  split; [exact Hsource|]. split; [exact Hresumption|].
  split; [exact Hcurrent|]. split; [exact Hrestore|].
  exact Hpost.
Qed.
