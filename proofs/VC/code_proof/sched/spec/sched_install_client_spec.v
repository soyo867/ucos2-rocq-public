Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The existing OSCtxSw callee's post-hook installation cut: copy the
    selected priority/current caches and transfer the physical parked
    stack owner. This is the memory effect already specified at the C
    call boundary; the stores are in the port, not additional C statements.
    Prefix selection, outgoing SP and hook execution precede this cut.

    The actor is the actual outgoing invocation. Selecting another stack
    does not retire it or manufacture a return to the observing caller.
    High-cache consistency and the destination come from this real source
    cut, not a new public SemPend input or an all-hooks preservation law. *)
Definition os_sched_install_client (external : OsSchedExternalResources)
  (context : OsSchedCallContext) (outgoing : TaskStackFragments)
  (incoming : TaskStackLease) (resumed : TaskStackFragments) : KernelClientAction :=
  {| kernel_client_actor := Some context.(os_sched_call_invocation);
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun _ before after =>
       os_sched_saved_stack_binding context outgoing before /\
       os_sched_destination_binding external context outgoing before incoming resumed /\
       sched_high_ready_consistency before.(TskState) before.(SchedState) /\
       after = os_sched_install_context context outgoing incoming before |}.

(** Park/take changes parkedTaskStacks, while the used nodes and complete
    invocation/lifecycle registry are unchanged. These literal projections
    support the existing wait, owner-history and current-stage consumers;
    no assertion that the entire Task state is equal is used. *)
Lemma os_sched_install_client_state_frame : forall external context outgoing incoming resumed
  sg before after,
  kernel_client_step (os_sched_install_client external context outgoing incoming resumed)
    sg before after ->
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) /\
  after.(TskState).(taskLifecycle) = before.(TskState).(taskLifecycle) /\
  after.(EventState) = before.(EventState) /\
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  after.(IntrState) = before.(IntrState) /\
  after.(NameState) = before.(NameState) /\
  after.(TimerState) = before.(TimerState).
Proof.
  intros external context outgoing incoming resumed sg before after [_ [_ [_ ->]]].
  repeat split; reflexivity.
Qed.

(** The existing global validity proof already covers park/take and the
    cache stores. The selected live node supplies the priority bound.
    Registration therefore uses an ordinary proved certificate, with no
    new field in CriticalRegionResources or platform axiom. *)
Lemma os_sched_install_client_certificate : forall external context outgoing incoming resumed,
  KernelClientCertificate (os_sched_install_client external context outgoing incoming resumed).
Proof.
  intros external context outgoing incoming resumed; constructor.
  - intros sg before after Hvalid [Hsaved [Hdestination [Hhigh ->]]].
    apply os_sched_install_context_preserves_validity; [exact Hvalid|exact Hsaved|].
    destruct Hdestination as [_ [[node [Hnode [_ [Hpriority _]]]] _]].
    intros priority Hpriority_value.
    assert (priority = node.(curPrio)) by congruence; subst priority.
    pose proof (proj1 (proj2 Hvalid)) as Htasks.
    assert (Hrange : forall slot task,
      before.(TskState).(inUsedTaskStates) slot = Some task ->
      task_priority_in_range sg task.(curPrio)).
    { unfold task_in_range in Htasks; tauto. }
    eapply Hrange; exact Hnode.
  - intros sg before after observer Hvalid [_ [_ [_ ->]]] Hforeign.
    reflexivity.
  - intros sg before after observer origin Hvalid [_ [_ [_ ->]]] Hnormal Hactive.
    exact Hactive.
  - intros sg before after observer Hvalid [_ [_ [_ ->]]] Hforeign.
    reflexivity.
Qed.

(** Consume the actual ordered cache-write/SP-read endpoint. The existing
    deterministic heap theorem identifies its output with the producer's
    output; the action, selected slot and whole resource map consequently
    describe this same step. An arbitrary descriptor-indexed local may be
    instantiated as [resource]; nothing erases and rebuilds its entries.
    The frame applies only to these masked local memory effects. *)
Lemma os_sched_install_client_resources :
  forall external sg context outgoing state incoming resumed
    (resource : (TaskID * nat) -> (TaskStackRegion * TaskStackFragments) -> Assertion)
    (frame : Assertion) before after sp,
  os_sched_saved_stack_binding context outgoing state ->
  os_sched_destination_binding external context outgoing state incoming resumed ->
  sched_high_ready_consistency state.(TskState) state.(SchedState) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (UCOS2_inv sg state **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource state.(TskState).(parkedTaskStacks) ** frame) before ->
  sched_install_heap_fragment sg before after (task_slot_addr sg incoming.(stackLeaseSlot)) sp ->
  let current := os_sched_install_context context outgoing incoming state in
  kernel_client_step (os_sched_install_client external context outgoing incoming resumed)
    sg state current /\
  task_current_at current incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
  external.(os_sched_arch_restore_source) incoming sp resumed /\
  (UCOS2_inv sg current ** task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
   resource (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
   store_parked_continuations resource current.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external sg context outgoing state incoming resumed resource frame before after sp
    Hsaved Hdestination Hhigh Haddress Hpre Hactual current.
  destruct (os_sched_install_continuation_map_resources external sg context outgoing state
    incoming resumed resource frame before Hsaved Hdestination Haddress Hpre)
    as [produced [actual_sp [Hrun [[Hcurrent Hrestore] Hpost]]]].
  destruct (sched_install_heap_fragment_deterministic sg before produced after
    (task_slot_addr sg incoming.(stackLeaseSlot)) actual_sp
    (task_slot_addr sg incoming.(stackLeaseSlot)) sp Hrun Hactual)
    as [Hheap [Hpointer Hsp]].
  subst produced actual_sp.
  split.
  - exact (conj Hsaved (conj Hdestination (conj Hhigh eq_refl))).
  - exact (conj Hcurrent (conj Hrestore Hpost)).
Qed.

(** One already executed foreign installation can be appended to the
    existing raw client trace. Registration and the actual outgoing actor
    remain explicit, just as for every other KernelClientTraceStep. This
    proves no future schedule, eventual return, or arbitrary client law. *)
Lemma os_sched_install_client_registered_trace :
  forall external context outgoing incoming resumed clients sg observer before after,
  clients (os_sched_install_client external context outgoing incoming resumed) ->
  context.(os_sched_call_invocation) <> observer ->
  kernel_client_step (os_sched_install_client external context outgoing incoming resumed)
    sg before after ->
  kernel_client_trace clients sg observer before false after.
Proof.
  intros external context outgoing incoming resumed clients sg observer before after
    Hregistered Hforeign Hstep.
  eapply KernelClientTraceStep with
    (action := os_sched_install_client external context outgoing incoming resumed)
    (middle := after) (stopped := false).
  - exact Hregistered.
  - cbn; congruence.
  - intros invocation Hnone; discriminate.
  - exact Hstep.
  - constructor.
Qed.
