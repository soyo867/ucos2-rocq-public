Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This is exactly the currently proved allocation/counter/publication
    registry, not all kernel clients. The task actor is supplied by source
    call classification; the independent Event actor is the actual
    next-allocation identifier, not a fabricated anonymous action. *)
Inductive mutex_del_allocation_source_client (actor : option nat) : KernelClientAction -> Prop :=
| MutexDelAllocationIntEnter :
    mutex_del_allocation_source_client actor (kernel_full_profile_cut_client KernelFullIntEnter)
| MutexDelAllocationIntExit : forall running,
    mutex_del_allocation_source_client actor
      (kernel_full_profile_cut_client (KernelFullIntExitCounter running))
| MutexDelAllocationTaskPublish : forall publication,
    mutex_del_allocation_source_client actor (task_create_stack_publication_client publication)
| MutexDelAllocationEventAllocate : forall invocation,
    mutex_del_allocation_source_client actor (event_create_allocate_client actor invocation).

Lemma mutex_del_allocate_resumption_source : forall external port actor sg observer origin state result returned,
  actor <> Some observer ->
  event_create_allocate_critical state result returned ->
  kernel_resumption_task_source_trace external port (mutex_del_allocation_source_client actor)
    sg observer None origin state false origin returned.
Proof.
  intros external port actor sg observer origin state result returned Hforeign Hstep.
  set (invocation := state.(EventState).(eventLifecycle).(eventNextInvocation)).
  change (kernel_resumption_task_source_trace external port (mutex_del_allocation_source_client actor)
    sg observer None origin state (kernel_client_stops (event_create_allocate_client actor invocation) observer)
    origin returned).
  eapply kernel_client_framed_step_resumption_source with
    (action := event_create_allocate_client actor invocation).
  - constructor.
  - exact Hforeign.
  - intros; discriminate.
  - split; [reflexivity|]. exists result; exact Hstep.
  - unfold event_create_allocate_critical in Hstep.
    destruct state.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]]; reflexivity.
  - unfold event_create_allocate_critical in Hstep.
    destruct state.(EventState).(unUsedEventStates).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [image [_ [_ ->]]]; reflexivity.
Qed.

Lemma mutex_del_creator_heap_extension_source : forall external port actor sg observer,
  actor <> Some observer ->
  kernel_client_heap_extension_source external port (mutex_del_allocation_source_client actor)
    sg observer None mutex_del_creator_heap_effect.
Proof.
  intros external port actor sg observer Hforeign cut state next returned origin Hcompatible Hstep.
  destruct Hstep; split; try exact I;
    exists false, origin; eapply mutex_del_allocate_resumption_source; eassumption.
Qed.

Lemma mutex_del_allocation_segment_nonstopping : forall external port actor sg observer event_observer
  origin state stopped returned_origin returned,
  kernel_client_task_source_trace external port (mutex_del_allocation_source_client actor)
    sg observer event_observer origin state stopped returned_origin returned -> stopped = false.
Proof.
  intros external port actor sg observer event_observer origin state stopped returned_origin returned Htrace.
  induction Htrace as [origin state|action first before middle transient last after stopped
    Hregistered Hactor Hevent Hstep Hsource Htail IH].
  - reflexivity.
  - rewrite IH; destruct Hregistered; reflexivity.
Qed.

Lemma mutex_del_allocation_trace_nonstopping : forall external port actor sg observer event_observer
  origin state stopped returned_origin returned,
  kernel_resumption_task_source_trace external port (mutex_del_allocation_source_client actor)
    sg observer event_observer origin state stopped returned_origin returned -> stopped = false.
Proof.
  intros external port actor sg observer event_observer origin state stopped returned_origin returned Htrace.
  induction Htrace as [origin state|first before stopped1 middle transient stopped2 last after
    Hsegment Htimer Htail IH].
  - reflexivity.
  - pose proof (mutex_del_allocation_segment_nonstopping external port actor sg observer
      event_observer first before stopped1 middle transient Hsegment) as Hfirst.
    rewrite Hfirst, IH; reflexivity.
Qed.

(** Concrete consumer of the generic SAME-edge lifting theorem. The
    logical source trace and current typed resource come from the actual
    heap trace already used by Del. Exhaustion stays Closed; allocation
    stays Extra(pointer); TaskPublication still needs its real input.
    This adds neither caller execution resources nor a return guarantee.
    Broader source families and final IRQ transfer still require their own
    proved instances and inclusion in the enclosing critical registry. *)
Lemma mutex_del_allocation_trace_source_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) actor sg observer cut before next after
  (frame : Assertion) state origin,
  actor <> Some observer ->
  kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_trace mutex_del_creator_heap_step sg cut before next after ->
  (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg cut state ** frame) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace mutex_del_creator_heap_effect sg cut state next returned /\
    kernel_resumption_task_source_trace external port (mutex_del_allocation_source_client actor)
      sg observer None origin state false returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg next returned ** frame) after.
Proof.
  intros external platform port abi actor sg observer cut before next after frame state origin
    Hforeign Hcompatible Htrace Hpre.
  destruct (kernel_client_heap_trace_source_resources external platform port Z abi
    (mutex_del_creator_heap_resources abi) mutex_del_creator_heap_step mutex_del_creator_heap_effect
    (mutex_del_allocation_source_client actor) sg observer None
    (mutex_del_creator_heap_extension_valid external platform port abi)
    ltac:(constructor) ltac:(intros; constructor) ltac:(intros; constructor)
    (mutex_del_creator_heap_extension_source external port actor sg observer Hforeign)
    cut before next after frame Htrace state origin Hcompatible Hpre)
    as [returned [stopped [returned_origin [Hlogical [Hsource [Hnext Hpost]]]]]].
  pose proof (mutex_del_allocation_trace_nonstopping external port actor sg observer None
    origin state stopped returned_origin returned Hsource) as ->.
  exists returned, returned_origin; split; [exact Hlogical|].
  split; [exact Hsource|]. split; assumption.
Qed.
