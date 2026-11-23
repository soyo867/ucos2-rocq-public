Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.helpers Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_allocation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Import UCOS2_C_Rules EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Every projected action has its existing configured-program source
    classification. This supplies a compositional member proof; it does
    not replace the complete registry by this creator family. Ordinary
    validity/resource certificates remain separately required. *)
Lemma mutex_program_creator_source_client : forall actor creator action,
  mutex_del_creator_source_client actor creator action -> mutex_program_source_client action.
Proof.
  intros actor creator action Hsource; destruct Hsource.
  - destruct H.
    + apply MutexProgramSourceProfileCut.
    + apply MutexProgramSourceProfileCut.
    + apply MutexProgramSourceTaskPublication.
    + apply mutex_program_event_allocate_registered.
  - apply mutex_program_event_private_store_registered.
  - apply MutexProgramSourceNonMutexPublication; destruct creator; discriminate.
Qed.

(** These are real counter instructions inside a pending creator cut.
    The private ECB is not forced to finish/publish before IntEnter or the
    no-schedule IntExit branch can run. A scheduling IntExit, Queue's QCB,
    and a second private creator are separate source stages, not erased. *)
Lemma mutex_del_creator_int_enter_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload pointer state
  (frame : Assertion) before after,
  (mutex_del_creator_call_stack_pending abi focus payload sg pointer state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  (mutex_del_creator_call_stack_pending abi focus payload sg pointer (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port abi sg focus payload pointer state frame before after Hpre Hsource.
  assert (Hopen : mutex_del_creator_call_stack_pending abi focus payload sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
      (kernel_client_call_stack_world abi sg focus payload state **
        (event_private_storage_rep sg eid allocation ** frame))).
  { unfold mutex_del_creator_call_stack_pending; Intros eid allocation; Exists eid allocation; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [Hfacts Howned]]].
  pose proof (kernel_client_int_enter_keeps_call_stack external platform port abi sg focus payload state
    (event_private_storage_rep sg eid allocation ** frame) before after Howned Hsource) as Hpost.
  assert (Hclose : kernel_client_call_stack_world abi sg focus payload (os_int_enter_state state) **
      (event_private_storage_rep sg eid allocation ** frame) |--
    mutex_del_creator_call_stack_pending abi focus payload sg pointer (os_int_enter_state state) ** frame).
  { unfold mutex_del_creator_call_stack_pending; Exists eid allocation.
    unfold os_int_enter_state; cbn [replace_IntrS EventState]; entailer!. }
  exact (Hclose after Hpost).
Qed.

Lemma mutex_del_creator_int_exit_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload pointer state
  (frame : Assertion) before after,
  (mutex_del_creator_call_stack_pending abi focus payload sg pointer state ** frame) before ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (mutex_del_creator_call_stack_pending abi focus payload sg pointer
    (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi sg focus payload pointer state frame before after Hpre Hsource.
  assert (Hopen : mutex_del_creator_call_stack_pending abi focus payload sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
      (kernel_client_call_stack_world abi sg focus payload state **
        (event_private_storage_rep sg eid allocation ** frame))).
  { unfold mutex_del_creator_call_stack_pending; Intros eid allocation; Exists eid allocation; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [Hfacts Howned]]].
  pose proof (kernel_client_int_exit_keeps_call_stack external platform port abi sg focus payload state
    (event_private_storage_rep sg eid allocation ** frame) before after Howned Hsource) as Hpost.
  assert (Hclose : kernel_client_call_stack_world abi sg focus payload
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      (event_private_storage_rep sg eid allocation ** frame) |--
    mutex_del_creator_call_stack_pending abi focus payload sg pointer
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame).
  { unfold mutex_del_creator_call_stack_pending; Exists eid allocation.
    unfold os_int_exit_counter_state; cbn [replace_IntrS EventState]; entailer!. }
  exact (Hclose after Hpost).
Qed.

(** A real initializer field cut can precede another IRQ. The permitted
    field/value comes from this creator's C initializer list; the step
    owns and writes the current image, preserving allocation identity.
    Whole C program order is supplied by its cursor/path, not claimed by
    this single-operation projection. *)
Lemma mutex_del_creator_field_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload creator pointer state field stored
  (frame : Assertion) before after,
  mutex_del_creator_arguments creator ->
  In (field, stored) (mutex_del_creator_fields sg creator) ->
  kernel_heap_execution (event_create_field_writes pointer field stored) before after ->
  (mutex_del_creator_call_stack_pending abi focus payload sg pointer state ** frame) before ->
  exists eid allocation,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (mutex_del_creator_call_stack_pending abi focus payload sg pointer
      (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame) after.
Proof.
  intros external platform port abi sg focus payload creator pointer state field stored frame before after
    Hargs Hin Hsource Hpre.
  pose proof (mutex_del_creator_fields_in_range sg creator Hargs) as Hranges.
  rewrite Forall_forall in Hranges; specialize (Hranges (field, stored) Hin).
  cbn [fst snd] in Hranges; destruct Hranges as [Hfield Hrange].
  assert (Hopen : mutex_del_creator_call_stack_pending abi focus payload sg pointer state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        kernel_client_call_stack_facts focus payload state) &&
      (event_private_storage_rep sg eid allocation ** kernel_program_inv sg state **
        (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold mutex_del_creator_call_stack_pending; Intros eid allocation; Exists eid allocation.
    unfold kernel_client_call_stack_world; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp Hfocus]]]] Howned]]].
  destruct (event_create_private_field_heap sg state eid allocation field stored before _
    Hget Hfield Hrange Howned) as [final [produced [Hlookup [Hrun Hpost]]]].
  rewrite <- Hpointer in Hrun.
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  set (updated := {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
    eventPrivateGeneration := allocation.(eventPrivateGeneration); eventPrivateQueue := allocation.(eventPrivateQueue);
    eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
    eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |}).
  assert (Hupdated : (event_private_write state.(EventState) eid allocation field (Some stored)).(eventLifecycle).(eventPrivate)
    eid = Some updated) by apply kernel_map_set_same.
  assert (final = updated) by congruence; subst final.
  exists eid, allocation; split; [exact Hpointer|]. split; [exact Hget|].
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold mutex_del_creator_call_stack_pending; Exists eid updated.
    unfold kernel_client_call_stack_world, kernel_client_call_stack_facts in *.
    cbn [replace_EventS EventState TskState].
    unfold updated; cbn [eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
  exact (Hclose after Hpost).
Qed.

Inductive mutex_del_creator_interrupt_step creator sg :
  KernelClientHeapCut Z -> model -> KernelClientHeapCut Z -> model -> Prop :=
| MutexDelCreatorInterruptBase : forall cut before next after,
    mutex_del_creator_publication_step creator sg cut before next after ->
    mutex_del_creator_interrupt_step creator sg cut before next after
| MutexDelCreatorInterruptEnter : forall pointer before after,
    kernel_client_int_enter_fragment sg before after ->
    mutex_del_creator_interrupt_step creator sg (KernelClientHeapExtra pointer) before
      (KernelClientHeapExtra pointer) after
| MutexDelCreatorInterruptExit : forall pointer before after,
    os_int_exit_masked_no_schedule_fragment sg before after ->
    mutex_del_creator_interrupt_step creator sg (KernelClientHeapExtra pointer) before
      (KernelClientHeapExtra pointer) after
| MutexDelCreatorInterruptField : forall pointer field stored before after,
    In (field, stored) (mutex_del_creator_fields sg creator) ->
    kernel_heap_execution (event_create_field_writes pointer field stored) before after ->
    mutex_del_creator_interrupt_step creator sg (KernelClientHeapExtra pointer) before
      (KernelClientHeapExtra pointer) after.

Inductive mutex_del_creator_interrupt_effect creator sg :
  KernelClientHeapCut Z -> UCOS2_Verify_State -> KernelClientHeapCut Z -> UCOS2_Verify_State -> Prop :=
| MutexDelCreatorInterruptBaseState : forall cut state next returned,
    mutex_del_creator_publication_effect creator sg cut state next returned ->
    mutex_del_creator_interrupt_effect creator sg cut state next returned
| MutexDelCreatorInterruptEnterState : forall pointer state,
    mutex_del_creator_interrupt_effect creator sg (KernelClientHeapExtra pointer) state
      (KernelClientHeapExtra pointer) (os_int_enter_state state)
| MutexDelCreatorInterruptExitState : forall pointer state,
    mutex_del_creator_interrupt_effect creator sg (KernelClientHeapExtra pointer) state
      (KernelClientHeapExtra pointer) (os_int_exit_counter_state state.(SchedState).(isRunning) state)
| MutexDelCreatorInterruptFieldState : forall pointer state eid allocation field stored,
    pointer = event_pool_addr sg eid ->
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    In (field, stored) (mutex_del_creator_fields sg creator) ->
    mutex_del_creator_interrupt_effect creator sg (KernelClientHeapExtra pointer) state
      (KernelClientHeapExtra pointer)
      (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state).

Lemma mutex_del_creator_interrupt_extension : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator,
  mutex_del_creator_arguments creator ->
  kernel_client_call_stack_extension_valid abi (mutex_del_creator_call_stack_pending abi focus payload)
    focus payload (mutex_del_creator_interrupt_step creator) (mutex_del_creator_interrupt_effect creator).
Proof.
  intros external platform port abi focus payload creator Hargs sg cut before next after state frame Hsource Hpre.
  destruct Hsource.
  - destruct (mutex_del_creator_call_stack_extension external platform port abi focus payload creator Hargs
      sg cut before next after state frame H Hpre) as [returned [Hlogical Hpost]].
    exists returned; split; [constructor; exact Hlogical|exact Hpost].
  - exists (os_int_enter_state state); split; [apply MutexDelCreatorInterruptEnterState|].
    eapply mutex_del_creator_int_enter_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state);
      split; [apply MutexDelCreatorInterruptExitState|].
    eapply mutex_del_creator_int_exit_resources; eassumption.
  - destruct (mutex_del_creator_field_resources external platform port abi sg focus payload creator pointer
      state field stored frame before after Hargs H H0 Hpre) as [eid [allocation [Hpointer [Hget Hpost]]]].
    exists (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state).
    split; [eapply MutexDelCreatorInterruptFieldState; eassumption|exact Hpost].
Qed.

Lemma mutex_del_creator_interrupt_extension_source : forall external port actor creator sg observer,
  actor <> Some observer -> sg.(osKernelConfig).(cfgEventNames) = false ->
  kernel_client_heap_extension_source external port (mutex_del_creator_source_client actor creator)
    sg observer None (mutex_del_creator_interrupt_effect creator).
Proof.
  intros external port actor creator sg observer Hforeign Hnames cut state next returned origin Hcompatible Hstep.
  destruct Hstep.
  - eapply mutex_del_creator_publication_extension_source; eassumption.
  - split; [exact I|]. exists false, origin.
    change (kernel_resumption_task_source_trace external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state
      (kernel_client_stops (kernel_full_profile_cut_client KernelFullIntEnter) observer)
      origin (os_int_enter_state state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := kernel_full_profile_cut_client KernelFullIntEnter).
    + apply MutexDelCreatorSourceAllocation; constructor.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + reflexivity.
  - split; [exact I|]. exists false, origin.
    change (kernel_resumption_task_source_trace external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state
      (kernel_client_stops (kernel_full_profile_cut_client
        (KernelFullIntExitCounter state.(SchedState).(isRunning))) observer)
      origin (os_int_exit_counter_state state.(SchedState).(isRunning) state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))).
    + apply MutexDelCreatorSourceAllocation; constructor.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + reflexivity.
  - split; [exact I|]. exists false, origin.
    change (kernel_resumption_task_source_trace external port (mutex_del_creator_source_client actor creator)
      sg observer None origin state
      (kernel_client_stops (event_create_private_store_client actor eid allocation field stored) observer)
      origin (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := event_create_private_store_client actor eid allocation field stored).
    + apply MutexDelCreatorSourceStore.
    + exact Hforeign.
    + intros; discriminate.
    + split; [exact H0|reflexivity].
    + reflexivity.
    + reflexivity.
Qed.

Lemma mutex_del_creator_interrupt_state_source : forall creator sg cut state next returned,
  kernel_client_heap_state_step (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  mutex_owner_source_step sg state returned.
Proof.
  intros creator sg cut state next returned Hstep; destruct Hstep.
  - apply MutexOwnerSourceFrame; reflexivity.
  - apply MutexOwnerSourceFrame; reflexivity.
  - eapply MutexOwnerSourceCreator with (creator := creator); apply KernelClientHeapPublishState; eassumption.
  - destruct H.
    + eapply MutexOwnerSourceCreator with (creator := creator); apply KernelClientHeapExtraState; eassumption.
    + apply MutexOwnerSourceFrame; reflexivity.
    + apply MutexOwnerSourceFrame; reflexivity.
    + apply MutexOwnerSourceFrame; reflexivity.
Qed.

Lemma mutex_program_creator_interrupt_state_trace : forall initial creator sg cut state next returned,
  mutex_program_reachable initial sg state ->
  kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  mutex_program_reachable initial sg returned.
Proof.
  intros initial creator sg cut state next returned Hreachable Htrace.
  revert Hreachable; induction Htrace; intro Hreachable; [exact Hreachable|].
  apply IHHtrace; eapply mutex_program_source_step_reachable; [exact Hreachable|].
  eapply mutex_del_creator_interrupt_state_source; eassumption.
Qed.

Lemma mutex_program_creator_interrupt_call_stack_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients actor creator initial
  sg observer origin focus payload cut before next after (frame : Assertion) state,
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  mutex_program_reachable initial sg state -> kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg cut before next after ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
    sg focus payload cut state ** frame) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer None
      origin state false returned_origin returned /\
    mutex_program_reachable initial sg returned /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload next returned ** frame) after.
Proof.
  intros external platform port abi clients actor creator initial sg observer origin focus payload cut before
    next after frame state Hinclude Hforeign Hargs Hreachable Hcompatible Htrace Hpre.
  pose proof (mutex_del_creator_call_stack_resources_valid external platform port abi sg focus payload cut state
    frame before Hpre) as [Hvalid _].
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { pose proof Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  destruct (kernel_client_call_stack_trace_source_resources external platform port Z abi
    (mutex_del_creator_call_stack_pending abi focus payload) focus payload
    (mutex_del_creator_interrupt_step creator) (mutex_del_creator_interrupt_effect creator)
    (mutex_del_creator_source_client actor creator) sg observer None
    (mutex_del_creator_interrupt_extension external platform port abi focus payload creator Hargs)
    ltac:(constructor; constructor) ltac:(intros; constructor; constructor)
    ltac:(intros; constructor; constructor)
    (mutex_del_creator_interrupt_extension_source external port actor creator sg observer Hforeign Hnames)
    cut before next after frame Htrace state origin Hcompatible Hpre)
    as [returned [stopped [returned_origin [Hlogical [Hsource [Hnext Hpost]]]]]].
  pose proof (mutex_del_creator_source_trace_nonstopping external port actor creator sg observer None
    origin state stopped returned_origin returned Hsource) as ->.
  exists returned, returned_origin; split; [exact Hlogical|]. split.
  - eapply kernel_resumption_task_source_trace_inclusion; eassumption.
  - split; [eapply mutex_program_creator_interrupt_state_trace; eassumption|]. split; assumption.
Qed.
