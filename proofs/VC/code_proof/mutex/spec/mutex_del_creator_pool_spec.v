Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_call_stack_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_type_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_allocation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Import UCOS2_C_Rules EventStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** At a whole-pool cut this cursor owns no second ECB. The allocation's
    bytes are in event_private_pool_rep outside this assertion. A creator
    borrows them only during its actual field/publication instruction.
    Other pending creators may remain in the same existing private map. *)
Definition mutex_del_creator_pool_cursor {external platform port}
  (abi : Armv7aContinuationABI external platform port) focus payload sg pointer state : Assertion :=
  EX eid allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
    kernel_client_call_stack_world abi sg focus payload state.

Lemma mutex_del_creator_pool_allocate : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload sg state before cut after (frame : Assertion),
  mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after ->
  (kernel_client_call_stack_world abi sg focus payload state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists returned,
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
      sg focus payload cut returned ** event_private_pool_rep sg returned.(EventState) ** frame) after.
Proof.
  intros external platform port abi focus payload sg state before cut after frame Hsource Hpre.
  assert (Hopen : kernel_client_call_stack_world abi sg focus payload state **
      event_private_pool_rep sg state.(EventState) ** frame |--
    coq_prop (kernel_client_call_stack_facts focus payload state) &&
    (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) **
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_call_stack_world; entailer!. }
  destruct (Hopen before Hpre) as [Hfocus Howned].
  destruct Hsource as [heap Hbinding Hread|before pointer next after Hbinding Hnonzero Hread Hnext Hwrites].
  - destruct (event_private_pool_allocate_heap sg state heap _ Hbinding Howned)
      as [result [allocated [produced [Hhead [Hstep [Hrun Hpost]]]]]].
    pose proof (pointer_load_deterministic _ _ _ _ Hread Hhead) as Hpointer.
    destruct result as [[eid image]|].
    + destruct Hrun as [Hnonzero _]; cbn [event_create_return_ptr] in Hpointer.
      exfalso; apply Hnonzero; symmetry; exact Hpointer.
    + destruct (event_create_allocate_critical_empty_frame _ _ Hstep) as [_ ->].
      exists state; split; [constructor; exact Hstep|exact Hpre].
  - destruct (event_private_pool_allocate_heap sg state before _ Hbinding Howned)
      as [result [allocated [produced [Hhead [Hstep [Hrun Hpost]]]]]].
    pose proof (pointer_load_deterministic _ _ _ _ Hread Hhead) as Hpointer.
    destruct result as [[eid image]|].
    + cbn [event_create_return_ptr] in Hpointer.
      destruct Hrun as [Hpositive [actual_next [Hnext_read Hwrite]]].
      assert (next = actual_next).
      { rewrite Hpointer in Hnext; eapply pointer_load_deterministic; eassumption. }
      subst actual_next.
      assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
      pose proof (event_create_allocate_critical_task_frame _ _ _ Hstep) as Htasks.
      pose proof (proj2 (event_create_allocate_critical_private_result state eid image allocated Hstep)) as Hlookup.
      exists allocated; split.
      * rewrite Hpointer; econstructor; exact Hstep.
      * assert (Hclose : kernel_program_inv sg allocated ** event_private_pool_rep sg allocated.(EventState) **
          (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) |--
          kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
            sg focus payload (KernelClientHeapExtra pointer) allocated **
            event_private_pool_rep sg allocated.(EventState) ** frame).
        { cbn [kernel_client_call_stack_resources]; unfold mutex_del_creator_pool_cursor.
          Exists eid (sem_create_allocation_identity state image).
          unfold kernel_client_call_stack_world, kernel_client_call_stack_facts in *.
          rewrite Htasks; cbn [sem_create_allocation_identity eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
        exact (Hclose after Hpost).
    + cbn [event_create_return_ptr] in Hpointer; exfalso; apply Hnonzero; exact Hpointer.
Qed.

Lemma mutex_del_creator_pool_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload sg creator state eid allocation image,
  UCOS2_state_inv sg state ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation.(eventPrivateMutexPCP) = None ->
  mutex_del_creator_arguments creator ->
  allocation.(eventPrivateStorage) = event_create_stores_image image (mutex_del_creator_fields sg creator) ->
  kernel_client_call_stack_world abi sg focus payload state ** event_private_pool_rep sg state.(EventState) |--
  kernel_client_call_stack_world abi sg focus payload (mutex_del_creator_published_state creator state eid allocation) **
    event_private_pool_rep sg (mutex_del_creator_published_state creator state eid allocation).(EventState).
Proof.
  intros external platform port abi focus payload sg creator state eid allocation image Hvalid Hget Hqueue Hpcp Hargs Himage.
  sep_apply_l_atomic (event_private_pool_split_publish sg state.(EventState) eid allocation
    (mutex_del_creator_event creator allocation) Hget).
  sepcon_assoc_change.
  sep_apply_l_atomic (mutex_del_creator_call_stack_publish external platform port abi focus payload sg creator state
    eid allocation image Hvalid Hget Hqueue Hpcp Hargs Himage).
  cbn [mutex_del_creator_published_state replace_EventS EventState]; entailer!.
Qed.

Lemma mutex_del_creator_pool_initialization : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload sg creator pointer state before (frame : Assertion),
  mutex_del_creator_arguments creator ->
  (mutex_del_creator_pool_cursor abi focus payload sg pointer state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists eid allocation initialized final after,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    event_create_private_stores eid (mutex_del_creator_fields sg creator) state tt initialized /\
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write))
        (mutex_del_creator_fields sg creator)) before after /\
    (kernel_client_call_stack_world abi sg focus payload
      (mutex_del_creator_published_state creator initialized eid final) **
      event_private_pool_rep sg (mutex_del_creator_published_state creator initialized eid final).(EventState) ** frame) after.
Proof.
  intros external platform port abi focus payload sg creator pointer state before frame Hargs Hpre.
  assert (Hopen : mutex_del_creator_pool_cursor abi focus payload sg pointer state **
      event_private_pool_rep sg state.(EventState) ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        UCOS2_state_inv sg state /\ kernel_client_call_stack_facts focus payload state) &&
      (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) **
        (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold mutex_del_creator_pool_cursor; Intros eid allocation; Exists eid allocation.
    unfold kernel_client_call_stack_world, kernel_program_inv; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp [Hvalid Hfocus]]]]] Howned]]].
  destruct (event_private_pool_prefix_heap sg eid (mutex_del_creator_fields sg creator) state allocation before _
    Hget (mutex_del_creator_fields_in_range sg creator Hargs) Howned)
    as [final [initialized [after [Hstores [Hfinal [Hwrites Hafter]]]]]].
  pose proof (event_create_private_stores_preserves_validity sg eid _ state tt initialized Hvalid Hstores) as Hinitialized.
  destruct (event_create_private_stores_post_allocation eid _ state tt initialized allocation Hget Hstores)
    as [actual [Hactual [_ [_ [Hqueue_final Himage]]]]].
  assert (actual = final) by congruence; subst actual.
  pose proof (event_create_private_stores_mutex_pcp_eq eid _ state tt initialized allocation final
    Hget Hstores Hfinal) as Hpcp_final.
  assert (Htasks : initialized.(TskState) = state.(TskState)).
  { pose proof (event_create_private_stores_published_frame eid _ state tt initialized Hstores); tauto. }
  assert (Hclose : kernel_program_inv sg initialized ** event_private_pool_rep sg initialized.(EventState) **
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) |--
    kernel_client_call_stack_world abi sg focus payload
      (mutex_del_creator_published_state creator initialized eid final) **
      event_private_pool_rep sg (mutex_del_creator_published_state creator initialized eid final).(EventState) ** frame).
  { eapply derivable1_trans.
    2: { apply derivable1_sepcon_mono; [eapply mutex_del_creator_pool_publish; eassumption || congruence|reflexivity]. }
    unfold kernel_client_call_stack_world, kernel_client_call_stack_facts in *; rewrite Htasks; entailer!. }
  exists eid, allocation, initialized, final, after.
  split; [exact Hpointer|]. split; [exact Hget|]. split; [exact Hstores|]. split; [exact Hfinal|].
  split; [rewrite Hpointer; exact Hwrites|exact (Hclose after Hafter)].
Qed.

Lemma mutex_del_creator_pool_publication_extension : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator,
  mutex_del_creator_arguments creator ->
  event_private_pool_call_stack_extension_valid abi (mutex_del_creator_pool_cursor abi focus payload)
    focus payload (mutex_del_creator_publication_step creator) (mutex_del_creator_publication_effect creator).
Proof.
  intros external platform port abi focus payload creator Hargs sg cut before next after state frame Hsource Hpre.
  destruct Hsource as [before cut after Hallocate|pointer before after Hwrites].
  - destruct (mutex_del_creator_pool_allocate external platform port abi focus payload sg state before cut
      after frame Hallocate Hpre) as [returned [Hstep Hafter]].
    exists returned; split; [constructor; exact Hstep|exact Hafter].
  - destruct (mutex_del_creator_pool_initialization external platform port abi focus payload sg creator pointer
      state before frame Hargs Hpre) as [eid [allocation [initialized [final [produced
        [Hpointer [Hget [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
    exists (mutex_del_creator_published_state creator initialized eid final).
    split; [econstructor; eassumption|exact Hafter].
Qed.

(** Lifting an ALREADY proved actual instruction law. Used below only
    for the two concrete counter producers, whose Event state is equal.
    This is not a law supplied by the ABI or by an arbitrary handler. *)
Lemma mutex_del_creator_pool_cursor_transport : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload pointer state next before after
  (frame : Assertion),
  next.(EventState) = state.(EventState) ->
  (forall private_frame : Assertion,
    (kernel_client_call_stack_world abi sg focus payload state ** private_frame) before ->
    (kernel_client_call_stack_world abi sg focus payload next ** private_frame) after) ->
  (mutex_del_creator_pool_cursor abi focus payload sg pointer state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  (mutex_del_creator_pool_cursor abi focus payload sg pointer next **
    event_private_pool_rep sg next.(EventState) ** frame) after.
Proof.
  intros external platform port abi sg focus payload pointer state next before after frame Hevent Hactual Hpre.
  assert (Hopen : mutex_del_creator_pool_cursor abi focus payload sg pointer state **
      event_private_pool_rep sg state.(EventState) ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
      (kernel_client_call_stack_world abi sg focus payload state **
        (event_private_pool_rep sg state.(EventState) ** frame))).
  { unfold mutex_del_creator_pool_cursor; Intros eid allocation; Exists eid allocation; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [Hfacts Howned]]].
  pose proof (Hactual _ Howned) as Hafter.
  assert (Hclose : kernel_client_call_stack_world abi sg focus payload next **
      (event_private_pool_rep sg state.(EventState) ** frame) |--
    mutex_del_creator_pool_cursor abi focus payload sg pointer next **
      event_private_pool_rep sg next.(EventState) ** frame).
  { unfold mutex_del_creator_pool_cursor; Exists eid allocation; rewrite Hevent; entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma mutex_del_creator_pool_field : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload creator pointer state field stored
  (frame : Assertion) before after,
  mutex_del_creator_arguments creator -> In (field, stored) (mutex_del_creator_fields sg creator) ->
  kernel_heap_execution (event_create_field_writes pointer field stored) before after ->
  (mutex_del_creator_pool_cursor abi focus payload sg pointer state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists eid allocation,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (mutex_del_creator_pool_cursor abi focus payload sg pointer
      (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) **
      event_private_pool_rep sg (event_private_write state.(EventState) eid allocation field (Some stored)) ** frame) after.
Proof.
  intros external platform port abi sg focus payload creator pointer state field stored frame before after
    Hargs Hin Hsource Hpre.
  pose proof (mutex_del_creator_fields_in_range sg creator Hargs) as Hranges.
  rewrite Forall_forall in Hranges; specialize (Hranges (field, stored) Hin).
  cbn [fst snd] in Hranges; destruct Hranges as [Hfield Hrange].
  assert (Hopen : mutex_del_creator_pool_cursor abi focus payload sg pointer state **
      event_private_pool_rep sg state.(EventState) ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        kernel_client_call_stack_facts focus payload state) &&
      (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) **
        (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold mutex_del_creator_pool_cursor; Intros eid allocation; Exists eid allocation.
    unfold kernel_client_call_stack_world; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp Hfocus]]]] Howned]]].
  destruct (event_private_pool_field_heap sg state eid allocation field stored before _ Hget Hfield Hrange Howned)
    as [final [produced [Hlookup [Hrun Hpost]]]].
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
  { unfold mutex_del_creator_pool_cursor; Exists eid updated.
    unfold kernel_client_call_stack_world, kernel_client_call_stack_facts in *.
    cbn [replace_EventS EventState TskState].
    unfold updated; cbn [eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
  exact (Hclose after Hpost).
Qed.

Lemma mutex_del_creator_pool_extension : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator,
  mutex_del_creator_arguments creator ->
  event_private_pool_call_stack_extension_valid abi (mutex_del_creator_pool_cursor abi focus payload)
    focus payload (mutex_del_creator_interrupt_step creator) (mutex_del_creator_interrupt_effect creator).
Proof.
  intros external platform port abi focus payload creator Hargs sg cut before next after state frame Hsource Hpre.
  destruct Hsource.
  - destruct (mutex_del_creator_pool_publication_extension external platform port abi focus payload creator Hargs
      sg cut before next after state frame H Hpre) as [returned [Hlogical Hpost]].
    exists returned; split; [constructor; exact Hlogical|exact Hpost].
  - exists (os_int_enter_state state); split; [apply MutexDelCreatorInterruptEnterState|].
    eapply mutex_del_creator_pool_cursor_transport with (state := state); [reflexivity| |exact Hpre].
    intros; eapply kernel_client_int_enter_keeps_call_stack; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state);
      split; [apply MutexDelCreatorInterruptExitState|].
    eapply mutex_del_creator_pool_cursor_transport with (state := state); [reflexivity| |exact Hpre].
    intros; eapply kernel_client_int_exit_keeps_call_stack; eassumption.
  - destruct (mutex_del_creator_pool_field external platform port abi sg focus payload creator pointer
      state field stored frame before after Hargs H H0 Hpre) as [eid [allocation [Hpointer [Hget Hpost]]]].
    exists (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state).
    split; [eapply MutexDelCreatorInterruptFieldState; eassumption|exact Hpost].
Qed.

Lemma mutex_del_creator_pool_resources_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload cut state (frame : Assertion),
  kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
    sg focus payload cut state ** event_private_pool_rep sg state.(EventState) ** frame |--
  coq_prop (UCOS2_state_inv sg state) && TT.
Proof.
  intros; destruct cut; cbn [kernel_client_call_stack_resources].
  - unfold kernel_client_call_stack_world, kernel_program_inv; entailer!.
  - unfold kernel_client_call_stack_publication; entailer!.
  - unfold mutex_del_creator_pool_cursor; Intros eid allocation.
    unfold kernel_client_call_stack_world, kernel_program_inv; entailer!.
Qed.

Lemma mutex_del_creator_step_preserves_private_types_defined : forall creator sg cut state next returned,
  UCOS2_state_inv sg state -> event_private_types_defined state.(EventState) ->
  kernel_client_heap_state_step (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  event_private_types_defined returned.(EventState).
Proof.
  intros creator sg cut state next returned Hvalid Htypes Hstep; destruct Hstep.
  - exact Htypes.
  - exact Htypes.
  - exact Htypes.
  - destruct H.
    + destruct H.
      * destruct H; eapply event_create_allocate_preserves_private_types_defined; eassumption.
      * unfold mutex_del_creator_published_state; cbn [replace_EventS EventState].
        apply event_publish_preserves_private_types_defined.
        eapply event_create_private_stores_preserves_private_types_defined; eassumption.
    + exact Htypes.
    + exact Htypes.
    + cbn [replace_EventS EventState].
      eapply event_private_write_preserves_private_types_defined; eassumption.
Qed.

(** A checked SAME-edge composition: concrete heap, strong focused call,
    all private ECBs, initialized Type observations, approved owner-use
    history and registered source history reach one common state. This
    remains the named source projection, embedded into the enclosing
    program by inclusion; it does not remove other enabled clients. *)
Lemma mutex_program_creator_pool_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients actor creator initial
  sg observer focus payload cut before next after (frame : Assertion),
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg cut before next after ->
  forall state origin,
  mutex_program_reachable initial sg state -> event_private_types_defined state.(EventState) ->
  kernel_client_heap_observer_cut observer cut ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
    sg focus payload cut state ** event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer None
      origin state false returned_origin returned /\
    mutex_program_reachable initial sg returned /\ event_private_types_defined returned.(EventState) /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_pool_cursor abi focus payload)
      sg focus payload next returned ** event_private_pool_rep sg returned.(EventState) ** frame) after.
Proof.
  intros external platform port abi clients actor creator initial sg observer focus payload cut before next after
    frame Hinclude Hforeign Hargs Htrace.
  induction Htrace; intros state origin Hreachable Htypes Hcompatible Hpre.
  - exists state, origin; split; [constructor|]. split; [constructor|].
    split; [exact Hreachable|]. split; [exact Htypes|]. split; assumption.
  - pose proof (proj1 (mutex_del_creator_pool_resources_valid external platform port abi sg focus payload cut state
      frame before Hpre)) as Hvalid.
    assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
    { pose proof Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
    destruct (event_private_pool_call_stack_step external platform port Z abi
      (mutex_del_creator_pool_cursor abi focus payload) focus payload
      (mutex_del_creator_interrupt_step creator) (mutex_del_creator_interrupt_effect creator)
      (mutex_del_creator_pool_extension external platform port abi focus payload creator Hargs)
      sg cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    assert (Hmiddle_reachable : mutex_program_reachable initial sg middle_state).
    { eapply mutex_program_source_step_reachable; [exact Hreachable|].
      eapply mutex_del_creator_interrupt_state_source; exact Hstep. }
    pose proof (mutex_del_creator_step_preserves_private_types_defined creator sg cut state middle_cut
      middle_state Hvalid Htypes Hstep) as Hmiddle_types.
    destruct (kernel_client_heap_state_step_source external port Z
      (mutex_del_creator_source_client actor creator) sg observer None (mutex_del_creator_interrupt_effect creator)
      ltac:(constructor; constructor) ltac:(intros; constructor; constructor)
      ltac:(intros; constructor; constructor)
      (mutex_del_creator_interrupt_extension_source external port actor creator sg observer Hforeign Hnames)
      cut state middle_cut middle_state origin Hcompatible Hstep)
      as [Hmiddle_compatible [stopped [middle_origin Hsource]]].
    pose proof (mutex_del_creator_source_trace_nonstopping external port actor creator sg observer None
      origin state stopped middle_origin middle_state Hsource) as ->.
    destruct (IHHtrace middle_state middle_origin Hmiddle_reachable Hmiddle_types Hmiddle_compatible Hmiddle)
      as [returned [returned_origin [Htail [Htail_source [Hreachable_returned [Htypes_returned [Hcompatible_returned Hpost]]]]]]].
    exists returned, returned_origin; split; [econstructor; eassumption|]. split.
    + replace false with (orb false false) by reflexivity.
      eapply kernel_resumption_task_source_trace_trans; [|exact Htail_source].
      eapply kernel_resumption_task_source_trace_inclusion; eassumption.
    + split; [exact Hreachable_returned|]. split; [exact Htypes_returned|]. split; assumption.
Qed.
