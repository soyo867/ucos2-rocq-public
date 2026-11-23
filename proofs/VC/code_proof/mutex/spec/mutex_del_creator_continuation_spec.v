Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_stack_equiv_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_heap_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Resource interpretation of the EXISTING creator cuts. The world is
    the shared generic continuation invariant; the Extra case adds only
    the existing allocation cursor facts. All private bytes stay in the
    one outer pool. There is no second registry, history or state record.

    [active] identifies the actual running cut and is not forced to None.
    A TaskPublication cut consumes its real initial descriptor's local;
    the initial-entry None=emp instance is supplied by its C caller. *)
Definition mutex_del_creator_continuation_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) local sg active
  (cut : KernelClientHeapCut Z) state : Assertion :=
  match cut with
  | KernelClientHeapClosed => kernel_continuation_inv abi kernel_program_inv local sg active state
  | KernelClientHeapTaskPublication publication =>
      coq_prop (UCOS2_state_inv sg state /\ task_stack_live_coverage state.(TskState) active /\
        task_create_stack_publication_input sg publication state /\
        0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
        0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
      (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
         state publication.(stack_publication_slot) publication.(stack_publication_image) **
       task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
       local (task_create_stack_publication_continuation publication) **
       store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg)
  | KernelClientHeapExtra pointer =>
      EX eid allocation,
        coq_prop (pointer = event_pool_addr sg eid /\
          state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
          allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
        kernel_continuation_inv abi kernel_program_inv local sg active state
  end.

(** Only the final logical publication changes the owner of the already
    initialized ECB. The existing Sem/Mbox merge supplies that change;
    the generic map is an untouched frame because TaskState is identical. *)
Lemma mutex_del_creator_continuation_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg active creator state eid allocation image,
  UCOS2_state_inv sg state ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation.(eventPrivateMutexPCP) = None ->
  mutex_del_creator_arguments creator ->
  allocation.(eventPrivateStorage) = event_create_stores_image image (mutex_del_creator_fields sg creator) ->
  kernel_continuation_inv abi kernel_program_inv local sg active state **
    event_private_pool_rep sg state.(EventState) |--
  kernel_continuation_inv abi kernel_program_inv local sg active
    (mutex_del_creator_published_state creator state eid allocation) **
    event_private_pool_rep sg (mutex_del_creator_published_state creator state eid allocation).(EventState).
Proof.
  intros external platform port abi local sg active creator state eid allocation image
    Hvalid Hget Hqueue Hpcp Hargs Himage.
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hmerge : event_private_storage_rep sg eid allocation **
      (event_raw_rep sg state.(TskState) state.(EventState) ** queue_storage_rep sg state.(EventState) **
        UCOS2_raw_rep_missing_event_queue sg state) |--
    UCOS2_inv sg (mutex_del_creator_published_state creator state eid allocation)).
  { destruct creator; cbn [mutex_del_creator_fields mutex_del_creator_arguments] in Hargs, Himage;
      rewrite event_create_stores_image_initialization_eq in Himage;
      unfold mutex_del_creator_published_state; cbn [mutex_del_creator_event].
    - eapply sem_create_publish_merge; try eassumption; [lia|apply event_name_valid_disabled; exact Hnames].
    - eapply mbox_create_publish_merge; try eassumption; apply event_name_valid_disabled; exact Hnames. }
  assert (Hopen : kernel_continuation_inv abi kernel_program_inv local sg active state **
      event_private_pool_rep sg state.(EventState) |--
    coq_prop (task_stack_live_coverage state.(TskState) active) &&
    ((event_private_storage_rep sg eid allocation **
       (event_raw_rep sg state.(TskState) state.(EventState) **
        queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state)) **
     (event_private_pool_rep sg (mutex_del_creator_published_state creator state eid allocation).(EventState) **
      unmap_table_rep sg **
      store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
        state.(TskState).(parkedTaskStacks)))).
  { unfold kernel_continuation_inv; Intros.
    sep_apply_l_atomic (event_private_pool_split_publish sg state.(EventState) eid allocation
      (mutex_del_creator_event creator allocation) Hget).
    rewrite kernel_program_inv_split_unmap, (UCOS2_inv_split_event_queue sg state).
    unfold mutex_del_creator_published_state; cbn [replace_EventS EventState]; Intros; entailer!. }
  intros heap Hpre; destruct (Hopen heap Hpre) as [Hcoverage Howned].
  assert (Hclose : UCOS2_inv sg (mutex_del_creator_published_state creator state eid allocation) **
      (event_private_pool_rep sg (mutex_del_creator_published_state creator state eid allocation).(EventState) **
       unmap_table_rep sg **
       store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks)) |--
    kernel_continuation_inv abi kernel_program_inv local sg active
      (mutex_del_creator_published_state creator state eid allocation) **
    event_private_pool_rep sg (mutex_del_creator_published_state creator state eid allocation).(EventState)).
  { unfold kernel_continuation_inv; rewrite kernel_program_inv_split_unmap.
    unfold mutex_del_creator_published_state; cbn [replace_EventS TskState EventState]; entailer!. }
  apply (Hclose heap); destruct Howned as [owned [rest [Hjoin [Hmerge_input Hrest]]]].
  exists owned, rest; split; [exact Hjoin|]. split; [apply Hmerge; exact Hmerge_input|exact Hrest].
Qed.

Lemma mutex_del_creator_continuation_allocate : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg active state before cut after (frame : Assertion),
  mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after ->
  (mutex_del_creator_continuation_resources abi local sg active KernelClientHeapClosed state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists returned,
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned /\
    (mutex_del_creator_continuation_resources abi local sg active cut returned **
      event_private_pool_rep sg returned.(EventState) ** frame) after.
Proof.
  intros external platform port abi local sg active state before cut after frame Hsource Hpre.
  assert (Hopen : mutex_del_creator_continuation_resources abi local sg active KernelClientHeapClosed state **
      event_private_pool_rep sg state.(EventState) ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) active) &&
    (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) **
     (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
        state.(TskState).(parkedTaskStacks) ** frame))).
  { cbn [mutex_del_creator_continuation_resources]; unfold kernel_continuation_inv; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
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
      * match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
        { cbn [mutex_del_creator_continuation_resources].
          Exists eid (sem_create_allocation_identity state image).
          unfold kernel_continuation_inv; rewrite Htasks.
          cbn [sem_create_allocation_identity eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
        exact (Hclose after Hpost).
    + cbn [event_create_return_ptr] in Hpointer; exfalso; apply Hnonzero; exact Hpointer.
Qed.

Lemma mutex_del_creator_continuation_field : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg active creator pointer state field stored
  (frame : Assertion) before after,
  mutex_del_creator_arguments creator -> In (field, stored) (mutex_del_creator_fields sg creator) ->
  kernel_heap_execution (event_create_field_writes pointer field stored) before after ->
  (mutex_del_creator_continuation_resources abi local sg active (KernelClientHeapExtra pointer) state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists eid allocation,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (mutex_del_creator_continuation_resources abi local sg active (KernelClientHeapExtra pointer)
      (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state) **
      event_private_pool_rep sg (event_private_write state.(EventState) eid allocation field (Some stored)) ** frame) after.
Proof.
  intros external platform port abi local sg active creator pointer state field stored frame before after
    Hargs Hin Hsource Hpre.
  pose proof (mutex_del_creator_fields_in_range sg creator Hargs) as Hranges.
  rewrite Forall_forall in Hranges; specialize (Hranges (field, stored) Hin).
  cbn [fst snd] in Hranges; destruct Hranges as [Hfield Hrange].
  assert (Hopen : mutex_del_creator_continuation_resources abi local sg active (KernelClientHeapExtra pointer) state **
      event_private_pool_rep sg state.(EventState) ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        task_stack_live_coverage state.(TskState) active) &&
      (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) **
        (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
          state.(TskState).(parkedTaskStacks) ** frame))).
  { cbn [mutex_del_creator_continuation_resources]; Intros eid allocation; Exists eid allocation.
    unfold kernel_continuation_inv; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp Hcoverage]]]] Howned]]].
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
  { cbn [mutex_del_creator_continuation_resources]; Exists eid updated.
    unfold kernel_continuation_inv; cbn [replace_EventS EventState TskState].
    unfold updated; cbn [eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
  exact (Hclose after Hpost).
Qed.

Lemma mutex_del_creator_continuation_initialization : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg active creator pointer state before (frame : Assertion),
  mutex_del_creator_arguments creator ->
  (mutex_del_creator_continuation_resources abi local sg active (KernelClientHeapExtra pointer) state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists eid allocation initialized final after,
    pointer = event_pool_addr sg eid /\
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    event_create_private_stores eid (mutex_del_creator_fields sg creator) state tt initialized /\
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes pointer (fst write) (snd write))
        (mutex_del_creator_fields sg creator)) before after /\
    (mutex_del_creator_continuation_resources abi local sg active KernelClientHeapClosed
      (mutex_del_creator_published_state creator initialized eid final) **
      event_private_pool_rep sg (mutex_del_creator_published_state creator initialized eid final).(EventState) ** frame) after.
Proof.
  intros external platform port abi local sg active creator pointer state before frame Hargs Hpre.
  assert (Hopen : mutex_del_creator_continuation_resources abi local sg active (KernelClientHeapExtra pointer) state **
      event_private_pool_rep sg state.(EventState) ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
        UCOS2_state_inv sg state /\ task_stack_live_coverage state.(TskState) active) &&
      (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) **
        (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
          state.(TskState).(parkedTaskStacks) ** frame))).
  { cbn [mutex_del_creator_continuation_resources]; Intros eid allocation; Exists eid allocation.
    unfold kernel_continuation_inv, kernel_program_inv; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget [Hqueue [Hpcp [Hvalid Hcoverage]]]]] Howned]]].
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
  match type of Hafter with ?P after => assert (Hclose : P |--
    mutex_del_creator_continuation_resources abi local sg active KernelClientHeapClosed
      (mutex_del_creator_published_state creator initialized eid final) **
    event_private_pool_rep sg (mutex_del_creator_published_state creator initialized eid final).(EventState) ** frame) end.
  { cbn [mutex_del_creator_continuation_resources]; eapply derivable1_trans.
    2: { apply derivable1_sepcon_mono; [eapply mutex_del_creator_continuation_publish; eassumption || congruence|reflexivity]. }
    unfold kernel_continuation_inv; rewrite Htasks; entailer!. }
  exists eid, allocation, initialized, final, after.
  split; [exact Hpointer|]. split; [exact Hget|]. split; [exact Hstores|]. split; [exact Hfinal|].
  split; [rewrite Hpointer; exact Hwrites|exact (Hclose after Hafter)].
Qed.

(** Interpret one existing concrete registry step. Counter operations use
    their actual proved C fragments. Task publication consumes the new
    entry's local explicitly. Each creator Extra uses the real allocator,
    field store or publication producer above; no Extra preservation law
    is demanded of an environment. *)
Lemma mutex_del_creator_continuation_step : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local active creator,
  mutex_del_creator_arguments creator ->
  forall sg cut before next after state (frame : Assertion),
  kernel_client_heap_step (mutex_del_creator_interrupt_step creator) sg cut before next after ->
  (mutex_del_creator_continuation_resources abi local sg active cut state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists returned,
    kernel_client_heap_state_step (mutex_del_creator_interrupt_effect creator) sg cut state next returned /\
    (mutex_del_creator_continuation_resources abi local sg active next returned **
      event_private_pool_rep sg returned.(EventState) ** frame) after.
Proof.
  intros external platform port abi local active creator Hargs sg.
  assert (Henter : forall state before after (frame : Assertion),
    (kernel_continuation_inv abi kernel_program_inv local sg active state ** frame) before ->
    kernel_client_int_enter_fragment sg before after ->
    (kernel_continuation_inv abi kernel_program_inv local sg active (os_int_enter_state state) ** frame) after).
  { intros state before after frame Hpre Hsource.
    assert (Hsplit : kernel_continuation_inv abi kernel_program_inv local sg active state ** frame |--
      coq_prop (task_stack_live_coverage state.(TskState) active) &&
      (UCOS2_inv sg state ** (unmap_table_rep sg **
        store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
          state.(TskState).(parkedTaskStacks) ** frame))).
    { unfold kernel_continuation_inv; rewrite kernel_program_inv_split_unmap; entailer!. }
    destruct (Hsplit before Hpre) as [Hcoverage Hheap].
    pose proof (kernel_client_int_enter_writes sg state _ before after Hheap Hsource) as Hwrites.
    destruct (os_int_enter_source_heap_frames_private sg state _ before Hheap) as [produced [Hrun Hpost]].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
    match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hmerge : P |-- Q) end end.
    { unfold kernel_continuation_inv; rewrite kernel_program_inv_split_unmap.
      unfold os_int_enter_state; cbn [replace_IntrS TskState]; entailer!. }
    exact (Hmerge after Hpost). }
  assert (Hexit : forall state before after (frame : Assertion),
    (kernel_continuation_inv abi kernel_program_inv local sg active state ** frame) before ->
    os_int_exit_masked_no_schedule_fragment sg before after ->
    (kernel_continuation_inv abi kernel_program_inv local sg active
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after).
  { intros state before after frame Hpre Hsource.
    assert (Hsplit : kernel_continuation_inv abi kernel_program_inv local sg active state ** frame |--
      coq_prop (task_stack_live_coverage state.(TskState) active) &&
      (UCOS2_inv sg state ** (unmap_table_rep sg **
        store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
          state.(TskState).(parkedTaskStacks) ** frame))).
    { unfold kernel_continuation_inv; rewrite kernel_program_inv_split_unmap; entailer!. }
    destruct (Hsplit before Hpre) as [Hcoverage [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]]].
    destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw) as [middle [Hcounter Hraw_after]].
    destruct (os_int_exit_masked_counter_fragment_frame sg owned _ middle rest before Hcounter Hjoin)
      as [produced [Hwhole Hjoined]].
    assert (produced = after).
    { destruct Hsource; eapply os_int_exit_masked_counter_final_eq; eassumption. }
    subst produced.
    assert (Hafter : (UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      (unmap_table_rep sg **
       store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame)) after).
    { exists middle, rest; split; [exact Hjoined|]. split; [split; assumption|exact Hrest]. }
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hmerge : P |-- Q) end end.
    { unfold kernel_continuation_inv; rewrite kernel_program_inv_split_unmap.
      unfold os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
    exact (Hmerge after Hafter). }
  assert (Hcursor : forall pointer state returned before after (frame : Assertion),
    returned.(EventState) = state.(EventState) ->
    (forall private_frame,
      (kernel_continuation_inv abi kernel_program_inv local sg active state ** private_frame) before ->
      (kernel_continuation_inv abi kernel_program_inv local sg active returned ** private_frame) after) ->
    (mutex_del_creator_continuation_resources abi local sg active (KernelClientHeapExtra pointer) state **
      event_private_pool_rep sg state.(EventState) ** frame) before ->
    (mutex_del_creator_continuation_resources abi local sg active (KernelClientHeapExtra pointer) returned **
      event_private_pool_rep sg returned.(EventState) ** frame) after).
  { intros pointer state returned before after frame Hevent Hactual Hpre.
    assert (Hopen : mutex_del_creator_continuation_resources abi local sg active (KernelClientHeapExtra pointer) state **
        event_private_pool_rep sg state.(EventState) ** frame |--
      EX eid allocation,
        coq_prop (pointer = event_pool_addr sg eid /\
          state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
          allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None) &&
        (kernel_continuation_inv abi kernel_program_inv local sg active state **
          (event_private_pool_rep sg state.(EventState) ** frame))).
    { cbn [mutex_del_creator_continuation_resources]; Intros eid allocation; Exists eid allocation; entailer!. }
    destruct (Hopen before Hpre) as [eid [allocation [Hfacts Howned]]].
    pose proof (Hactual _ Howned) as Hafter.
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { cbn [mutex_del_creator_continuation_resources]; Exists eid allocation; rewrite Hevent; entailer!. }
    exact (Hclose after Hafter). }
  intros cut before next after state frame Hsource Hpre; destruct Hsource.
  - exists (os_int_enter_state state); split; [constructor|].
    assert (Horder : mutex_del_creator_continuation_resources abi local sg active KernelClientHeapClosed state **
        event_private_pool_rep sg state.(EventState) ** frame |--
      kernel_continuation_inv abi kernel_program_inv local sg active state **
        (event_private_pool_rep sg state.(EventState) ** frame)).
    { cbn [mutex_del_creator_continuation_resources]; entailer!. }
    pose proof (Henter state before after _ (Horder before Hpre) H) as Hpost.
    match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { cbn [mutex_del_creator_continuation_resources os_int_enter_state replace_IntrS EventState]; entailer!. }
    exact (Hclose after Hpost).
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split; [constructor|].
    assert (Horder : mutex_del_creator_continuation_resources abi local sg active KernelClientHeapClosed state **
        event_private_pool_rep sg state.(EventState) ** frame |--
      kernel_continuation_inv abi kernel_program_inv local sg active state **
        (event_private_pool_rep sg state.(EventState) ** frame)).
    { cbn [mutex_del_creator_continuation_resources]; entailer!. }
    pose proof (Hexit state before after _ (Horder before Hpre) H) as Hpost.
    match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { cbn [mutex_del_creator_continuation_resources os_int_exit_counter_state replace_IntrS EventState]; entailer!. }
    exact (Hclose after Hpost).
  - assert (Hsplit : mutex_del_creator_continuation_resources abi local sg active
        (KernelClientHeapTaskPublication publication) state ** event_private_pool_rep sg state.(EventState) ** frame |--
      coq_prop (UCOS2_state_inv sg state /\ task_stack_live_coverage state.(TskState) active /\
        task_create_stack_publication_input sg publication state /\
        0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
        0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
      (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
         state publication.(stack_publication_slot) publication.(stack_publication_image) **
       (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
        local (task_create_stack_publication_continuation publication) **
        store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
          state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg **
        (event_private_pool_rep sg state.(EventState) ** frame)))).
    { cbn [mutex_del_creator_continuation_resources]; entailer!. }
    destruct (Hsplit before Hpre) as [[Hvalid [Hcoverage [Hinput [Hpriority Hpointer]]]] Hheap].
    destruct (kernel_task_publication_continuation_source external platform port abi sg publication state
      local active (event_private_pool_rep sg state.(EventState) ** frame) before after
      Hvalid Hinput Hcoverage Hpriority Hpointer Hheap H) as [Hstep [Hcovered Howned]].
    exists (task_create_stack_publication_state sg publication state); split; [constructor; exact Hinput|].
    match type of Howned with ?P after => match goal with |- ?Q after => assert (Hmerge : P |-- Q) end end.
    { cbn [mutex_del_creator_continuation_resources]; unfold kernel_continuation_inv; entailer!. }
    exact (Hmerge after Howned).
  - destruct H.
    + destruct H as [before cut after Hallocate|pointer before after Hwrites].
      * destruct (mutex_del_creator_continuation_allocate external platform port abi local sg active
          state before cut after frame Hallocate Hpre) as [returned [Hlogical Hpost]].
        exists returned; split; [constructor; constructor; constructor; exact Hlogical|exact Hpost].
      * destruct (mutex_del_creator_continuation_initialization external platform port abi local sg active
          creator pointer state before frame Hargs Hpre)
          as [eid [allocation [initialized [final [produced [Hpointer [Hget [Hstores [Hfinal [Hrun Hpost]]]]]]]]]].
        assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
        exists (mutex_del_creator_published_state creator initialized eid final).
        split; [constructor; constructor; econstructor; eassumption|exact Hpost].
    + exists (os_int_enter_state state); split.
      * apply KernelClientHeapExtraState; apply MutexDelCreatorInterruptEnterState.
      * eapply (Hcursor pointer state (os_int_enter_state state) before after frame);
          [reflexivity| |exact Hpre].
        intros; eapply Henter; eassumption.
    + exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split.
      * apply KernelClientHeapExtraState; apply MutexDelCreatorInterruptExitState.
      * eapply (Hcursor pointer state
          (os_int_exit_counter_state state.(SchedState).(isRunning) state) before after frame);
          [reflexivity| |exact Hpre].
        intros; eapply Hexit; eassumption.
    + destruct (mutex_del_creator_continuation_field external platform port abi local sg active creator
        pointer state field stored frame before after Hargs H H0 Hpre)
        as [eid [allocation [Hpointer [Hget Hpost]]]].
      exists (replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state).
      split; [constructor; eapply MutexDelCreatorInterruptFieldState; eassumption|exact Hpost].
Qed.

(** The SAME actual heap trace produces both the state trace and current
    whole pool/map. The Type property follows from each precise creator
    field list. It is not appended as a new public Del premise. The initial
    facts are already the source-owned [mutex_del_stack_resources]. *)
Lemma mutex_del_creator_continuation_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local active clients actor creator
  sg observer cut before next after (frame : Assertion),
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg cut before next after ->
  forall state origin,
  mutex_program_selected_reachable sg state -> mutex_del_private_types_non_mutex state.(EventState) ->
  kernel_client_heap_observer_cut observer cut ->
  (mutex_del_creator_continuation_resources abi local sg active cut state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer None
      origin state false returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    (coq_prop (mutex_program_selected_reachable sg returned /\
       mutex_del_private_types_non_mutex returned.(EventState)) &&
     (mutex_del_creator_continuation_resources abi local sg active next returned **
       event_private_pool_rep sg returned.(EventState) ** frame)) after.
Proof.
  intros external platform port abi local active clients actor creator sg observer cut before next after frame
    Hinclude Hforeign Hargs Htrace.
  induction Htrace; intros state origin Hreachable Htypes Hcut Hpre.
  - exists state, origin; split; [constructor|]. split; [constructor|].
    split; [exact Hcut|split; [exact (conj Hreachable Htypes)|exact Hpre]].
  - assert (Hvalid : UCOS2_state_inv sg state).
    { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
      { destruct cut; cbn [mutex_del_creator_continuation_resources].
        - unfold kernel_continuation_inv, kernel_program_inv; entailer!.
        - entailer!.
        - Intros eid allocation; unfold kernel_continuation_inv, kernel_program_inv; entailer!. }
      exact (proj1 (Hobserve before Hpre)). }
    assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
    { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
    destruct (mutex_del_creator_continuation_step external platform port abi local active creator Hargs
      sg cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    assert (Hreachable_middle : mutex_program_selected_reachable sg middle_state).
    { eapply mutex_program_source_step_reachable; [exact Hreachable|].
      eapply mutex_del_creator_interrupt_state_source; exact Hstep. }
    pose proof (mutex_del_creator_step_preserves_private_non_mutex creator sg cut state middle_cut
      middle_state Hvalid Htypes Hstep) as Htypes_middle.
    destruct (kernel_client_heap_state_step_source external port Z
      (mutex_del_creator_source_client actor creator) sg observer None (mutex_del_creator_interrupt_effect creator)
      ltac:(constructor; constructor) ltac:(intros; constructor; constructor)
      ltac:(intros; constructor; constructor)
      (mutex_del_creator_interrupt_extension_source external port actor creator sg observer Hforeign Hnames)
      cut state middle_cut middle_state origin Hcut Hstep)
      as [Hcompatible [stopped [middle_origin Hsource]]].
    pose proof (mutex_del_creator_source_trace_nonstopping external port actor creator sg observer None
      origin state stopped middle_origin middle_state Hsource) as ->.
    destruct (IHHtrace middle_state middle_origin Hreachable_middle Htypes_middle Hcompatible Hmiddle)
      as [returned [returned_origin [Hstates [Htail_source [Hnext Hpost]]]]].
    exists returned, returned_origin; split; [econstructor; eassumption|]. split.
    + replace false with (orb false false) by reflexivity.
      eapply kernel_resumption_task_source_trace_trans; [|exact Htail_source].
      eapply kernel_resumption_task_source_trace_inclusion; eassumption.
    + split; assumption.
Qed.

(** Close the actual returned registry world, ready for the selected-call
    consumer below. This is the C heap trace above, not a postcondition
    supplied by an unspecified foreign caller. The source trace retains
    its actual actor and both state endpoints. *)
Lemma mutex_del_creator_continuation_closed_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local active clients actor creator
  sg observer state origin before after (frame : Assertion),
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
    KernelClientHeapClosed before KernelClientHeapClosed after ->
  (kernel_continuation_inv abi mutex_del_stack_resources local sg active state ** frame) before ->
  exists returned returned_origin,
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg
      KernelClientHeapClosed state KernelClientHeapClosed returned /\
    kernel_resumption_task_source_trace external port clients sg observer None
      origin state false returned_origin returned /\
    (kernel_continuation_inv abi mutex_del_stack_resources local sg active returned ** frame) after.
Proof.
  intros external platform port abi local active clients actor creator sg observer state origin before after frame
    Hinclude Hforeign Hargs Htrace Hpre.
  assert (Hopen : kernel_continuation_inv abi mutex_del_stack_resources local sg active state ** frame |--
    coq_prop (mutex_program_selected_reachable sg state /\ mutex_del_private_types_non_mutex state.(EventState)) &&
    (mutex_del_creator_continuation_resources abi local sg active KernelClientHeapClosed state **
      event_private_pool_rep sg state.(EventState) ** frame)).
  { cbn [mutex_del_creator_continuation_resources]; unfold kernel_continuation_inv, mutex_del_stack_resources; entailer!. }
  destruct (Hopen before Hpre) as [[Hreachable Htypes] Howned].
  destruct (mutex_del_creator_continuation_trace external platform port abi local active clients actor creator
    sg observer KernelClientHeapClosed before KernelClientHeapClosed after frame Hinclude Hforeign Hargs Htrace
    state origin Hreachable Htypes I Howned)
    as [returned [returned_origin [Hstates [Hsource [Hcut [[Hreachable_now Htypes_now] Hpost]]]]]].
  exists returned, returned_origin; split; [exact Hstates|]. split; [exact Hsource|].
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { cbn [mutex_del_creator_continuation_resources]; unfold kernel_continuation_inv, mutex_del_stack_resources; entailer!. }
  exact (Hclose after Hpost).
Qed.

(** The real last selection consumes the SAME current whole pool and
    map produced by the C registry. Outgoing capture and selection are
    actual present-cut inputs supplied by the Scheduler producer, not a
    promise that a future call returns. Only this final masked install
    and the existing uninterrupted Restore contract frame the pool.

    The returned map keeps every [other] local. This is the source-side
    result needed by the forthcoming parameterized Del public interface;
    no arbitrary local is forgotten to satisfy its older fixed-map post. *)
Lemma mutex_del_creator_continuation_selected_return : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg context outgoing hooked source_tasks original saved acquired other resumed before (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let local := kernel_sched_saved_local_at environment.(mutex_del_call_platform) critical sg
    source_tasks original saved acquired other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(mutex_del_call_external) context outgoing hooked
    original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_continuation_inv abi mutex_del_stack_resources local sg
     (Some (task_stack_key context.(os_sched_call_stack))) hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   (armv7a_task_switch_control task_abi context ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      kernel_stack_call_same_call returned original /\ kernel_call_task_source returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        (kernel_continuation_call_closed abi mutex_del_stack_resources other sg
           (Some (task_stack_key original.(os_sched_call_stack))) returned
           (armv7a_irq_fiq_mask saved) current ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg context outgoing hooked source_tasks original saved acquired
    other resumed before frame abi local resource current Hactive Hsaved Hdestination Haddress Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (mutex_program_selected_reachable sg hooked /\
      mutex_del_private_types_non_mutex hooked.(EventState) /\
      task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack)))) &&
    (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
     resource (task_stack_key context.(os_sched_call_stack))
       (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
     store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
     (armv7a_task_switch_control task_abi context ** unmap_table_rep sg **
       (event_private_pool_rep sg hooked.(EventState) ** frame)))) end.
  { unfold kernel_continuation_inv, mutex_del_stack_resources; rewrite kernel_program_inv_split_unmap;
      fold resource; entailer!. }
  destruct (Hopen before Hpre) as [[Hreachable [Htypes Hcoverage]] Howned].
  destruct (os_sched_modular_saved_call_return environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) critical arch abi task_abi restore
    sg context outgoing hooked source_tasks original saved acquired other resumed before
    (event_private_pool_rep sg hooked.(EventState) ** frame)
    Hactive Hsaved Hdestination Haddress Hcoverage Howned)
    as [installed [selected [Hinstall [Hreads [Hlease Hrestore]]]]].
  assert (Hreachable_now : mutex_program_selected_reachable sg current).
  { eapply mutex_program_source_step_reachable; [exact Hreachable|].
    apply MutexOwnerSourceFrame; reflexivity. }
  assert (Hevents : current.(EventState) = hooked.(EventState)) by reflexivity.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hcall [Hi [Ho [Hs [Hsource Htail]]]]].
  split; [unfold kernel_stack_call_same_call; auto|]. split; [exact Hsource|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Htail cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix)
    as [Hrun [Hlr [Hmemory Hclosed]]].
  split; [exact Hrun|].
  match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources.
    rewrite Hevents; entailer!. }
  exact (Hclose after Hclosed).
Qed.

(** The CURRENT canonical Del post is precisely the empty-other-local
    instance. Only emp is removed in this consequence. The arbitrary-local
    result above must be retained when moving the public interface to the
    shared protocol; using this lemma with nonempty locals is impossible. *)
Lemma mutex_del_continuation_empty_local_runtime_output : forall environment sg original returned mask current,
  kernel_stack_call_same_call returned original ->
  kernel_call_task_source returned current ->
  kernel_continuation_call_closed environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (fun _ => emp) sg
    (Some (task_stack_key original.(os_sched_call_stack))) returned mask current |--
  mutex_del_runtime_return environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg original mask.
Proof.
  intros environment sg original returned mask current Hsame Hsource.
  assert (Hactive : task_stack_call_active_key original = Some (task_stack_key original.(os_sched_call_stack))).
  { destruct Hsame as [Hi [Ho Hs]].
    pose proof (proj1 Hsource) as Horigin; rewrite Ho, Hs in Horigin.
    unfold task_stack_call_active_key; rewrite Horigin; reflexivity. }
  sep_apply_l_atomic (proj1 (kernel_continuation_call_closed_emp_equiv _ _ _
    environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
    (Some (task_stack_key original.(os_sched_call_stack))) returned mask current)).
  unfold mutex_del_runtime_return, mutex_del_runtime_return_at.
  Exists returned current environment.
  unfold mutex_del_callsite_environment, kernel_stack_call_closed, kernel_stack_inv.
  rewrite Hactive; entailer!.
Qed.

(** Direct consumer for the existing canonical OS_Sched call in Del.
    Its input is the actual selector world (obtainable from the creator
    trace above), not an assumed Scheduler post. For a nonempty [other]
    policy callers use [mutex_del_creator_continuation_selected_return]
    until the public Del interface carries that same parameter. *)
Lemma mutex_del_creator_continuation_selected_runtime_return : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  sg context outgoing hooked source_tasks original saved acquired resumed before (frame : Assertion),
  let abi := environment.(mutex_del_call_continuations) in
  let local := kernel_sched_saved_local_at environment.(mutex_del_call_platform) critical sg
    source_tasks original saved acquired (fun _ => emp) in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(mutex_del_call_external) context outgoing hooked
    original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_continuation_inv abi mutex_del_stack_resources local sg
     (Some (task_stack_key context.(os_sched_call_stack))) hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   (armv7a_task_switch_control task_abi context ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored cursor written middle final_cursor after,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor restored written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
      (mutex_del_runtime_return environment environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) sg original (armv7a_irq_fiq_mask saved) ** frame) after).
Proof.
  intros environment critical arch task_abi restore sg context outgoing hooked source_tasks original saved acquired
    resumed before frame abi local resource Hactive Hsaved Hdestination Haddress Hpre.
  destruct (mutex_del_creator_continuation_selected_return environment critical arch task_abi restore
    sg context outgoing hooked source_tasks original saved acquired (fun _ => emp) resumed before frame
    Hactive Hsaved Hdestination Haddress Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease Hreturn]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored cursor written middle final_cursor after Htask_restore Hr0 Hmask Hprefix Hsuffix.
  destruct (Hreturn restored Htask_restore) as [Hsame [Hsource Htail]].
  destruct (Htail cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix) as [Hrun Hclosed].
  split; [exact Hrun|].
  match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (mutex_del_continuation_empty_local_runtime_output environment sg original
      (kernel_selected_call selected (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked))
      (armv7a_irq_fiq_mask saved) (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked)
      Hsame Hsource); entailer!. }
  exact (Hclose after Hclosed).
Qed.
