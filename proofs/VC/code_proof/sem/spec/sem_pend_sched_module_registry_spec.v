Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_legacy_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_preparation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.mbox.spec.mbox_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_allocation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_dispatch_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_publication_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_task_prepare_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_module_dispatch_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_receipt_producer_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma sem_pend_allocation_client_registered : forall external actor action,
  mutex_del_allocation_source_client actor action -> sched_task_registered_client external action.
Proof.
  intros external actor action Hmember; destruct Hmember.
  - apply sched_task_int_enter_registered.
  - apply sched_task_int_exit_counter_registered.
  - apply sched_task_stack_publication_registered.
  - apply sched_task_event_allocate_registered.
Qed.

Lemma sem_pend_task_detach_client_registered : forall external priority entry slot rest image,
  sched_task_registered_client external
    (task_creation_client (TaskDetachFreeHead priority entry slot rest image)).
Proof.
  intros; apply sched_task_register_named_source.
  - apply SchedTaskSourceNontimer; constructor.
  - apply task_creation_client_certificate.
  - intros sg before after [_ [_ ->]]; reflexivity.
  - intros sg before after Hvalid [_ [_ ->]] Hready; exact Hready.
Qed.

Lemma sem_pend_prepare_client_registered : forall external action,
  sem_pend_task_prepare_source_client action -> sched_task_registered_client external action.
Proof.
  intros external action Hmember; destruct Hmember.
  - apply sched_task_int_enter_registered.
  - apply sched_task_int_exit_counter_registered.
  - apply sched_task_stack_publication_registered.
  - apply sched_task_reserve_client_registered.
  - apply sem_pend_task_detach_client_registered.
Qed.

(** The actual creator argument and allocation metadata are consumed here.
    Broad creator source membership does not contain the last premise. *)
Lemma sem_pend_creator_publication_registered : forall external actor creator eid allocation,
  mutex_del_creator_arguments creator -> allocation.(eventPrivateMutexPCP) = None ->
  sched_task_registered_client external
    (event_create_publication_client actor eid allocation (mutex_del_creator_event creator allocation)).
Proof.
  intros external actor creator eid allocation Hargs Hpcp.
  destruct creator; cbn [mutex_del_creator_arguments] in Hargs;
    apply sched_task_event_publication_registered;
    try reflexivity; try discriminate; try exact Hpcp.
  - apply sem_create_event_fields_consistency.
  - intro sg; apply sem_create_event_payload_consistency; lia.
  - apply mbox_create_event_fields_consistency.
  - intro sg; apply mbox_create_event_payload_consistency; exact Hargs.
Qed.

(** Observe the specific pending owner, correlating its existential slot
    and allocation with the actual source effect's lookup. *)
Lemma sem_pend_creator_pending_mutex_pcp : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg pointer state eid allocation heap (frame : Assertion),
  pointer = event_pool_addr sg eid ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  (sem_pend_creator_fields_pending abi local sg pointer state ** frame) heap ->
  allocation.(eventPrivateMutexPCP) = None.
Proof.
  intros * Hpointer Hget Hpre.
  assert (Hopen : sem_pend_creator_fields_pending abi local sg pointer state ** frame |--
    EX found actual, coq_prop (pointer = event_pool_addr sg found /\
      state.(EventState).(eventLifecycle).(eventPrivate) found = Some actual /\
      actual.(eventPrivateMutexPCP) = None) && TT).
  { unfold sem_pend_creator_fields_pending; Intros found actual; Exists found actual; entailer!. }
  destruct (Hopen heap Hpre) as [found [actual [[Haddress [Hlookup Hpcp]] Hrest]]].
  assert (found = eid) by (apply event_pool_addr_injective with (sg := sg); congruence); subst found.
  assert (actual = allocation) by congruence; subst actual; exact Hpcp.
Qed.

Lemma sem_pend_creator_stores_registered_receipt : forall external port actor sg observer origin eid writes
  state result returned,
  actor <> Some observer -> UCOS2_state_inv sg state ->
  event_create_private_stores eid writes state result returned ->
  exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
      sg observer None origin state false origin returned trace.
Proof.
  intros external port actor sg observer origin eid writes; induction writes as [|[field stored] rest IH];
    intros state result returned Hforeign Hvalid Hstores.
  - destruct Hstores as [_ ->].
    exists (@KernelClientTaskSourceNil external port (sched_task_registered_client external) sg observer None origin state).
    constructor.
  - destruct Hstores as [allocation [Hget Htail]].
    set (middle := replace_EventS (event_private_write state.(EventState) eid allocation field (Some stored)) state).
    assert (Hmiddle : UCOS2_state_inv sg middle) by (apply UCOS2_event_private_write_preserves_validity; assumption).
    destruct (IH middle result returned Hforeign Hmiddle Htail) as [tail Htail_receipt].
    assert (Hhead : exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
        sg observer None origin state false origin middle,
        sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
          sg observer None origin state false origin middle trace).
    { eapply sem_pend_dispatch_framed_step_receipt with
        (action := event_create_private_store_client actor eid allocation field stored).
      - apply sched_task_event_private_store_registered.
      - exact Hforeign.
      - intros; discriminate.
      - split; [exact Hget|reflexivity].
      - reflexivity.
      - apply TmrTaskCallNontimer; [constructor|split; [exact Hget|reflexivity]].
      - apply sem_pend_source_state_facts_from_valid; exact Hvalid. }
    destruct Hhead as [head Hhead_receipt].
    exact (sem_pend_dispatch_client_receipt_append external port (sched_task_registered_client external)
      sg observer None origin state false origin middle head Hhead_receipt false origin returned tail Htail_receipt).
Qed.

Lemma sem_pend_creator_publication_effect_registered_receipt :
  forall external platform port (abi : Armv7aContinuationABI external platform port) local actor creator sg observer
    cut state next returned origin before (frame : Assertion),
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  mutex_del_creator_publication_effect creator sg cut state next returned ->
  (sem_pend_creator_fields_resources abi local sg cut state ** frame) before ->
  exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
      sg observer None origin state false origin returned trace.
Proof.
  intros external platform port abi local actor creator sg observer cut state next returned origin before frame
    Hforeign Hargs Heffect Hpre.
  pose proof (sem_pend_creator_fields_resources_valid external platform port abi local sg cut state before frame Hpre) as Hvalid.
  destruct Heffect as [cut state returned Hallocate|pointer state eid allocation initialized final Hpointer Hget Hstores Hfinal].
  - destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer KernelClientHeapClosed
      state cut returned origin Hforeign I (KernelClientHeapExtraState _ _ _ _ _ _ Hallocate)
      (sem_pend_source_state_facts_from_valid sg state Hvalid)) as [_ [trace Hreceipt]].
    eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
    intros action Hmember; eapply sem_pend_allocation_client_registered; exact Hmember.
  - pose proof (sem_pend_creator_pending_mutex_pcp external platform port abi local sg pointer state eid allocation
      before frame Hpointer Hget Hpre) as Hpcp.
    pose proof (event_create_private_stores_mutex_pcp_eq eid _ state tt initialized allocation final
      Hget Hstores Hfinal) as Hpcp_final.
    pose proof (event_create_private_stores_preserves_validity sg eid _ state tt initialized Hvalid Hstores) as Hinitialized.
    assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
    { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
    destruct (sem_pend_creator_stores_registered_receipt external port actor sg observer origin eid
      (mutex_del_creator_fields sg creator) state tt initialized Hforeign Hvalid Hstores) as [head Hhead].
    assert (Htail : exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
        sg observer None origin initialized false origin (mutex_del_creator_published_state creator initialized eid final),
        sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
          sg observer None origin initialized false origin (mutex_del_creator_published_state creator initialized eid final) trace).
    { eapply sem_pend_dispatch_framed_step_receipt with
        (action := event_create_publication_client actor eid final (mutex_del_creator_event creator final)).
      - apply sem_pend_creator_publication_registered; [exact Hargs|congruence].
      - exact Hforeign.
      - intros; discriminate.
      - split; [exact Hfinal|]. split; [apply event_name_valid_disabled; exact Hnames|reflexivity].
      - reflexivity.
      - apply TmrTaskCallNontimer; [constructor|].
        split; [exact Hfinal|]. split; [apply event_name_valid_disabled; exact Hnames|reflexivity].
      - apply sem_pend_source_state_facts_from_valid; exact Hinitialized. }
    destruct Htail as [tail Htail_receipt].
    exact (sem_pend_dispatch_client_receipt_append external port (sched_task_registered_client external)
      sg observer None origin state false origin initialized head Hhead false origin _ tail Htail_receipt).
Qed.

Lemma sem_pend_creator_interrupt_effect_registered_receipt :
  forall external platform port (abi : Armv7aContinuationABI external platform port) local actor creator sg observer
    cut state next returned origin before (frame : Assertion),
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  mutex_del_creator_interrupt_effect creator sg cut state next returned ->
  (sem_pend_creator_fields_resources abi local sg cut state ** frame) before ->
  exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
      sg observer None origin state false origin returned trace.
Proof.
  intros external platform port abi local actor creator sg observer cut state next returned origin before frame
    Hforeign Hargs Heffect Hpre.
  pose proof (sem_pend_creator_fields_resources_valid external platform port abi local sg cut state before frame Hpre) as Hvalid.
  destruct Heffect.
  - eapply sem_pend_creator_publication_effect_registered_receipt; eassumption.
  - eapply sem_pend_dispatch_framed_step_receipt with (action := kernel_full_profile_cut_client KernelFullIntEnter).
    + apply sched_task_int_enter_registered.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + apply TmrTaskCallProfile; split; [exact I|reflexivity].
    + apply sem_pend_source_state_facts_from_valid; exact Hvalid.
  - eapply sem_pend_dispatch_framed_step_receipt with
      (action := kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))).
    + apply sched_task_int_exit_counter_registered.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + apply TmrTaskCallProfile; split; [exact I|reflexivity].
    + apply sem_pend_source_state_facts_from_valid; exact Hvalid.
  - eapply sem_pend_dispatch_framed_step_receipt with
      (action := event_create_private_store_client actor eid allocation field stored).
    + apply sched_task_event_private_store_registered.
    + exact Hforeign.
    + intros; discriminate.
    + split; [exact H0|reflexivity].
    + reflexivity.
    + apply TmrTaskCallNontimer; [constructor|split; [exact H0|reflexivity]].
    + apply sem_pend_source_state_facts_from_valid; exact Hvalid.
Qed.

Lemma sem_pend_module_prepare_step_registered_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg observer
  cut before next after state origin (frame : Assertion),
  sem_pend_task_prepare_observer_cut observer cut ->
  kernel_client_heap_step task_create_stack_heap_step sg cut before next after ->
  (sem_pend_sched_module_resources abi saved_local sg
    (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) state ** frame) before ->
  exists returned,
    kernel_client_heap_state_step sem_pend_sched_module_effect sg
      (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) state
      (sem_pend_sched_module_cut SemPendTaskPrepareCut next) returned /\
    (exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
        sg observer None origin state false origin returned trace) /\
    (sem_pend_sched_module_resources abi saved_local sg
      (sem_pend_sched_module_cut SemPendTaskPrepareCut next) returned ** frame) after.
Proof.
  intros * Hobserver Hstep Hpre; rewrite sem_pend_sched_module_prepare_resources in Hpre.
  destruct (sem_pend_task_prepare_fields_step_receipt external platform port abi saved_local sg observer
    cut before next after state origin frame Hobserver Hstep Hpre)
    as [returned [Heffect [[trace Hreceipt] [Hnext Hpost]]]].
  exists returned; split; [apply sem_pend_sched_module_prepare_state_step; exact Heffect|].
  split.
  - eapply sem_pend_dispatch_client_receipt_inclusion; [apply sem_pend_prepare_client_registered|exact Hreceipt].
  - rewrite sem_pend_sched_module_prepare_resources; exact Hpost.
Qed.

(** The physical selected component is invoked once. Its actual next
    owner and effect stay together while literal actions are registered. *)
Lemma sem_pend_module_step_registered_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local actor sg observer cut before next after
  (step : kernel_client_heap_step sem_pend_sched_module_step sg cut before next after),
  sem_pend_sched_module_step_binding actor observer sg cut before next after step ->
  forall state origin (frame : Assertion),
  (sem_pend_sched_module_resources abi saved_local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_step sem_pend_sched_module_effect sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
        sg observer None origin state false origin returned trace) /\
    (sem_pend_sched_module_resources abi saved_local sg next returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor sg observer cut before next after step Hbinding.
  destruct Hbinding; intros state origin frame Hpre.
  - eapply (sem_pend_module_prepare_step_registered_receipt external platform port abi saved_local sg observer
      KernelClientHeapClosed before KernelClientHeapClosed after state origin frame);
      [exact I|constructor; exact run|exact Hpre].
  - eapply (sem_pend_module_prepare_step_registered_receipt external platform port abi saved_local sg observer
      KernelClientHeapClosed before KernelClientHeapClosed after state origin frame);
      [exact I|constructor; exact run|exact Hpre].
  - eapply (sem_pend_module_prepare_step_registered_receipt external platform port abi saved_local sg observer
      (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after state origin frame);
      [exact H|constructor; exact run|exact Hpre].
  - rewrite sem_pend_sched_module_allocation_resources in Hpre.
    pose proof (sem_pend_allocation_fields_source_facts external platform port abi
      (task_create_continuation_local saved_local) sg cut state before frame Hpre) as Hfacts.
    destruct (sem_pend_allocation_fields_extra_resources external platform port abi
      (task_create_continuation_local saved_local) sg cut before next after state frame run Hpre)
      as [returned [Heffect Hpost]].
    assert (Hobserver : kernel_client_heap_observer_cut observer cut) by (destruct run; exact I).
    destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer cut state next returned origin
      H Hobserver (KernelClientHeapExtraState mutex_del_creator_heap_effect sg cut state next returned Heffect) Hfacts)
      as [Hnext [trace Hreceipt]].
    exists returned; split.
    + apply KernelClientHeapExtraState; apply SemPendSchedModuleAllocationEffect; exact Heffect.
    + split.
      * eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
        intros action Hmember; eapply sem_pend_allocation_client_registered; exact Hmember.
      * rewrite sem_pend_sched_module_allocation_resources; exact Hpost.
  - rewrite sem_pend_sched_module_creator_resources in Hpre.
    destruct (sem_pend_creator_interrupt_fields_extra external platform port abi
      (task_create_continuation_local saved_local) creator H sg cut before next after state frame run Hpre)
      as [returned [Heffect Hpost]].
    exists returned; split.
    + apply KernelClientHeapExtraState; apply SemPendSchedModuleCreatorEffect; exact Heffect.
    + split.
      * eapply sem_pend_creator_interrupt_effect_registered_receipt; eassumption.
      * rewrite sem_pend_sched_module_creator_resources; exact Hpost.
  - eapply sem_pend_module_prepare_step_registered_receipt;
      [exact H|constructor; exact run|exact Hpre].
Qed.

Lemma sem_pend_module_trace_registered_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local actor sg observer cut before next after
  (run : kernel_client_heap_trace sem_pend_sched_module_step sg cut before next after),
  sem_pend_sched_module_trace_binding actor observer sg cut before next after run ->
  forall state origin (frame : Assertion),
  (sem_pend_sched_module_resources abi saved_local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace sem_pend_sched_module_effect sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
        sg observer None origin state false origin returned trace) /\
    (sem_pend_sched_module_resources abi saved_local sg next returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor sg observer cut before next after run Hbinding.
  induction Hbinding as [cut heap|cut before middle_cut middle next after step tail Hstep Htail IH];
    intros state origin frame Hpre.
  - exists state; split; [constructor|]. split; [|exact Hpre].
    exists (@KernelClientTaskSourceNil external port (sched_task_registered_client external) sg observer None origin state).
    constructor.
  - destruct (sem_pend_module_step_registered_receipt external platform port abi saved_local actor sg observer
      cut before middle_cut middle step Hstep state origin frame Hpre)
      as [middle_state [Heffect [[head Hhead] Hmiddle]]].
    destruct (IH middle_state origin frame Hmiddle) as [returned [Hstate [[last Hlast] Hpost]]].
    exists returned; split; [econstructor; eassumption|]. split; [|exact Hpost].
    exact (sem_pend_dispatch_client_receipt_append external port (sched_task_registered_client external)
      sg observer None origin state false origin middle_state head Hhead false origin returned last Hlast).
Qed.

(** Keep the allocation factory's own returned state and owner. The
    known empty/initial metadata comes from that actual allocation edge. *)
Lemma sem_pend_allocation_fields_creator_pending : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg state cut returned after (frame : Assertion),
  mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned ->
  (sem_pend_allocation_fields_resources abi local sg cut returned ** frame) after ->
  (sem_pend_creator_fields_resources abi local sg cut returned ** frame) after.
Proof.
  intros external platform port abi local sg state cut returned after frame Heffect Hafter.
  destruct Heffect; [exact Hafter|].
  pose proof (proj2 (event_create_allocate_critical_private_result state eid image returned H)) as Hget.
  assert (Hclose : sem_pend_allocation_fields_resources abi local sg
      (KernelClientHeapExtra (event_pool_addr sg eid)) returned ** frame |--
      sem_pend_creator_fields_resources abi local sg (KernelClientHeapExtra (event_pool_addr sg eid)) returned ** frame).
  { cbn [sem_pend_allocation_fields_resources]; Intros found allocation.
    assert (Hbindings : event_pool_addr sg eid = event_pool_addr sg found /\
      returned.(EventState).(eventLifecycle).(eventPrivate) found = Some allocation) by tauto.
    destruct Hbindings as [Haddress Hlookup].
    assert (found = eid) by (apply event_pool_addr_injective with (sg := sg); congruence); subst found.
    assert (allocation = sem_create_allocation_identity state image)
      by (unfold sem_create_allocation_identity; congruence); subst allocation.
    cbn [sem_pend_creator_fields_resources]; unfold sem_pend_creator_fields_pending.
    Exists eid (sem_create_allocation_identity state image).
    cbn [sem_create_allocation_identity eventPrivateQueue eventPrivateMutexPCP]; entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma sem_pend_module_creator_registered :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    saved_local actor creator sg observer state origin before (frame : Assertion),
  actor <> Some observer -> mutex_del_creator_arguments creator -> sem_create_source_binding sg ->
  (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg state ** frame) before ->
  exists after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      KernelClientHeapClosed before KernelClientHeapClosed after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg KernelClientHeapClosed state KernelClientHeapClosed returned /\
      (exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
          sg observer None origin state false origin returned,
        sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
          sg observer None origin state false origin returned trace) /\
      (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor creator sg observer state origin before frame
    Hforeign Hargs Hbinding Hpre.
  destruct (sem_pend_allocation_fields_produces_receipt external platform port abi
    (task_create_continuation_local saved_local) actor sg observer origin state before frame Hforeign Hbinding Hpre)
    as [cut [popped [allocated [Hallocate [Hstate [[first Hfirst] Hallocated]]]]]].
  pose proof (sem_pend_allocation_fields_creator_pending external platform port abi
    (task_create_continuation_local saved_local) sg state cut allocated popped frame Hstate Hallocated) as Hpending.
  destruct (sem_pend_dispatch_client_receipt_inclusion external port (mutex_del_allocation_source_client actor)
    (sched_task_registered_client external) sg observer None
    (sem_pend_allocation_client_registered external actor) _ _ _ _ _ first Hfirst) as [head Hhead].
  assert (Hfinish : exists after returned,
    kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut popped KernelClientHeapClosed after /\
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut allocated KernelClientHeapClosed returned /\
    (exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
        sg observer None origin allocated false origin returned,
      sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
        sg observer None origin allocated false origin returned trace) /\
    (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg returned ** frame) after).
  { destruct Hstate as [state allocated Hempty|state allocated eid image Hdetach].
    - exists popped, allocated; split; [constructor|]. split; [constructor|]. split; [|exact Hpending].
      exists (@KernelClientTaskSourceNil external port (sched_task_registered_client external) sg observer None origin allocated).
      constructor.
    - destruct (sem_pend_creator_initialization_fields_publish external platform port abi
        (task_create_continuation_local saved_local) sg creator (event_pool_addr sg eid) allocated popped frame Hargs Hpending)
        as [actual [allocation [initialized [final [after [Hpointer [Hget [Hstores [Hfinal [Hrun Hpost]]]]]]]]]].
      assert (Heffect : mutex_del_creator_publication_effect creator sg (KernelClientHeapExtra (event_pool_addr sg eid))
        allocated KernelClientHeapClosed (mutex_del_creator_published_state creator initialized actual final))
        by (econstructor; eassumption).
      exists after, (mutex_del_creator_published_state creator initialized actual final); split.
      + eapply KernelClientHeapTraceCons; [apply KernelClientHeapRegistered; apply MutexDelCreatorPublicationFinish; exact Hrun|constructor].
      + split; [eapply KernelClientHeapStateTraceCons; [apply KernelClientHeapExtraState; exact Heffect|constructor]|].
        split; [|exact Hpost]. eapply sem_pend_creator_publication_effect_registered_receipt; eassumption. }
  destruct Hfinish as [after [returned [tail [Htail_state [[last Hlast] Hpost]]]]].
  assert (oldrun : kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg
    KernelClientHeapClosed before KernelClientHeapClosed after).
  { eapply KernelClientHeapTraceCons.
    - apply KernelClientHeapRegistered; apply MutexDelCreatorPublicationAllocate; exact Hallocate.
    - exact tail. }
  destruct (sem_pend_sched_module_publication_trace_binding actor creator sg observer
    KernelClientHeapClosed before KernelClientHeapClosed after Hforeign Hargs oldrun I) as [run [Hrun Hnext]].
  exists after, run; split; [exact Hrun|]. exists returned; split.
  - apply (sem_pend_sched_module_publication_state_trace creator sg KernelClientHeapClosed state KernelClientHeapClosed returned).
    eapply KernelClientHeapStateTraceCons; [|exact Htail_state].
    apply KernelClientHeapExtraState; constructor; exact Hstate.
  - split; [|exact Hpost].
    exact (sem_pend_dispatch_client_receipt_append external port (sched_task_registered_client external)
      sg observer None origin state false origin allocated head Hhead false origin returned last Hlast).
Qed.

Lemma sem_pend_module_allocation_registered :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    saved_local actor sg observer state origin before (frame : Assertion),
  actor <> Some observer -> sem_create_source_binding sg ->
  (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg state ** frame) before ->
  exists cut after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      KernelClientHeapClosed before (sem_pend_sched_module_cut SemPendAllocationCut cut) after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg KernelClientHeapClosed state
        (sem_pend_sched_module_cut SemPendAllocationCut cut) returned /\
      (exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
          sg observer None origin state false origin returned,
        sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
          sg observer None origin state false origin returned trace) /\
      (sem_pend_sched_module_resources abi saved_local sg
        (sem_pend_sched_module_cut SemPendAllocationCut cut) returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor sg observer state origin before frame Hforeign Hbinding Hpre.
  destruct (sem_pend_allocation_fields_produces_receipt external platform port abi
    (task_create_continuation_local saved_local) actor sg observer origin state before frame Hforeign Hbinding Hpre)
    as [cut [after [allocated [Hallocate [Hstate [Hcalls Hpost]]]]]].
  pose (step := @KernelClientHeapRegistered SemPendSchedModuleCut sem_pend_sched_module_step sg
    KernelClientHeapClosed before (sem_pend_sched_module_cut SemPendAllocationCut cut) after
    (SemPendSchedModuleAllocation sg KernelClientHeapClosed before cut after Hallocate)).
  pose (run := @KernelClientHeapTraceCons SemPendSchedModuleCut sem_pend_sched_module_step sg
    KernelClientHeapClosed before _ after _ after step
    (@KernelClientHeapTraceNil SemPendSchedModuleCut sem_pend_sched_module_step sg _ after)).
  assert (Hrun : sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run).
  { unfold run; constructor; [|constructor]. unfold step.
    exact (SemPendSchedModuleAllocationBinding actor observer sg KernelClientHeapClosed before cut after Hallocate Hforeign). }
  exists cut, after, run; split; [exact Hrun|].
  exists allocated; split.
  - eapply KernelClientHeapStateTraceCons; [|constructor].
    apply KernelClientHeapExtraState.
    exact (SemPendSchedModuleAllocationEffect sg KernelClientHeapClosed state cut allocated Hstate).
  - split.
    + destruct Hcalls as [trace Hreceipt].
      eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
      intros action Hmember; eapply sem_pend_allocation_client_registered; exact Hmember.
    + rewrite sem_pend_sched_module_allocation_resources; exact Hpost.
Qed.

Lemma sem_pend_module_prepare_registered :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    saved_local actor sg observer origin input slot rest (frame : Assertion) before,
  input.(stack_input_call).(os_sched_call_invocation) <> observer ->
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state) ** frame) before ->
  exists after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      (KernelClientHeapExtra (SemPendTaskPrepareCut input)) before KernelClientHeapClosed after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg
        (KernelClientHeapExtra (SemPendTaskPrepareCut input)) input.(stack_input_state) KernelClientHeapClosed returned /\
      (exists trace : kernel_client_task_source_trace external port (sched_task_registered_client external)
          sg observer None origin input.(stack_input_state) false origin returned,
        sem_pend_client_source_local_receipt external port (sched_task_registered_client external)
          sg observer None origin input.(stack_input_state) false origin returned trace) /\
      (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor sg observer origin input slot rest frame before
    Hforeign Hnest Hfree Hhead Hpre.
  assert (Hfacts : task_create_stack_input_facts sg input).
  { destruct Hpre as [owned [rest_heap [Hjoin [[[Hsame Hfacts] Howned] Hframe]]]]; exact Hfacts. }
  destruct (sem_pend_task_prepare_fields_produces_calls external platform port abi saved_local sg input slot rest
    frame before Hnest Hfree Hhead Hpre) as [image [prepared [Hprepare [Hdetach [Hreserve [Hcall Howned]]]]]].
  assert (Himage : input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some image)
    by exact (proj2 (proj2 (proj2 Hdetach))).
  pose proof (sem_pend_task_prepare_fields_valid external platform port abi saved_local sg
    (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image))
    (task_create_stack_input_detached input slot rest image) prepared frame Howned) as Hvalid.
  destruct (sem_pend_task_publication_fields_produces external platform port abi
    (task_create_continuation_local saved_local) sg (task_create_stack_prepared_publication input slot image)
    (task_create_stack_input_detached input slot rest image) frame prepared Howned)
    as [after [Hpublish [Hpublication Hpost]]].
  pose proof (tmr_task_source_call_receipt_step _ _ _ _ _ Hpublication) as Hpublication_step.
  assert (oldrun : kernel_client_heap_trace task_create_stack_heap_step sg
    (KernelClientHeapExtra input) before KernelClientHeapClosed after).
  { eapply KernelClientHeapTraceCons; [apply KernelClientHeapRegistered; exact Hprepare|].
    eapply KernelClientHeapTraceCons; [apply KernelClientHeapPublish; exact Hpublish|constructor]. }
  destruct (sem_pend_sched_module_prepare_trace_binding actor sg observer
    (KernelClientHeapExtra input) before KernelClientHeapClosed after oldrun Hforeign) as [run [Hrun Hnext]].
  exists after, run; split; [exact Hrun|].
  exists (task_create_stack_publication_state sg (task_create_stack_prepared_publication input slot image)
    (task_create_stack_input_detached input slot rest image)); split.
  - eapply KernelClientHeapStateTraceCons.
    + apply KernelClientHeapExtraState.
      eapply (SemPendSchedModulePrepareEffect sg (KernelClientHeapExtra input) input.(stack_input_state)
        (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image))
        (task_create_stack_input_detached input slot rest image)); constructor.
    + eapply KernelClientHeapStateTraceCons; [apply KernelClientHeapPublishState; exact (proj1 Hpublication_step)|constructor].
  - split; [|exact Hpost].
    destruct (sem_pend_task_prepare_client_receipt external port sg observer origin input slot rest image
      Hforeign Hfacts Hfree Hhead Himage) as [head Hhead_receipt].
    destruct (sem_pend_task_prepare_builtin_receipt external port sg observer
      (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image))
      (task_create_stack_input_detached input slot rest image) KernelClientHeapClosed
      (task_create_stack_publication_state sg (task_create_stack_prepared_publication input slot image)
        (task_create_stack_input_detached input slot rest image)) origin Hforeign Hvalid
      ltac:(constructor; exact (proj1 Hpublication_step))) as [_ [tail Htail_receipt]].
    destruct (sem_pend_dispatch_client_receipt_append external port sem_pend_task_prepare_source_client
      sg observer None origin input.(stack_input_state) false origin (task_create_stack_input_detached input slot rest image)
      head Hhead_receipt false origin _ tail Htail_receipt) as [trace Hreceipt].
    eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
    intros action Hmember; apply sem_pend_prepare_client_registered; exact Hmember.
Qed.

(** Only membership of the literal actions already present in this finite
    source tree is recorded. This is not an inclusion of whole registries. *)
Inductive sem_pend_client_source_occurs external port clients sg observer event_observer (action : KernelClientAction) :
  forall first before stopped last after,
  kernel_client_task_source_trace external port clients sg observer event_observer first before stopped last after -> Prop :=
| SemPendClientSourceHead : forall first before middle transient last after stopped member foreign event_foreign step execution tail,
    sem_pend_client_source_occurs external port clients sg observer event_observer action _ _ _ _ _
      (@KernelClientTaskSourceStep external port clients sg observer event_observer
        action first before middle transient last after stopped member foreign event_foreign step execution tail)
| SemPendClientSourceTail : forall head first before middle transient last after stopped member foreign event_foreign step execution tail,
    sem_pend_client_source_occurs external port clients sg observer event_observer action middle transient stopped last after tail ->
    sem_pend_client_source_occurs external port clients sg observer event_observer action _ _ _ _ _
      (@KernelClientTaskSourceStep external port clients sg observer event_observer
        head first before middle transient last after stopped member foreign event_foreign step execution tail).

Definition sem_pend_client_source_membership external port clients
  (target : KernelClientAction -> Prop) sg observer event_observer first before stopped last after
  (trace : kernel_client_task_source_trace external port clients sg observer event_observer
    first before stopped last after) : Prop :=
  forall action, sem_pend_client_source_occurs external port clients sg observer event_observer action
    first before stopped last after trace -> target action.

Lemma sem_pend_client_receipt_with_membership :
  forall external port clients target sg observer event_observer first before stopped last after
    (trace : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped last after),
  sem_pend_client_source_local_receipt external port clients sg observer event_observer
    first before stopped last after trace ->
  sem_pend_client_source_membership external port clients target sg observer event_observer
    first before stopped last after trace ->
  exists included : kernel_client_task_source_trace external port target sg observer event_observer
      first before stopped last after,
    sem_pend_client_source_local_receipt external port target sg observer event_observer
      first before stopped last after included.
Proof.
  intros external port clients target sg observer event_observer first before stopped last after trace Hreceipt.
  induction Hreceipt as [origin state|action first before middle transient last after stopped
    member foreign event_foreign step execution tail Hcall Hfacts Htail IH]; intro Hmembers.
  - exists (@KernelClientTaskSourceNil external port target sg observer event_observer origin state); constructor.
  - assert (Hmember : target action) by (apply Hmembers; constructor).
    assert (Htail_members : sem_pend_client_source_membership external port clients target sg observer event_observer
      middle transient stopped last after tail).
    { intros actual Hoccurs; apply Hmembers; constructor 2; exact Hoccurs. }
    destruct (IH Htail_members) as [included Hinclude].
    exists (@KernelClientTaskSourceStep external port target sg observer event_observer
      action first before middle transient last after stopped Hmember foreign event_foreign step execution included).
    constructor; assumption.
Qed.

(** The caller's original critical parameter is kept. Its finite literal
    memberships must come from the same actual source leaves. Coverage in
    the opposite direction is never used to manufacture this input. *)
Lemma sem_pend_client_membership_prefix_receipt :
  forall environment critical clients sg observer origin state returned after
    (trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) clients sg observer None origin state false origin returned),
  sem_pend_client_source_local_receipt environment.(task_stack_call_external)
    environment.(task_stack_call_port) clients sg observer None origin state false origin returned trace ->
  sem_pend_client_source_membership environment.(task_stack_call_external)
    environment.(task_stack_call_port) clients critical.(critical_region_clients)
    sg observer None origin state false origin returned trace ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix
      environment critical sg observer state returned after,
    sem_pend_sched_prefix_receipt environment critical sg observer state returned after prefix.
Proof.
  intros environment critical clients sg observer origin state returned after trace Hreceipt Hmembers.
  destruct (sem_pend_client_receipt_with_membership _ _ _ _ _ _ _ _ _ _ _ _ trace Hreceipt Hmembers)
    as [included Hinclude].
  destruct (sem_pend_client_local_receipt_raw_trace _ _ _ _ _ _ _ _ _ _ _ included Hinclude) as [raw Hraw].
  exists (@SchedulerPhaseCandidate.OsSchedTaskReturnPrefixLegacy environment critical sg observer _ _ after
    (@LegacyTaskReturnPrefix.OsSchedTaskReturnPrefixClients environment critical sg observer _ _ after raw)).
  constructor; exact Hraw.
Qed.

(** One existing concrete registry instance. No equality with an arbitrary
    current caller's critical parameter is asserted. *)
Lemma sem_pend_registered_client_prefix_receipt :
  forall environment resources sg observer origin state returned after
    (trace : kernel_client_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) (sched_task_registered_client environment.(task_stack_call_external))
      sg observer None origin state false origin returned),
  sem_pend_client_source_local_receipt environment.(task_stack_call_external)
    environment.(task_stack_call_port) (sched_task_registered_client environment.(task_stack_call_external))
    sg observer None origin state false origin returned trace ->
  exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment
      (sched_task_source_region environment.(task_stack_call_external) resources) sg observer state returned after,
    sem_pend_sched_prefix_receipt environment
      (sched_task_source_region environment.(task_stack_call_external) resources) sg observer state returned after prefix.
Proof.
  intros environment resources sg observer origin state returned after trace Hreceipt.
  eapply sem_pend_client_membership_prefix_receipt; [exact Hreceipt|].
  clear Hreceipt; intros action Hoccurs; induction Hoccurs; assumption.
Qed.

(** The concrete source-region consumers below use each factory's original
    output witness. They never rerun the module interpreter after obtaining
    a returned state. The arbitrary-critical consumer remains separate. *)
Lemma sem_pend_module_allocation_prefix :
  forall environment resources saved_local actor sg observer state (origin : TaskInvocationOrigin) before (frame : Assertion),
  actor <> Some observer -> sem_create_source_binding sg ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations)
    (task_create_continuation_local saved_local) sg state ** frame) before ->
  exists cut after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      KernelClientHeapClosed before (sem_pend_sched_module_cut SemPendAllocationCut cut) after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg KernelClientHeapClosed state
        (sem_pend_sched_module_cut SemPendAllocationCut cut) returned /\
      exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment
          (sched_task_source_region environment.(task_stack_call_external) resources) sg observer state returned after,
        sem_pend_sched_prefix_receipt environment
          (sched_task_source_region environment.(task_stack_call_external) resources) sg observer state returned after prefix /\
        (sem_pend_sched_module_resources environment.(task_stack_call_continuations) saved_local sg
          (sem_pend_sched_module_cut SemPendAllocationCut cut) returned ** frame) after.
Proof.
  intros environment resources saved_local actor sg observer state origin before frame Hforeign Hbinding Hpre.
  destruct (sem_pend_module_allocation_registered environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    saved_local actor sg observer state origin before frame Hforeign Hbinding Hpre)
    as [cut [after [run [Hrun [returned [Hstate [[trace Hreceipt] Hpost]]]]]]].
  destruct (sem_pend_registered_client_prefix_receipt environment resources sg observer origin state returned after trace Hreceipt)
    as [prefix Hprefix].
  exists cut, after, run; split; [exact Hrun|]. exists returned; split; [exact Hstate|].
  exists prefix; split; assumption.
Qed.

Lemma sem_pend_module_creator_prefix :
  forall environment resources saved_local actor creator sg observer state (origin : TaskInvocationOrigin) before (frame : Assertion),
  actor <> Some observer -> mutex_del_creator_arguments creator -> sem_create_source_binding sg ->
  (kernel_client_continuation_fields_world environment.(task_stack_call_continuations)
    (task_create_continuation_local saved_local) sg state ** frame) before ->
  exists after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      KernelClientHeapClosed before KernelClientHeapClosed after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg KernelClientHeapClosed state KernelClientHeapClosed returned /\
      exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment
          (sched_task_source_region environment.(task_stack_call_external) resources) sg observer state returned after,
        sem_pend_sched_prefix_receipt environment
          (sched_task_source_region environment.(task_stack_call_external) resources) sg observer state returned after prefix /\
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations)
          (task_create_continuation_local saved_local) sg returned ** frame) after.
Proof.
  intros environment resources saved_local actor creator sg observer state origin before frame Hforeign Hargs Hbinding Hpre.
  destruct (sem_pend_module_creator_registered environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    saved_local actor creator sg observer state origin before frame Hforeign Hargs Hbinding Hpre)
    as [after [run [Hrun [returned [Hstate [[trace Hreceipt] Hpost]]]]]].
  destruct (sem_pend_registered_client_prefix_receipt environment resources sg observer origin state returned after trace Hreceipt)
    as [prefix Hprefix].
  exists after, run; split; [exact Hrun|]. exists returned; split; [exact Hstate|].
  exists prefix; split; assumption.
Qed.

Lemma sem_pend_module_prepare_prefix :
  forall environment resources saved_local actor sg observer (origin : TaskInvocationOrigin) input slot rest (frame : Assertion) before,
  input.(stack_input_call).(os_sched_call_invocation) <> observer ->
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (sem_pend_task_prepare_fields_input environment.(task_stack_call_continuations) saved_local sg input
    input.(stack_input_state) ** frame) before ->
  exists after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      (KernelClientHeapExtra (SemPendTaskPrepareCut input)) before KernelClientHeapClosed after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg
        (KernelClientHeapExtra (SemPendTaskPrepareCut input)) input.(stack_input_state) KernelClientHeapClosed returned /\
      exists prefix : SchedulerPhaseCandidate.os_sched_task_return_prefix environment
          (sched_task_source_region environment.(task_stack_call_external) resources)
          sg observer input.(stack_input_state) returned after,
        sem_pend_sched_prefix_receipt environment
          (sched_task_source_region environment.(task_stack_call_external) resources)
          sg observer input.(stack_input_state) returned after prefix /\
        (kernel_client_continuation_fields_world environment.(task_stack_call_continuations)
          (task_create_continuation_local saved_local) sg returned ** frame) after.
Proof.
  intros environment resources saved_local actor sg observer origin input slot rest frame before Hforeign Hnest Hfree Hhead Hpre.
  destruct (sem_pend_module_prepare_registered environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    saved_local actor sg observer origin input slot rest frame before Hforeign Hnest Hfree Hhead Hpre)
    as [after [run [Hrun [returned [Hstate [[trace Hreceipt] Hpost]]]]]].
  destruct (sem_pend_registered_client_prefix_receipt environment resources sg observer origin
    input.(stack_input_state) returned after trace Hreceipt) as [prefix Hprefix].
  exists after, run; split; [exact Hrun|]. exists returned; split; [exact Hstate|].
  exists prefix; split; assumption.
Qed.
