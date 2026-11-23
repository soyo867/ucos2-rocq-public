Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_allocation_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Import EventStateDef KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This component uses the existing allocation registry, not the open
    Extra family. The local facts are extracted at the actual incoming
    cut, including a private pointer cut and a prepared publication cut. *)
Lemma sem_pend_allocation_resources_source_facts :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg cut state heap (frame : Assertion),
  (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg cut state ** frame) heap ->
  sem_pend_source_state_facts sg state.
Proof.
  intros external platform port abi sg cut state heap frame Hpre.
  assert (Hopen : kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi)
    sg cut state ** frame |-- coq_prop (UCOS2_state_inv sg state) && TT).
  { destruct cut; cbn [kernel_client_heap_resources].
    - unfold kernel_client_heap_world, kernel_program_inv; entailer!.
    - unfold kernel_client_heap_publication; entailer!.
    - unfold mutex_del_creator_heap_resources; Intros eid allocation.
      unfold kernel_client_heap_world, kernel_program_inv; entailer!. }
  apply sem_pend_source_state_facts_from_valid; exact (proj1 (Hopen heap Hpre)).
Qed.

(** The following physical adapter owns six Flag fields, not the missing
    padding map. Only the Event module is opened; the real remaining fields,
    Timer resources, unmap table and caller's frame are all retained. *)
Definition sem_pend_event_fields_pool_frame sg state : Assertion :=
  store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
  event_free_storage_rep sg state.(EventState) **
  UCOS2_fields_raw_rep_missing_module sg state EventModule ** unmap_table_rep sg.

Definition sem_pend_event_fields_node_frame sg state eid image : Assertion :=
  event_storage_without_field false (event_pool_addr sg eid) image EventPtrField **
  event_free_storage_without_eid sg state.(EventState) eid **
  store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
  UCOS2_fields_raw_rep_missing_module sg state EventModule ** unmap_table_rep sg.

Lemma sem_pend_event_fields_split_head : forall sg state,
  kernel_program_fields_inv sg state --||--
  coq_prop (UCOS2_state_inv sg state) &&
    (sg.(g_OSEventFreeList) # Ptr |-> sem_create_pool_head sg state **
     sem_pend_event_fields_pool_frame sg state).
Proof.
  intros sg state.
  unfold kernel_program_fields_inv, kernel_program_fields_rep.
  rewrite (UCOS2_fields_raw_rep_split_module sg state EventModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold event_raw_rep, event_free_root_rep, sem_create_pool_head,
    sem_pend_event_fields_pool_frame; split; entailer!.
Qed.

Lemma sem_pend_event_fields_split_node : forall sg state eid rest image,
  sem_create_source_binding sg -> UCOS2_state_inv sg state ->
  state.(EventState).(unUsedEventStates) = eid :: rest ->
  state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  sem_pend_event_fields_pool_frame sg state |--
    (event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
    sem_pend_event_fields_node_frame sg state eid image.
Proof.
  intros sg state eid rest image Hsource Hvalid Hhead Himage.
  destruct (sem_create_pool_nonempty_facts sg state eid rest Hvalid Hhead)
    as [Hrange [actual [Hactual Hnext]]].
  assert (actual = image) by congruence; subst actual.
  unfold sem_pend_event_fields_pool_frame, sem_pend_event_fields_node_frame.
  sep_apply_l_atomic (event_free_storage_split_eid sg state.(EventState) eid image Himage).
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  rewrite Hnames.
  sep_apply_l_atomic (event_storage_split_field false (event_pool_addr sg eid) image
    EventPtrField ltac:(unfold event_fields; simpl; tauto)).
  unfold event_cell, event_field_offset; rewrite Hnext; entailer!.
Qed.

Lemma sem_pend_event_fields_detach_frame_eq : forall sg state eid rest image,
  UCOS2_state_inv sg state -> state.(EventState).(unUsedEventStates) = eid :: rest ->
  UCOS2_fields_raw_rep_missing_module sg state EventModule =
  UCOS2_fields_raw_rep_missing_module sg
    (replace_EventS (event_detach_head state.(EventState) eid rest image) state) EventModule.
Proof.
  intros sg state eid rest image Hvalid Hhead.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_free_unallocated sg state.(EventState) eid Hpool
    ltac:(rewrite Hhead; simpl; auto)) as [_ Hprivate].
  apply UCOS2_fields_raw_rep_missing_module_frame_eq; [reflexivity|].
  intros m Hflag Hevent; destruct m; try contradiction; try reflexivity.
  cbn [UCOS2_module_rep replace_EventS].
  symmetry; apply queue_storage_event_detach_head_eq; exact Hprivate.
Qed.

Lemma sem_pend_event_fields_merge_detached_node : forall sg state eid rest image,
  UCOS2_state_inv sg state -> state.(EventState).(unUsedEventStates) = eid :: rest ->
  state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     sem_pend_event_fields_node_frame sg state eid image) |--
  event_storage_rep false (event_pool_addr sg eid) image **
    kernel_program_fields_inv sg
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state).
Proof.
  intros sg state eid rest image Hvalid Hhead Himage.
  destruct (sem_create_pool_nonempty_facts sg state eid rest Hvalid Hhead)
    as [Hrange [actual [Hactual Hnext]]].
  assert (actual = image) by congruence; subst actual.
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hcell : (event_pool_addr sg eid + 4) # Ptr |->
      event_encode_pool_link sg (hd_error rest) =
    event_cell (event_pool_addr sg eid) EventPtrField (image EventPtrField)).
  { unfold event_cell, event_field_offset; rewrite Hnext; reflexivity. }
  unfold sem_pend_event_fields_node_frame; rewrite Hcell.
  assert (Hrestore :
    (event_cell (event_pool_addr sg eid) EventPtrField (image EventPtrField) **
     event_storage_without_field false (event_pool_addr sg eid) image EventPtrField) **
     event_free_storage_without_eid sg state.(EventState) eid |--
     event_free_storage_rep sg state.(EventState)).
  { sep_apply_l_atomic (event_storage_merge_field false (event_pool_addr sg eid) image
      EventPtrField ltac:(unfold event_fields; simpl; tauto)).
    rewrite <- Hnames; apply event_free_storage_merge_eid; exact Himage. }
  assert (Hpool_merge :
    (store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
     event_free_storage_rep sg state.(EventState) **
     sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest)) **
     UCOS2_fields_raw_rep_missing_module sg state EventModule ** unmap_table_rep sg |--
    event_storage_rep false (event_pool_addr sg eid) image **
    kernel_program_fields_inv sg
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state)).
  { sep_apply_l_atomic (event_detach_head_reconstructs_raw_rep sg state.(TskState)
      state.(EventState) eid rest image Himage).
    pose proof (UCOS2_event_detach_head_preserves_validity sg state eid rest image Hvalid Hhead) as Hpost.
    unfold kernel_program_fields_inv, kernel_program_fields_rep.
    rewrite (UCOS2_fields_raw_rep_split_module sg
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state)
      EventModule ltac:(discriminate)).
    cbn [UCOS2_module_rep replace_EventS].
    rewrite <- (sem_pend_event_fields_detach_frame_eq sg state eid rest image Hvalid Hhead).
    rewrite Hnames; entailer!. }
  assert (Hnode_merge :
    ((event_cell (event_pool_addr sg eid) EventPtrField (image EventPtrField) **
      event_storage_without_field false (event_pool_addr sg eid) image EventPtrField) **
      event_free_storage_without_eid sg state.(EventState) eid) **
    (store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
     sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     UCOS2_fields_raw_rep_missing_module sg state EventModule ** unmap_table_rep sg) |--
    event_storage_rep false (event_pool_addr sg eid) image **
    kernel_program_fields_inv sg
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state)).
  { sep_apply_l_atomic Hrestore.
    match goal with |- ?P |-- _ =>
      assert (Horder : P |--
        (store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
         event_free_storage_rep sg state.(EventState) **
         sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest)) **
         UCOS2_fields_raw_rep_missing_module sg state EventModule ** unmap_table_rep sg) by entailer!
    end.
    exact (fun heap Howned => Hpool_merge heap (Horder heap Howned)). }
  match goal with |- ?P |-- _ =>
    assert (Horder : P |--
      ((event_cell (event_pool_addr sg eid) EventPtrField (image EventPtrField) **
        event_storage_without_field false (event_pool_addr sg eid) image EventPtrField) **
        event_free_storage_without_eid sg state.(EventState) eid) **
      (store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
       sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
       UCOS2_fields_raw_rep_missing_module sg state EventModule ** unmap_table_rep sg)) by entailer!
  end.
  exact (fun heap Howned => Hnode_merge heap (Horder heap Howned)).
Qed.

(** These are the original free-pop's two pointer reads and one pointer
    store. The post-state is chosen by that actual write, with every
    non-Event resource retained in the very same frame. *)
Lemma sem_pend_event_detach_fields_resources : forall sg state eid rest before (frame : Assertion),
  sem_create_source_binding sg -> state.(EventState).(unUsedEventStates) = eid :: rest ->
  (kernel_program_fields_inv sg state ** frame) before ->
  exists image after,
    state.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image /\
    event_pool_addr sg eid <> 0 /\
    pointer_load sg.(g_OSEventFreeList) (event_pool_addr sg eid) before /\
    pointer_load (event_pool_addr sg eid + 4) (event_encode_pool_link sg (hd_error rest)) before /\
    kernel_heap_execution (pointer_store_writes sg.(g_OSEventFreeList)
      (event_encode_pool_link sg (hd_error rest))) before after /\
    event_create_allocate_critical state (Some (eid, image))
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state) /\
    (event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
     kernel_program_fields_inv sg
       (replace_EventS (event_detach_head state.(EventState) eid rest image) state) ** frame) after.
Proof.
  intros sg state eid rest before frame Hsource Hhead Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { destruct Hpre as [owned [other [Hjoin [Hinv Hother]]]]; exact (proj1 Hinv). }
  destruct (sem_create_pool_nonempty_facts sg state eid rest Hvalid Hhead)
    as [Hrange [image [Himage Hnext]]].
  pose proof Hsource as [_ [_ [_ Hlayout]]].
  destruct (Hlayout eid Hrange) as [[Hpositive Hupper] Hlink].
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hopen : kernel_program_fields_inv sg state ** frame |--
    sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_pend_event_fields_node_frame sg state eid image ** frame))).
  { rewrite sem_pend_event_fields_split_head; Intros.
    sep_apply_l_atomic (sem_pend_event_fields_split_node sg state eid rest image
      Hsource Hvalid Hhead Himage).
    unfold sem_create_pool_head; rewrite Hhead; cbn [hd_error event_encode_pool_link]; entailer!. }
  pose proof (Hopen before Hpre) as Howned.
  pose proof (framed_pointer_store_load _ _ _ _ Howned) as Hread_head.
  assert (Hnext_order : sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_pend_event_fields_node_frame sg state eid image ** frame)) |--
    (event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
    (sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
     sem_pend_event_fields_node_frame sg state eid image ** frame)) by entailer!.
  pose proof (framed_pointer_store_load _ _ _ _ (Hnext_order before Howned)) as Hread_next.
  assert (Hwrite_order : sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_pend_event_fields_node_frame sg state eid image ** frame)) |--
    sg.(g_OSEventFreeList) # Ptr |->_ **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_pend_event_fields_node_frame sg state eid image ** frame))).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSEventFreeList) (event_pool_addr sg eid)); entailer!. }
  destruct (framed_pointer_store_execution _ _ _ before (proj1 Hread_next)
    (Hwrite_order before Howned)) as [after [Hwrite Hafter]].
  assert (Hclose : sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
    ((event_pool_addr sg eid + 4) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
     (sem_pend_event_fields_node_frame sg state eid image ** frame)) |--
    event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
    kernel_program_fields_inv sg
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state) ** frame).
  { unfold event_private_storage_rep, sem_create_allocation_identity.
    cbn [eventPrivateStorage]; rewrite Hnames; cancel frame.
    apply sem_pend_event_fields_merge_detached_node; assumption. }
  exists image, after; split; [exact Himage|]. split; [lia|].
  split; [exact Hread_head|]. split; [exact Hread_next|]. split; [exact Hwrite|]. split.
  - unfold event_create_allocate_critical; rewrite Hhead.
    exists image; repeat split; assumption || reflexivity.
  - exact (Hclose after Hafter).
Qed.

Lemma sem_pend_event_allocate_fields_source : forall sg state before (frame : Assertion),
  sem_create_source_binding sg -> (kernel_program_fields_inv sg state ** frame) before ->
  exists result allocated after,
    pointer_load sg.(g_OSEventFreeList) (event_create_return_ptr sg result) before /\
    event_create_allocate_critical state result allocated /\
    (match result with
     | None => after = before
     | Some (eid, _) => event_pool_addr sg eid <> 0 /\ exists next,
         pointer_load (event_pool_addr sg eid + 4) next before /\
         kernel_heap_execution (pointer_store_writes sg.(g_OSEventFreeList) next) before after
     end) /\
    (kernel_program_fields_inv sg allocated **
     (match result with None => emp | Some (eid, image) =>
        event_private_storage_rep sg eid (sem_create_allocation_identity state image) end) ** frame) after.
Proof.
  intros sg state before frame Hsource Hpre.
  destruct state.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  - exists None, state, before.
    assert (Hroot : kernel_program_fields_inv sg state ** frame |--
      sg.(g_OSEventFreeList) # Ptr |-> 0 ** (sem_pend_event_fields_pool_frame sg state ** frame)).
    { rewrite sem_pend_event_fields_split_head.
      unfold sem_create_pool_head; rewrite Hhead; cbn [hd_error event_encode_pool_link]; entailer!. }
    split; [exact (framed_pointer_store_load _ _ _ _ (Hroot before Hpre))|].
    split; [unfold event_create_allocate_critical; rewrite Hhead; split; reflexivity|].
    split; [reflexivity|].
    assert (Hclose : kernel_program_fields_inv sg state ** frame |--
      kernel_program_fields_inv sg state ** emp ** frame) by entailer!.
    exact (Hclose before Hpre).
  - destruct (sem_pend_event_detach_fields_resources sg state eid rest before frame Hsource Hhead Hpre)
      as [image [after [Himage [Hnonzero [Hread [Hnext [Hwrite [Hstep Hafter]]]]]]]].
    exists (Some (eid, image)),
      (replace_EventS (event_detach_head state.(EventState) eid rest image) state), after.
    split; [exact Hread|]. split; [exact Hstep|]. split.
    + split; [exact Hnonzero|]. exists (event_encode_pool_link sg (hd_error rest)); split; assumption.
    + assert (Hclose : event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
        kernel_program_fields_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) ** frame |--
        kernel_program_fields_inv sg (replace_EventS (event_detach_head state.(EventState) eid rest image) state) **
        event_private_storage_rep sg eid (sem_create_allocation_identity state image) ** frame) by entailer!.
      exact (Hclose after Hafter).
Qed.

(** A literal client-frame edge keeps its actual action, step proof and
    execution origin. This helper is consumed by each concrete case below. *)
Lemma sem_pend_dispatch_framed_step_receipt :
  forall external port clients sg observer event_observer origin action before after,
  clients action -> kernel_client_actor action <> Some observer ->
  (forall invocation, event_observer = Some invocation -> kernel_client_event_actor action <> Some invocation) ->
  kernel_client_step action sg before after ->
  before.(SchedState).(curTaskID) = after.(SchedState).(curTaskID) ->
  tmr_task_source_call_receipt external action sg before after -> sem_pend_source_state_facts sg before ->
  exists trace : kernel_client_task_source_trace external port clients sg observer event_observer
    origin before (kernel_client_stops action observer) origin after,
    sem_pend_client_source_local_receipt external port clients sg observer event_observer
      origin before (kernel_client_stops action observer) origin after trace.
Proof.
  intros * Hmember Hforeign Hevent Hstep Hcurrent Hcall Hfacts.
  rewrite <- (Bool.orb_false_r (kernel_client_stops action observer)).
  pose (execution := @TaskExecutionClientFrame external port sg action origin before after Hstep Hcurrent).
  exists (@KernelClientTaskSourceStep external port clients sg observer event_observer
    action origin before origin after origin after false Hmember Hforeign Hevent Hstep execution
    (@KernelClientTaskSourceNil external port clients sg observer event_observer origin after)).
  constructor; [exact Hcall|exact Hfacts|constructor].
Qed.

Lemma sem_pend_allocation_heap_state_step_receipt :
  forall external port actor sg observer cut state next returned origin,
  actor <> Some observer -> kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_state_step mutex_del_creator_heap_effect sg cut state next returned ->
  sem_pend_source_state_facts sg state ->
  kernel_client_heap_observer_cut observer next /\
  exists trace : kernel_client_task_source_trace external port (mutex_del_allocation_source_client actor)
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port (mutex_del_allocation_source_client actor)
      sg observer None origin state false origin returned trace.
Proof.
  intros * Hforeign Hobserver Hstep Hfacts; destruct Hstep.
  - split; [exact I|].
    eapply sem_pend_dispatch_framed_step_receipt with
      (action := kernel_full_profile_cut_client KernelFullIntEnter).
    + constructor.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + apply TmrTaskCallProfile; split; [exact I|reflexivity].
    + exact Hfacts.
  - split; [exact I|].
    eapply sem_pend_dispatch_framed_step_receipt with
      (action := kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))).
    + constructor.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + apply TmrTaskCallProfile; split; [exact I|reflexivity].
    + exact Hfacts.
  - split; [exact I|].
    eapply sem_pend_dispatch_framed_step_receipt with (action := task_create_stack_publication_client publication).
    + constructor.
    + cbn [task_create_stack_publication_client kernel_client_actor].
      cbn [kernel_client_heap_observer_cut] in Hobserver; congruence.
    + intros; discriminate.
    + split; [exact H|reflexivity].
    + apply task_create_stack_publication_current_pointer_eq.
    + apply TmrTaskCallNontimer; [constructor|split; [exact H|reflexivity]].
    + exact Hfacts.
  - destruct H; split; [exact I| |exact I|].
    all: eapply sem_pend_dispatch_framed_step_receipt with
      (action := event_create_allocate_client actor state.(EventState).(eventLifecycle).(eventNextInvocation));
      [constructor|exact Hforeign|intros; discriminate|
       split; [reflexivity|eexists; eassumption]| |
       apply TmrTaskCallNontimer; [constructor|split; [reflexivity|eexists; eassumption]]|exact Hfacts].
    all: unfold event_create_allocate_critical in H;
      destruct state.(EventState).(unUsedEventStates);
      [destruct H as [_ ->]|destruct H as [actual_image [_ [_ ->]]]]; reflexivity.
Qed.

Lemma sem_pend_dispatch_client_receipt_append :
  forall external port clients sg observer event_observer first before stopped1 middle transient
    (prefix : kernel_client_task_source_trace external port clients sg observer event_observer
      first before stopped1 middle transient),
  sem_pend_client_source_local_receipt external port clients sg observer event_observer
    first before stopped1 middle transient prefix ->
  forall stopped2 last after
    (suffix : kernel_client_task_source_trace external port clients sg observer event_observer
      middle transient stopped2 last after),
  sem_pend_client_source_local_receipt external port clients sg observer event_observer
    middle transient stopped2 last after suffix ->
  exists trace : kernel_client_task_source_trace external port clients sg observer event_observer
    first before (orb stopped1 stopped2) last after,
    sem_pend_client_source_local_receipt external port clients sg observer event_observer
      first before (orb stopped1 stopped2) last after trace.
Proof.
  intros external port clients sg observer event_observer first before stopped1 middle transient prefix Hprefix.
  induction Hprefix as [origin state|action first before middle transient last after stopped
    member foreign event_foreign step execution tail receipt facts Htail IH];
    intros stopped2 final final_state suffix Hsuffix.
  - exists suffix; exact Hsuffix.
  - destruct (IH stopped2 final final_state suffix Hsuffix) as [joined Hjoined].
    rewrite <- Bool.orb_assoc.
    exists (@KernelClientTaskSourceStep external port clients sg observer event_observer
      action first before middle transient final final_state (orb stopped stopped2)
      member foreign event_foreign step execution joined).
    constructor; assumption.
Qed.

(** The original allocation interpreter's Hstep/Hmiddle cut is consumed
    here before either is erased. Every actual heap step remains present,
    including Empty, Detach and all three built-in constructors. *)
Lemma sem_pend_allocation_trace_source_receipt_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    actor sg observer cut before next after (frame : Assertion),
  actor <> Some observer ->
  kernel_client_heap_trace mutex_del_creator_heap_step sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace mutex_del_creator_heap_effect sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port (mutex_del_allocation_source_client actor)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (mutex_del_allocation_source_client actor)
        sg observer None origin state false origin returned trace) /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg next returned ** frame) after.
Proof.
  intros external platform port abi actor sg observer cut before next after frame Hforeign Htrace.
  induction Htrace; intros state origin Hobserver Hpre.
  - exists state; split; [constructor|]. split.
    + exists (@KernelClientTaskSourceNil external port (mutex_del_allocation_source_client actor)
        sg observer None origin state); constructor.
    + split; assumption.
  - pose proof (sem_pend_allocation_resources_source_facts _ _ _ abi sg cut state before frame Hpre) as Hfacts.
    destruct (kernel_client_heap_step_resources external platform port Z abi
      (mutex_del_creator_heap_resources abi) mutex_del_creator_heap_step mutex_del_creator_heap_effect
      (mutex_del_creator_heap_extension_valid external platform port abi)
      sg cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer cut state
      middle_cut middle_state origin Hforeign Hobserver Hstep Hfacts) as [Hmiddle_observer [head Hhead]].
    destruct (IHHtrace middle_state origin Hmiddle_observer Hmiddle)
      as [returned [Htail [[tail Htail_receipt] [Hfinal Hpost]]]].
    exists returned; split; [econstructor; eassumption|]. split; [|split; assumption].
    exact (sem_pend_dispatch_client_receipt_append external port
      (mutex_del_allocation_source_client actor) sg observer None origin state false origin middle_state
      head Hhead false origin returned tail Htail_receipt).
Qed.

(** Immediate Sem consumer of the same concrete component output. The
    arbitrary next cut and its owner remain; allocation need not publish
    or return a closed/public endpoint to obtain its finite receipt. *)
Lemma sem_pend_allocation_trace_waiter_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    actor sg observer cut before next after (frame : Assertion) state (origin : TaskInvocationOrigin) tid old eid generation,
  actor <> Some observer -> kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_trace mutex_del_creator_heap_step sg cut before next after ->
  (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg cut state ** frame) before ->
  state.(TskState).(inUsedTaskStates) tid = Some old -> sem_pend_wait_continuation eid generation old ->
  exists returned,
    kernel_client_heap_state_trace mutex_del_creator_heap_effect sg cut state next returned /\
    sem_pend_task_projection state.(TskState) returned.(TskState) tid old /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg next returned ** frame) after.
Proof.
  intros external platform port abi actor sg observer cut before next after frame state origin tid old eid generation
    Hforeign Hobserver Htrace Hpre Hold Hwait.
  destruct (sem_pend_allocation_trace_source_receipt_resources external platform port abi actor sg observer
    cut before next after frame Hforeign Htrace state origin Hobserver Hpre)
    as [returned [Hstates [[trace Hreceipt] [Hnext Hpost]]]].
  exists returned; split; [exact Hstates|]. split.
  - eapply sem_pend_client_source_local_projection; eassumption.
  - split; assumption.
Qed.

(** The real allocation pointer selects the extra owner. Closed and
    publication cuts are the existing strong fields owners; the new extra
    cut keeps that same map plus the actual private ECB, including its bytes. *)
Definition sem_pend_allocation_fields_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) local sg
  (cut : KernelClientHeapCut Z) state : Assertion :=
  match cut with
  | KernelClientHeapClosed => kernel_client_continuation_fields_world abi local sg state
  | KernelClientHeapTaskPublication publication =>
      kernel_client_continuation_fields_publication abi local sg publication state
  | KernelClientHeapExtra pointer => EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) &&
      (kernel_client_continuation_fields_world abi local sg state **
        event_private_storage_rep sg eid allocation)
  end.

Lemma sem_pend_allocation_fields_source_facts :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local sg cut state heap (frame : Assertion),
  (sem_pend_allocation_fields_resources abi local sg cut state ** frame) heap ->
  sem_pend_source_state_facts sg state.
Proof.
  intros external platform port abi local sg cut state heap frame Hpre.
  assert (Hopen : sem_pend_allocation_fields_resources abi local sg cut state ** frame |--
    coq_prop (UCOS2_state_inv sg state) && TT).
  { destruct cut; cbn [sem_pend_allocation_fields_resources].
    - unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
        kernel_program_fields_inv; entailer!.
    - unfold kernel_client_continuation_fields_publication; entailer!.
    - Intros eid allocation.
      unfold kernel_client_continuation_fields_world, kernel_continuation_inv,
        kernel_program_fields_inv; entailer!. }
  apply sem_pend_source_state_facts_from_valid; exact (proj1 (Hopen heap Hpre)).
Qed.

Lemma sem_pend_allocation_fields_extra_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local sg cut before next after state (frame : Assertion),
  mutex_del_creator_heap_step sg cut before next after ->
  (sem_pend_allocation_fields_resources abi local sg cut state ** frame) before ->
  exists returned,
    mutex_del_creator_heap_effect sg cut state next returned /\
    (sem_pend_allocation_fields_resources abi local sg next returned ** frame) after.
Proof.
  intros external platform port abi local sg cut before next after state frame Hsource Hpre.
  assert (Hpre_closed : (kernel_client_continuation_fields_world abi local sg state ** frame) before).
  { destruct Hsource; exact Hpre. }
  assert (Hsplit : kernel_client_continuation_fields_world abi local sg state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) None) &&
    (kernel_program_fields_inv sg state **
     (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv; entailer!. }
  destruct (Hsplit before Hpre_closed) as [Hcoverage Hheap].
  destruct Hsource as [heap Hbinding Hread|before pointer next after Hbinding Hnonzero Hread Hnext Hwrites].
  - destruct (sem_pend_event_allocate_fields_source sg state heap _ Hbinding Hheap)
      as [result [allocated [produced [Hhead [Hstep [Hrun Hpost]]]]]].
    pose proof (pointer_load_deterministic _ _ _ _ Hread Hhead) as Hpointer.
    destruct result as [[eid image]|].
    + destruct Hrun as [Hnonzero _]; cbn [event_create_return_ptr] in Hpointer.
      exfalso; apply Hnonzero; symmetry; exact Hpointer.
    + destruct (event_create_allocate_critical_empty_frame _ _ Hstep) as [_ ->].
      exists state; split; [constructor; exact Hstep|exact Hpre_closed].
  - destruct (sem_pend_event_allocate_fields_source sg state before _ Hbinding Hheap)
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
      * assert (Hmerge : kernel_program_fields_inv sg allocated **
          event_private_storage_rep sg eid (sem_create_allocation_identity state image) **
          (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
            state.(TskState).(parkedTaskStacks) ** frame) |--
          sem_pend_allocation_fields_resources abi local sg (KernelClientHeapExtra pointer) allocated ** frame).
        { cbn [sem_pend_allocation_fields_resources].
          Exists eid (sem_create_allocation_identity state image).
          unfold kernel_client_continuation_fields_world, kernel_continuation_inv.
          rewrite Htasks; entailer!. }
        exact (Hmerge after Hpost).
    + cbn [event_create_return_ptr] in Hpointer; exfalso; apply Hnonzero; exact Hpointer.
Qed.

(** This is an actual fields Hmodules instance for precisely the original
    allocation component. The three built-ins use their checked physical
    transports; Extra uses the two concrete free-pop branches above. *)
Lemma sem_pend_allocation_fields_resource_guarantee :
  forall external platform port (abi : Armv7aContinuationABI external platform port) local,
  kernel_client_fields_resource_guarantee (sem_pend_allocation_fields_resources abi local)
    mutex_del_creator_heap_step mutex_del_creator_heap_effect.
Proof.
  intros external platform port abi local sg cut before next after state frame Hstep Hpre.
  destruct Hstep.
  - exists (os_int_enter_state state); split; [constructor|].
    eapply kernel_client_int_enter_continuation_fields_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state).
    split; [constructor|].
    eapply kernel_client_int_exit_continuation_fields_resources; eassumption.
  - assert (Hbuiltin : @kernel_client_heap_step Z (fun _ _ _ _ _ => False) sg
      (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after).
    { constructor; exact H. }
    destruct (kernel_client_builtin_fields_resource_guarantee_proof external platform port Z abi local
      sg (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after state frame
      Hbuiltin Hpre) as [returned [Heffect Hpost]].
    exists returned; split; [|exact Hpost].
    inversion Heffect; subst; [constructor; assumption|contradiction].
  - destruct (sem_pend_allocation_fields_extra_resources external platform port abi local sg
      cut before next after state frame H Hpre) as [returned [Heffect Hpost]].
    exists returned; split; [constructor; exact Heffect|exact Hpost].
Qed.

(** The physical allocation producer is consumed immediately to form the
    original registry's exact heap step and its matching source receipt.
    No preselected abstract output or private owner is required. *)
Lemma sem_pend_allocation_fields_produces_receipt :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local actor sg observer origin state before (frame : Assertion),
  actor <> Some observer -> sem_create_source_binding sg ->
  (kernel_client_continuation_fields_world abi local sg state ** frame) before ->
  exists cut after returned,
    mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after /\
    mutex_del_creator_heap_effect sg KernelClientHeapClosed state cut returned /\
    (exists trace : kernel_client_task_source_trace external port (mutex_del_allocation_source_client actor)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (mutex_del_allocation_source_client actor)
        sg observer None origin state false origin returned trace) /\
    (sem_pend_allocation_fields_resources abi local sg cut returned ** frame) after.
Proof.
  intros external platform port abi local actor sg observer origin state before frame Hforeign Hbinding Hpre.
  assert (Hsplit : kernel_client_continuation_fields_world abi local sg state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) None) &&
    (kernel_program_fields_inv sg state **
     (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv; entailer!. }
  destruct (Hsplit before Hpre) as [Hcoverage Hheap].
  destruct (sem_pend_event_allocate_fields_source sg state before _ Hbinding Hheap)
    as [result [allocated [after [Hread [Hstep [Hrun Hpost]]]]]].
  assert (Hsource : exists cut, mutex_del_creator_heap_step sg KernelClientHeapClosed before cut after).
  { destruct result as [[eid image]|].
    - destruct Hrun as [Hnonzero [next [Hnext Hwrite]]].
      exists (KernelClientHeapExtra (event_pool_addr sg eid)); econstructor; eassumption.
    - subst after; exists KernelClientHeapClosed; constructor; assumption. }
  destruct Hsource as [cut Hsource].
  destruct (sem_pend_allocation_fields_extra_resources external platform port abi local sg
    KernelClientHeapClosed before cut after state frame Hsource Hpre) as [returned [Heffect Hafter]].
  pose proof (sem_pend_allocation_fields_source_facts external platform port abi local sg
    KernelClientHeapClosed state before frame Hpre) as Hfacts.
  destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer KernelClientHeapClosed
    state cut returned origin Hforeign I (KernelClientHeapExtraState _ _ _ _ _ _ Heffect) Hfacts)
    as [_ Hreceipt].
  exists cut, after, returned; repeat split; assumption.
Qed.

Lemma sem_pend_allocation_fields_trace_receipt_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local actor sg observer cut before next after (frame : Assertion),
  actor <> Some observer ->
  kernel_client_heap_trace mutex_del_creator_heap_step sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (sem_pend_allocation_fields_resources abi local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace mutex_del_creator_heap_effect sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port (mutex_del_allocation_source_client actor)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (mutex_del_allocation_source_client actor)
        sg observer None origin state false origin returned trace) /\
    kernel_client_heap_observer_cut observer next /\
    (sem_pend_allocation_fields_resources abi local sg next returned ** frame) after.
Proof.
  intros external platform port abi local actor sg observer cut before next after frame Hforeign Htrace.
  induction Htrace; intros state origin Hobserver Hpre.
  - exists state; split; [constructor|]. split.
    + exists (@KernelClientTaskSourceNil external port (mutex_del_allocation_source_client actor)
        sg observer None origin state); constructor.
    + split; assumption.
  - pose proof (sem_pend_allocation_fields_source_facts external platform port abi local sg
      cut state before frame Hpre) as Hfacts.
    destruct (sem_pend_allocation_fields_resource_guarantee external platform port abi local sg
      cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer cut state
      middle_cut middle_state origin Hforeign Hobserver Hstep Hfacts) as [Hmiddle_observer [head Hhead]].
    destruct (IHHtrace middle_state origin Hmiddle_observer Hmiddle)
      as [returned [Htail [[tail Htail_receipt] [Hfinal Hpost]]]].
    exists returned; split; [econstructor; eassumption|]. split; [|split; assumption].
    exact (sem_pend_dispatch_client_receipt_append external port
      (mutex_del_allocation_source_client actor) sg observer None origin state false origin middle_state
      head Hhead false origin returned tail Htail_receipt).
Qed.
