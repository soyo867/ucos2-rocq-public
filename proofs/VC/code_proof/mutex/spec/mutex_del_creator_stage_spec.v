Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_type_loan_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_slot_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_call_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual creator, not Del, is interrupted here. Its ECB remains a
    separate pending-client owner. Register save consumes its running
    permission; the real counter/SP stores park its physical frame and
    add exactly one capsule to the WHOLE existing map. Other dormant
    callers, including an earlier Del, retain their existing ABI entries.

    These are the first-level running-task source conditions of the
    adopted entry producer, not a classification of nested/Boot IRQs. *)
Lemma mutex_del_creator_irq_save_deposit : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry pointer node handler saved publication (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  (os_int_exit_frame_save_pre external platform handler **
    (mutex_del_creator_heap_resources abi sg pointer entry ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists final,
    saved.(armv7a_continuation_call) = Some call /\
    saved.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp)) saved_heap final /\
    (mutex_del_creator_heap_resources abi sg pointer
       (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
         saved.(armv7a_continuation_fragments)) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry pointer node handler saved publication frame before saved_heap
    call Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication
    Hsp Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler saved before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hmask [Hpc [Hsavedsp Hfragments]]]]]].
  destruct (armv7a_save_transition_resources _ _ _ abi handler saved call _ before saved_heap
    Hcall eq_refl Hbinding Hmask Hpc Hsavedsp Hfragments Hpre Hsave) as [Hwrites Hsaved].
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  change (call.(os_sched_call_stack) = saved.(armv7a_continuation_stack)) in Hstack.
  assert (Hopen :
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi saved **
    (mutex_del_creator_heap_resources abi sg pointer entry ** frame) |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        entry.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) &&
      ((UCOS2_inv sg entry ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments)) **
       (armv7a_dormant_continuation abi saved **
        armv7a_task_continuations abi entry.(TskState).(parkedTaskStacks) **
        unmap_table_rep sg ** event_private_storage_rep sg eid allocation **
        interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** frame))).
  { unfold mutex_del_creator_heap_resources; Intros eid allocation; Exists eid allocation.
    unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap, Hstack; entailer!. }
  destruct (Hopen saved_heap Hsaved) as [eid [allocation [[Hpointer Hget]
    [owned [rest [Hjoin [Howned Hrest]]]]]]].
  destruct (armv7a_irq_live_entry_parks_stack sg entry node saved.(armv7a_continuation_sp)
    call saved.(armv7a_continuation_fragments) publication owned Hrunning Hnesting Hcurrent
    Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Howned)
    as [updated [Hrun Hupdated]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  assert (Hcapsule : armv7a_dormant_continuation abi saved |--
    armv7a_task_continuation_entry abi (task_stack_key saved.(armv7a_continuation_stack))
      (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { pose proof (armv7a_task_continuation_entry_resources _ _ _ abi saved Hbinding) as Hentry_resource.
    unfold armv7a_task_continuation_resource in Hentry_resource; rewrite Hcall in Hentry_resource.
    exact Hentry_resource. }
  assert (Hpark : UCOS2_inv sg
      (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
        saved.(armv7a_continuation_fragments)) **
    (armv7a_dormant_continuation abi saved **
     armv7a_task_continuations abi entry.(TskState).(parkedTaskStacks) **
     unmap_table_rep sg ** event_private_storage_rep sg eid allocation **
     interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame) |--
    mutex_del_creator_heap_resources abi sg pointer
      (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
        saved.(armv7a_continuation_fragments)) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)).
  { sep_apply_l_atomic Hcapsule; rewrite <- Hstack.
    unfold armv7a_task_continuations.
    sep_apply_l_atomic (store_parked_continuations_park (armv7a_task_continuation_entry abi)
      entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      saved.(armv7a_continuation_fragments) Hnone).
    unfold mutex_del_creator_heap_resources; Exists eid allocation.
    unfold kernel_client_heap_world; rewrite kernel_program_inv_split_unmap.
    unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, os_sched_save_current_sp,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    cbn [replace_TskS replace_IntrS TskState EventState glob_task_set_parked_stacks parkedTaskStacks].
    rewrite Hnode; cbn [replace_TskS EventState TskState glob_task_set_usedtask parkedTaskStacks]; entailer!. }
  exists final; split; [exact Hcall|]. split; [exact Hpc|]. split; [exact Hwrites|].
  split; [exact Hwhole|]. apply (Hpark final).
  exists updated, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** A pending ECB can accompany any REGISTERED source cut. This is not a
    new global invariant and does not obtain bytes from a Closed world.
    The extra resource is supplied by free-pop and remains physically
    separate on the SAME heap at each cut. *)
Definition mutex_del_creator_carried_resources {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port) extra_resources
  sg pointer (cut : KernelClientHeapCut Extra) state : Assertion :=
  EX eid allocation,
    coq_prop (pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) &&
    (kernel_client_heap_resources abi extra_resources sg cut state **
     event_private_storage_rep sg eid allocation).

(** The three built-in real source clients leave EventState untouched.
    An additional client must prove its own lookup transport for this
    observer; this is an internal OS-client obligation, not a CPU/BSP law.
    Creator field writes use the separate adopted image-update producer
    instead of satisfying a false unchanged-allocation condition. *)
Lemma mutex_del_creator_client_lookup : forall Extra extra_effect sg cut state next returned,
  (forall cut state next returned eid allocation,
    UCOS2_state_inv sg state ->
    extra_effect sg cut state next returned ->
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) ->
  UCOS2_state_inv sg state ->
  @kernel_client_heap_state_step Extra extra_effect sg cut state next returned ->
  forall eid allocation,
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation.
Proof.
  intros Extra extra_effect sg cut state next returned Hextra Hvalid Hstep eid allocation Hget.
  destruct Hstep.
  - exact Hget.
  - exact Hget.
  - exact Hget.
  - eapply Hextra; eassumption.
Qed.

Lemma mutex_del_creator_registered_step : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources extra_step extra_effect,
  @kernel_client_heap_extension_valid external platform port Extra abi extra_resources extra_step extra_effect ->
  (forall sg cut state, kernel_client_heap_resources abi extra_resources sg cut state |--
    coq_prop (UCOS2_state_inv sg state)) ->
  (forall sg cut state next returned eid allocation,
    UCOS2_state_inv sg state ->
    extra_effect sg cut state next returned ->
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) ->
  forall sg pointer cut state before next after (frame : Assertion),
  kernel_client_heap_step extra_step sg cut before next after ->
  (mutex_del_creator_carried_resources abi extra_resources sg pointer cut state ** frame) before ->
  exists returned, kernel_client_heap_state_step extra_effect sg cut state next returned /\
    (forall eid allocation, state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
      returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) /\
    (mutex_del_creator_carried_resources abi extra_resources sg pointer next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources extra_step extra_effect Hextension Hcut_valid Hlookup
    sg pointer cut state before next after frame Hsource Hpre.
  assert (Hopen : mutex_del_creator_carried_resources abi extra_resources sg pointer cut state ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) &&
      (kernel_client_heap_resources abi extra_resources sg cut state **
       (event_private_storage_rep sg eid allocation ** frame))).
  { unfold mutex_del_creator_carried_resources; Intros eid allocation; Exists eid allocation; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer Hget] Howned]]].
  assert (Hvalid : UCOS2_state_inv sg state).
  { destruct Howned as [owned [rest [_ [Howned _]]]].
    exact (Hcut_valid sg cut state owned Howned). }
  destruct (kernel_client_heap_step_resources external platform port Extra abi extra_resources extra_step
    extra_effect Hextension sg cut before next after state _ Hsource Howned)
    as [returned [Hstep Hreturned]].
  pose proof (mutex_del_creator_client_lookup Extra extra_effect sg cut state next returned
    (Hlookup sg) Hvalid Hstep eid allocation Hget) as Hget_returned.
  exists returned; split; [exact Hstep|]. split.
  - exact (mutex_del_creator_client_lookup Extra extra_effect sg cut state next returned
      (Hlookup sg) Hvalid Hstep).
  -
  assert (Hclose : kernel_client_heap_resources abi extra_resources sg next returned **
      (event_private_storage_rep sg eid allocation ** frame) |--
    mutex_del_creator_carried_resources abi extra_resources sg pointer next returned ** frame).
  { unfold mutex_del_creator_carried_resources; Exists eid allocation; entailer!. }
  exact (Hclose after Hreturned).
Qed.

Lemma mutex_del_creator_registered_trace : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources extra_step extra_effect,
  @kernel_client_heap_extension_valid external platform port Extra abi extra_resources extra_step extra_effect ->
  (forall sg cut state, kernel_client_heap_resources abi extra_resources sg cut state |--
    coq_prop (UCOS2_state_inv sg state)) ->
  (forall sg cut state next returned eid allocation,
    UCOS2_state_inv sg state ->
    extra_effect sg cut state next returned ->
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) ->
  forall sg pointer cut before next after (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after -> forall state,
  (mutex_del_creator_carried_resources abi extra_resources sg pointer cut state ** frame) before ->
  exists returned, kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    (forall eid allocation, state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
      returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) /\
    (mutex_del_creator_carried_resources abi extra_resources sg pointer next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources extra_step extra_effect Hextension Hcut_valid Hlookup
    sg pointer cut before next after frame Hsource; induction Hsource; intros state Hpre.
  - exists state; split; [constructor|]. split; [auto|exact Hpre].
  - destruct (mutex_del_creator_registered_step external platform port Extra abi extra_resources
      extra_step extra_effect Hextension Hcut_valid Hlookup sg pointer cut state before middle_cut middle frame H Hpre)
      as [middle_state [Hstep [Hlookup_middle Hmiddle]]].
    destruct (IHHsource middle_state Hmiddle) as [returned [Htail [Hlookup_returned Hreturned]]].
    exists returned; split; [econstructor; eassumption|].
    split; [intros; apply Hlookup_returned, Hlookup_middle; assumption|exact Hreturned].
Qed.

(** Concrete instantiation includes real Event allocation. A second
    allocation does not replace an already-pending creator. *)
Lemma mutex_del_registered_cut_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg cut state,
  kernel_client_heap_resources abi (mutex_del_creator_heap_resources abi) sg cut state |--
    coq_prop (UCOS2_state_inv sg state).
Proof.
  intros external platform port abi sg cut state; destruct cut;
    cbn [kernel_client_heap_resources].
  - unfold kernel_client_heap_world, kernel_program_inv; entailer!.
  - unfold kernel_client_heap_publication; entailer!.
  - unfold mutex_del_creator_heap_resources; Intros eid allocation.
    unfold kernel_client_heap_world, kernel_program_inv; entailer!.
Qed.

Lemma mutex_del_allocate_keeps_existing_private : forall sg state result returned eid allocation,
  UCOS2_state_inv sg state -> event_create_allocate_critical state result returned ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation.
Proof.
  intros sg state result returned eid allocation Hvalid Hstep Hget.
  unfold event_create_allocate_critical in Hstep.
  destruct state.(EventState).(unUsedEventStates) as [|head tail] eqn:Hfree.
  - destruct Hstep as [_ ->]; exact Hget.
  - destruct Hstep as [image [_ [_ ->]]].
    pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
    destruct (event_pool_free_unallocated sg state.(EventState) head Hpool
      ltac:(rewrite Hfree; left; reflexivity)) as [_ Hnone].
    assert (Hdifferent : eid <> head) by congruence.
    cbn [replace_EventS EventState event_detach_head eventLifecycle eventPrivate].
    unfold kernel_map_set; destruct (Z.eq_dec eid head); [contradiction|exact Hget].
Qed.

Lemma mutex_del_creator_extension_lookup : forall sg cut state next returned eid allocation,
  UCOS2_state_inv sg state -> mutex_del_creator_heap_effect sg cut state next returned ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation.
Proof.
  intros sg cut state next returned eid allocation Hvalid Hstep Hget.
  destruct Hstep; eapply mutex_del_allocate_keeps_existing_private; eassumption.
Qed.

(** Closed is only the CURRENT client cut. The pending creator remains
    owned alongside it. The concrete registry includes real free-pop,
    Task publication and both counter clients; it is not a classification
    theorem for all code that a BSP or another task might execute. *)
Lemma mutex_del_creator_registered_type : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg pointer state before after observed (frame : Assertion),
  kernel_client_heap_trace mutex_del_creator_heap_step sg
    KernelClientHeapClosed before KernelClientHeapClosed after ->
  (pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer state observed ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace mutex_del_creator_heap_effect sg
      KernelClientHeapClosed state KernelClientHeapClosed returned /\
    (pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer returned observed ** frame) after.
Proof.
  intros external platform port abi sg pointer state before after observed frame Hsource Hpre.
  assert (Hopen : pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer state observed ** frame |--
    EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\
        state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateStorage) EventTypeField = Some observed) &&
      (mutex_del_creator_carried_resources abi (mutex_del_creator_heap_resources abi) sg pointer
        KernelClientHeapClosed state ** frame)).
  { unfold mutex_del_creator_type_residual; Intros eid allocation.
    assert (Hbindings : pointer = event_pool_addr sg eid /\
      state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateStorage) EventTypeField = Some observed) by tauto.
    destruct Hbindings as [Hpointer [Hget Htype]].
    rewrite Hpointer; sep_apply_l_atomic (event_private_storage_rep_merge_type sg eid allocation observed Htype).
    Exists eid allocation; unfold mutex_del_creator_carried_resources; Exists eid allocation.
    cbn [kernel_client_heap_resources]; entailer!. }
  destruct (Hopen before Hpre) as [eid [allocation [[Hpointer [Hget Htype]] Howned]]].
  destruct (mutex_del_creator_registered_trace external platform port Z abi
    (mutex_del_creator_heap_resources abi) mutex_del_creator_heap_step mutex_del_creator_heap_effect
    (mutex_del_creator_heap_extension_valid external platform port abi)
    (mutex_del_registered_cut_valid external platform port abi) mutex_del_creator_extension_lookup
    sg pointer KernelClientHeapClosed before KernelClientHeapClosed after frame Hsource state Howned)
    as [returned [Hlogical [Hlookup Hreturned]]].
  exists returned; split; [exact Hlogical|].
  assert (Hclose : mutex_del_creator_carried_resources abi (mutex_del_creator_heap_resources abi)
      sg pointer KernelClientHeapClosed returned ** frame |--
    pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer returned observed ** frame).
  { change (mutex_del_creator_heap_resources abi sg pointer returned ** frame |--
      pointer # UChar |-> observed ** mutex_del_creator_type_residual abi sg pointer returned observed ** frame).
    sep_apply_l_atomic (mutex_del_creator_heap_resources_split_type external platform port abi sg pointer
      returned eid allocation observed Hpointer (Hlookup eid allocation Hget) Htype); entailer!. }
  exact (Hclose after Hreturned).
Qed.

(** Exactly the first-level physical entry obligations of the adopted
    producer. There is deliberately no ready-list or later-exit promise. *)
Definition mutex_del_creator_irq_input sg state handler saved node publication : Prop :=
  let call := handler.(os_int_exit_interrupted_call) in
  state.(SchedState).(isRunning) = true /\ state.(IntrState).(intNesting) = 0 /\
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) /\
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) /\
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) /\
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) /\
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) /\
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) saved.(armv7a_continuation_sp).

(** Concrete missing release cut: creator's DSB/MSR, then actual IRQ
    register save and counter/SP writes, on joined endpoints. Its private
    ECB is retained only through these actual steps. The linked +8 is the
    supplied interrupted-PC binding at BX, not an invented deployment
    address, and this theorem does not execute the still-pending BX. *)
Lemma mutex_del_creator_release_irq_deposit : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg call saved_mask acquired state pointer handler saved node publication restore_entry
  cursor before written_cursor released saved_heap (frame : Assertion),
  cursor.(kernel_restore_r0) = saved_mask ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  handler.(os_int_exit_interrupted_call) = call ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved_mask ->
  handler.(os_int_exit_interrupted_pc) = restore_entry + 8 ->
  mutex_del_creator_irq_input sg state handler saved node publication ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved_mask acquired **
    os_sched_context_resources external call ** mutex_del_creator_heap_resources abi sg pointer state **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor released ->
  armv7a_save_transition abi handler saved released saved_heap ->
  exists handler_heap,
    written_cursor = kernel_restore_write_cpsr cursor /\
    saved.(armv7a_continuation_call) = Some call /\
    saved.(armv7a_continuation_pc) = restore_entry + 8 /\
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      released.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg state call.(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp)) saved_heap handler_heap /\
    (mutex_del_creator_heap_resources abi sg pointer
       (armv7a_irq_live_parked_state state call saved.(armv7a_continuation_sp)
         saved.(armv7a_continuation_fragments)) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) handler_heap.
Proof.
  intros external platform port critical arch abi restore sg call saved_mask acquired state pointer handler
    saved node publication restore_entry cursor before written_cursor released saved_heap frame
    Hr0 Hmask Hcall Hhandler_mask Hpc Hinput Hpre Hprefix Hsave.
  assert (Hopen : critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved_mask acquired ** os_sched_context_resources external call **
      mutex_del_creator_heap_resources abi sg pointer state **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved_mask acquired ** os_sched_context_resources external call **
      (mutex_del_creator_heap_resources abi sg pointer state **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame))
    by entailer!.
  destruct (armv7a_restore_prefix_releases_critical_region external platform critical arch restore
    sg call saved_mask acquired cursor before written_cursor released _ Hr0 Hmask (Hopen before Hpre) Hprefix)
    as [Hcursor [Hmemory Hreleased]].
  assert (Hirq : kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask saved_mask) **
      (mutex_del_creator_heap_resources abi sg pointer state **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) |--
    os_int_exit_frame_save_pre external platform handler **
      (mutex_del_creator_heap_resources abi sg pointer state ** frame)).
  { unfold os_int_exit_frame_save_pre; rewrite Hcall, Hhandler_mask; entailer!. }
  destruct Hinput as [Hrunning [Hnesting [Hcurrent [Hnode [Hid [Hgen [Hnone [Haddress
    [Hregion [Hgeometry [Hpublication Hsp]]]]]]]]]]].
  destruct (mutex_del_creator_irq_save_deposit external platform port abi sg state pointer node handler saved
    publication frame released saved_heap Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp (Hirq released Hreleased) Hsave)
    as [handler_heap [Hsaved_call [Hsaved_pc [Hwrites [Hentry Hafter]]]]].
  rewrite Hcall in Hsaved_call, Hentry, Hafter; rewrite Hpc in Hsaved_pc.
  exists handler_heap; split; [exact Hcursor|]. split; [exact Hsaved_call|].
  split; [exact Hsaved_pc|]. split; [exact Hwrites|]. split; assumption.
Qed.
