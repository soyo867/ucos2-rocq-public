Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_pool_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_callee_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Preserve the pending call stored in the SAME parked map. Del can
    change priorities and waiter fields, but its actual critical semantics
    preserves each generation/SP pair and every dormant frame. *)
Lemma mutex_del_call_stacks_critical_reindex : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg eid option entry result checkpoint focus,
  mutex_del_critical sg eid option entry result checkpoint ->
  armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) |--
  armv7a_task_call_stacks abi checkpoint.(TskState) focus checkpoint.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg eid option entry result checkpoint focus Hrun.
  destruct (mutex_del_critical_call_fields_eq _ _ _ _ _ _ Hrun)
    as [Hnodes [Hstacks Hrest]].
  assert (Hlookup : forall slot node, checkpoint.(TskState).(inUsedTaskStates) slot = Some node ->
    exists old, entry.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode; specialize (Hnodes slot); rewrite Hnode in Hnodes.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    cbn in Hnodes; injection Hnodes as Hg Hsp; exists old; auto. }
  rewrite Hstacks; unfold armv7a_task_call_stacks, store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros key payload Hparked.
  unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec;
    [|unfold armv7a_task_stack_entry]; Intros saved.
  all: assert (Hsp : task_stack_live_sp entry.(TskState) key saved.(armv7a_continuation_sp)) by tauto.
  all: assert (Hafter : task_stack_live_sp checkpoint.(TskState) key saved.(armv7a_continuation_sp)).
  1,3: intros node Hnode Hgen;
    destruct (Hlookup (fst key) node Hnode) as [old [Hold [Hg Hvalue]]];
    rewrite <- Hvalue; apply Hsp; [exact Hold|congruence].
  all: Exists saved; entailer!.
Qed.

(** This is only a masked C-body cut. A source producer must establish
    the executing foreign task separately; in particular this rule does
    not legalize OSMutexDel inside an ISR. The whole current private pool
    and focused stack map are reconstructed before any returning call. *)
Lemma mutex_del_registry_critical_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload entry checkpoint eid option result,
  mutex_del_critical sg eid option entry result checkpoint ->
  coq_prop (mutex_program_selected_reachable sg entry /\
    mutex_del_private_types_non_mutex entry.(EventState) /\
    kernel_client_call_stack_facts focus payload entry) &&
  (kernel_program_inv sg checkpoint **
    armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
    event_private_pool_rep sg entry.(EventState)) |--
  mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed checkpoint.
Proof.
  intros external platform port abi sg focus payload entry checkpoint eid option result Hrun.
  Intros_p Hfacts; destruct Hfacts as [Hhistory [Htypes [Hcoverage Hfocus]]].
  destruct (mutex_del_critical_call_fields_eq _ _ _ _ _ _ Hrun)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  assert (Hcoverage' : task_stack_live_coverage checkpoint.(TskState) None).
  { eapply task_stack_live_coverage_used_map_frame; [|exact Hstacks|exact Hcoverage].
    intros slot node Hnode; specialize (Hnodes slot); rewrite Hnode in Hnodes.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    cbn in Hnodes; injection Hnodes as Hg Hsp; exists old; auto. }
  assert (Hhistory' : mutex_program_selected_reachable sg checkpoint).
  { eapply mutex_program_source_history_reachable; [exact Hhistory|].
    eapply mutex_program_del_critical_source; exact Hrun. }
  assert (Htypes' : mutex_del_private_types_non_mutex checkpoint.(EventState)).
  { unfold mutex_del_private_types_non_mutex in *; rewrite Hprivate; exact Htypes. }
  sep_apply_l_atomic (mutex_del_call_stacks_critical_reindex external platform port abi sg eid option
    entry result checkpoint focus Hrun).
  unfold mutex_del_stack_registry, kernel_client_call_stack_resources,
    kernel_client_call_stack_world, kernel_client_call_stack_facts, event_private_pool_rep.
  rewrite Hprivate; entailer!; rewrite Hstacks; exact Hfocus.
Qed.

(** Actual owner adjustment, all wake iterations, the second PCP-table
    clear and the four recycle writes update this physical registry. The
    event state after deletion is derived from the same heap execution. *)
Lemma mutex_del_registry_always_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload eid entry prepared event mutex
  before prepared_heap after (frame : Assertion),
  mutex_del_parent_layout sg -> valid_event_id sg eid ->
  mutex_del_parent_entry sg eid entry event mutex ->
  (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed entry ** frame) before ->
  mutex_del_prepare_source_execution sg (event_addr sg eid) eid entry prepared before prepared_heap ->
  mutex_del_always_after_prepare_execution sg (event_addr sg eid) prepared_heap after ->
  let checkpoint := mutex_del_always_checkpoint sg eid event prepared in
  mutex_del_critical sg eid 1 entry
    (0, (OS_ERR_NONE, negb (Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0))) checkpoint /\
  mutex_owner_source_history sg entry checkpoint /\
  (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed checkpoint ** frame) after.
Proof.
  intros external platform port abi sg focus payload eid entry prepared event mutex before prepared_heap after
    frame Hlayout Hid Hparent Hpre Hprepare Hbody checkpoint.
  assert (Hopen : mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed entry ** frame |--
    coq_prop (mutex_program_selected_reachable sg entry /\
      mutex_del_private_types_non_mutex entry.(EventState) /\
      kernel_client_call_stack_facts focus payload entry) &&
    (kernel_program_inv sg entry **
      (armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
       event_private_pool_rep sg entry.(EventState) ** frame))).
  { unfold mutex_del_stack_registry, kernel_client_call_stack_resources, kernel_client_call_stack_world;
      entailer!. }
  destruct (Hopen before Hpre) as [Hfacts Howned].
  pose proof (mutex_del_prepare_source_resources sg eid entry prepared event mutex before prepared_heap
    _ Hlayout Hparent Howned Hprepare) as Hprepared.
  destruct (mutex_del_always_after_prepare_resources sg eid entry prepared event mutex prepared_heap after _
    (event_table_layout_select sg eid (proj1 (proj2 Hlayout)) Hid) Hprepared Hbody) as [Hcritical Hafter].
  split; [exact Hcritical|]. split; [eapply mutex_program_del_critical_source; exact Hcritical|].
  assert (Hmerge : kernel_program_inv sg checkpoint **
      armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
      event_private_pool_rep sg entry.(EventState) |--
    mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed checkpoint).
  { intros heap Hheap; apply (mutex_del_registry_critical_merge external platform port abi sg focus payload
      entry checkpoint eid 1 _ Hcritical); split; assumption. }
  match type of Hafter with ?P after =>
    assert (Hclose : P |-- mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed checkpoint ** frame)
  end.
  { apply derivable1_trans with (y := (kernel_program_inv sg checkpoint **
      armv7a_task_call_stacks abi entry.(TskState) focus entry.(TskState).(parkedTaskStacks) **
      event_private_pool_rep sg entry.(EventState)) ** frame).
    - unfold checkpoint; entailer!.
    - sep_apply_l_atomic Hmerge; entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma mutex_del_creator_trace_owner_history : forall creator sg cut state next returned,
  kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  mutex_owner_source_history sg state returned.
Proof.
  intros creator sg cut state next returned Htrace; induction Htrace.
  - constructor.
  - eapply mutex_owner_source_history_trans; [|exact IHHtrace].
    apply mutex_owner_source_step_history; eapply mutex_del_creator_interrupt_state_source; exact H.
Qed.

Lemma mutex_del_creator_step_preserves_non_mutex_slot : forall creator sg eid cut state next returned,
  (forall event, state.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) <> OS_EVENT_TYPE_MUTEX) ->
  kernel_client_heap_state_step (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  forall event, returned.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) <> OS_EVENT_TYPE_MUTEX.
Proof.
  intros creator sg eid cut state next returned Hnonmutex Hstep; destruct Hstep;
    try exact Hnonmutex.
  destruct H; try exact Hnonmutex.
  destruct H.
  - destruct H; unfold event_create_allocate_critical in H;
      destruct (state.(EventState).(unUsedEventStates)) as [|head rest].
    all: try solve [destruct H as [_ ->]; exact Hnonmutex].
    all: destruct H as [image' [_ [_ ->]]]; exact Hnonmutex.
  - intros event Hget.
    cbn [mutex_del_creator_published_state replace_EventS EventState event_publish inUsedEventStates] in Hget.
    unfold kernel_map_set in Hget; destruct (Z.eq_dec eid eid0).
    + injection Hget as <-; destruct creator; discriminate.
    + rewrite (proj1 (event_create_private_stores_published_frame _ _ _ _ _ H1)) in Hget.
      exact (Hnonmutex event Hget).
Qed.

Lemma mutex_del_creator_trace_preserves_non_mutex_slot : forall creator sg eid cut state next returned,
  kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  (forall event, state.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) <> OS_EVENT_TYPE_MUTEX) ->
  forall event, returned.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) <> OS_EVENT_TYPE_MUTEX.
Proof.
  intros creator sg eid cut state next returned Htrace; induction Htrace; intro Hnonmutex.
  - exact Hnonmutex.
  - apply IHHtrace; eapply mutex_del_creator_step_preserves_non_mutex_slot; eassumption.
Qed.

Lemma mutex_del_non_mutex_slot_type_load : forall sg state eid before (frame : Assertion),
  valid_event_id sg eid -> mutex_del_private_types_non_mutex state.(EventState) ->
  (forall event, state.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) <> OS_EVENT_TYPE_MUTEX) ->
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists kind, uchar_load (event_addr sg eid) kind before /\
    mutex_del_runtime_type_observation sg eid state kind /\ kind <> 4.
Proof.
  intros sg state eid before frame Hid Htypes Hnonmutex Hpre.
  assert (Hopen : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame))
    by (unfold kernel_program_inv; entailer!).
  destruct (Hopen before Hpre) as [Hvalid Howned].
  destruct (mutex_del_runtime_slot_cases sg state eid Hvalid Hid)
    as [[event Hpublic]|[allocation Hprivate]].
  - assert (Hsplit : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame |--
      event_addr sg eid # UChar |-> event_slot_type_value state.(EventState) eid **
      (mutex_del_runtime_pool_type_frame sg eid state (event_slot_type_value state.(EventState) eid) ** frame)).
    { sep_apply_l_atomic (mutex_del_runtime_type_public_split sg state eid event Hpublic); entailer!. }
    exists (event_slot_type_value state.(EventState) eid); split.
    + eapply framed_uchar_store_load; exact (Hsplit before Hpre).
    + split; [left; exists event; auto|].
      unfold event_slot_type_value; destruct (state.(EventState).(inUsedEventStates) eid) as [found|] eqn:Hget;
        [|lia].
      specialize (Hnonmutex found eq_refl); destruct found.(eventType); cbn; congruence.
  - destruct (Htypes eid allocation Hprivate) as [kind [Htype Hnot]].
    assert (Hsplit : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) ** frame |--
      event_addr sg eid # UChar |-> kind ** (mutex_del_runtime_pool_type_frame sg eid state kind ** frame)).
    { sep_apply_l_atomic (mutex_del_runtime_type_private_split sg state eid allocation kind Hprivate Htype Hnot);
        entailer!. }
    exists kind; split; [eapply framed_uchar_store_load; exact (Hsplit before Hpre)|].
    split; [right; exists allocation; auto|exact Hnot].
Qed.

Lemma mutex_del_creator_trace_preserves_return_cut : forall creator sg cut state next returned,
  kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg cut state next returned ->
  (match cut with KernelClientHeapTaskPublication _ => False | _ => True end) ->
  match next with KernelClientHeapTaskPublication _ => False | _ => True end.
Proof.
  intros creator sg cut state next returned Htrace; induction Htrace; intro Hcut; [exact Hcut|].
  apply IHHtrace; destruct H; cbn in *; try exact I; try contradiction.
  destruct H; cbn; try exact I.
  destruct H; cbn; try exact I.
  destruct H; exact I.
Qed.

(** Forgetting a creator's pure cursor retains its allocation in the
    whole current private pool. Its bytes and the interrupted call's
    dormant frame are preserved at the final return cut. *)
Lemma mutex_del_registry_non_mutex_type_load : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload cut state eid before (frame : Assertion),
  valid_event_id sg eid ->
  (match cut with KernelClientHeapTaskPublication _ => False | _ => True end) ->
  (forall event, state.(EventState).(inUsedEventStates) eid = Some event ->
    event.(eventType) <> OS_EVENT_TYPE_MUTEX) ->
  (mutex_del_stack_registry abi sg focus payload cut state ** frame) before ->
  exists kind, uchar_load (event_addr sg eid) kind before /\
    mutex_del_runtime_type_observation sg eid state kind /\ kind <> 4 /\
    (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state ** frame) before.
Proof.
  intros external platform port abi sg focus payload cut state eid before frame Hid Hcut Hnonmutex Hpre.
  assert (Hclosed : (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state ** frame) before).
  { assert (Hclose : mutex_del_stack_registry abi sg focus payload cut state ** frame |--
      mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state ** frame).
    { destruct cut; [reflexivity|contradiction|].
      unfold mutex_del_stack_registry, kernel_client_call_stack_resources, mutex_del_creator_pool_cursor.
      Intros slot allocation; entailer!. }
    exact (Hclose before Hpre). }
  assert (Hopen : mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed state ** frame |--
    coq_prop (mutex_del_private_types_non_mutex state.(EventState)) &&
    (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) **
     (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold mutex_del_stack_registry, kernel_client_call_stack_resources, kernel_client_call_stack_world;
      entailer!. }
  destruct (Hopen before Hclosed) as [Htypes Howned].
  destruct (mutex_del_non_mutex_slot_type_load sg state eid before _ Hid Htypes Hnonmutex Howned)
    as [kind [Hload [Hobservation Hkind]]].
  exists kind; split; [exact Hload|]. split; [exact Hobservation|]. split; assumption.
Qed.

(** The allocator/initializer starts on the heap produced by deletion.
    This allows the free-list head just written by Del to be popped and
    reused. Both the physical trace and the owner-history projection refer
    to that one sequence. Foreign execution ownership and the final
    selected return remain the surrounding producer's responsibility. *)
Lemma mutex_del_registry_recycle_creator_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients actor creator sg observer origin
  focus payload eid entry prepared event mutex before prepared_heap recycled next after (frame : Assertion),
  mutex_del_parent_layout sg -> valid_event_id sg eid ->
  mutex_del_parent_entry sg eid entry event mutex ->
  (forall action, mutex_del_creator_source_client actor creator action -> clients action) ->
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed entry ** frame) before ->
  mutex_del_prepare_source_execution sg (event_addr sg eid) eid entry prepared before prepared_heap ->
  mutex_del_always_after_prepare_execution sg (event_addr sg eid) prepared_heap recycled ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg
    KernelClientHeapClosed recycled next after ->
  exists returned returned_origin kind,
    mutex_owner_source_history sg entry returned /\
    (forall current, returned.(EventState).(inUsedEventStates) eid = Some current ->
      current.(eventType) <> OS_EVENT_TYPE_MUTEX) /\
    kernel_client_heap_state_trace (mutex_del_creator_interrupt_effect creator) sg
      KernelClientHeapClosed (mutex_del_always_checkpoint sg eid event prepared) next returned /\
    kernel_resumption_task_source_trace external port clients sg observer None origin
      (mutex_del_always_checkpoint sg eid event prepared) false returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    uchar_load (event_addr sg eid) kind after /\
    mutex_del_runtime_type_observation sg eid returned kind /\ kind <> 4 /\
    (mutex_del_stack_registry abi sg focus payload KernelClientHeapClosed returned ** frame) after.
Proof.
  intros external platform port abi clients actor creator sg observer origin focus payload eid entry prepared
    event mutex before prepared_heap recycled next after frame Hlayout Hid Hparent Hinclude Hforeign Hargs
    Hpre Hprepare Hrecycle Hcreator.
  destruct (mutex_del_registry_always_resources external platform port abi sg focus payload eid entry
    prepared event mutex before prepared_heap recycled frame Hlayout Hid Hparent Hpre Hprepare Hrecycle)
    as [Hcritical [Hhistory Hrecycled]].
  destruct (mutex_del_stack_creator_trace external platform port abi clients actor creator sg observer focus
    payload KernelClientHeapClosed recycled next after frame Hinclude Hforeign Hargs Hcreator
    (mutex_del_always_checkpoint sg eid event prepared) origin I Hrecycled)
    as [returned [returned_origin [Hstates [Hsource [Hcut Hafter]]]]].
  assert (Hnonmutex : forall current, returned.(EventState).(inUsedEventStates) eid = Some current ->
    current.(eventType) <> OS_EVENT_TYPE_MUTEX).
  { eapply mutex_del_creator_trace_preserves_non_mutex_slot; [exact Hstates|].
    intros current Hget.
    cbn [mutex_del_always_checkpoint mutex_del_recycle_state replace_EventS EventState event_recycle
      inUsedEventStates] in Hget; rewrite kernel_map_set_same in Hget; discriminate. }
  destruct (mutex_del_registry_non_mutex_type_load external platform port abi sg focus payload next returned eid
    after frame Hid (mutex_del_creator_trace_preserves_return_cut creator sg _ _ _ _ Hstates I)
    Hnonmutex Hafter) as [kind [Hload [Hobs [Hkind Hclosed]]]].
  exists returned, returned_origin, kind; split.
  - eapply mutex_owner_source_history_trans; [exact Hhistory|].
    eapply mutex_del_creator_trace_owner_history; exact Hstates.
  - split; [exact Hnonmutex|]. split; [exact Hstates|]. split; [exact Hsource|].
    split; [exact Hcut|]. split; [exact Hload|]. split; [exact Hobs|]. split; assumption.
Qed.

Section RecheckErrorReturn.
Context (environment : MutexDelCallEnvironment) (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) =>
      mutex_del_restore_handler_owner environment.(mutex_del_call_platform)
        environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

(** The actual protected Type load consumes the Save Ensure of the C
    carrier. It can read a public recycled/reused slot or an initialized
    private slot. The same byte is returned to its current owner before
    Restore; the old pre-Save event image is never used for this read. *)
Lemma mutex_del_recheck_error_source_post : forall critical arch
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  original mask saved initial pe eid option kind perr old_error cpu_sr before (frame : Assertion),
  pe = event_addr sg eid -> valid_event_id sg eid ->
  mutex_del_parent_prefix_ok pe initial eid ->
  (mutex_del_source_save_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) critical sg original mask saved initial **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  uchar_load (pe + OSEventType_off) kind before -> kind <> 4 ->
  exists acquired actual,
    mutex_del_runtime_type_observation sg eid acquired kind /\
    mutex_del_runtime_save_facts sg mask saved initial acquired /\
    kernel_stack_call_same_call actual original /\
    (forall restore_entry cursor written released returned final resumed final_cursor restored after,
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor before written released ->
      mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
        environment.(mutex_del_call_continuations) sg Local local_step normal_return
        handler_stack handler_fragments (armv7a_irq_fiq_mask saved) (restore_entry + 8)
        cursor.(kernel_restore_lr) actual acquired released returned final resumed ->
      armv7a_restore_suffix_transition restore written resumed final_cursor restored ->
      kernel_heap_execution [(perr, encode_os_err_code OS_ERR_EVENT_TYPE)] restored after ->
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (mutex_del_runtime_post environment environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) sg original mask initial pe option eid pe
         (encode_os_err_code OS_ERR_EVENT_TYPE) **
       (perr # UChar |-> encode_os_err_code OS_ERR_EVENT_TYPE) ** (cpu_sr # UInt |-> saved) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame) after).
Proof.
  intros critical arch restore original mask saved initial pe eid option kind perr old_error cpu_sr before frame
    Hpointer Hid Hprefix Hpre Hread Hnot.
  assert (Hopen : mutex_del_source_save_post environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical sg original mask saved initial **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    EX acquired,
      coq_prop (mutex_del_call_stage original acquired /\
        mutex_del_runtime_save_facts sg mask saved initial acquired) &&
      (kernel_program_inv sg acquired **
       mutex_del_runtime_acquired environment environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) sg original acquired **
       (critical_region_masked environment.(mutex_del_call_platform) critical sg
          original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
        (perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved) **
        task_stack_fragments_rep handler_stack handler_fragments ** frame))).
  { unfold mutex_del_source_save_post; Intros acquired; Exists acquired; entailer!. }
  destruct (Hopen before Hpre) as [acquired [[Hstage Hfacts] Howned]].
  set (rest := critical_region_masked environment.(mutex_del_call_platform) critical sg
    original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Hsplit : kernel_program_inv sg acquired **
      mutex_del_runtime_acquired environment environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) sg original acquired ** rest |--
    EX observed, event_addr sg eid # UChar |-> observed **
      (mutex_del_runtime_type_frame environment environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) sg original eid acquired observed ** rest)).
  { sep_apply_l_atomic (mutex_del_runtime_type_split environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg original eid acquired Hid); Intros observed;
      Exists observed; entailer!. }
  destruct (Hsplit before Howned) as [observed Hobserved].
  assert (Hactual : uchar_load (event_addr sg eid) observed before)
    by (eapply framed_uchar_store_load; exact Hobserved).
  rewrite Hpointer in Hread; unfold OSEventType_off in Hread; rewrite Z.add_0_r in Hread.
  assert (Ekind : observed = kind) by (eapply uchar_load_deterministic; eassumption); subst observed.
  assert (Hmerge : event_addr sg eid # UChar |-> kind **
      (mutex_del_runtime_type_frame environment environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) sg original eid acquired kind ** rest) |--
    coq_prop (mutex_del_runtime_type_observation sg eid acquired kind) &&
    (mutex_del_source_restore_pre environment environment.(mutex_del_call_external)
       environment.(mutex_del_call_platform) critical sg original mask saved acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved) ** frame)))).
  { sep_apply_l_atomic (mutex_del_runtime_type_merge environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg original eid acquired kind); Intros_p Hobs.
    unfold rest.
    assert (Hrestore : critical_region_masked environment.(mutex_del_call_platform) critical sg
        original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
        kernel_program_inv sg acquired **
        mutex_del_runtime_acquired environment environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) sg original acquired |--
      mutex_del_source_restore_pre environment environment.(mutex_del_call_external)
        environment.(mutex_del_call_platform) critical sg original mask saved acquired acquired).
    { apply derivable1_trans with (y :=
        mutex_del_runtime_program_restore_pre environment.(mutex_del_call_platform) critical sg
          original mask saved initial acquired acquired **
        mutex_del_runtime_acquired environment environment.(mutex_del_call_external)
          environment.(mutex_del_call_platform) sg original acquired).
      - unfold mutex_del_runtime_program_restore_pre; entailer!.
      - apply mutex_del_source_restore_merge; [left; reflexivity|exact Hstage]. }
    apply derivable1_trans with (y :=
      (critical_region_masked environment.(mutex_del_call_platform) critical sg
         original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
       kernel_program_inv sg acquired **
       mutex_del_runtime_acquired environment environment.(mutex_del_call_external)
         environment.(mutex_del_call_platform) sg original acquired) **
      ((perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)).
    - entailer!.
    - sep_apply_l_atomic Hrestore; entailer!. }
  destruct (Hmerge before Hobserved) as [Hobs Hrestore_pre].
  assert (Hactual_open : mutex_del_source_restore_pre environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) critical sg original mask saved acquired acquired **
      (task_stack_fragments_rep handler_stack handler_fragments **
       ((perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved) ** frame)) |--
    EX actual, coq_prop (kernel_stack_call_same_call actual original) &&
      (mutex_del_source_restore_at environment critical sg original actual mask saved acquired acquired **
       (task_stack_fragments_rep handler_stack handler_fragments **
        ((perr # UChar |-> old_error) ** (cpu_sr # UInt |-> saved) ** frame)))).
  { sep_apply_l_atomic (mutex_del_source_restore_open environment critical sg original mask saved acquired acquired).
    Intros actual; unfold mutex_del_source_restore_at; Intros_p Hfacts'; Exists actual; entailer!. }
  destruct (Hactual_open before Hrestore_pre) as [actual [Hsame Hrestore_at]].
  exists acquired, actual; split; [exact Hobs|]. split; [exact Hfacts|]. split; [exact Hsame|].
  intros restore_entry cursor written released returned final resumed final_cursor restored after
    Hr0 Hmask Hrestore_prefix Hirqs Hrestore_suffix Herror.
  destruct (mutex_del_source_restore_callee_post environment sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore original actual mask saved acquired
    acquired restore_entry cursor before written released returned final resumed final_cursor restored _
    Hr0 Hmask Hrestore_at Hrestore_prefix Hirqs Hrestore_suffix) as [Hword Hreturned].
  split; [exact Hword|].
  match type of Hreturned with ?P restored => assert (Hstore_input : P |--
    (perr # UChar |-> old_error) **
    (mutex_del_source_return environment environment.(mutex_del_call_external)
       environment.(mutex_del_call_platform) sg original mask **
     (cpu_sr # UInt |-> saved) ** task_stack_fragments_rep handler_stack handler_fragments ** frame))
    by entailer! end.
  destruct (kernel_heap_framed_uchar_store perr old_error (encode_os_err_code OS_ERR_EVENT_TYPE)
    _ restored ltac:(cbn; lia) (Hstore_input restored Hreturned)) as [produced [Hwrite Hafter]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (mutex_del_source_return_forget environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg original mask).
    sep_apply_l_atomic (mutex_del_runtime_type_error_return environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg original mask saved initial acquired pe option eid kind
      Hprefix Hfacts Hobs Hnot); entailer!. }
  exact (Hclose after Hafter).
Qed.
End RecheckErrorReturn.
