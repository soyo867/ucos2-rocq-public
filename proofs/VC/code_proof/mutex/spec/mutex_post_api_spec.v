Require Export Ucos2Verify.VC.code.mutex.spec.mutex_post_parent_spec.
Require Export Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
Require Export Ucos2Verify.lib.atomic_ops_lib.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_modular_call_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_sched_interface_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Export Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The Post guard order is ISR, NULL, Type.  Reuse the public-slot view
    used by SemPend/Del: FREE objects keep their real Type-error branch.
    The same selected handle-lifetime protocol is required only when the
    three ordered guards continue to Save, not on an early return. *)
Definition mutex_post_api_prefix (pe : Z) (state : UCOS2_Verify_State) eid : Prop :=
  mutex_post_before_save_error pe (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) = None.

Definition mutex_post_api_input critical sg invocation pe before eid observed : Prop :=
  before.(IntrState).(intNesting) > 0 \/ pe = 0 \/
  (pe = event_addr sg eid /\ valid_event_id sg eid /\
   sem_query_public_slot before eid observed /\
   (mutex_post_api_prefix pe before eid ->
    mutex_query_handle_protocol critical sg invocation eid)).

Definition mutex_post_api_call_admission call pe before eid : Prop :=
  mutex_post_api_prefix pe before eid ->
  mutex_del_task_call_stage call before /\ kernel_call_stack_available call before.

(** Only static interpretation facts are added to the old native carrier.
    In the pinned os_tcb declaration, OSTCBStkPtr is the first field. *)
Definition mutex_post_api_layout sg : Prop :=
  mutex_del_parent_layout sg.

Lemma mutex_post_api_prefix_fields : forall pe state eid,
  mutex_post_api_prefix pe state eid ->
  state.(IntrState).(intNesting) <= 0 /\ pe <> 0 /\
  event_slot_type_value state.(EventState) eid = 4.
Proof.
  intros pe state eid H; unfold mutex_post_api_prefix in H.
  apply mutex_post_before_save_continues_iff; exact H.
Qed.

(** These histories classify only the existing owner-use projection.
    Priority-table/scheduler fields are framed by that projection; they
    remain covered separately by the native C transformer and validity proof. *)
Lemma mutex_post_prepare_source : forall sg mutex owner entry prepared,
  mutex_post_prepare sg mutex owner entry prepared ->
  mutex_owner_source_history sg entry prepared.
Proof.
  intros * Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; constructor|].
  destruct Hprepare as [node [priority [Hnode [_ ->]]]].
  unfold mutex_post_owner_priority_state; destruct Z.eq_dec.
  - apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity.
  - eapply mutex_program_task_fields_source with (old := node)
      (new := mutex_priority_task node priority); try reflexivity; exact Hnode.
Qed.

Lemma mutex_post_empty_source : forall sg state eid event mutex caller,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some caller -> event.(waitList) = [] ->
  mutex_owner_source_history sg state (mutex_post_owner_state state eid event mutex None None).
Proof.
  intros * He Htype Hfields Howner Hempty.
  eapply MutexOwnerHistoryStep.
  - apply mutex_owner_source_step_history; eapply MutexOwnerSourceRelease with (eid := eid).
    unfold atomic_mutex_release.
    exists event; eexists; exists mutex; eexists; exists caller.
    do 2 eexists; repeat first [assumption | reflexivity | split].
  - apply MutexOwnerSourceFrame; reflexivity.
Qed.

Lemma mutex_post_handover_source : forall sg state eid event mutex caller priority woken found owner,
  UCOS2_state_inv sg state ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some caller ->
  encode_event_wait_grp event.(waitList) state.(TskState) <> 0 ->
  event_task_rdy sg state eid PendMutex 0 PendOK = Some (priority, woken) ->
  woken.(EventState).(inUsedEventStates) eid = Some found ->
  woken.(TskState).(prioTbl) priority = PTTask owner ->
  mutex_owner_source_history sg state
    (mutex_post_owner_state woken eid found mutex (Some owner) (Some priority)).
Proof.
  intros * Hvalid He Htype Hfields Howner Hgroup Hwake Hfound Htable.
  destruct (event_wake_decompose sg state eid event PendMutex 0 PendOK priority woken
    Hvalid He ltac:(rewrite Htype; reflexivity) Hgroup Hwake)
    as [tid [tail [old [Hlist [Hold [Hp [Ew [Hw Hlookup]]]]]]]].
  rewrite Hlookup in Hfound; injection Hfound as Efound; subst found.
  assert (Hselection : state.(TskState).(prioTbl) old.(curPrio) = PTTask tid).
  { pose proof Hvalid as [Hprofile [Htasks [_ [[_ [_ [_ [_ [_ [_ Hentries]]]]]] _]]]].
    destruct (event_wait_priority_table_entry sg state.(TskState) eid event tid tail
      (proj1 Hprofile) Htasks (Hentries eid event He) Hlist) as [node [Hnode [Hprio Hsel]]].
    rewrite Hold in Hnode; injection Hnode as E; subst node; congruence. }
  assert (Eowner : owner = tid).
  { rewrite Ew, Hp in Htable; change (state.(TskState).(prioTbl) old.(curPrio) = PTTask owner) in Htable.
    rewrite Hselection in Htable; congruence. }
  subst owner priority woken.
  eapply mutex_owner_source_history_trans.
  - apply mutex_owner_source_step_history; eapply MutexOwnerSourceHandover with (eid := eid) (tid := tid); [exact Hvalid|].
    unfold atomic_mutex_release_with_handover.
    exists event; eexists; exists mutex; eexists; exists caller, old.
    do 6 eexists; exists tail; repeat first [assumption | reflexivity | split].
  - eapply mutex_program_task_fields_source with
      (new := task_event_wake_single old PendMutex 0 PendOK).
    + cbn; rewrite Z.eqb_refl; reflexivity.
    + reflexivity.
    + reflexivity.
    + apply functional_extensionality; intros slot.
      cbn [mutex_post_owner_state replace_EventS event_wake_state replace_SchedS
        replace_TskS TskState inUsedTaskStates glob_task_set_usedtask].
      destruct (Z.eqb slot tid); reflexivity.
    + apply functional_extensionality; intros slot.
      cbn [mutex_post_owner_state replace_EventS event_wake_state replace_SchedS
        replace_TskS EventState inUsedEventStates update_event_field_raw].
      destruct (Z.eqb slot eid); reflexivity.
Qed.

Lemma mutex_post_api_input_slot : forall critical sg invocation pe before eid observed,
  mutex_post_api_input critical sg invocation pe before eid observed ->
  before.(IntrState).(intNesting) <= 0 -> pe <> 0 ->
  pe = event_addr sg eid /\ valid_event_id sg eid /\ sem_query_public_slot before eid observed.
Proof.
  intros * [Hisr|[Hnull|[Hpe [Hid [Hslot Hprotocol]]]]] Hnest Hnonnull;
    try lia; auto.
Qed.

Lemma mutex_post_api_input_live : forall critical sg invocation pe before eid observed,
  mutex_post_api_input critical sg invocation pe before eid observed ->
  mutex_post_api_prefix pe before eid ->
  mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_MUTEX /\
  mutex_query_handle_protocol critical sg invocation eid.
Proof.
  intros * Hinput Hprefix.
  destruct (mutex_post_api_prefix_fields _ _ _ Hprefix) as [Hnest [Hnonnull Htype]].
  destruct Hinput as [Hisr|[Hnull|[Hpe [Hid [Hslot Hprotocol]]]]]; try lia.
  split.
  - destruct Hslot as [Hused|[Hnone Hfree]]; [exact Hused|].
    unfold event_slot_type_value in Htype; rewrite Hnone in Htype; discriminate.
  - split; [|apply Hprotocol; exact Hprefix].
    destruct Hslot as [Hused|[Hnone Hfree]].
    + unfold event_slot_type_value, mutex_query_lookup in *; rewrite Hused in Htype.
      destruct observed.(eventType); cbn in Htype; congruence.
    + unfold event_slot_type_value in Htype; rewrite Hnone in Htype; discriminate.
Qed.

Lemma mutex_post_api_source_acquire : forall external port critical sg call returned pe before eid observed
  mask saved acquired,
  UCOS2_state_inv sg before ->
  mutex_post_api_input critical sg call.(os_sched_call_invocation) pe before eid observed ->
  mutex_post_api_prefix pe before eid ->
  kernel_call_save_source external port critical sg call returned mask saved before acquired ->
  exists current, mutex_query_acquire_facts critical sg call.(os_sched_call_invocation)
    eid mask saved before acquired observed current.
Proof.
  intros * Hvalid Hinput Hprefix Hsave.
  destruct (mutex_post_api_input_live _ _ _ _ _ _ _ Hinput Hprefix)
    as [Hlookup [Htype Hprotocol]].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg
    call.(os_sched_call_invocation) before acquired Hinterval Hvalid) as [Hvalid' _].
  destruct (mutex_query_handle_interval_preserves_identity critical sg
    call.(os_sched_call_invocation) eid before acquired observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgeneration Hcurrent_type]]].
  destruct Hsave as [_ [_ [_ [_ Hsaved]]]].
  exists current; unfold mutex_query_acquire_facts;
    repeat first [assumption | split | congruence].
Qed.

(** Post only changes priority/ready fields, waiter fields and the public
    Event owner.  Reuse Del's exact call-field observation and its generic
    task-source preservation theorem; there is no second stack model. *)
Lemma mutex_post_prepare_call_fields_eq : forall sg mutex owner entry prepared,
  mutex_post_prepare sg mutex owner entry prepared -> mutex_del_call_fields_eq entry prepared.
Proof.
  intros * Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; apply mutex_del_call_fields_eq_refl|].
  destruct Hprepare as [node [priority [Hnode [_ ->]]]].
  unfold mutex_post_owner_priority_state; destruct Z.eq_dec.
  - repeat split; intros; reflexivity.
  - split.
    + intros slot; cbn [mutex_post_relocated_state mutex_post_reserved_state
        mutex_del_ceiling_view mutex_del_ceiling_view_tasks mutex_del_relocated_state
        replace_SchedS replace_TskS TskState mutex_del_relocated_tasks inUsedTaskStates].
      apply glob_task_set_usedtask_observation with (old := node); [exact Hnode|reflexivity].
    + repeat split; reflexivity.
Qed.

Lemma mutex_post_critical_call_fields_eq : forall sg eid caller entry result schedule checkpoint,
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  mutex_del_call_fields_eq entry checkpoint.
Proof.
  intros * Hcritical.
  assert (Howner : forall state event mutex owner snapshot,
    mutex_del_call_fields_eq state (mutex_post_owner_state state eid event mutex owner snapshot))
    by (intros; repeat split; intros; reflexivity).
  destruct Hcritical.
  - apply mutex_del_call_fields_eq_refl.
  - eapply mutex_del_call_fields_eq_trans; [|apply Howner].
    eapply mutex_post_prepare_call_fields_eq; eassumption.
  - eapply mutex_del_call_fields_eq_trans; [|apply Howner].
    eapply mutex_del_call_fields_eq_trans.
    + eapply mutex_post_prepare_call_fields_eq; eassumption.
    + eapply mutex_del_wake_call_fields_eq; eassumption.
Qed.

Lemma mutex_post_prepare_preserves_runnable : forall sg mutex owner before after,
  mutex_post_prepare sg mutex owner before after -> mutex_del_preserves_runnable before after.
Proof.
  intros * Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; apply mutex_del_preserves_runnable_refl|].
  destruct Hprepare as [node [priority [Hnode [_ ->]]]].
  unfold mutex_post_owner_priority_state; destruct Z.eq_dec.
  - intros tid old Hold Hready; exists old; exact (conj Hold Hready).
  - intros tid old Hold Hready.
    cbn [mutex_post_relocated_state mutex_post_reserved_state mutex_del_ceiling_view
      mutex_del_ceiling_view_tasks mutex_del_relocated_state replace_SchedS replace_TskS
      TskState mutex_del_relocated_tasks inUsedTaskStates glob_task_set_usedtask].
    destruct (Z.eqb tid owner) eqn:Hsame.
    + apply Z.eqb_eq in Hsame; subst tid; assert (old = node) by congruence; subst old.
      exists (mutex_priority_task node priority); split; [reflexivity|exact Hready].
    + exists old; auto.
Qed.

Lemma mutex_post_critical_preserves_runnable : forall sg eid caller before result schedule after,
  mutex_post_critical sg eid caller before result schedule after ->
  mutex_del_preserves_runnable before after.
Proof.
  intros * Hcritical; destruct Hcritical.
  - apply mutex_del_preserves_runnable_refl.
  - change (mutex_del_preserves_runnable entry prepared).
    eapply mutex_post_prepare_preserves_runnable; eassumption.
  - change (mutex_del_preserves_runnable entry woken).
    eapply mutex_del_preserves_runnable_trans.
    + eapply mutex_post_prepare_preserves_runnable; eassumption.
    + eapply mutex_del_wake_preserves_runnable; eassumption.
Qed.

Lemma mutex_post_prepare_interrupt_frame : forall sg mutex owner before after,
  mutex_post_prepare sg mutex owner before after -> after.(IntrState) = before.(IntrState).
Proof.
  intros * Hprepare; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; reflexivity|].
  destruct Hprepare as [node [priority [_ [_ ->]]]].
  unfold mutex_post_owner_priority_state; destruct Z.eq_dec; reflexivity.
Qed.

Lemma mutex_post_critical_interrupt_frame : forall sg eid caller before result schedule after,
  mutex_post_critical sg eid caller before result schedule after ->
  after.(IntrState) = before.(IntrState).
Proof.
  intros * Hcritical; destruct Hcritical; [reflexivity| |].
  - change (prepared.(IntrState) = entry.(IntrState));
      eapply mutex_post_prepare_interrupt_frame; eassumption.
  - change (woken.(IntrState) = entry.(IntrState)).
    destruct (mutex_del_wake_interrupt_frame _ _ _ _ _ _ _ _ H5) as [Hinterrupt Hrunning].
    rewrite Hinterrupt; eapply mutex_post_prepare_interrupt_frame; eassumption.
Qed.

Lemma mutex_post_critical_preserves_task_call_stage : forall sg eid caller before result schedule after call,
  mutex_post_critical sg eid caller before result schedule after ->
  mutex_del_task_call_stage call before -> mutex_del_task_call_stage call after.
Proof.
  intros * Hcritical [Hsource Hready]; split.
  - eapply mutex_del_call_fields_preserve_task_source;
      [eapply mutex_post_critical_call_fields_eq; exact Hcritical|exact Hsource].
  - intros Henabled.
    assert (Hentry_enabled : os_sched_selection_enabled before = true).
    { unfold os_sched_selection_enabled in *.
      rewrite (mutex_post_critical_interrupt_frame _ _ _ _ _ _ _ Hcritical) in Henabled.
      exact Henabled. }
    destruct (Hready Hentry_enabled) as [node [Hnode Hrun]].
    exact (mutex_post_critical_preserves_runnable _ _ _ _ _ _ _ Hcritical _ _ Hnode Hrun).
Qed.

Lemma mutex_post_critical_source : forall sg eid caller entry result schedule after,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  task_slot_addr sg caller <> 1 ->
  mutex_post_critical sg eid caller entry result schedule after ->
  mutex_owner_source_history sg entry after.
Proof.
  intros * Hvalid Huse Hpointer Hrun; destruct Hrun.
  - constructor.
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    assert (He : prepared.(EventState).(inUsedEventStates) eid = Some event) by (rewrite Hevents; exact H).
    eapply mutex_owner_source_history_trans; [eapply mutex_post_prepare_source; exact H3|].
    eapply mutex_post_empty_source; try eassumption.
    exact (mutex_del_event_group_zero_implies_empty sg prepared eid event Hprepared He H4).
  - destruct (mutex_post_prepare_properties sg entry eid event mutex caller prepared
      Hvalid Huse H H0 H1 H2 Hpointer H3) as [Hprepared [Hevents Hslot]].
    assert (He : prepared.(EventState).(inUsedEventStates) eid = Some event) by (rewrite Hevents; exact H).
    eapply mutex_owner_source_history_trans; [eapply mutex_post_prepare_source; exact H3|].
    eapply mutex_post_handover_source; eassumption.
Qed.

Lemma mutex_post_continuation_critical_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg active entry checkpoint eid caller result schedule,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  task_slot_addr sg caller <> 1 ->
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  kernel_program_inv sg checkpoint ** mutex_del_continuation_critical_frame abi saved_local sg active entry |--
  kernel_continuation_inv abi mutex_del_stack_resources (task_create_continuation_local saved_local) sg active checkpoint.
Proof.
  intros * Hvalid Huse Hpointer Hrun.
  destruct (mutex_post_critical_call_fields_eq _ _ _ _ _ _ _ Hrun)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  assert (Hlookup : forall slot node, checkpoint.(TskState).(inUsedTaskStates) slot = Some node ->
    exists old, entry.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode; specialize (Hnodes slot); rewrite Hnode in Hnodes.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    cbn in Hnodes; injection Hnodes as Hg Hsp; exists old; auto. }
  unfold mutex_del_continuation_critical_frame; Intros_p Hfacts.
  destruct Hfacts as [Hhistory [Htypes Hcoverage]].
  assert (Hcoverage' : task_stack_live_coverage checkpoint.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame; [|exact Hstacks|exact Hcoverage].
    intros slot node Hnode; destruct (Hlookup slot node Hnode) as [old [Hold [Hg Hsp]]].
    exists old; split; [exact Hold|symmetry; exact Hg]. }
  assert (Hhistory' : mutex_program_selected_reachable sg checkpoint).
  { eapply mutex_program_source_history_reachable; [exact Hhistory|].
    eapply mutex_post_critical_source; eassumption. }
  assert (Htypes' : mutex_del_private_types_non_mutex checkpoint.(EventState)).
  { unfold mutex_del_private_types_non_mutex in *; rewrite Hprivate; exact Htypes. }
  assert (Hcapsules : store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState)
       (task_create_continuation_local saved_local)) entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState)
       (task_create_continuation_local saved_local)) checkpoint.(TskState).(parkedTaskStacks)).
  { rewrite Hstacks; apply kernel_saved_continuation_map_reindex.
    intros key payload node Hparked Hnode Hgen; eapply Hlookup; exact Hnode. }
  sep_apply_l_atomic Hcapsules.
  unfold kernel_continuation_inv, mutex_del_stack_resources, event_private_pool_rep.
  rewrite Hprivate; entailer!.
Qed.

(** Minimal C continuation cut: the calling task is live/current, its
    continuation is owned here, and only an enabled scheduler needs a
    nonempty ready set. It does not assert that all callers are runnable. *)
Definition mutex_post_api_stage (sg : StableGlobVars) call state : Prop :=
  kernel_call_task_source call state /\ kernel_call_stack_available call state /\
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []).

Lemma mutex_post_api_stage_from_task : forall sg call state,
  UCOS2_state_inv sg state -> mutex_del_task_call_stage call state ->
  kernel_call_stack_available call state -> mutex_post_api_stage sg call state.
Proof.
  intros * Hvalid Hstage Havailable; split; [exact (proj1 Hstage)|].
  split; [exact Havailable|].
  eapply mutex_del_task_call_stage_ready; eassumption.
Qed.

Lemma mutex_post_api_stage_call_cut : forall sg call state,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg state ->
  mutex_post_api_stage sg call state -> os_sched_call_cut sg call state.
Proof.
  intros * Hlayout Hvalid [Hsource [Havailable Hready]].
  split; [exact Hready|]. intros Hswitch; split.
  - eapply kernel_call_task_source_current_storage; try eassumption.
    eapply kernel_call_task_source_stack_field_address; eassumption.
  - unfold kernel_call_stack_available in Havailable; rewrite (proj1 Hsource) in Havailable; exact Havailable.
Qed.

Lemma mutex_post_critical_preserves_ready_nonempty : forall sg eid caller before result schedule after,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after ->
  mutex_post_critical sg eid caller before result schedule after ->
  before.(SchedState).(readyList) <> [] -> after.(SchedState).(readyList) <> [].
Proof.
  intros * Hvalid Hafter Hrun Hnonempty.
  destruct before.(SchedState).(readyList) as [|tid tail] eqn:Hlist; [contradiction|].
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hsched.
  destruct (proj1 Hsched tid ltac:(rewrite Hlist; left; reflexivity)) as [node [Hnode [_ Hready]]].
  destruct (mutex_post_critical_preserves_runnable _ _ _ _ _ _ _ Hrun _ _ Hnode Hready)
    as [current [Hcurrent Hrunready]].
  pose proof (proj1 (proj1 (proj2 (proj2 Hafter)))) as Hsched'.
  pose proof (proj1 (proj2 (proj2 Hsched')) _ _ Hcurrent Hrunready) as Hin.
  intros Hempty; rewrite Hempty in Hin; contradiction.
Qed.

Lemma mutex_post_critical_preserves_api_stage : forall sg eid caller before result schedule after call,
  UCOS2_state_inv sg before -> UCOS2_state_inv sg after ->
  mutex_post_critical sg eid caller before result schedule after ->
  mutex_post_api_stage sg call before -> mutex_post_api_stage sg call after.
Proof.
  intros * Hvalid Hafter Hrun [Hsource [Havailable Hready]].
  pose proof (mutex_post_critical_call_fields_eq _ _ _ _ _ _ _ Hrun) as Hfields.
  split; [eapply mutex_del_call_fields_preserve_task_source; eassumption|].
  split.
  - unfold kernel_call_stack_available in *.
    destruct call.(os_sched_call_origin); [exact I|].
    rewrite (proj1 (proj2 Hfields)); exact Havailable.
  - intros Henabled; eapply (mutex_post_critical_preserves_ready_nonempty sg eid caller
      before result schedule after Hvalid Hafter Hrun).
    apply Hready; unfold os_sched_selection_enabled in *.
    rewrite (mutex_post_critical_interrupt_frame _ _ _ _ _ _ _ Hrun) in Henabled; exact Henabled.
Qed.

Lemma mutex_post_modular_save_stage : forall external port critical sg call returned mask saved before acquired,
  kernel_sched_ready_clients critical -> UCOS2_state_inv sg before ->
  mutex_post_api_stage sg call before ->
  kernel_call_save_source external port critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  kernel_call_control_rely sg before acquired -> mutex_post_api_stage sg call acquired.
Proof.
  intros * Hclients Hvalid [Hsource [Havailable Hready]] Hsave [Hsame Hnormal] [Hrunning Hintr].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  split.
  - apply (proj1 (task_tcb_init_stack_same_call_source_iff returned call acquired Hsame)).
    eapply kernel_call_save_source_preserves_task_source; eassumption.
  - split.
    + pose proof (Hnormal Havailable) as Hreturned.
      unfold kernel_call_stack_available in *; rewrite (proj1 (proj2 Hsame)) in Hreturned; exact Hreturned.
    + intros Henabled.
      eapply critical_region_interval_preserves_sched_ready; try eassumption.
      apply Hready; unfold os_sched_selection_enabled in *; rewrite Hintr in Henabled; exact Henabled.
Qed.

Definition mutex_post_api_save_pre environment external platform critical saved_local
  sg original mask before : Assertion :=
  coq_prop (mutex_post_api_stage sg original before /\ kernel_sched_ready_clients critical) &&
  mutex_del_continuation_entry environment external platform saved_local sg original mask before.

Definition mutex_post_api_save_post environment external platform critical saved_local
  sg original mask saved before : Assertion :=
  EX acquired,
    coq_prop (mutex_post_api_stage sg original acquired /\
      critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
      interrupt_saved_value mask saved) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved acquired ** UCOS2_inv sg acquired ** unmap_table_rep sg **
     mutex_del_continuation_acquired environment external platform saved_local sg original acquired).

Lemma mutex_post_modular_save_pre : forall environment external platform critical saved_local
  sg original mask before,
  mutex_post_api_save_pre environment external platform critical saved_local sg original mask before |--
  coq_prop (mutex_del_callsite_environment environment external platform /\
    UCOS2_state_inv sg before /\ mutex_post_api_stage sg original before /\ kernel_sched_ready_clients critical) &&
  kernel_continuation_call_closed environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) sg
    (task_stack_call_active_key original) original mask before.
Proof.
  intros; unfold mutex_post_api_save_pre; Intros_p Hfacts.
  unfold mutex_del_continuation_entry; Intros selected; destruct H as [Henv ->].
  unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources,
    kernel_program_inv; entailer!.
Qed.

Lemma mutex_post_modular_save_post : forall environment critical saved_local sg original mask saved before,
  UCOS2_state_inv sg before -> mutex_post_api_stage sg original before -> kernel_sched_ready_clients critical ->
  kernel_call_modular_save_post environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local)
    critical kernel_call_control_rely sg original mask saved before |--
  mutex_post_api_save_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical saved_local sg original mask saved before.
Proof.
  intros * Hvalid Hstage Hclients.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  destruct H as [Hsave [Hnormal Hrely]].
  pose proof (mutex_post_modular_save_stage _ _ _ _ _ _ _ _ _ _
    Hclients Hvalid Hstage Hsave Hnormal Hrely) as Hstage'.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct Hnormal as [[Hi [Ho Hstack]] Havailable].
  destruct Hsave as [_ [_ [_ [_ Hsaved]]]].
  unfold mutex_post_api_save_post; Exists acquired.
  unfold kernel_continuation_call_masked, kernel_continuation_inv, mutex_del_stack_resources,
    mutex_del_continuation_acquired, mutex_del_continuation_stack_support.
  Exists environment returned.
  unfold mutex_del_callsite_environment, kernel_stack_call_same_call.
  rewrite kernel_program_inv_split_unmap; rewrite Hi, Ho.
  unfold task_stack_call_active_key; rewrite Ho; entailer!.
Qed.

Lemma mutex_post_continuation_restore_merge : forall environment external platform critical saved_local
  sg original mask saved entry checkpoint eid caller result schedule,
  UCOS2_state_inv sg entry -> mutex_owner_event_unlinked entry.(TskState) entry.(EventState) ->
  task_slot_addr sg caller <> 1 -> interrupt_saved_value mask saved ->
  mutex_post_critical sg eid caller entry result schedule checkpoint ->
  critical_region_masked platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) saved entry ** UCOS2_inv sg checkpoint ** unmap_table_rep sg **
  mutex_del_continuation_acquired environment external platform saved_local sg original entry |--
  mutex_del_continuation_restore_pre environment external platform critical saved_local sg
    original mask saved entry checkpoint.
Proof.
  intros * Hvalid Huse Hpointer Hsaved Hrun.
  unfold mutex_del_continuation_acquired, mutex_del_continuation_stack_support; Intros selected returned.
  destruct H as [[He Hp] [Hsame [Hreach [Htypes [Hcoverage Hselected]]]]]; subst external platform selected.
  destruct Hsame as [Hi [Ho Hstack]].
  assert (Hworld : kernel_program_inv sg checkpoint **
      mutex_del_continuation_critical_frame environment.(mutex_del_call_continuations)
        saved_local sg (task_stack_call_active_key original) entry |--
    kernel_continuation_inv environment.(mutex_del_call_continuations) mutex_del_stack_resources
      (task_create_continuation_local saved_local) sg (task_stack_call_active_key original) checkpoint).
  { eapply mutex_post_continuation_critical_merge; eassumption. }
  assert (Hinput : critical_region_masked environment.(mutex_del_call_platform) critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) saved entry ** UCOS2_inv sg checkpoint ** unmap_table_rep sg **
      event_private_pool_rep sg entry.(EventState) ** os_sched_context_resources environment.(mutex_del_call_external) returned **
      store_parked_continuations
        (kernel_saved_continuation_entry environment.(mutex_del_call_continuations) entry.(TskState)
          (task_create_continuation_local saved_local)) entry.(TskState).(parkedTaskStacks) |--
    critical_region_masked environment.(mutex_del_call_platform) critical sg returned.(os_sched_call_invocation)
      returned.(os_sched_call_origin) saved entry ** os_sched_context_resources environment.(mutex_del_call_external) returned **
    (kernel_program_inv sg checkpoint ** mutex_del_continuation_critical_frame environment.(mutex_del_call_continuations)
        saved_local sg (task_stack_call_active_key original) entry)).
  { unfold mutex_del_continuation_critical_frame; rewrite Hi, Ho, kernel_program_inv_split_unmap; entailer!. }
  sep_apply_l_atomic Hinput; sep_apply_l_atomic Hworld.
  unfold mutex_del_continuation_restore_pre; Exists environment returned.
  unfold kernel_continuation_call_masked, mutex_del_callsite_environment, kernel_stack_call_same_call; entailer!.
Qed.

Definition mutex_post_api_restore_pre environment external platform critical saved_local
  sg original mask saved acquired checkpoint : Assertion :=
  coq_prop (mutex_post_api_stage sg original checkpoint /\ kernel_sched_ready_clients critical) &&
  mutex_del_continuation_restore_pre environment external platform critical saved_local sg
    original mask saved acquired checkpoint.

Definition mutex_post_api_restore_post environment external platform saved_local
  sg original mask : Assertion :=
  EX returned current,
    coq_prop (mutex_post_api_stage sg returned current /\ kernel_stack_call_same_call returned original) &&
    mutex_del_continuation_entry environment external platform saved_local sg returned mask current.

Lemma mutex_post_api_stage_same_call : forall sg original returned state,
  kernel_stack_call_same_call returned original ->
  mutex_post_api_stage sg original state -> mutex_post_api_stage sg returned state.
Proof.
  intros * Hsame [Hsource [Havailable Hready]]; split.
  - apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original state Hsame)); exact Hsource.
  - split; [|exact Hready]. unfold kernel_call_stack_available in *.
    rewrite (proj1 (proj2 Hsame)); exact Havailable.
Qed.

Lemma mutex_post_modular_restore_pre : forall environment external platform critical saved_local
  sg original mask saved acquired checkpoint,
  mutex_post_api_restore_pre environment external platform critical saved_local
    sg original mask saved acquired checkpoint |--
  EX call,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call call original /\ interrupt_saved_value mask saved /\
      mutex_post_api_stage sg call checkpoint /\ kernel_sched_ready_clients critical) &&
    kernel_continuation_call_masked environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key call) call saved acquired checkpoint.
Proof.
  intros; unfold mutex_post_api_restore_pre; Intros_p Hfacts.
  destruct Hfacts as [Hstage Hclients].
  unfold mutex_del_continuation_restore_pre; Intros selected call.
  destruct H as [Henv [Hsame [Hsaved ->]]].
  assert (Hstage' : mutex_post_api_stage sg call checkpoint)
    by (eapply mutex_post_api_stage_same_call; eassumption).
  assert (Hactive : task_stack_call_active_key call = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; destruct Hsame as [_ [Ho _]]; rewrite Ho; reflexivity. }
  Exists call; rewrite Hactive; entailer!.
Qed.

Lemma mutex_post_modular_restore_post : forall environment critical saved_local
  sg original call mask released,
  kernel_stack_call_same_call call original -> UCOS2_state_inv sg released ->
  mutex_post_api_stage sg call released -> kernel_sched_ready_clients critical ->
  kernel_call_modular_restore_post environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical kernel_call_control_rely
    sg call mask released |--
  mutex_post_api_restore_post environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) saved_local sg original mask.
Proof.
  intros * Hcall Hvalid [Hsource [Havailable Hready]] Hclients.
  unfold kernel_call_modular_restore_post; Intros returned current.
  destruct H as [Htrace [[Hsame Hnormal] [Hrunning Hintr]]].
  assert (Hsame_original : kernel_stack_call_same_call returned original).
  { destruct Hsame as [Hi [Ho Hs]], Hcall as [Hi' [Ho' Hs']].
    unfold kernel_stack_call_same_call; repeat split; congruence. }
  assert (Hsource' : kernel_call_task_source returned current).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  assert (Hstage' : mutex_post_api_stage sg returned current).
  { split; [exact Hsource'|]. split; [apply Hnormal; exact Havailable|].
    intros Henabled.
    assert (Hready_before : released.(SchedState).(readyList) <> []).
    { apply Hready; unfold os_sched_selection_enabled in *; rewrite Hintr in Henabled; exact Henabled. }
    exact (proj2 (kernel_call_registered_rely_preserves_invariant _ _ _ kernel_sched_ready_inv
      sg call returned released current Hclients Htrace (conj Hvalid Hready_before))). }
  unfold mutex_post_api_restore_post, mutex_del_continuation_entry.
  Exists returned current environment; unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_post_api_restore_post_return : forall environment external platform saved_local sg original mask,
  mutex_post_api_restore_post environment external platform saved_local sg original mask |--
  mutex_del_continuation_return environment external platform saved_local sg original mask.
Proof.
  intros; unfold mutex_post_api_restore_post; Intros returned current.
  destruct H as [Hstage Hsame].
  unfold mutex_del_continuation_entry; Intros selected; destruct H as [Henv ->].
  assert (Hactive : task_stack_call_active_key returned = task_stack_call_active_key original).
  { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
  unfold mutex_del_continuation_return, mutex_del_continuation_return_at.
  Exists returned current environment; rewrite Hactive; entailer!.
Qed.

Definition mutex_post_api_post environment external platform critical saved_local
  sg original mask pe before eid observed code : Assertion :=
  (coq_prop (exists error,
      mutex_post_before_save_error pe (event_slot_type_value before.(EventState) eid)
        before.(IntrState).(intNesting) = Some error /\ code = encode_os_err_code error) &&
    mutex_del_continuation_entry environment external platform saved_local sg original mask before) ||
  (EX acquired current caller node result schedule committed,
    coq_prop (mutex_post_api_prefix pe before eid /\
      critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
      mutex_query_lookup acquired eid current /\ current.(eventType) = OS_EVENT_TYPE_MUTEX /\
      current.(eventGeneration) = observed.(eventGeneration) /\
      mutex_post_native_caller sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
        acquired original caller node /\
      mutex_post_critical sg eid caller acquired result schedule committed /\ code = encode_os_err_code result) &&
    mutex_del_continuation_return environment external platform saved_local sg original mask).

Lemma mutex_post_api_cold_return : forall environment external platform critical saved_local sg original mask
  pe before eid observed error,
  mutex_post_before_save_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) = Some error ->
  mutex_del_continuation_entry environment external platform saved_local sg original mask before |--
  mutex_post_api_post environment external platform critical saved_local sg original mask
    pe before eid observed (encode_os_err_code error).
Proof.
  intros * Herror heap Howned; left; split; [exists error; auto|exact Howned].
Qed.

Lemma mutex_post_api_critical_return : forall environment external platform critical saved_local sg original mask
  pe before eid observed acquired current caller node result schedule committed,
  mutex_post_api_prefix pe before eid ->
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired ->
  mutex_query_lookup acquired eid current -> current.(eventType) = OS_EVENT_TYPE_MUTEX ->
  current.(eventGeneration) = observed.(eventGeneration) ->
  mutex_post_native_caller sg original.(os_sched_call_invocation) original.(os_sched_call_origin)
    acquired original caller node ->
  mutex_post_critical sg eid caller acquired result schedule committed ->
  mutex_del_continuation_return environment external platform saved_local sg original mask |--
  mutex_post_api_post environment external platform critical saved_local sg original mask
    pe before eid observed (encode_os_err_code result).
Proof.
  intros * Hprefix Hinterval Hlookup Htype Hgeneration Hcaller Hrun heap Howned.
  right; exists acquired, current, caller, node, result, schedule, committed.
  split; [repeat first [assumption | split | reflexivity]|exact Howned].
Qed.

Definition mutex_post_api_scheduler_link sg critical : Prop :=
  os_sched_global_addresses sg &("OSIntNesting") &("OSLockNesting")
    &("OSPrioHighRdy") &("OSPrioCur") &("OSTCBHighRdy") &("OSTCBPrioTbl")
    &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl") /\
  kernel_sched_ready_clients critical.

Definition mutex_post_api_assumptions critical sg original invocation origin pe before eid observed : Prop :=
  UCOS2_state_inv sg before /\ mutex_post_api_input critical sg invocation pe before eid observed /\
  original.(os_sched_call_invocation) = invocation /\ original.(os_sched_call_origin) = origin /\
  mutex_post_api_call_admission original pe before eid /\
  (mutex_post_api_prefix pe before eid -> mutex_post_api_scheduler_link sg critical).

Definition mutex_post_api_entry_frame environment external platform saved_local sg original mask before : Assertion :=
  interrupt_platform_running platform original.(os_sched_call_invocation) original.(os_sched_call_origin) mask **
  mutex_del_continuation_entry_support environment external platform saved_local sg original before.

Lemma mutex_post_api_entry_split : forall environment external platform saved_local sg original mask before,
  mutex_del_continuation_entry environment external platform saved_local sg original mask before |--
  mutex_post_api_entry_frame environment external platform saved_local sg original mask before ** UCOS2_inv sg before.
Proof.
  intros; unfold mutex_del_continuation_entry; Intros selected.
  unfold mutex_del_callsite_environment in *; destruct H as [[He Hp] Hselected]; subst external platform.
  unfold kernel_continuation_call_closed, kernel_call_execution_owned, kernel_continuation_inv,
    mutex_del_stack_resources.
  rewrite kernel_program_inv_split_unmap.
  unfold mutex_post_api_entry_frame, mutex_del_continuation_entry_support; Exists selected.
  unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_post_api_entry_merge : forall environment external platform saved_local sg original mask before,
  mutex_post_api_entry_frame environment external platform saved_local sg original mask before ** UCOS2_inv sg before |--
  mutex_del_continuation_entry environment external platform saved_local sg original mask before.
Proof.
  intros; unfold mutex_post_api_entry_frame, mutex_del_continuation_entry_support; Intros selected.
  destruct H as [[He Hp] [Hreach [Htypes [Hcoverage Hselected]]]]; subst external platform.
  unfold mutex_del_continuation_entry; Exists selected.
  unfold kernel_continuation_call_closed, kernel_call_execution_owned, kernel_continuation_inv,
    mutex_del_stack_resources, mutex_del_callsite_environment.
  rewrite kernel_program_inv_split_unmap; entailer!.
Qed.

Definition mutex_post_api_sched_pre environment external platform critical saved_local sg original mask : Assertion :=
  coq_prop (mutex_post_api_scheduler_link sg critical) &&
  mutex_post_api_restore_post environment external platform saved_local sg original mask.

Lemma mutex_post_api_sched_pre_open : forall environment external platform critical saved_local sg original mask,
  kernel_tcb_stack_field_layout sg ->
  mutex_post_api_sched_pre environment external platform critical saved_local sg original mask |--
  EX returned current,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\ mutex_post_api_scheduler_link sg critical) &&
    os_sched_continuation_call_pre (mutex_del_runtime_sched_environment environment) saved_local
      mutex_del_stack_resources sg returned mask current.
Proof.
  intros * Hlayout; unfold mutex_post_api_sched_pre; Intros_p Hlink.
  unfold mutex_post_api_restore_post; Intros returned current; destruct H as [Hstage Hsame].
  unfold mutex_del_continuation_entry; Intros selected; destruct H as [Henv ->].
  assert (Hvalid : kernel_continuation_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key returned) returned mask current |--
    coq_prop (UCOS2_state_inv sg current) &&
    kernel_continuation_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key returned) returned mask current).
  { unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources,
      kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hvalid; Intros_p Hstate.
  pose proof (mutex_post_api_stage_call_cut _ _ _ Hlayout Hstate Hstage) as Hcut.
  Exists returned current.
  unfold os_sched_continuation_call_pre, os_sched_continuation_pre;
    cbn [mutex_del_runtime_sched_environment task_stack_call_continuations]; entailer!.
Qed.

Lemma mutex_post_api_sched_post : forall environment external platform saved_local sg original returned mask before,
  mutex_del_callsite_environment environment external platform ->
  kernel_stack_call_same_call returned original ->
  os_sched_continuation_return_post (mutex_del_runtime_sched_environment environment) saved_local
    mutex_del_stack_resources sg returned mask before |--
  mutex_del_continuation_return environment external platform saved_local sg original mask.
Proof.
  intros * [He Hp] Hsame; subst external platform.
  sep_apply_l_atomic (mutex_del_continuation_sched_post environment environment saved_local sg returned mask before eq_refl).
  eapply mutex_del_continuation_return_same_call; exact Hsame.
Qed.

Lemma mutex_post_api_owned_pointer : forall sg state caller node,
  tcb_field_address (task_slot_addr sg caller) TCBStkPtr = task_slot_addr sg caller ->
  state.(TskState).(inUsedTaskStates) caller = Some node ->
  UCOS2_inv sg state |-- coq_prop (task_slot_addr sg caller <> 1) && UCOS2_inv sg state.
Proof.
  intros * Haddress Hnode.
  assert (Hstorage : task_public_storage sg state.(TskState) |--
      coq_prop (task_slot_addr sg caller <> 1) && task_public_storage sg state.(TskState)).
  { eapply derivable1_trans; [apply task_public_storage_split_task; exact Hnode|].
    sep_apply_l_atomic (mutex_del_task_storage_pointer_not_reserved sg caller node Haddress).
    Intros_p Hpointer.
    sep_apply_l_atomic (task_public_storage_merge_task sg state.(TskState) caller node Hnode).
    entailer!. }
  rewrite UCOS2_inv_split_task.
  unfold task_shared_rep; Intros_p Hvalid.
  apply _derivable1_andp_intros; [|entailer!].
  sep_apply_l_atomic Hstorage; Intros_p Hpointer; entailer!.
Qed.

Lemma mutex_post_api_live_fields : forall sg state eid current,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid current -> current.(eventType) = OS_EVENT_TYPE_MUTEX ->
  exists mutex, current.(mutexFields) = Some mutex.
Proof.
  intros * Hvalid Hlookup Htype.
  destruct (mutex_del_parent_recheck_live_fields sg state eid current Hvalid
    (or_introl Hlookup) ltac:(unfold event_slot_type_value, mutex_query_lookup in *;
      rewrite Hlookup, Htype; reflexivity)) as [mutex [_ [_ Hfields]]].
  exists mutex; exact Hfields.
Qed.

Lemma mutex_post_api_type_unsigned : forall state eid,
  unsigned_last_nbits (event_slot_type_value state eid) 32 = event_slot_type_value state eid.
Proof.
  intros; unfold event_slot_type_value.
  destruct (inUsedEventStates state eid) as [event|]; [destruct (eventType event)|]; reflexivity.
Qed.

Lemma mutex_post_api_prefix_of_guards : forall pe before eid,
  before.(IntrState).(intNesting) <= 0 -> pe <> 0 ->
  unsigned_last_nbits (event_slot_type_value before.(EventState) eid) 32 = 4 ->
  mutex_post_api_prefix pe before eid.
Proof.
  intros * Hnest Hnull Htype; rewrite mutex_post_api_type_unsigned in Htype.
  apply mutex_post_before_save_continues_iff; auto.
Qed.

Lemma mutex_post_api_interval_acquire : forall critical sg invocation pe before eid observed acquired,
  UCOS2_state_inv sg before -> mutex_post_api_input critical sg invocation pe before eid observed ->
  mutex_post_api_prefix pe before eid -> critical_region_interval critical sg invocation before acquired ->
  exists current mutex, mutex_query_lookup acquired eid current /\ current.(eventType) = OS_EVENT_TYPE_MUTEX /\
    current.(mutexFields) = Some mutex /\ current.(eventGeneration) = observed.(eventGeneration) /\
    UCOS2_state_inv sg acquired.
Proof.
  intros * Hvalid Hinput Hprefix Hinterval.
  destruct (mutex_post_api_input_live _ _ _ _ _ _ _ Hinput Hprefix) as [Hlookup [Htype Hprotocol]].
  destruct (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid) as [Hafter _].
  destruct (mutex_query_handle_interval_preserves_identity critical sg invocation eid before acquired observed
    Hprotocol Hinterval Hvalid Hlookup) as [current [Hcurrent [Hgen Hkind]]].
  assert (Hmutex : current.(eventType) = OS_EVENT_TYPE_MUTEX) by congruence.
  destruct (mutex_post_api_live_fields sg acquired eid current Hafter Hcurrent Hmutex) as [mutex Hfields].
  exists current, mutex; repeat first [assumption|split].
  all: try congruence.
Qed.

Lemma mutex_post_api_restore_merge : forall environment external platform critical saved_local sg original
  mask saved eid caller acquired checkpoint result schedule,
  UCOS2_state_inv sg acquired -> mutex_owner_event_unlinked acquired.(TskState) acquired.(EventState) ->
  task_slot_addr sg caller <> 1 -> interrupt_saved_value mask saved ->
  mutex_post_api_stage sg original acquired -> kernel_sched_ready_clients critical ->
  mutex_post_critical sg eid caller acquired result schedule checkpoint ->
  critical_region_masked platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) saved acquired ** UCOS2_inv sg checkpoint ** unmap_table_rep sg **
  mutex_del_continuation_acquired environment external platform saved_local sg original acquired |--
  mutex_post_api_restore_pre environment external platform critical saved_local sg original mask saved acquired checkpoint.
Proof.
  intros * Hvalid Huse Hpointer Hsaved Hstage Hclients Hrun.
  assert (Hpeek : UCOS2_inv sg checkpoint |-- coq_prop (UCOS2_state_inv sg checkpoint) && UCOS2_inv sg checkpoint)
    by (unfold UCOS2_inv; entailer!).
  sep_apply_l_atomic Hpeek; Intros_p Hafter.
  pose proof (mutex_post_critical_preserves_api_stage _ _ _ _ _ _ _ _ Hvalid Hafter Hrun Hstage) as Hstage'.
  sep_apply_l_atomic (mutex_post_continuation_restore_merge environment external platform critical saved_local sg original
    mask saved acquired checkpoint eid caller result schedule Hvalid Huse Hpointer Hsaved Hrun).
  unfold mutex_post_api_restore_pre; entailer!.
Qed.

Lemma mutex_post_prepare_reserved_slot : forall sg mutex caller acquired prepared,
  mutex_post_prepare sg mutex caller acquired prepared ->
  mutex.(mfPCP) = sg.(osPrioMutexCeilDis) \/ prepared.(TskState).(prioTbl) mutex.(mfPCP) = PTReserved.
Proof.
  intros * Hprepare; unfold mutex_post_prepare in Hprepare; destruct Z.eq_dec as [Hdisabled|Henabled]; [left; exact Hdisabled|].
  destruct Hprepare as [node [priority [Hnode [Hscan ->]]]].
  right; rewrite mutex_post_owner_priority_table_eq; apply update_prio_tbl_same.
Qed.
