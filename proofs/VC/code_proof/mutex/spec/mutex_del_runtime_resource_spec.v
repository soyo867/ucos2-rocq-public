Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Logic.Classical_Prop.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_slot_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_program_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Section RuntimeResources.
Variable source_env : MutexDelCallEnvironment.

(** The runtime domain is the existing source-owned strong world. This is
    not a coercion from the old weak map. The environment binds all calls
    to one interpretation; it contains no new law or source obligation. *)
Definition mutex_del_runtime_entry external platform sg original mask state : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform /\ environment = source_env) &&
    kernel_stack_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources sg (task_stack_call_active_key original) original mask state.

Definition mutex_del_runtime_entry_support external platform sg original state : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      mutex_program_selected_reachable sg state /\
      mutex_del_private_types_non_mutex state.(EventState) /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key original) /\
      environment = source_env) &&
    (os_sched_context_resources external original ** unmap_table_rep sg **
     event_private_pool_rep sg state.(EventState) **
     armv7a_task_stack_continuations environment.(mutex_del_call_continuations)
       state.(TskState) state.(TskState).(parkedTaskStacks)).

Lemma mutex_del_runtime_entry_split : forall external platform critical sg original mask state,
  mutex_del_runtime_entry external platform sg original mask state |--
  mutex_query_closed platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) mask state **
  mutex_del_runtime_entry_support external platform sg original state.
Proof.
  intros; unfold mutex_del_runtime_entry; Intros environment.
  unfold mutex_del_callsite_environment in *; destruct H as [[He Hp] Hsource]; subst external platform.
  unfold kernel_stack_call_closed, kernel_call_execution_owned, kernel_stack_inv,
    mutex_del_stack_resources.
  rewrite mutex_query_closed_equiv, kernel_program_inv_split_unmap.
  unfold mutex_del_runtime_entry_support; Exists environment.
  unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_del_runtime_slot_cases : forall sg state eid,
  UCOS2_state_inv sg state -> valid_event_id sg eid ->
  (exists event, sem_query_public_slot state eid event) \/
  (exists allocation, state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation).
Proof.
  intros sg state eid Hvalid Hrange.
  destruct (state.(EventState).(eventLifecycle).(eventPrivate) eid) as [allocation|] eqn:Hprivate;
    [right; eauto|left].
  destruct (state.(EventState).(inUsedEventStates) eid) as [event|] eqn:Hused.
  - exists event; left; exact Hused.
  - assert (Hfree : In eid state.(EventState).(unUsedEventStates)).
    { apply NNPP; intros Hnot.
      destruct Hvalid as [_ [_ [_ [[[[Hnd [Hfree Hpartition]] Hdisjoint] Hrest] Hother]]]].
      destruct (proj2 (Hpartition eid) (conj Hrange Hnot)) as [value Hget].
      unfold event_allocated_slots in Hget; rewrite Hprivate, Hused in Hget; discriminate. }
    exists {| eventType := OS_EVENT_TYPE_UNUSED; mutexFields := None;
      semFields := None; mboxFields := None; queueFields := None; waitList := [];
      eventGeneration := 0; eventName := 0; eventPadding1 := None;
      eventPadding2 := None; eventPadding3 := None; eventPadding19 := None |}.
    right; auto.
Qed.

Lemma mutex_del_runtime_entry_merge : forall external platform critical sg original mask state,
  mutex_query_closed platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) mask state **
  mutex_del_runtime_entry_support external platform sg original state |--
  mutex_del_runtime_entry external platform sg original mask state.
Proof.
  intros; unfold mutex_del_runtime_entry_support; Intros environment.
  destruct H as [[He Hp] [Hreach [Htypes [Hcoverage Hsource]]]]; subst external platform.
  unfold mutex_del_runtime_entry; Exists environment.
  unfold kernel_stack_call_closed, kernel_call_execution_owned, kernel_stack_inv,
    mutex_del_stack_resources, mutex_del_callsite_environment.
  rewrite mutex_query_closed_equiv, kernel_program_inv_split_unmap; entailer!.
Qed.

(** Save's caller needs the source projection used by the existing owner
    protocol, not the false flattening of IRQ SP deposit/final take into
    ordinary client steps. Source producers must prove this SAME interval.
    This relation does not supply any physical resource. *)
Definition mutex_del_runtime_save_facts sg mask saved before acquired : Prop :=
  mutex_owner_source_history sg before acquired /\ UCOS2_state_inv sg acquired /\
  interrupt_saved_value mask saved.

Definition mutex_del_runtime_stack_support external platform sg original state : Assertion :=
  EX environment returned,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\
      mutex_program_selected_reachable sg state /\
      mutex_del_private_types_non_mutex state.(EventState) /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key original) /\
      environment = source_env) &&
    (os_sched_context_resources external returned **
     armv7a_task_stack_continuations environment.(mutex_del_call_continuations)
       state.(TskState) state.(TskState).(parkedTaskStacks)).

Definition mutex_del_runtime_acquired external platform sg original state : Assertion :=
  event_private_pool_rep sg state.(EventState) **
  mutex_del_runtime_stack_support external platform sg original state.

Definition mutex_del_runtime_save_post external platform critical sg original mask saved before : Assertion :=
  EX acquired,
    coq_prop (mutex_del_runtime_save_facts sg mask saved before acquired) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved acquired ** kernel_program_inv sg acquired **
     mutex_del_runtime_acquired external platform sg original acquired).

Lemma mutex_del_runtime_save_post_from_masked : forall environment critical sg original returned
  mask saved before acquired,
  environment = source_env ->
  mutex_owner_source_history sg before acquired ->
  kernel_stack_call_same_call returned original -> interrupt_saved_value mask saved ->
  kernel_stack_call_masked environment.(mutex_del_call_continuations)
    mutex_del_stack_resources critical sg (task_stack_call_active_key original)
    returned saved acquired acquired |--
  mutex_del_runtime_save_post environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical sg original mask saved before.
Proof.
  intros environment critical sg original returned mask saved before acquired Henv_source Hsource Hsame Hsaved.
  destruct Hsame as [Hi [Ho Hs]].
  unfold kernel_stack_call_masked, kernel_stack_inv, mutex_del_stack_resources.
  unfold mutex_del_runtime_save_post; Exists acquired.
  unfold mutex_del_runtime_acquired, mutex_del_runtime_stack_support; Exists environment returned.
  unfold mutex_del_runtime_save_facts, kernel_stack_call_same_call,
    mutex_del_callsite_environment, kernel_program_inv; rewrite Hi, Ho; entailer!.
Qed.

(** The private alternative borrows from the SAME whole pool and retains
    its missing map. The exposed-cut source fact only selects its value;
    the storage owner supplies the actual byte. No pool survives a call as
    an independent stale frame. *)
Definition mutex_del_runtime_type_observation (sg : StableGlobVars) eid state kind : Prop :=
  (exists event, sem_query_public_slot state eid event /\
    kind = event_slot_type_value state.(EventState) eid) \/
  (exists allocation,
    state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    allocation.(eventPrivateStorage) EventTypeField = Some kind /\ kind <> 4).

Definition mutex_del_runtime_pool_type_frame sg eid state kind : Assertion :=
  (EX event,
    coq_prop (UCOS2_state_inv sg state /\ sem_query_public_slot state eid event /\
      kind = event_slot_type_value state.(EventState) eid) &&
    (sem_query_type_frame sg state eid ** unmap_table_rep sg **
     event_private_pool_rep sg state.(EventState))) ||
  (EX allocation,
    coq_prop (state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateStorage) EventTypeField = Some kind /\ kind <> 4) &&
    (kernel_program_inv sg state ** event_private_storage_without_type sg eid allocation **
     event_private_pool_missing_eid sg state.(EventState) eid)).

Definition mutex_del_runtime_type_frame external platform sg original eid state kind : Assertion :=
  mutex_del_runtime_pool_type_frame sg eid state kind **
  mutex_del_runtime_stack_support external platform sg original state.

Lemma mutex_del_runtime_type_public_split : forall sg state eid event,
  sem_query_public_slot state eid event ->
  kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) |--
  event_addr sg eid # UChar |-> event_slot_type_value state.(EventState) eid **
  mutex_del_runtime_pool_type_frame sg eid state (event_slot_type_value state.(EventState) eid).
Proof.
  intros sg state eid event Hslot.
  assert (Hopen : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) |--
    coq_prop (UCOS2_state_inv sg state) &&
    (event_addr sg eid # UChar |-> event_slot_type_value state.(EventState) eid **
     (sem_query_type_frame sg state eid ** unmap_table_rep sg ** event_private_pool_rep sg state.(EventState)))).
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (sem_query_type_split_full sg state eid event Hslot).
    unfold OSEventType_off; rewrite Z.add_0_r; entailer!. }
  intros heap Hpre; destruct (Hopen heap Hpre) as [Hvalid [cell [rest [Hjoin [Hcell Hrest]]]]].
  exists cell, rest; split; [exact Hjoin|]. split; [exact Hcell|].
  left; exists event; split; [exact (conj Hvalid (conj Hslot eq_refl))|exact Hrest].
Qed.

Lemma mutex_del_runtime_type_private_split : forall sg state eid allocation kind,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateStorage) EventTypeField = Some kind -> kind <> 4 ->
  kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) |--
  event_addr sg eid # UChar |-> kind ** mutex_del_runtime_pool_type_frame sg eid state kind.
Proof.
  intros sg state eid allocation kind Hget Hkind Hnot.
  assert (Hopen : kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState) |--
    event_addr sg eid # UChar |-> kind **
    (kernel_program_inv sg state ** event_private_storage_without_type sg eid allocation **
     event_private_pool_missing_eid sg state.(EventState) eid)).
  { sep_apply_l_atomic (event_private_pool_split_eid sg state.(EventState) eid allocation Hget).
    sep_apply_l_atomic (event_private_storage_rep_split_type sg eid allocation kind Hkind).
    unfold event_addr, event_pool_addr; entailer!. }
  intros heap Hpre; destruct (Hopen heap Hpre) as [cell [rest [Hjoin [Hcell Hrest]]]].
  exists cell, rest; split; [exact Hjoin|]. split; [exact Hcell|].
  right; exists allocation; split; [exact (conj Hget (conj Hkind Hnot))|exact Hrest].
Qed.

Lemma mutex_del_runtime_pool_type_merge : forall sg state eid kind,
  event_addr sg eid # UChar |-> kind ** mutex_del_runtime_pool_type_frame sg eid state kind |--
  coq_prop (mutex_del_runtime_type_observation sg eid state kind) &&
  (kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState)).
Proof.
  intros sg state eid kind heap [cell [rest [Hjoin [Hcell [Hpublic|Hprivate]]]]].
  - destruct Hpublic as [event [[Hvalid [Hslot Hvalue]] Hrest]].
    split; [left; exists event; auto|].
    assert (Hmerge : event_addr sg eid # UChar |-> kind **
      (sem_query_type_frame sg state eid ** unmap_table_rep sg ** event_private_pool_rep sg state.(EventState)) |--
      kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState)).
    { rewrite Hvalue.
      replace (event_addr sg eid) with (event_addr sg eid + OSEventType_off) at 1
        by (unfold OSEventType_off; lia).
      sep_apply_l_atomic (sem_query_type_merge_full sg state eid Hvalid).
      rewrite kernel_program_inv_split_unmap; entailer!. }
    apply Hmerge; exists cell, rest; split; [exact Hjoin|split; assumption].
  - destruct Hprivate as [allocation [[Hget [Hkind Hnot]] Hrest]].
    split; [right; exists allocation; auto|].
    assert (Hmerge : event_addr sg eid # UChar |-> kind **
      (kernel_program_inv sg state ** event_private_storage_without_type sg eid allocation **
       event_private_pool_missing_eid sg state.(EventState) eid) |--
      kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState)).
    { unfold event_addr.
      sep_apply_l_atomic (event_private_storage_rep_merge_type sg eid allocation kind Hkind).
      sep_apply_l_atomic (event_private_pool_merge_eid sg state.(EventState) eid allocation Hget); entailer!. }
    apply Hmerge; exists cell, rest; split; [exact Hjoin|split; assumption].
Qed.

Lemma mutex_del_runtime_type_merge : forall external platform sg original eid state kind,
  event_addr sg eid # UChar |-> kind **
    mutex_del_runtime_type_frame external platform sg original eid state kind |--
  coq_prop (mutex_del_runtime_type_observation sg eid state kind) &&
  (kernel_program_inv sg state ** mutex_del_runtime_acquired external platform sg original state).
Proof.
  intros; unfold mutex_del_runtime_type_frame, mutex_del_runtime_acquired.
  sep_apply_l_atomic (mutex_del_runtime_pool_type_merge sg state eid kind); entailer!.
Qed.

Lemma mutex_del_runtime_type_split : forall external platform sg original eid state,
  valid_event_id sg eid ->
  kernel_program_inv sg state ** mutex_del_runtime_acquired external platform sg original state |--
  EX kind, event_addr sg eid # UChar |-> kind **
    mutex_del_runtime_type_frame external platform sg original eid state kind.
Proof.
  intros external platform sg original eid state Hid.
  assert (Hvalid : kernel_program_inv sg state |--
    coq_prop (UCOS2_state_inv sg state) && kernel_program_inv sg state).
  { unfold kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hvalid; Intros_p Hstate.
  unfold mutex_del_runtime_acquired, mutex_del_runtime_stack_support; Intros environment returned.
  destruct H as [Henv [Hsame [Hreach [Htypes [Hcoverage Hsource]]]]].
  destruct (mutex_del_runtime_slot_cases sg state eid Hstate Hid)
    as [[event Hpublic]|[allocation Hprivate]].
  - sep_apply_l_atomic (mutex_del_runtime_type_public_split sg state eid event Hpublic).
    Exists (event_slot_type_value state.(EventState) eid).
    unfold mutex_del_runtime_type_frame, mutex_del_runtime_stack_support; Exists environment returned; entailer!.
  - destruct (Htypes eid allocation Hprivate) as [kind [Htype Hnot]].
    sep_apply_l_atomic (mutex_del_runtime_type_private_split sg state eid allocation kind Hprivate Htype Hnot).
    Exists kind.
    unfold mutex_del_runtime_type_frame, mutex_del_runtime_stack_support; Exists environment returned; entailer!.
Qed.

Lemma mutex_del_runtime_acquired_owner_use : forall external platform sg original state,
  mutex_del_runtime_acquired external platform sg original state |--
  coq_prop (mutex_owner_event_unlinked state.(TskState) state.(EventState)) &&
  mutex_del_runtime_acquired external platform sg original state.
Proof.
  intros; unfold mutex_del_runtime_acquired, mutex_del_runtime_stack_support; Intros environment returned.
  destruct H as [Henv [Hsame [Hreach [Htypes [Hcoverage Hsource]]]]].
  assert (Howner : mutex_owner_event_unlinked state.(TskState) state.(EventState)).
  { eapply mutex_program_reachable_owner_use; [|exact Hreach].
    intros; eapply mutex_program_selected_initial_empty; eassumption. }
  Exists environment returned; entailer!.
Qed.

Lemma mutex_del_runtime_type_mutex : forall external platform sg original eid state,
  event_addr sg eid # UChar |-> 4 **
    mutex_del_runtime_type_frame external platform sg original eid state 4 |--
  EX event mutex,
    coq_prop (mutex_del_parent_entry sg eid state event mutex) &&
    (UCOS2_raw_rep sg state ** unmap_table_rep sg **
     mutex_del_runtime_acquired external platform sg original state).
Proof.
  intros; sep_apply_l_atomic (mutex_del_runtime_type_merge external platform sg original eid state 4).
  Intros_p Hobs.
  assert (Hvalid : kernel_program_inv sg state |--
    coq_prop (UCOS2_state_inv sg state) && kernel_program_inv sg state).
  { unfold kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hvalid; Intros_p Hstate.
  sep_apply_l_atomic (mutex_del_runtime_acquired_owner_use external platform sg original state); Intros_p Howner.
  destruct Hobs as [[event [Hslot Hvalue]]|[allocation [Hget [Hkind Hnot]]]]; [|contradiction].
  destruct (mutex_del_parent_recheck_live_fields sg state eid event Hstate Hslot (eq_sym Hvalue))
    as [mutex [Hlookup [Htype Hfields]]].
  Exists event mutex; unfold mutex_del_parent_entry, kernel_program_inv, kernel_program_rep; entailer!.
Qed.

Lemma mutex_del_runtime_restore_stage : forall external platform critical sg original saved entry checkpoint,
  mutex_del_stack_checkpoint sg entry checkpoint ->
  critical_region_masked platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) saved entry ** kernel_program_inv sg checkpoint **
    mutex_del_runtime_acquired external platform sg original entry |--
  EX environment returned,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\ environment = source_env) &&
    kernel_stack_call_masked environment.(mutex_del_call_continuations)
      mutex_del_stack_resources critical sg (task_stack_call_active_key original)
      returned saved entry checkpoint.
Proof.
  intros external platform critical sg original saved entry checkpoint Hcheckpoint.
  unfold mutex_del_runtime_acquired, mutex_del_runtime_stack_support; Intros environment returned.
  destruct H as [[He Hp] [Hsame [Hreach [Htypes [Hcoverage Hsource]]]]]; subst external platform.
  destruct Hsame as [Hi [Ho Hs]].
  assert (Hinput : critical_region_masked environment.(mutex_del_call_platform) critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) saved entry ** kernel_program_inv sg checkpoint **
      event_private_pool_rep sg entry.(EventState) ** os_sched_context_resources environment.(mutex_del_call_external) returned **
      armv7a_task_stack_continuations environment.(mutex_del_call_continuations)
        entry.(TskState) entry.(TskState).(parkedTaskStacks) |--
    mutex_del_stack_restore_input environment.(mutex_del_call_continuations) critical sg
      (task_stack_call_active_key original) returned saved entry checkpoint).
  { unfold mutex_del_stack_restore_input, mutex_del_stack_critical_frame; rewrite Hi, Ho; entailer!. }
  sep_apply_l_atomic Hinput.
  sep_apply_l_atomic (mutex_del_stack_restore_input_masked _ _ _ environment.(mutex_del_call_continuations)
    critical sg (task_stack_call_active_key original) returned saved entry checkpoint).
  Exists environment returned; unfold mutex_del_callsite_environment, kernel_stack_call_same_call; entailer!.
Qed.
End RuntimeResources.
