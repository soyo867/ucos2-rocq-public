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
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_program_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_stack_equiv_spec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.

(** Generic parked-call resources for the existing Del C contract.
    The old interfaces remain unchanged and retain their emp instance.
    The same saved_local is transported through actual critical updates;
    no continuation owner is weakened and reconstructed. *)

Definition mutex_del_continuation_critical_frame {external platform port}
  (abi : Armv7aContinuationABI external platform port) saved_local sg active entry : Assertion :=
  coq_prop (mutex_program_selected_reachable sg entry /\
    mutex_del_private_types_non_mutex entry.(EventState) /\
    task_stack_live_coverage entry.(TskState) active) &&
  (event_private_pool_rep sg entry.(EventState) **
   store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState)
       (task_create_continuation_local saved_local)) entry.(TskState).(parkedTaskStacks)).

Lemma mutex_del_continuation_world_split_critical_frame : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg active entry,
  kernel_continuation_inv abi mutex_del_stack_resources (task_create_continuation_local saved_local) sg active entry --||--
  kernel_program_inv sg entry ** mutex_del_continuation_critical_frame abi saved_local sg active entry.
Proof.
  intros; unfold kernel_continuation_inv, mutex_del_stack_resources, mutex_del_continuation_critical_frame;
    split; entailer!.
Qed.

Lemma mutex_del_continuation_critical_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg active entry checkpoint eid option result,
  mutex_del_critical sg eid option entry result checkpoint ->
  kernel_program_inv sg checkpoint ** mutex_del_continuation_critical_frame abi saved_local sg active entry |--
  kernel_continuation_inv abi mutex_del_stack_resources (task_create_continuation_local saved_local) sg active checkpoint.
Proof.
  intros external platform port abi saved_local sg active entry checkpoint eid option result Hrun.
  destruct (mutex_del_critical_call_fields_eq _ _ _ _ _ _ Hrun)
    as [Hnodes [Hstacks [Hlife [Hcurrent Hprivate]]]].
  assert (Hlookup : forall slot node, checkpoint.(TskState).(inUsedTaskStates) slot = Some node ->
    exists old, entry.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode; specialize (Hnodes slot); rewrite Hnode in Hnodes.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold;
      [|discriminate].
    cbn in Hnodes; injection Hnodes as Hg Hsp; exists old; auto. }
  unfold mutex_del_continuation_critical_frame; Intros_p Hfacts.
  destruct Hfacts as [Hhistory [Htypes Hcoverage]].
  assert (Hcoverage' : task_stack_live_coverage checkpoint.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame; [|exact Hstacks|exact Hcoverage].
    intros slot node Hnode; destruct (Hlookup slot node Hnode) as [old [Hold [Hg Hsp]]].
    exists old; split; [exact Hold|symmetry; exact Hg]. }
  assert (Hhistory' : mutex_program_selected_reachable sg checkpoint).
  { eapply mutex_program_source_history_reachable; [exact Hhistory|].
    eapply mutex_program_del_critical_source; exact Hrun. }
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

Section ContinuationResources.
Variable source_env : MutexDelCallEnvironment.

Definition mutex_del_continuation_entry external platform saved_local sg original mask state : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform /\ environment = source_env) &&
    kernel_continuation_call_closed environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) sg (task_stack_call_active_key original) original mask state.

Definition mutex_del_continuation_entry_support external platform saved_local sg original state : Assertion :=
  EX environment,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      mutex_program_selected_reachable sg state /\
      mutex_del_private_types_non_mutex state.(EventState) /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key original) /\
      environment = source_env) &&
    (os_sched_context_resources external original ** unmap_table_rep sg **
     event_private_pool_rep sg state.(EventState) **
     store_parked_continuations (kernel_saved_continuation_entry environment.(mutex_del_call_continuations) state.(TskState)
       (task_create_continuation_local saved_local)) state.(TskState).(parkedTaskStacks)).

Lemma mutex_del_continuation_entry_split : forall external platform critical saved_local sg original mask state,
  mutex_del_continuation_entry external platform saved_local sg original mask state |--
  mutex_query_closed platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) mask state **
  mutex_del_continuation_entry_support external platform saved_local sg original state.
Proof.
  intros; unfold mutex_del_continuation_entry; Intros environment.
  unfold mutex_del_callsite_environment in *; destruct H as [[He Hp] Hsource]; subst external platform.
  unfold kernel_continuation_call_closed, kernel_call_execution_owned, kernel_continuation_inv,
    mutex_del_stack_resources.
  rewrite mutex_query_closed_equiv, kernel_program_inv_split_unmap.
  unfold mutex_del_continuation_entry_support; Exists environment.
  unfold mutex_del_callsite_environment; entailer!.
Qed.

Lemma mutex_del_continuation_entry_merge : forall external platform critical saved_local sg original mask state,
  mutex_query_closed platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) mask state **
  mutex_del_continuation_entry_support external platform saved_local sg original state |--
  mutex_del_continuation_entry external platform saved_local sg original mask state.
Proof.
  intros; unfold mutex_del_continuation_entry_support; Intros environment.
  destruct H as [[He Hp] [Hreach [Htypes [Hcoverage Hsource]]]]; subst external platform.
  unfold mutex_del_continuation_entry; Exists environment.
  unfold kernel_continuation_call_closed, kernel_call_execution_owned, kernel_continuation_inv,
    mutex_del_stack_resources, mutex_del_callsite_environment.
  rewrite mutex_query_closed_equiv, kernel_program_inv_split_unmap; entailer!.
Qed.

Definition mutex_del_continuation_stack_support external platform saved_local sg original state : Assertion :=
  EX environment returned,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\
      mutex_program_selected_reachable sg state /\
      mutex_del_private_types_non_mutex state.(EventState) /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key original) /\
      environment = source_env) &&
    (os_sched_context_resources external returned **
     store_parked_continuations (kernel_saved_continuation_entry environment.(mutex_del_call_continuations) state.(TskState)
       (task_create_continuation_local saved_local)) state.(TskState).(parkedTaskStacks)).

Definition mutex_del_continuation_acquired external platform saved_local sg original state : Assertion :=
  event_private_pool_rep sg state.(EventState) **
  mutex_del_continuation_stack_support external platform saved_local sg original state.

Definition mutex_del_continuation_save_post external platform critical saved_local sg original mask saved before : Assertion :=
  EX acquired,
    coq_prop (mutex_del_runtime_save_facts sg mask saved before acquired) &&
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) saved acquired ** kernel_program_inv sg acquired **
     mutex_del_continuation_acquired external platform saved_local sg original acquired).

Lemma mutex_del_continuation_save_post_from_masked : forall environment critical saved_local sg original returned
  mask saved before acquired,
  environment = source_env ->
  mutex_owner_source_history sg before acquired ->
  kernel_stack_call_same_call returned original -> interrupt_saved_value mask saved ->
  kernel_continuation_call_masked environment.(mutex_del_call_continuations)
    mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg (task_stack_call_active_key original)
    returned saved acquired acquired |--
  mutex_del_continuation_save_post environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical saved_local sg original mask saved before.
Proof.
  intros environment critical saved_local sg original returned mask saved before acquired Henv_source Hsource Hsame Hsaved.
  destruct Hsame as [Hi [Ho Hs]].
  unfold kernel_continuation_call_masked, kernel_continuation_inv, mutex_del_stack_resources.
  unfold mutex_del_continuation_save_post; Exists acquired.
  unfold mutex_del_continuation_acquired, mutex_del_continuation_stack_support; Exists environment returned.
  unfold mutex_del_runtime_save_facts, kernel_stack_call_same_call,
    mutex_del_callsite_environment, kernel_program_inv; rewrite Hi, Ho; entailer!.
Qed.

Definition mutex_del_continuation_type_frame external platform saved_local sg original eid state kind : Assertion :=
  mutex_del_runtime_pool_type_frame sg eid state kind **
  mutex_del_continuation_stack_support external platform saved_local sg original state.

Lemma mutex_del_continuation_type_merge : forall external platform saved_local sg original eid state kind,
  event_addr sg eid # UChar |-> kind **
    mutex_del_continuation_type_frame external platform saved_local sg original eid state kind |--
  coq_prop (mutex_del_runtime_type_observation sg eid state kind) &&
  (kernel_program_inv sg state ** mutex_del_continuation_acquired external platform saved_local sg original state).
Proof.
  intros; unfold mutex_del_continuation_type_frame, mutex_del_continuation_acquired.
  sep_apply_l_atomic (mutex_del_runtime_pool_type_merge sg state eid kind); entailer!.
Qed.

Lemma mutex_del_continuation_type_split : forall external platform saved_local sg original eid state,
  valid_event_id sg eid ->
  kernel_program_inv sg state ** mutex_del_continuation_acquired external platform saved_local sg original state |--
  EX kind, event_addr sg eid # UChar |-> kind **
    mutex_del_continuation_type_frame external platform saved_local sg original eid state kind.
Proof.
  intros external platform saved_local sg original eid state Hid.
  assert (Hvalid : kernel_program_inv sg state |--
    coq_prop (UCOS2_state_inv sg state) && kernel_program_inv sg state).
  { unfold kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hvalid; Intros_p Hstate.
  unfold mutex_del_continuation_acquired, mutex_del_continuation_stack_support; Intros environment returned.
  destruct H as [Henv [Hsame [Hreach [Htypes [Hcoverage Hsource]]]]].
  destruct (mutex_del_runtime_slot_cases sg state eid Hstate Hid)
    as [[event Hpublic]|[allocation Hprivate]].
  - sep_apply_l_atomic (mutex_del_runtime_type_public_split sg state eid event Hpublic).
    Exists (event_slot_type_value state.(EventState) eid).
    unfold mutex_del_continuation_type_frame, mutex_del_continuation_stack_support; Exists environment returned; entailer!.
  - destruct (Htypes eid allocation Hprivate) as [kind [Htype Hnot]].
    sep_apply_l_atomic (mutex_del_runtime_type_private_split sg state eid allocation kind Hprivate Htype Hnot).
    Exists kind.
    unfold mutex_del_continuation_type_frame, mutex_del_continuation_stack_support; Exists environment returned; entailer!.
Qed.

Lemma mutex_del_continuation_acquired_owner_use : forall external platform saved_local sg original state,
  mutex_del_continuation_acquired external platform saved_local sg original state |--
  coq_prop (mutex_owner_event_unlinked state.(TskState) state.(EventState)) &&
  mutex_del_continuation_acquired external platform saved_local sg original state.
Proof.
  intros; unfold mutex_del_continuation_acquired, mutex_del_continuation_stack_support; Intros environment returned.
  destruct H as [Henv [Hsame [Hreach [Htypes [Hcoverage Hsource]]]]].
  assert (Howner : mutex_owner_event_unlinked state.(TskState) state.(EventState)).
  { eapply mutex_program_reachable_owner_use; [|exact Hreach].
    intros; eapply mutex_program_selected_initial_empty; eassumption. }
  Exists environment returned; entailer!.
Qed.

Lemma mutex_del_continuation_type_mutex : forall external platform saved_local sg original eid state,
  event_addr sg eid # UChar |-> 4 **
    mutex_del_continuation_type_frame external platform saved_local sg original eid state 4 |--
  EX event mutex,
    coq_prop (mutex_del_parent_entry sg eid state event mutex) &&
    (UCOS2_raw_rep sg state ** unmap_table_rep sg **
     mutex_del_continuation_acquired external platform saved_local sg original state).
Proof.
  intros; sep_apply_l_atomic (mutex_del_continuation_type_merge external platform saved_local sg original eid state 4).
  Intros_p Hobs.
  assert (Hvalid : kernel_program_inv sg state |--
    coq_prop (UCOS2_state_inv sg state) && kernel_program_inv sg state).
  { unfold kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hvalid; Intros_p Hstate.
  sep_apply_l_atomic (mutex_del_continuation_acquired_owner_use external platform saved_local sg original state); Intros_p Howner.
  destruct Hobs as [[event [Hslot Hvalue]]|[allocation [Hget [Hkind Hnot]]]]; [|contradiction].
  destruct (mutex_del_parent_recheck_live_fields sg state eid event Hstate Hslot (eq_sym Hvalue))
    as [mutex [Hlookup [Htype Hfields]]].
  Exists event mutex; unfold mutex_del_parent_entry, kernel_program_inv, kernel_program_rep; entailer!.
Qed.

Lemma mutex_del_continuation_restore_stage : forall external platform critical saved_local sg original saved entry checkpoint,
  mutex_del_stack_checkpoint sg entry checkpoint ->
  critical_region_masked platform critical sg original.(os_sched_call_invocation)
    original.(os_sched_call_origin) saved entry ** kernel_program_inv sg checkpoint **
    mutex_del_continuation_acquired external platform saved_local sg original entry |--
  EX environment returned,
    coq_prop (mutex_del_callsite_environment environment external platform /\
      kernel_stack_call_same_call returned original /\ environment = source_env) &&
    kernel_continuation_call_masked environment.(mutex_del_call_continuations)
      mutex_del_stack_resources (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key original) returned saved entry checkpoint.
Proof.
  intros external platform critical saved_local sg original saved entry checkpoint Hcheckpoint.
  unfold mutex_del_continuation_acquired, mutex_del_continuation_stack_support; Intros environment returned.
  destruct H as [[He Hp] [Hsame [Hreach [Htypes [Hcoverage Hsource]]]]]; subst external platform.
  destruct Hsame as [Hi [Ho Hs]].
  assert (Hworld : kernel_program_inv sg checkpoint **
      mutex_del_continuation_critical_frame environment.(mutex_del_call_continuations)
        saved_local sg (task_stack_call_active_key original) entry |--
    kernel_continuation_inv environment.(mutex_del_call_continuations) mutex_del_stack_resources
      (task_create_continuation_local saved_local) sg (task_stack_call_active_key original) checkpoint).
  { destruct Hcheckpoint as [->|[eid [option [result Hrun]]]].
    - apply (proj2 (mutex_del_continuation_world_split_critical_frame _ _ _
        environment.(mutex_del_call_continuations) saved_local sg (task_stack_call_active_key original) entry)).
    - eapply mutex_del_continuation_critical_merge; exact Hrun. }
  assert (Hinput : critical_region_masked environment.(mutex_del_call_platform) critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) saved entry ** kernel_program_inv sg checkpoint **
      event_private_pool_rep sg entry.(EventState) ** os_sched_context_resources environment.(mutex_del_call_external) returned **
      store_parked_continuations
        (kernel_saved_continuation_entry environment.(mutex_del_call_continuations) entry.(TskState)
          (task_create_continuation_local saved_local)) entry.(TskState).(parkedTaskStacks) |--
    critical_region_masked environment.(mutex_del_call_platform) critical sg returned.(os_sched_call_invocation)
      returned.(os_sched_call_origin) saved entry ** os_sched_context_resources environment.(mutex_del_call_external) returned **
    (kernel_program_inv sg checkpoint **
      mutex_del_continuation_critical_frame environment.(mutex_del_call_continuations)
        saved_local sg (task_stack_call_active_key original) entry)).
  { unfold mutex_del_continuation_critical_frame; rewrite Hi, Ho; entailer!. }
  sep_apply_l_atomic Hinput; sep_apply_l_atomic Hworld.
  Exists environment returned.
  unfold kernel_continuation_call_masked, mutex_del_callsite_environment, kernel_stack_call_same_call; entailer!.
Qed.

End ContinuationResources.

(** Compatibility is restricted to the empty saved-local family. Both
    directions retain the same descriptor, binding and live-SP facts. *)
Lemma mutex_del_continuation_entry_emp_equiv : forall source_env external platform sg original mask state,
  mutex_del_continuation_entry source_env external platform (fun _ => emp) sg original mask state --||--
  mutex_del_runtime_entry source_env external platform sg original mask state.
Proof.
  intros source_env external platform sg original mask state.
  assert (Hlocal : task_create_continuation_local (fun _ => emp) = (fun _ => emp)).
  { apply functional_extensionality; intros descriptor.
    unfold task_create_continuation_local; destruct descriptor.(armv7a_continuation_call); reflexivity. }
  unfold mutex_del_continuation_entry, mutex_del_runtime_entry.
  rewrite Hlocal; split; Intros environment; Exists environment.
  - sep_apply_l_atomic (proj1 (kernel_continuation_call_closed_emp_equiv _ _ _
      environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
      (task_stack_call_active_key original) original mask state)); entailer!.
  - sep_apply_l_atomic (proj2 (kernel_continuation_call_closed_emp_equiv _ _ _
      environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
      (task_stack_call_active_key original) original mask state)); entailer!.
Qed.
