Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual selected program owner, established at boot and transported
    by this configuration's registered source edges. This is intentionally
    NOT equivalent to the former arbitrary-valid-state entry. It adds no
    owner-use, current-task or ready premise: owner-use is DERIVED from the
    boot/source history; CPU, stack, table and parked-map ownership remain
    exactly the physical interface's resources.

    The ARM/BSP and application/ISR implementations remain outside scope;
    their previously approved execution/client-use contracts are explicit.
    No future Save/Restore or scheduler return is promised by this owner. *)
Definition mutex_del_program_entry_closed external platform
  (configuration : MutexProgramConfiguration) sg original mask state : Assertion :=
  coq_prop (mutex_program_reachable mutex_program_selected_initial sg state) &&
  mutex_del_callsite_entry_closed external platform (mutex_program_region configuration)
    sg original mask state.

Definition mutex_del_program_entry_support external platform sg original state : Assertion :=
  coq_prop (mutex_program_reachable mutex_program_selected_initial sg state) &&
  mutex_del_callsite_entry_support external platform sg original state.

Lemma mutex_del_program_entry_history : forall external platform configuration sg original mask state,
  mutex_del_program_entry_closed external platform configuration sg original mask state |--
    coq_prop (mutex_program_selected_reachable sg state) &&
    mutex_del_program_entry_closed external platform configuration sg original mask state.
Proof. intros * heap [Hhistory Howned]; split; [exact Hhistory|split; assumption]. Qed.

Lemma mutex_del_program_interval_owner_use : forall configuration sg invocation before entry,
  mutex_program_selected_reachable sg before -> UCOS2_state_inv sg before ->
  critical_region_interval (mutex_program_region configuration) sg invocation before entry ->
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState).
Proof.
  intros configuration sg invocation before entry Hhistory Hvalid Hinterval.
  destruct (mutex_program_region_interval_reachable configuration mutex_program_selected_initial
    sg invocation before entry (conj Hvalid Hhistory) Hinterval) as [_ Hentry].
  eapply mutex_program_reachable_owner_use; [|exact Hentry].
  apply mutex_program_selected_initial_empty.
Qed.

Lemma mutex_del_program_entry_split : forall external platform configuration sg original mask state,
  mutex_del_program_entry_closed external platform configuration sg original mask state |--
    mutex_query_closed platform (mutex_program_region configuration) sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin) mask state **
    mutex_del_program_entry_support external platform sg original state.
Proof.
  intros; unfold mutex_del_program_entry_closed, mutex_del_program_entry_support; Intros_p Hhistory.
  sep_apply_l_atomic (mutex_del_callsite_entry_split external platform
    (mutex_program_region configuration) sg original mask state); entailer!.
Qed.

Lemma mutex_del_program_entry_merge : forall external platform configuration sg original mask state,
  mutex_query_closed platform (mutex_program_region configuration) sg
      original.(os_sched_call_invocation) original.(os_sched_call_origin) mask state **
    mutex_del_program_entry_support external platform sg original state |--
  mutex_del_program_entry_closed external platform configuration sg original mask state.
Proof.
  intros; unfold mutex_del_program_entry_closed, mutex_del_program_entry_support; Intros_p Hhistory.
  sep_apply_l_atomic (mutex_del_callsite_entry_merge external platform
    (mutex_program_region configuration) sg original mask state); entailer!.
Qed.

Lemma mutex_del_program_entry_source : forall external platform configuration sg original mask state,
  mutex_del_program_entry_closed external platform configuration sg original mask state |--
    coq_prop (mutex_owner_region_source_protocol (mutex_program_region configuration) sg /\
      mutex_owner_program_history sg state) &&
    mutex_del_callsite_entry_closed external platform (mutex_program_region configuration)
      sg original mask state.
Proof.
  intros external platform configuration sg original mask state heap [Hreachable Howned].
  split; [split|exact Howned].
  - apply mutex_program_region_protocol.
  - apply mutex_program_selected_reachable_history; exact Hreachable.
Qed.

(** The same actual first-call stack producer establishes the configured
    entry. Fresh invocation registration changes neither live Task fields
    nor Event fields, so this is a proved source-history step, not a new
    platform guarantee. No independent acquired state is chosen. *)
Lemma mutex_del_program_initial_entry : forall environment configuration sg
  (entry_abi : Armv7aInitialCallABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations)) state initial fragments,
  armv7a_initial_frame_binding initial ->
  task_stack_fragments_in_range initial.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 fragments ->
  task_current_at state initial.(armv7a_continuation_stack).(stackLeaseSlot)
    initial.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  let call := armv7a_initial_call initial state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  coq_prop (mutex_program_reachable mutex_program_selected_initial sg state) &&
    (mutex_del_interface_world environment sg state **
     armv7a_initial_execution environment.(mutex_del_call_continuations) initial **
     task_stack_fragments_rep initial.(armv7a_continuation_stack).(stackLeaseRegion) fragments) |--
  coq_prop (kernel_call_task_source call (armv7a_initial_call_registered initial state)) &&
    mutex_del_program_entry_closed environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) configuration sg call
      (armv7a_irq_fiq_mask initial.(armv7a_continuation_cpsr))
      (armv7a_initial_call_registered initial state).
Proof.
  intros environment configuration sg entry_abi state initial fragments Hbinding Hrange Hcurrent call.
  Intros_p Hreachable.
  assert (Hafter : mutex_program_reachable mutex_program_selected_initial sg
      (armv7a_initial_call_registered initial state)).
  { eapply mutex_program_source_step_reachable; [exact Hreachable|].
    apply MutexOwnerSourceFrame; reflexivity. }
  pose proof (mutex_del_interface_initial_entry environment (mutex_program_region configuration)
    sg entry_abi state initial fragments Hbinding Hrange Hcurrent) as Hentry.
  cbv zeta in Hentry; fold call in Hentry; sep_apply_l_atomic Hentry.
  Intros_p Hcall.
  unfold mutex_del_program_entry_closed.
  sep_apply_l_atomic (mutex_del_callsite_entry_from_interface environment (mutex_program_region configuration)
    sg call (armv7a_irq_fiq_mask initial.(armv7a_continuation_cpsr))
    (armv7a_initial_call_registered initial state)); entailer!.
Qed.
