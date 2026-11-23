(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SimpleC.SL.Mem.
Require Import SimpleC.SL.ConAssertion.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import ArrayLib.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import AUXLib.ListLib.
From MonadLib Require Import Monad.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_observer_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module BuiltinComponent.





























Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Import FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
















Import TaskStateDef SchedStateDef.
Local Open Scope Z_scope.


Lemma os_int_exit_configured_transfer_hooked_eq :
  forall environment sg handler entry transfer,
  os_int_exit_transfer_source
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer ->
  transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true entry.
Proof.
  intros environment sg handler entry transfer [_ [_ [_ [Hhook _]]]].
  exact Hhook.
Qed.
Lemma os_int_exit_configured_transfer_state_frame :
  forall environment sg handler entry transfer,
  os_int_exit_transfer_source
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer ->
  let current := os_int_exit_installed_state transfer in
  current.(TskState).(inUsedTaskStates) = entry.(TskState).(inUsedTaskStates) /\
  current.(TskState).(taskLifecycle) = entry.(TskState).(taskLifecycle) /\
  current.(EventState) = entry.(EventState) /\
  current.(NameState) = entry.(NameState) /\
  current.(TimerState) = entry.(TimerState).
Proof.
  intros environment sg handler entry transfer Htransfer current.
  pose proof (os_int_exit_configured_transfer_hooked_eq
    environment sg handler entry transfer Htransfer) as Hhook.
  unfold current, os_int_exit_installed_state; rewrite Hhook.
  repeat split; reflexivity.
Qed.
Lemma os_int_exit_configured_transfer_preserves_observer_cache :
  forall environment sg handler entry transfer observer observer_origin,
  os_int_exit_transfer_source
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer ->
  task_invocation_active entry.(TskState) observer observer_origin ->
  task_invocation_active (os_int_exit_installed_state transfer).(TskState)
    observer observer_origin /\
  sched_observer_current_cache observer_origin (os_int_exit_installed_state transfer).
Proof.
  intros environment sg handler entry transfer observer observer_origin Htransfer Hactive.
  split.
  - pose proof (os_int_exit_configured_transfer_hooked_eq
      environment sg handler entry transfer Htransfer) as Hhook.
    unfold os_int_exit_installed_state; rewrite Hhook; exact Hactive.
  - apply sched_current_consistency_implies_observer_cache.
    eapply os_int_exit_destination_installs_current_consistency.
    destruct Htransfer as [_ [_ [_ [_ [Hdestination _]]]]]; exact Hdestination.
Qed.














Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma task_observer_lifetime_transport_inactive : forall observer origin before after,
  task_observer_lifetime_transport observer origin before after ->
  task_observer_lifetime before observer origin ->
  ~ task_invocation_active before observer origin ->
  ~ task_invocation_active after observer origin.
Proof. intros observer origin before after Hstep Hlife Hgone Hactive; apply Hgone; exact (proj2 (Hstep Hlife) Hactive). Qed.

Lemma task_commit_observer_lifetime_transport : forall tasks p invocation node observer origin,
  task_commit_identity tasks p invocation node ->
  task_observer_lifetime_transport observer origin tasks (task_commit tasks p invocation node).
Proof.
  intros tasks p invocation node observer origin Hidentity [Hreg [Hbound [Hg Hprivate]]]; split.
  - split; [exact Hreg|]. split; [exact Hbound|]. split; [exact Hg|].
    destruct origin as [|slot generation]; [exact I|].
    intros q entry allocation Hentry Halloc Hslot; simpl in Hentry.
    destruct (Z.eq_dec q p); [discriminate|]. eapply Hprivate; eassumption.
  - intros [Hmap [Hret Hlive]]; split; [exact Hmap|]. split; [exact Hret|].
    destruct origin as [|slot generation]; [exact I|].
    destruct Hlive as [post [Hpost Hgen]].
    pose proof (task_commit_observation nat taskGeneration tasks p invocation node slot
      (fun _ _ _ => eq_refl)) as Hobs.
    rewrite Hpost in Hobs; simpl in Hobs.
    destruct (Z.eq_dec slot node.(taskID)) as [Heq|Hneq].
    + destruct Hidentity as [entry [allocation [Hentry [Hinv [Halloc [Hslot [Hgeneration Hpriority]]]]]]].
      exfalso; apply (Hprivate p entry allocation Hentry Halloc ltac:(congruence)); congruence.
    + destruct (tasks.(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
      exists old; split; [exact Hold|]. simpl in Hobs; congruence.
Qed.

(** Concrete C segments.  Counter stages admit raw fields, including legal
    nonclosed phases.  Publication and IRQ keep their actual callee owners.
    The code proof and each local frame belong to this one segment. *)















Inductive KernelCounterCOperation : Type :=
| KernelCounterCEnter
| KernelCounterCExit (observed_running : bool).

Definition kernel_counter_c_state operation state :=
  match operation with
  | KernelCounterCEnter => os_int_enter_state state
  | KernelCounterCExit observed => os_int_exit_counter_state observed state
  end.

Definition kernel_counter_c_writes operation sg state :=
  match operation with
  | KernelCounterCEnter => os_int_enter_heap_writes sg state
  | KernelCounterCExit observed => os_int_exit_counter_heap_writes sg observed state
  end.

Definition kernel_counter_c_code operation sg before after : Prop :=
  match operation with
  | KernelCounterCEnter => kernel_client_int_enter_fragment sg before after
  | KernelCounterCExit observed => os_int_exit_masked_counter_fragment sg before observed after
  end.

Lemma os_int_enter_fields_raw_frame_writes : forall sg state (frame : Assertion) before after,
  (UCOS2_fields_raw_rep sg state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  kernel_heap_execution (os_int_enter_heap_writes sg state) before after.
Proof.
  intros sg state frame before after [owned [rest [Hjoin [Hraw Hrest]]]] Hsource.
  pose proof (uchar_load_frame _ _ _ _ _
    (os_int_exit_fields_raw_running_load sg state owned Hraw) Hjoin) as Hr.
  pose proof (uchar_load_frame _ _ _ _ _
    (os_int_enter_fields_raw_nesting_load sg state owned Hraw) Hjoin) as Hn.
  unfold os_int_enter_heap_writes.
  destruct Hsource as [heap Hread|heap nesting Hread Hnest Hsat|heap nesting final Hread Hnest Hlt Hwrite].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    destruct state.(SchedState).(isRunning); [discriminate|].
    split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
    destruct state.(SchedState).(isRunning); [|discriminate].
    assert ((state.(IntrState).(intNesting) <? 255) = false) as ->
      by (apply Z.ltb_ge; exact Hsat).
    split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Heq.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as ->.
    destruct state.(SchedState).(isRunning); [|discriminate].
    assert ((state.(IntrState).(intNesting) <? 255) = true) as ->
      by (apply Z.ltb_lt; exact Hlt).
    exact Hwrite.
Qed.

Lemma os_int_exit_counter_fields_raw_frame_observation :
  forall sg state (frame : Assertion) before observed after,
  (UCOS2_fields_raw_rep sg state ** frame) before ->
  os_int_exit_masked_counter_fragment sg before observed after ->
  observed = state.(SchedState).(isRunning) /\
  kernel_heap_execution (os_int_exit_counter_heap_writes sg observed state) before after.
Proof.
  intros sg state frame before observed after [owned [rest [Hjoin [Hraw Hrest]]]] Hsource.
  pose proof (uchar_load_frame _ _ _ _ _
    (os_int_exit_fields_raw_running_load sg state owned Hraw) Hjoin) as Hr.
  pose proof (uchar_load_frame _ _ _ _ _
    (os_int_exit_fields_raw_nesting_load sg state owned Hraw) Hjoin) as Hn.
  destruct Hsource as [heap Hread|heap nesting final Hread Hnest Hrun].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Hvalue.
    destruct state.(SchedState).(isRunning); [discriminate|].
    split; [reflexivity|]. split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hr) as Hvalue.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest Hn) as Hcount.
    destruct state.(SchedState).(isRunning); [|discriminate].
    split; [reflexivity|]. subst nesting; exact Hrun.
Qed.

Lemma kernel_counter_c_fields_raw_post : forall operation sg state heap,
  UCOS2_fields_raw_rep sg state heap ->
  exists final,
    kernel_heap_execution (kernel_counter_c_writes operation sg state) heap final /\
    UCOS2_fields_raw_rep sg (kernel_counter_c_state operation state) final.
Proof.
  intros [|observed] sg state heap Hraw.
  - exact (os_int_enter_source_heap_fields_raw_post sg state heap Hraw).
  - exact (os_int_exit_counter_heap_fields_raw_post sg observed state heap Hraw).
Qed.

Lemma kernel_counter_c_fields_raw_transport : forall operation sg state (frame : Assertion)
  before after,
  kernel_counter_c_code operation sg before after ->
  (UCOS2_fields_raw_rep sg state ** frame) before ->
  (UCOS2_fields_raw_rep sg (kernel_counter_c_state operation state) ** frame) after.
Proof.
  intros operation sg state frame before after Hcode Hpre.
  assert (Hrun : kernel_heap_execution (kernel_counter_c_writes operation sg state) before after).
  { destruct operation as [|observed].
    - exact (os_int_enter_fields_raw_frame_writes sg state frame before after Hpre Hcode).
    - exact (proj2 (os_int_exit_counter_fields_raw_frame_observation
        sg state frame before observed after Hpre Hcode)). }
  destruct Hpre as [owned [rest [Hjoin [Hraw Hframe]]]].
  destruct (kernel_counter_c_fields_raw_post operation sg state owned Hraw)
    as [owned_after [Howned Hpost]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Howned Hjoin)
    as [produced [Hwhole Hfinal]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exists owned_after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

Record kernel_counter_c_completion operation sg state (frame : Assertion) before after
  (code : kernel_counter_c_code operation sg before after) : Prop := {
  kernel_counter_c_before_owned : (UCOS2_fields_raw_rep sg state ** frame) before;
  kernel_counter_c_after_owned :
    (UCOS2_fields_raw_rep sg (kernel_counter_c_state operation state) ** frame) after
}.

Lemma kernel_counter_c_completion_from_execution : forall operation sg state frame before after
  (code : kernel_counter_c_code operation sg before after),
  (UCOS2_fields_raw_rep sg state ** frame) before ->
  kernel_counter_c_completion operation sg state frame before after code.
Proof.
  intros operation sg state frame before after code Hpre; constructor; [exact Hpre|].
  eapply kernel_counter_c_fields_raw_transport; eassumption.
Qed.

Lemma kernel_counter_c_completion_from_c_post : forall operation sg state frame before after
  (code : kernel_counter_c_code operation sg before after),
  (UCOS2_fields_raw_rep sg state ** frame) before ->
  (UCOS2_fields_raw_rep sg (kernel_counter_c_state operation state) ** frame) after ->
  kernel_counter_c_completion operation sg state frame before after code.
Proof. intros; constructor; assumption. Qed.

Section KernelPublicationCSegment.
Context {external platform port} (abi : Armv7aContinuationABI external platform port)
  (local : Armv7aContinuation -> Assertion).

Record kernel_publication_c_completion sg publication state (frame : Assertion) before after
  (code : task_tcb_init_publication_tail_fragment sg
    (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after)
  (effect : kernel_client_step (task_create_stack_publication_client publication) sg state
    (task_create_stack_publication_state sg publication state)) : Prop := {
  kernel_publication_c_before_owned :
    (kernel_client_continuation_fields_publication abi local sg publication state ** frame) before;
  kernel_publication_c_after_owned :
    (kernel_client_continuation_fields_world abi local sg
      (task_create_stack_publication_state sg publication state) ** frame) after
}.

Lemma kernel_publication_c_completion_from_execution : forall sg publication state frame before after
  (code : task_tcb_init_publication_tail_fragment sg
    (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after),
  (kernel_client_continuation_fields_publication abi local sg publication state ** frame) before ->
  exists effect, kernel_publication_c_completion sg publication state frame before after code effect.
Proof.
  intros sg publication state frame before after code Hpre.
  assert (Hsplit :
    kernel_client_continuation_fields_publication abi local sg publication state ** frame |--
    coq_prop (UCOS2_state_inv sg state /\ task_stack_live_coverage state.(TskState) None /\
      task_create_stack_publication_input sg publication state /\
      0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
      0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
    (task_tcb_init_publication_fields_tail_storage sg (task_create_stack_publication_args publication)
       state publication.(stack_publication_slot) publication.(stack_publication_image) **
     (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
      local (task_create_stack_publication_continuation publication) **
      store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
        state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame))).
  { unfold kernel_client_continuation_fields_publication; entailer!. }
  destruct (Hsplit before Hpre) as [[Hvalid [Hcoverage [Hinput [Hpriority Hpointer]]]] Hheap].
  destruct (kernel_task_publication_continuation_fields_source external platform port abi sg
    publication state local None frame before after Hvalid Hinput Hcoverage Hpriority Hpointer
    Hheap code) as [effect [Hcovered Howned]].
  exists effect; constructor; [exact Hpre|].
  match type of Howned with ?P after =>
    assert (Hmerge : P |-- kernel_client_continuation_fields_world abi local sg
      (task_create_stack_publication_state sg publication state) ** frame)
  end.
  { unfold kernel_client_continuation_fields_world, kernel_continuation_inv; entailer!. }
  exact (Hmerge after Howned).
Qed.

Lemma kernel_publication_c_completion_preserves_observer :
  forall sg publication state frame before after code effect observer origin,
  kernel_publication_c_completion sg publication state frame before after code effect ->
  task_invocation_active state.(TskState) observer origin ->
  sched_observer_current_cache origin state ->
  task_invocation_active (task_create_stack_publication_state sg publication state).(TskState)
    observer origin /\
  sched_observer_current_cache origin (task_create_stack_publication_state sg publication state).
Proof.
  intros sg publication state frame before after code effect observer origin [Hpre Hpost] Hactive Hcache.
  assert (Hvalid : UCOS2_state_inv sg state).
  { destruct Hpre as [owned [rest [Hjoin [[Hfacts Howned] Hrest]]]]; exact (proj1 Hfacts). }
  split.
  - exact (kernel_client_preserves_continuation _ (task_create_stack_publication_certificate publication)
      sg state (task_create_stack_publication_state sg publication state) observer origin
      Hvalid effect eq_refl Hactive).
  - eapply task_create_stack_publication_preserves_observer_cache; eassumption.
Qed.

Lemma kernel_publication_c_completion_lifetime_result :
  forall sg publication state frame before after code effect observer origin,
  kernel_publication_c_completion sg publication state frame before after code effect ->
  task_observer_lifetime_result observer origin state.(TskState)
    (task_create_stack_publication_state sg publication state).(TskState) false.
Proof.
  intros sg publication state frame before after code effect observer origin Hcompletion.
  apply task_observer_lifetime_result_not_stopped.
  destruct (task_create_stack_publication_raw_projection sg publication state
    (task_create_stack_publication_state sg publication state) effect) as [Hraw Heq].
  rewrite Heq.
  eapply task_observer_lifetime_transport_trans with
    (middle := (task_create_stack_publication_raw_state sg publication state).(TskState)).
  - destruct Hraw as [Hguard [Hnames Hraw_eq]].
    rewrite Hraw_eq.
    apply task_commit_observer_lifetime_transport; exact (proj1 Hguard).
  - apply task_observer_lifetime_transport_fields; reflexivity.
Qed.
End KernelPublicationCSegment.

(** The terminal C callee begins at the ready checkpoint.  The original
    OSIntExit entry remains a separate parameter in its actual transfer.
    The surrounding C prefix must connect to this cut; no physical/ARM
    prefix is made a second prerequisite of this C contract graph. *)
Record kernel_irq_transfer_c_completion (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) sg handler saved entry transfer (frame : Assertion)
  before after : Prop := {
  kernel_irq_transfer_c_before_owned :
    (os_int_exit_transfer_pre
      (task_sw_hook_call_environment environment).(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      critical sg handler saved entry ** frame) before;
  kernel_irq_transfer_c_after_owned :
    (os_int_exit_transfer_post
      (task_sw_hook_call_environment environment).(task_stack_call_external)
      environment.(task_stack_call_port) sg handler saved entry transfer ** frame) after
}.

Lemma kernel_irq_transfer_c_completion_from_c_post :
  forall environment critical sg handler saved entry transfer frame before after,
  (os_int_exit_transfer_pre
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    critical sg handler saved entry ** frame) before ->
  (os_int_exit_transfer_post
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler saved entry transfer ** frame) after ->
  kernel_irq_transfer_c_completion environment critical sg handler saved entry transfer frame before after.
Proof. intros; constructor; assumption. Qed.

Lemma kernel_irq_transfer_c_completion_source :
  forall environment critical sg handler saved entry transfer frame before after,
  kernel_irq_transfer_c_completion environment critical sg handler saved entry transfer frame before after ->
  os_int_exit_transfer_source
    (task_sw_hook_call_environment environment).(task_stack_call_external)
    environment.(task_stack_call_port) sg handler entry transfer.
Proof.
  intros environment critical sg handler saved entry transfer frame before after [Hpre Hpost].
  destruct Hpost as [owned [rest [Hjoin [[Hsource Howned] Hrest]]]]; exact Hsource.
Qed.

Lemma kernel_irq_transfer_c_completion_preserves_observer :
  forall environment critical sg handler saved entry transfer frame before after observer origin,
  kernel_irq_transfer_c_completion environment critical sg handler saved entry transfer frame before after ->
  task_invocation_active (os_int_exit_ready_checkpoint true entry).(TskState) observer origin ->
  task_invocation_active (os_int_exit_installed_state transfer).(TskState) observer origin /\
  sched_observer_current_cache origin (os_int_exit_installed_state transfer).
Proof.
  intros environment critical sg handler saved entry transfer frame before after observer origin Hcall Hactive.
  exact (os_int_exit_configured_transfer_preserves_observer_cache environment sg handler entry transfer
    observer origin (kernel_irq_transfer_c_completion_source environment critical sg handler saved entry
      transfer frame before after Hcall) Hactive).
Qed.

Lemma kernel_irq_transfer_c_completion_lifetime_result :
  forall environment critical sg handler saved entry transfer frame before after observer origin,
  kernel_irq_transfer_c_completion environment critical sg handler saved entry transfer frame before after ->
  task_observer_lifetime_result observer origin
    (os_int_exit_ready_checkpoint true entry).(TskState)
    (os_int_exit_installed_state transfer).(TskState) false.
Proof.
  intros environment critical sg handler saved entry transfer frame before after observer origin Hcall.
  pose proof (kernel_irq_transfer_c_completion_source environment critical sg handler saved entry
    transfer frame before after Hcall) as Hsource.
  pose proof (os_int_exit_configured_transfer_state_frame environment sg handler entry transfer Hsource)
    as [Hlookup [Hlife Hrest]].
  apply task_observer_lifetime_result_not_stopped.
  apply task_observer_lifetime_transport_fields; [exact Hlife|].
  intro slot; rewrite Hlookup; reflexivity.
Qed.

Section KernelBuiltinCSegments.
Context (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (local : Armv7aContinuation -> Assertion) (sg : StableGlobVars).
Let abi := environment.(task_stack_call_continuations).

Inductive kernel_builtin_c_segment :
  UCOS2_Verify_State -> model -> UCOS2_Verify_State -> model -> Assertion -> Assertion -> Prop :=
| KernelBuiltinCCounter : forall operation state frame before after code,
    kernel_counter_c_completion operation sg state frame before after code ->
    kernel_builtin_c_segment state before (kernel_counter_c_state operation state) after
      (UCOS2_fields_raw_rep sg state ** frame)
      (UCOS2_fields_raw_rep sg (kernel_counter_c_state operation state) ** frame)
| KernelBuiltinCPublication : forall publication state frame before after code effect,
    kernel_publication_c_completion abi local sg publication state frame before after code effect ->
    kernel_builtin_c_segment state before (task_create_stack_publication_state sg publication state) after
      (kernel_client_continuation_fields_publication abi local sg publication state ** frame)
      (kernel_client_continuation_fields_world abi local sg
        (task_create_stack_publication_state sg publication state) ** frame)
| KernelBuiltinCIRQTransfer : forall handler saved entry transfer frame before after,
    kernel_irq_transfer_c_completion environment critical sg handler saved entry transfer frame before after ->
    kernel_builtin_c_segment (os_int_exit_ready_checkpoint true entry) before
      (os_int_exit_installed_state transfer) after
      (os_int_exit_transfer_pre
        (task_sw_hook_call_environment environment).(task_stack_call_external)
        environment.(task_stack_call_platform) environment.(task_stack_call_port)
        critical sg handler saved entry ** frame)
      (os_int_exit_transfer_post
        (task_sw_hook_call_environment environment).(task_stack_call_external)
        environment.(task_stack_call_port) sg handler saved entry transfer ** frame).

Lemma kernel_builtin_c_segment_resources : forall state before returned after input output,
  kernel_builtin_c_segment state before returned after input output ->
  input before /\ output after.
Proof.
  intros state before returned after input output Hsegment; destruct Hsegment; destruct H; split; assumption.
Qed.

Lemma kernel_builtin_c_segment_preserves_observer : forall state before returned after input output,
  kernel_builtin_c_segment state before returned after input output ->
  forall observer origin,
  task_invocation_active state.(TskState) observer origin ->
  sched_observer_current_cache origin state ->
  task_invocation_active returned.(TskState) observer origin /\
  sched_observer_current_cache origin returned.
Proof.
  intros state before returned after input output Hsegment; destruct Hsegment;
    intros observer origin Hactive Hcache.
  - destruct operation; split; assumption.
  - eapply kernel_publication_c_completion_preserves_observer; eassumption.
  - eapply kernel_irq_transfer_c_completion_preserves_observer; eassumption.
Qed.

Lemma kernel_builtin_c_segment_lifetime_result : forall state before returned after input output,
  kernel_builtin_c_segment state before returned after input output ->
  forall observer origin,
  task_observer_lifetime_result observer origin state.(TskState) returned.(TskState) false.
Proof.
  intros state before returned after input output Hsegment; destruct Hsegment; intros observer origin.
  - apply task_observer_lifetime_result_not_stopped.
    destruct operation; apply task_observer_lifetime_transport_refl.
  - eapply kernel_publication_c_completion_lifetime_result; eassumption.
  - eapply kernel_irq_transfer_c_completion_lifetime_result; eassumption.
Qed.
End KernelBuiltinCSegments.


















End BuiltinComponent.
Module InstallComponent.









































Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma os_sched_install_fields_client_resources :
  forall external sg context outgoing state incoming resumed
    (resource : (TaskID * nat) -> (TaskStackRegion * TaskStackFragments) -> Assertion)
    (frame : Assertion) before after sp,
  os_sched_saved_stack_binding context outgoing state ->
  os_sched_destination_binding external context outgoing state incoming resumed ->
  sched_high_ready_consistency state.(TskState) state.(SchedState) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (UCOS2_fields_inv sg state **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource state.(TskState).(parkedTaskStacks) ** frame) before ->
  sched_install_heap_fragment sg before after (task_slot_addr sg incoming.(stackLeaseSlot)) sp ->
  let current := os_sched_install_context context outgoing incoming state in
  kernel_client_step (os_sched_install_client external context outgoing incoming resumed)
    sg state current /\
  task_current_at current incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
  external.(os_sched_arch_restore_source) incoming sp resumed /\
  (UCOS2_fields_inv sg current ** task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
   resource (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
   store_parked_continuations resource current.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external sg context outgoing state incoming resumed resource frame before after sp
    Hsaved Hdestination Hhigh Haddress Hpre Hactual current.
  destruct (os_sched_install_fields_continuation_map_resources external sg context outgoing state
    incoming resumed resource frame before Hsaved Hdestination Haddress Hpre)
    as [produced [actual_sp [Hrun [[Hcurrent Hrestore] Hpost]]]].
  destruct (sched_install_heap_fragment_deterministic sg before produced after
    (task_slot_addr sg incoming.(stackLeaseSlot)) actual_sp
    (task_slot_addr sg incoming.(stackLeaseSlot)) sp Hrun Hactual)
    as [Hheap [Hpointer Hsp]].
  subst produced actual_sp.
  exact (conj (conj Hsaved (conj Hdestination (conj Hhigh eq_refl)))
    (conj Hcurrent (conj Hrestore Hpost))).
Qed.

Lemma os_sched_install_client_preserves_observer_cache :
  forall external context outgoing incoming resumed sg before after observer origin,
  kernel_client_step (os_sched_install_client external context outgoing incoming resumed)
    sg before after ->
  task_invocation_active before.(TskState) observer origin ->
  task_invocation_active after.(TskState) observer origin /\
    sched_observer_current_cache origin after.
Proof.
  intros external context outgoing incoming resumed sg before after observer origin
    [Hsaved [Hdestination [Hhigh ->]]] Hactive.
  split; [exact Hactive|].
  apply sched_current_consistency_implies_observer_cache.
  eapply os_sched_destination_installs_current_consistency; exact Hdestination.
Qed.

Record TaskInstallFieldsCall : Type := {
  task_install_fields_context : OsSchedCallContext;
  task_install_fields_outgoing : TaskStackFragments;
  task_install_fields_incoming : TaskStackLease;
  task_install_fields_resumed : TaskStackFragments;
  task_install_fields_entry : UCOS2_Verify_State
}.

Definition task_install_fields_current call :=
  os_sched_install_context call.(task_install_fields_context)
    call.(task_install_fields_outgoing) call.(task_install_fields_incoming)
    call.(task_install_fields_entry).

Section TaskInstallCCheckedOwners.
Context (environment : TaskStackCallEnvironment) (local : Armv7aContinuation -> Assertion).
Let abi := environment.(task_stack_call_continuations).
Definition task_install_fields_saved_resource call :=
  kernel_saved_continuation_entry abi call.(task_install_fields_entry).(TskState) local.

Definition task_install_fields_entry_owner sg call : Assertion :=
  let context := call.(task_install_fields_context) in
  let resource := task_install_fields_saved_resource call in
  UCOS2_fields_inv sg call.(task_install_fields_entry) **
  task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion)
    call.(task_install_fields_outgoing) **
  resource (task_stack_key context.(os_sched_call_stack))
    (context.(os_sched_call_stack).(stackLeaseRegion), call.(task_install_fields_outgoing)) **
  store_parked_continuations resource call.(task_install_fields_entry).(TskState).(parkedTaskStacks).

Definition task_install_fields_installed_owner sg call : Assertion :=
  let resource := task_install_fields_saved_resource call in
  let incoming := call.(task_install_fields_incoming) in
  UCOS2_fields_inv sg (task_install_fields_current call) **
  task_stack_fragments_rep incoming.(stackLeaseRegion) call.(task_install_fields_resumed) **
  resource (task_stack_key incoming) (incoming.(stackLeaseRegion), call.(task_install_fields_resumed)) **
  store_parked_continuations resource (task_install_fields_current call).(TskState).(parkedTaskStacks).

End TaskInstallCCheckedOwners.

(** The post-hook Task install is one real C segment.  The call record and
    owners below are the original checked fields module's exact objects;
    no registered-client or foreign-observer source is required. *)
Section TaskInstallCSegment.
Context (environment : TaskStackCallEnvironment) (local : Armv7aContinuation -> Assertion)
  (sg : StableGlobVars) (frame : Assertion).
Let external := environment.(task_stack_call_external).

Definition task_install_c_source call : Prop :=
  kernel_client_step (os_sched_install_client external call.(task_install_fields_context)
    call.(task_install_fields_outgoing) call.(task_install_fields_incoming)
    call.(task_install_fields_resumed)) sg call.(task_install_fields_entry)
    (task_install_fields_current call).

Definition task_install_c_post call sp : Assertion :=
  coq_prop (task_install_c_source call /\
    task_current_at (task_install_fields_current call)
      call.(task_install_fields_incoming).(stackLeaseSlot)
      call.(task_install_fields_incoming).(stackLeaseGeneration) /\
    external.(os_sched_arch_restore_source) call.(task_install_fields_incoming)
      sp call.(task_install_fields_resumed)) &&
  (task_install_fields_installed_owner environment local sg call ** frame).

(** Hactual is the original ordered heap-fragment proof, indexed by this
    same call's destination address and actual sp.  Hsource is the named
    install step from the same module post, not a new endpoint relation. *)
Inductive task_install_c_completion call before after sp
  (Hactual : sched_install_heap_fragment sg before after
    (task_slot_addr sg call.(task_install_fields_incoming).(stackLeaseSlot)) sp) :
  task_install_c_source call -> Prop :=
| TaskInstallCComplete : forall Hsource,
    tcb_field_address (task_slot_addr sg call.(task_install_fields_incoming).(stackLeaseSlot))
      TCBStkPtr = task_slot_addr sg call.(task_install_fields_incoming).(stackLeaseSlot) ->
    (task_install_fields_entry_owner environment local sg call ** frame) before ->
    task_current_at (task_install_fields_current call)
      call.(task_install_fields_incoming).(stackLeaseSlot)
      call.(task_install_fields_incoming).(stackLeaseGeneration) ->
    external.(os_sched_arch_restore_source) call.(task_install_fields_incoming)
      sp call.(task_install_fields_resumed) ->
    (task_install_fields_installed_owner environment local sg call ** frame) after ->
    task_install_c_completion call before after sp Hactual Hsource.

Definition task_install_c_segment call before after sp
  (Hactual : sched_install_heap_fragment sg before after
    (task_slot_addr sg call.(task_install_fields_incoming).(stackLeaseSlot)) sp) : Prop :=
  exists Hsource, task_install_c_completion call before after sp Hactual Hsource.

Lemma task_install_c_segment_from_actual_post : forall call before after sp Hactual,
  tcb_field_address (task_slot_addr sg call.(task_install_fields_incoming).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg call.(task_install_fields_incoming).(stackLeaseSlot) ->
  (task_install_fields_entry_owner environment local sg call ** frame) before ->
  task_install_c_post call sp after ->
  task_install_c_segment call before after sp Hactual.
Proof.
  intros call before after sp Hactual Haddress Hpre [[Hsource [Hcurrent Hrestore]] Hpost].
  exists Hsource; constructor; assumption.
Qed.

(** Concrete producer: the checked fields theorem consumes this original
    Hactual together with the real saved/destination/high/address facts.
    Its same-after-heap owner and named source populate the completion. *)
Lemma task_install_c_segment_from_actual_execution : forall call before after sp Hactual,
  os_sched_saved_stack_binding call.(task_install_fields_context)
    call.(task_install_fields_outgoing) call.(task_install_fields_entry) ->
  os_sched_destination_binding external call.(task_install_fields_context)
    call.(task_install_fields_outgoing) call.(task_install_fields_entry)
    call.(task_install_fields_incoming) call.(task_install_fields_resumed) ->
  sched_high_ready_consistency call.(task_install_fields_entry).(TskState)
    call.(task_install_fields_entry).(SchedState) ->
  tcb_field_address (task_slot_addr sg call.(task_install_fields_incoming).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg call.(task_install_fields_incoming).(stackLeaseSlot) ->
  (task_install_fields_entry_owner environment local sg call ** frame) before ->
  task_install_c_segment call before after sp Hactual.
Proof.
  intros call before after sp Hactual Hsaved Hdestination Hhigh Haddress Hpre.
  assert (Horder : task_install_fields_entry_owner environment local sg call ** frame |--
    UCOS2_fields_inv sg call.(task_install_fields_entry) **
    task_stack_fragments_rep call.(task_install_fields_context).(os_sched_call_stack).(stackLeaseRegion)
      call.(task_install_fields_outgoing) **
    task_install_fields_saved_resource environment local call
      (task_stack_key call.(task_install_fields_context).(os_sched_call_stack))
      (call.(task_install_fields_context).(os_sched_call_stack).(stackLeaseRegion),
        call.(task_install_fields_outgoing)) **
    store_parked_continuations (task_install_fields_saved_resource environment local call)
      call.(task_install_fields_entry).(TskState).(parkedTaskStacks) ** frame).
  { unfold task_install_fields_entry_owner; entailer!. }
  destruct (os_sched_install_fields_client_resources external sg call.(task_install_fields_context)
    call.(task_install_fields_outgoing) call.(task_install_fields_entry)
    call.(task_install_fields_incoming) call.(task_install_fields_resumed)
    (task_install_fields_saved_resource environment local call) frame before after sp
    Hsaved Hdestination Hhigh Haddress (Horder before Hpre) Hactual)
    as [Hsource [Hcurrent [Hrestore Hpost]]].
  assert (Howned_after :
    (task_install_fields_installed_owner environment local sg call ** frame) after).
  { match type of Hpost with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) end end.
    { unfold task_install_fields_installed_owner, task_install_fields_current; entailer!. }
    exact (Hclose after Hpost). }
  exists Hsource; constructor; assumption.
Qed.

Lemma task_install_c_segment_resources : forall call before after sp Hactual,
  task_install_c_segment call before after sp Hactual ->
  (task_install_fields_entry_owner environment local sg call ** frame) before /\
  (task_install_fields_installed_owner environment local sg call ** frame) after.
Proof.
  intros call before after sp Hactual [Hsource Hcompletion].
  destruct Hcompletion; split; assumption.
Qed.

(** The destination store establishes cache consistency.  Only the fixed
    observer's input active identity is needed; an input cache premise or
    a caller/observer inequality is unnecessary. *)
Lemma task_install_c_segment_preserves_observer :
  forall observer origin call before after sp Hactual,
  task_install_c_segment call before after sp Hactual ->
  task_invocation_active call.(task_install_fields_entry).(TskState) observer origin ->
  task_invocation_active (task_install_fields_current call).(TskState) observer origin /\
    sched_observer_current_cache origin (task_install_fields_current call).
Proof.
  intros observer origin call before after sp Hactual [Hsource Hcompletion] Hactive.
  eapply (os_sched_install_client_preserves_observer_cache external
    call.(task_install_fields_context) call.(task_install_fields_outgoing)
    call.(task_install_fields_incoming) call.(task_install_fields_resumed) sg
    call.(task_install_fields_entry) (task_install_fields_current call) observer origin);
    eassumption.
Qed.

(** Park/take changes the actual parked map only.  The used nodes and the
    complete registration/private/generation lifecycle remain unchanged;
    the inactive observer case therefore also cannot be resurrected. *)
Lemma task_install_c_segment_observer_lifetime_result :
  forall observer origin call before after sp Hactual,
  task_install_c_segment call before after sp Hactual ->
  task_observer_lifetime_result observer origin call.(task_install_fields_entry).(TskState)
    (task_install_fields_current call).(TskState) false.
Proof.
  intros observer origin call before after sp Hactual [Hsource Hcompletion].
  destruct (os_sched_install_client_state_frame external call.(task_install_fields_context)
    call.(task_install_fields_outgoing) call.(task_install_fields_incoming)
    call.(task_install_fields_resumed) sg call.(task_install_fields_entry)
    (task_install_fields_current call) Hsource) as [Hnodes [Hlifecycle Hrest]].
  apply task_observer_lifetime_result_not_stopped.
  apply task_observer_lifetime_transport_fields; [exact Hlifecycle|].
  intro slot; rewrite Hnodes; reflexivity.
Qed.
End TaskInstallCSegment.

(** Exact KernelCSegmentRelation shape, with a local frame for each actual
    atom.  The same Hactual remains available to the parent C-sequence. *)
Section TaskInstallCStep.
Context (environment : TaskStackCallEnvironment) (local : Armv7aContinuation -> Assertion)
  (sg : StableGlobVars).

Inductive task_install_c_step :
  UCOS2_Verify_State -> model -> Assertion -> bool ->
  UCOS2_Verify_State -> model -> Assertion -> Prop :=
| TaskInstallCStep : forall frame call before after sp Hactual,
    task_install_c_segment environment local sg frame call before after sp Hactual ->
    task_install_c_step call.(task_install_fields_entry) before
      (task_install_fields_entry_owner environment local sg call ** frame)
      false (task_install_fields_current call) after
      (task_install_fields_installed_owner environment local sg call ** frame).

Lemma task_install_c_step_resources : forall state before input stopped returned after output,
  task_install_c_step state before input stopped returned after output ->
  input before /\ output after.
Proof.
  intros state before input stopped returned after output Hstep; destruct Hstep.
  eapply task_install_c_segment_resources; exact H.
Qed.

Lemma task_install_c_step_preserves_observer :
  forall observer origin state before input stopped returned after output,
  task_install_c_step state before input stopped returned after output -> stopped = false ->
  task_invocation_active state.(TskState) observer origin /\ sched_observer_current_cache origin state ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros observer origin state before input stopped returned after output Hstep Hstop [Hactive Hcache].
  destruct Hstep; eapply task_install_c_segment_preserves_observer; eassumption.
Qed.

Lemma task_install_c_step_observer_lifetime_result :
  forall observer origin state before input stopped returned after output,
  task_install_c_step state before input stopped returned after output ->
  task_observer_lifetime_result observer origin state.(TskState) returned.(TskState) stopped.
Proof.
  intros observer origin state before input stopped returned after output Hstep; destruct Hstep.
  eapply task_install_c_segment_observer_lifetime_result; exact H.
Qed.
End TaskInstallCStep.









End InstallComponent.
Module WakeComponent.





























Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Import FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.























Import TaskStateDef SchedStateDef.
Local Open Scope Z_scope.














Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma task_observer_lifetime_transport_inactive : forall observer origin before after,
  task_observer_lifetime_transport observer origin before after ->
  task_observer_lifetime before observer origin ->
  ~ task_invocation_active before observer origin ->
  ~ task_invocation_active after observer origin.
Proof. intros observer origin before after Hstep Hlife Hgone Hactive; apply Hgone; exact (proj2 (Hstep Hlife) Hactive). Qed.
Lemma sched_observer_cache_fields_backward : forall origin before after,
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
  after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) ->
  (forall slot node, after.(TskState).(inUsedTaskStates) slot = Some node ->
    exists old, before.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(curPrio) = node.(curPrio)) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros [|slot generation] before after Hcurrent Hcache Hlookup Hbefore; [exact I|].
  intros node Hnode Hgeneration Hslot.
  destruct (Hlookup slot node Hnode) as [old [Hold [Hgen Hprio]]].
  rewrite Hcache, <- Hprio.
  apply (Hbefore old Hold); [rewrite Hgen; exact Hgeneration|].
  rewrite <- Hcurrent; exact Hslot.
Qed.
Lemma sched_observer_cache_update_task : forall origin before after tid old updated,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  updated.(curPrio) = old.(curPrio) ->
  after.(TskState) = glob_task_set_usedtask before.(TskState) tid updated ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
  after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros origin before after tid old updated Hold Hgen Hprio Htasks Hcurrent Hcache Hbefore.
  eapply sched_observer_cache_fields_backward; [exact Hcurrent|exact Hcache| |exact Hbefore].
  intros slot node Hnode; rewrite Htasks in Hnode.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot.
    injection Hnode as Hnode; subst node.
    exists old; split; [exact Hold|]. split; symmetry; assumption.
  - exists node; split; [exact Hnode|]. split; reflexivity.
Qed.
Lemma mutex_del_wake_preserves_observer_cache :
  forall sg origin before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros sg origin before eid kind message result priority after Hstep Hcache.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|] eqn:He; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |tid] eqn:Htable; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  eapply sched_observer_cache_update_task with
    (tid := tid) (old := old) (updated := task_event_wake_single old kind message result).
  - exact Hold.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [event_wake_state replace_SchedS SchedState]; unfold sched_wake_by_status.
    destruct task_status_is_suspended; reflexivity.
  - cbn [event_wake_state replace_SchedS SchedState]; unfold sched_wake_by_status.
    destruct task_status_is_suspended; reflexivity.
  - exact Hcache.
Qed.
(** Three named C updates.  Each constructor retains the literal helper
    result or the exact Tick node lookup; none accepts an arbitrary client. *)
Inductive kernel_wake_c_source (sg : StableGlobVars) :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| KernelWakeCFlagSource : forall entry pointer bits result schedule returned,
    flag_task_rdy sg entry pointer bits result = Some (schedule, returned) ->
    kernel_wake_c_source sg entry returned
| KernelWakeCEventSource : forall entry eid kind message result priority returned,
    event_task_rdy sg entry eid kind message result = Some (priority, returned) ->
    kernel_wake_c_source sg entry returned
| KernelWakeCTickSource : forall entry slot old,
    entry.(TskState).(inUsedTaskStates) slot = Some old ->
    kernel_wake_c_source sg entry (tick_task_step sg slot old entry).

Lemma kernel_wake_c_source_preserves_observer_cache : forall sg origin entry returned,
  kernel_wake_c_source sg entry returned ->
  sched_observer_current_cache origin entry -> sched_observer_current_cache origin returned.
Proof.
  intros sg origin entry returned Hsource Hcache; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply sched_observer_cache_update_task with (tid := waiter.(flagTask)) (old := old)
      (updated := task_flag_wake old bits result);
      try reflexivity; eassumption.
  - eapply mutex_del_wake_preserves_observer_cache; eassumption.
  - eapply sched_observer_cache_update_task with (tid := slot) (old := old) (updated := tick_task_update old).
    + exact H.
    + unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
    + exact (proj1 (proj2 (proj2 (tick_task_preserves_non_timeout_fields old)))).
    + apply tick_task_step_task_state_eq; exact H.
    + unfold tick_task_step, sched_wake_by_status; cbn zeta;
        repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
    + unfold tick_task_step, sched_wake_by_status; cbn zeta;
        repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
    + exact Hcache.
Qed.

Lemma kernel_wake_c_source_preserves_observer_active : forall sg entry returned observer origin,
  kernel_wake_c_source sg entry returned ->
  task_invocation_active entry.(TskState) observer origin ->
  task_invocation_active returned.(TskState) observer origin.
Proof.
  intros sg entry returned observer origin Hsource Hactive; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    change (task_invocation_active
      (glob_task_set_usedtask entry.(TskState) waiter.(flagTask) (task_flag_wake old bits result)) observer origin).
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive].
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hold|reflexivity|exact Hactive].
  - rewrite (tick_task_step_task_state_eq sg slot old entry H).
    eapply glob_task_set_usedtask_preserves_invocation_active; [exact H| |exact Hactive].
    unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
Qed.

Lemma kernel_wake_c_source_lifetime_result : forall sg entry returned observer origin,
  kernel_wake_c_source sg entry returned ->
  task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) false.
Proof.
  intros sg entry returned observer origin Hsource.
  apply task_observer_lifetime_result_not_stopped; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    eapply task_update_observer_lifetime_transport; [exact Hold|reflexivity].
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    eapply task_update_observer_lifetime_transport; [exact Hold|reflexivity].
  - rewrite (tick_task_step_task_state_eq sg slot old entry H).
    eapply task_update_observer_lifetime_transport; [exact H|].
    unfold tick_task_update; destruct (Z.eqb old.(dly) 0); reflexivity.
Qed.

(** Canonical typed arguments of the real event helper.  The raw helper
    remains valid for other byte inputs; these are the calls represented
    by event_task_rdy_source_client in the selected module semantics. *)
Lemma event_task_rdy_c_entry_source : forall sg entry eid event slot old kind message result,
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  event_task_rdy_entry sg entry.(TskState) eid event slot old ->
  event_task_rdy sg entry eid kind message result =
    Some (old.(curPrio), event_wake_state sg entry eid event slot old kind message result).
Proof.
  intros sg entry eid event slot old kind message result He Hentry.
  pose proof Hentry as [_ [_ [_ [_ [_ [_ Hold]]]]]].
  destruct (event_task_rdy_selection _ _ _ _ _ _ Hentry) as [Hpriority [Htable _]].
  unfold event_task_rdy; rewrite He, Hpriority, Htable, Hold; reflexivity.
Qed.

Definition event_ready_c_input sg entry eid event slot old kind result : Assertion :=
  event_task_rdy_pre sg entry.(TskState) eid event slot old
    (task_pend_mask kind) (encode_pend_status result)
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)).

Definition event_ready_c_output sg entry eid event slot old kind message result returned : Assertion :=
  event_task_rdy_post sg entry.(TskState) eid event slot old message
    (task_pend_mask kind) (encode_pend_status result)
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) returned.

(** Each constructor is a literal C pre/post completion, not a common
    closed world.  Flag keeps its node-return loan; Event keeps its raw
    helper cells; Tick uses the existing body merge on this exact heap. *)
Inductive kernel_wake_c_segment (sg : StableGlobVars) :
  UCOS2_Verify_State -> model -> Assertion -> UCOS2_Verify_State -> model -> Assertion -> Prop :=
| KernelWakeCFlagSegment : forall entry pointer waiter old bits result returned schedule checkpoint frame before after,
    (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) before ->
    flag_task_rdy sg entry pointer bits result = Some (schedule, checkpoint) ->
    ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
      (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame) after ->
    kernel_wake_c_segment sg entry before
      (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) checkpoint after
      ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
        (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame)
| KernelWakeCEventSegment : forall entry eid event slot old kind message result returned frame before after,
    entry.(EventState).(inUsedEventStates) eid = Some event ->
    event_task_rdy_entry sg entry.(TskState) eid event slot old ->
    (event_ready_c_input sg entry eid event slot old kind result ** frame) before ->
    (event_ready_c_output sg entry eid event slot old kind message result returned ** frame) after ->
    kernel_wake_c_segment sg entry before
      (event_ready_c_input sg entry eid event slot old kind result ** frame)
      (event_wake_state sg entry eid event slot old kind message result) after
      (event_ready_c_output sg entry eid event slot old kind message result returned ** frame)
| KernelWakeCTickSegment : forall entry slot old frame before after,
    entry.(TskState).(inUsedTaskStates) slot = Some old ->
    (UCOS2_inv sg entry ** frame) before ->
    (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame) after ->
    kernel_wake_c_segment sg entry before (UCOS2_inv sg entry ** frame)
      (tick_task_step sg slot old entry) after (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame).

Lemma flag_task_rdy_c_post_segment : forall sg entry pointer waiter old bits result returned frame before after,
  (flag_task_rdy_pre sg entry pointer waiter old bits ** frame) before ->
  (flag_task_rdy_post sg entry pointer waiter bits result returned ** frame) after ->
  exists (checkpoint : UCOS2_Verify_State) (schedule : bool),
    kernel_wake_c_segment sg entry before (flag_task_rdy_pre sg entry pointer waiter old bits ** frame)
      checkpoint after
      ((coq_prop (returned = (if schedule then 1 else 0) /\ valid_flag_state sg checkpoint.(FlagState)) &&
        (flag_task_rdy_resources sg checkpoint ** flag_node_return_loan sg.(osKernelConfig) waiter)) ** frame).
Proof.
  intros sg entry pointer waiter old bits result returned frame before after Hpre
    [hbody [hframe [Hjoin [[checkpoint [schedule [[Hstep [Hreturned Hvalid]] Hbody]]] Hframe]]]].
  exists checkpoint, schedule.
  refine (@KernelWakeCFlagSegment sg entry pointer waiter old bits result returned schedule checkpoint
    frame before after Hpre Hstep _).
  exists hbody, hframe; split; [exact Hjoin|]; split.
  - split; [exact (conj Hreturned Hvalid)|exact Hbody].
  - exact Hframe.
Qed.

Lemma event_task_rdy_c_post_segment :
  forall sg entry eid event slot old kind message result returned frame before after,
  entry.(EventState).(inUsedEventStates) eid = Some event ->
  (event_ready_c_input sg entry eid event slot old kind result ** frame) before ->
  (event_ready_c_output sg entry eid event slot old kind message result returned ** frame) after ->
  kernel_wake_c_segment sg entry before (event_ready_c_input sg entry eid event slot old kind result ** frame)
    (event_wake_state sg entry eid event slot old kind message result) after
    (event_ready_c_output sg entry eid event slot old kind message result returned ** frame).
Proof.
  intros sg entry eid event slot old kind message result returned frame before after He Hpre Hpost.
  pose proof Hpre as [hbody [hframe [Hjoin [[[Hentry Hbytes] Hbody] Hframe]]]].
  eapply KernelWakeCEventSegment; eassumption.
Qed.

Lemma time_tick_body_c_post_segment : forall sg entry slot old frame before after,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  time_tick_lookup entry slot old ->
  (UCOS2_inv sg entry ** frame) before ->
  ((time_tick_body_cells sg slot (tick_task_update old)
       (time_tick_ready_group (tick_task_step sg slot old entry))
       (time_tick_ready_rows (tick_task_step sg slot old entry)) **
     time_tick_body_residual sg entry slot old) ** frame) after ->
  kernel_wake_c_segment sg entry before (UCOS2_inv sg entry ** frame)
    (tick_task_step sg slot old entry) after (UCOS2_inv sg (tick_task_step sg slot old entry) ** frame).
Proof.
  intros sg entry slot old frame before after Hmulti Hlookup Hpre Hpost.
  pose proof Hpre as [hbody [hframe [Hjoin [[Hvalid Hbody] Hframe]]]].
  eapply KernelWakeCTickSegment; [exact Hlookup|exact Hpre|].
  destruct Hpost as [hout [houtside [Hjoin' [Hbody' Hframe']]]].
  exists hout, houtside; split; [exact Hjoin'|]; split; [|exact Hframe'].
  exact (time_tick_body_merge_task_step__task_update_backedges sg entry slot old
    Hmulti Hvalid Hlookup hout Hbody').
Qed.

Lemma kernel_wake_c_segment_source : forall sg entry before input returned after output,
  kernel_wake_c_segment sg entry before input returned after output -> kernel_wake_c_source sg entry returned.
Proof.
  intros sg entry before input returned after output Hsegment; destruct Hsegment.
  - eapply KernelWakeCFlagSource; eassumption.
  - eapply KernelWakeCEventSource; eapply event_task_rdy_c_entry_source; eassumption.
  - apply KernelWakeCTickSource; assumption.
Qed.

Lemma kernel_wake_c_segment_resources : forall sg entry before input returned after output,
  kernel_wake_c_segment sg entry before input returned after output -> input before /\ output after.
Proof. intros sg entry before input returned after output Hsegment; destruct Hsegment; auto. Qed.

Lemma kernel_wake_c_segment_preserves_observer : forall sg entry before input returned after output observer origin,
  kernel_wake_c_segment sg entry before input returned after output ->
  task_invocation_active entry.(TskState) observer origin /\ sched_observer_current_cache origin entry ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros sg entry before input returned after output observer origin Hsegment [Hactive Hcache].
  pose proof (kernel_wake_c_segment_source _ _ _ _ _ _ _ Hsegment) as Hsource; split.
  - eapply kernel_wake_c_source_preserves_observer_active; eassumption.
  - eapply kernel_wake_c_source_preserves_observer_cache; eassumption.
Qed.

Lemma kernel_wake_c_segment_lifetime_result : forall sg entry before input returned after output observer origin,
  kernel_wake_c_segment sg entry before input returned after output ->
  task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) false.
Proof.
  intros sg entry before input returned after output observer origin Hsegment.
  eapply kernel_wake_c_source_lifetime_result; eapply kernel_wake_c_segment_source; exact Hsegment.
Qed.













End WakeComponent.
Module StatusComponent.





























Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Import FlagPendSchedulerResources.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

























Import TaskStateDef SchedStateDef.
Local Open Scope Z_scope.














Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma task_observer_lifetime_transport_inactive : forall observer origin before after,
  task_observer_lifetime_transport observer origin before after ->
  task_observer_lifetime before observer origin ->
  ~ task_invocation_active before observer origin ->
  ~ task_invocation_active after observer origin.
Proof. intros observer origin before after Hstep Hlife Hgone Hactive; apply Hgone; exact (proj2 (Hstep Hlife) Hactive). Qed.
Lemma sched_observer_cache_fields_backward : forall origin before after,
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
  after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) ->
  (forall slot node, after.(TskState).(inUsedTaskStates) slot = Some node ->
    exists old, before.(TskState).(inUsedTaskStates) slot = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(curPrio) = node.(curPrio)) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros [|slot generation] before after Hcurrent Hcache Hlookup Hbefore; [exact I|].
  intros node Hnode Hgeneration Hslot.
  destruct (Hlookup slot node Hnode) as [old [Hold [Hgen Hprio]]].
  rewrite Hcache, <- Hprio.
  apply (Hbefore old Hold); [rewrite Hgen; exact Hgeneration|].
  rewrite <- Hcurrent; exact Hslot.
Qed.
Lemma sched_observer_cache_update_task : forall origin before after tid old updated,
  before.(TskState).(inUsedTaskStates) tid = Some old ->
  updated.(taskGeneration) = old.(taskGeneration) ->
  updated.(curPrio) = old.(curPrio) ->
  after.(TskState) = glob_task_set_usedtask before.(TskState) tid updated ->
  after.(SchedState).(curTaskID) = before.(SchedState).(curTaskID) ->
  after.(SchedState).(curSchedPrio) = before.(SchedState).(curSchedPrio) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros origin before after tid old updated Hold Hgen Hprio Htasks Hcurrent Hcache Hbefore.
  eapply sched_observer_cache_fields_backward; [exact Hcurrent|exact Hcache| |exact Hbefore].
  intros slot node Hnode; rewrite Htasks in Hnode.
  cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot.
    injection Hnode as Hnode; subst node.
    exists old; split; [exact Hold|]. split; symmetry; assumption.
  - exists node; split; [exact Hnode|]. split; reflexivity.
Qed.
Lemma mutex_del_wake_preserves_observer_cache :
  forall sg origin before eid kind message result priority after,
  event_task_rdy sg before eid kind message result = Some (priority, after) ->
  sched_observer_current_cache origin before -> sched_observer_current_cache origin after.
Proof.
  intros sg origin before eid kind message result priority after Hstep Hcache.
  unfold event_task_rdy in Hstep.
  destruct (before.(EventState).(inUsedEventStates) eid) as [event|] eqn:He; [|discriminate].
  destruct (before.(TskState).(prioTbl) (event_wait_priority before.(TskState) event))
    as [| |tid] eqn:Htable; try discriminate.
  destruct (before.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  eapply sched_observer_cache_update_task with
    (tid := tid) (old := old) (updated := task_event_wake_single old kind message result).
  - exact Hold.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [event_wake_state replace_SchedS SchedState]; unfold sched_wake_by_status.
    destruct task_status_is_suspended; reflexivity.
  - cbn [event_wake_state replace_SchedS SchedState]; unfold sched_wake_by_status.
    destruct task_status_is_suspended; reflexivity.
  - exact Hcache.
Qed.
(** These are the original acquired critical effects.  Error codes and
    local schedule decisions stay in their constructor payloads; the
    complete APIs' Restore and Scheduler calls are separate C segments. *)
Inductive kernel_status_c_source (sg : StableGlobVars) :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| KernelStatusCSuspendSource : forall entry priority result returned,
    task_suspend_critical sg priority entry result returned ->
    kernel_status_c_source sg entry returned
| KernelStatusCResumeSource : forall entry priority result returned,
    task_resume_critical sg priority entry result returned ->
    kernel_status_c_source sg entry returned
| KernelStatusCSemAcceptSource : forall entry eid count returned,
    sem_accept_critical sg eid entry count returned ->
    kernel_status_c_source sg entry returned.

Lemma kernel_status_c_source_current_eq : forall sg entry returned,
  kernel_status_c_source sg entry returned ->
  returned.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID).
Proof.
  intros sg entry returned Hsource; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [old [_ [_ ->]]]; reflexivity.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct Hstep as [old [_ Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        unfold task_resume_state, sched_resume_task, sched_wake_by_status;
          cbn [replace_SchedS replace_TskS SchedState];
          repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
      * destruct Hstep as [_ ->]; reflexivity.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); reflexivity.
Qed.

Lemma kernel_status_c_source_preserves_observer_cache : forall sg entry returned observer origin,
  kernel_status_c_source sg entry returned ->
  task_invocation_active entry.(TskState) observer origin ->
  sched_observer_current_cache origin entry -> sched_observer_current_cache origin returned.
Proof.
  intros sg entry returned observer origin Hsource Hactive Hcache.
  eapply sched_current_frame_preserves_observer_cache; [exact Hactive| | |exact Hcache].
  - eapply kernel_status_c_source_current_eq; exact Hsource.
  - intro Hcurrent; destruct Hsource.
    + eapply task_suspend_critical_preserves_current_consistency; eassumption.
    + eapply task_resume_critical_preserves_current_consistency; eassumption.
    + destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); exact Hcurrent.
Qed.

Lemma kernel_status_c_source_preserves_observer_active : forall sg entry returned observer origin,
  kernel_status_c_source sg entry returned ->
  task_invocation_active entry.(TskState) observer origin ->
  task_invocation_active returned.(TskState) observer origin.
Proof.
  intros sg entry returned observer origin Hsource Hactive; destruct Hsource.
  - exact (proj2 (task_suspend_critical_lifecycle_frame _ _ _ _ _ H) observer origin Hactive).
  - exact (proj2 (task_resume_critical_lifecycle_frame _ _ _ _ _ H) observer origin Hactive).
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount)); exact Hactive.
Qed.

Lemma kernel_status_c_source_lifetime_result : forall sg entry returned observer origin,
  kernel_status_c_source sg entry returned ->
  task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) false.
Proof.
  intros sg entry returned observer origin Hsource.
  apply task_observer_lifetime_result_not_stopped; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; apply task_observer_lifetime_transport_refl.
    + destruct Hstep as [_ ->]; apply task_observer_lifetime_transport_refl.
    + destruct Hstep as [old [Hold [_ ->]]].
      eapply task_update_observer_lifetime_transport; [exact Hold|reflexivity].
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; apply task_observer_lifetime_transport_refl.
    + destruct Hstep as [_ ->]; apply task_observer_lifetime_transport_refl.
    + destruct Hstep as [old [Hold Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        eapply task_update_observer_lifetime_transport; [exact Hold|reflexivity].
      * destruct Hstep as [_ ->]; apply task_observer_lifetime_transport_refl.
  - destruct H as [event [fields [_ [_ [_ ->]]]]]; destruct (Z.ltb 0 fields.(semCount));
      apply task_observer_lifetime_transport_refl.
Qed.

(** The critical body's real global owner, with its token, saved locals,
    context/capsules and caller resources left in the actual C frame.
    Allocation and publication loans are deliberately not forced into this
    owner: their own stage contracts have different resource shapes. *)
Record kernel_status_c_segment sg entry before returned after (frame : Assertion) : Prop := {
  kernel_status_c_segment_code : kernel_status_c_source sg entry returned;
  kernel_status_c_segment_input : (UCOS2_inv sg entry ** frame) before;
  kernel_status_c_segment_output : (UCOS2_inv sg returned ** frame) after
}.

Lemma task_suspend_critical_c_post_segment : forall sg entry before priority result returned after frame,
  (UCOS2_inv sg entry ** frame) before ->
  (coq_prop (task_suspend_critical sg priority entry result returned) &&
    (UCOS2_inv sg returned ** frame)) after ->
  kernel_status_c_segment sg entry before returned after frame.
Proof.
  intros sg entry before priority result returned after frame Hpre [Hcode Hpost].
  constructor; [eapply KernelStatusCSuspendSource; exact Hcode|exact Hpre|exact Hpost].
Qed.

Lemma task_resume_critical_c_post_segment : forall sg entry before priority result returned after frame,
  (UCOS2_inv sg entry ** frame) before ->
  (coq_prop (task_resume_critical sg priority entry result returned) &&
    (UCOS2_inv sg returned ** frame)) after ->
  kernel_status_c_segment sg entry before returned after frame.
Proof.
  intros sg entry before priority result returned after frame Hpre [Hcode Hpost].
  constructor; [eapply KernelStatusCResumeSource; exact Hcode|exact Hpre|exact Hpost].
Qed.

Lemma sem_accept_critical_c_post_segment : forall sg entry before eid count returned after frame,
  (UCOS2_inv sg entry ** frame) before ->
  (coq_prop (sem_accept_critical sg eid entry count returned) &&
    (UCOS2_inv sg returned ** frame)) after ->
  kernel_status_c_segment sg entry before returned after frame.
Proof.
  intros sg entry before eid count returned after frame Hpre [Hcode Hpost].
  constructor; [eapply KernelStatusCSemAcceptSource; exact Hcode|exact Hpre|exact Hpost].
Qed.

Lemma kernel_status_c_segment_resources : forall sg entry before returned after frame,
  kernel_status_c_segment sg entry before returned after frame ->
  (UCOS2_inv sg entry ** frame) before /\ (UCOS2_inv sg returned ** frame) after.
Proof. intros sg entry before returned after frame [Hsource Hpre Hpost]; auto. Qed.

Lemma kernel_status_c_segment_preserves_observer :
  forall sg entry before returned after frame observer origin,
  kernel_status_c_segment sg entry before returned after frame ->
  task_invocation_active entry.(TskState) observer origin /\ sched_observer_current_cache origin entry ->
  task_invocation_active returned.(TskState) observer origin /\ sched_observer_current_cache origin returned.
Proof.
  intros sg entry before returned after frame observer origin [Hsource Hpre Hpost] [Hactive Hcache].
  split.
  - eapply kernel_status_c_source_preserves_observer_active; eassumption.
  - eapply kernel_status_c_source_preserves_observer_cache; eassumption.
Qed.

Lemma kernel_status_c_segment_lifetime_result : forall sg entry before returned after frame observer origin,
  kernel_status_c_segment sg entry before returned after frame ->
  task_observer_lifetime_result observer origin entry.(TskState) returned.(TskState) false.
Proof.
  intros sg entry before returned after frame observer origin [Hsource Hpre Hpost].
  eapply kernel_status_c_source_lifetime_result; exact Hsource.
Qed.












End StatusComponent.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.
