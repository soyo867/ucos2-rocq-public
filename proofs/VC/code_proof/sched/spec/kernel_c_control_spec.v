(** Extracted from a passed fixed check; ordinary integration is pending. *)
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
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_api_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_idle_guard_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_builtin_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_c_primitive_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_create_c_segment_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_c_segment_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.











(** Control fields retained by these concrete C effects. Counter-changing
    Enter/Exit and task-delete phases are proved separately. *)
Module SelectedControlFrames.
Import EventStateDef StatusComponent WakeComponent CreationComponent
  EventCreationComponent QueueCreationComponent InstallComponent
  DeleteComponent PrimitiveComponent.

Lemma kernel_status_c_source_control : forall sg entry returned,
  kernel_status_c_source sg entry returned -> kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry returned Hsource; unfold kernel_call_control_rely; destruct Hsource.
  - destruct H as [cid [current [_ [_ [_ Hstep]]]]].
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg priority current))).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [old [_ [_ ->]]]; split; reflexivity.
  - destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority).
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [_ ->]; split; reflexivity.
    + destruct Hstep as [old [_ Hstep]]; destruct (task_is_suspended old.(stat)).
      * destruct Hstep as [_ ->].
        unfold task_resume_state, sched_resume_task, sched_wake_by_status;
          cbn [replace_SchedS replace_TskS SchedState IntrState];
          repeat match goal with |- context [if ?c then _ else _] => destruct c end;
          split; reflexivity.
      * destruct Hstep as [_ ->]; split; reflexivity.
  - destruct H as [event [fields [_ [_ [_ ->]]]]];
      destruct (Z.ltb 0 fields.(semCount)); split; reflexivity.
Qed.

Lemma kernel_status_c_segment_control : forall sg entry before returned after frame,
  kernel_status_c_segment sg entry before returned after frame ->
  kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry before returned after frame [Hsource Hpre Hpost].
  apply kernel_status_c_source_control; exact Hsource.
Qed.

Lemma kernel_task_creation_c_source_control : forall sg entry returned,
  kernel_task_creation_c_source sg entry returned -> kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry returned Hsource; unfold kernel_call_control_rely;
    destruct Hsource; try (split; reflexivity).
  - unfold task_create_critical in H; destruct (Z.ltb 0 entry.(IntrState).(intNesting)).
    + destruct H as [_ ->]; split; reflexivity.
    + destruct H as [_ Hstep]; destruct (entry.(TskState).(prioTbl) priority);
        destruct Hstep as [_ ->]; split; reflexivity.
  - destruct H2 as [_ ->]; split; reflexivity.
Qed.

Lemma kernel_task_creation_c_segment_control : forall sg entry before input returned after output,
  kernel_task_creation_c_segment sg entry before input returned after output ->
  kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry before input returned after output Hsegment.
  apply kernel_task_creation_c_source_control.
  eapply kernel_task_creation_c_segment_source; exact Hsegment.
Qed.

Lemma kernel_event_creation_c_source_control : forall sg entry returned,
  kernel_event_creation_c_source entry returned -> kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry returned Hsource; unfold kernel_call_control_rely;
    destruct Hsource; try (split; reflexivity).
  unfold event_create_allocate_critical in H; destruct (entry.(EventState).(unUsedEventStates)).
  - destruct H as [_ ->]; split; reflexivity.
  - destruct H as [image [_ [_ ->]]]; split; reflexivity.
Qed.

Lemma kernel_event_creation_c_segment_control : forall sg entry before input returned after output,
  kernel_event_creation_c_segment sg entry before input returned after output ->
  kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry before input returned after output Hsegment.
  apply kernel_event_creation_c_source_control.
  eapply kernel_event_creation_c_segment_source; exact Hsegment.
Qed.

Lemma kernel_queue_creation_c_source_control : forall sg entry returned,
  kernel_queue_creation_c_source sg entry returned -> kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry returned Hsource; unfold kernel_call_control_rely;
    destruct Hsource; [|split; reflexivity].
  destruct H0 as [allocation [Hget Hcode]]; destruct free;
    destruct Hcode as [_ ->]; split; reflexivity.
Qed.

Lemma kernel_queue_creation_c_segment_control : forall sg entry before input returned after output,
  kernel_queue_creation_c_segment sg entry before input returned after output ->
  kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry before input returned after output Hsegment.
  apply kernel_queue_creation_c_source_control.
  eapply kernel_queue_creation_c_segment_source; exact Hsegment.
Qed.

Lemma kernel_wake_c_source_control : forall sg entry returned,
  kernel_wake_c_source sg entry returned -> kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry returned Hsource; unfold kernel_call_control_rely; destruct Hsource.
  - destruct (flag_task_rdy_result _ _ _ _ _ _ _ H)
      as [waiter [flags [old [Hunlink [Hold [-> Hschedule]]]]]].
    split; reflexivity.
  - unfold event_task_rdy in H.
    destruct (entry.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
    destruct (entry.(TskState).(prioTbl) (event_wait_priority entry.(TskState) event))
      as [| |slot]; try discriminate.
    destruct (entry.(TskState).(inUsedTaskStates) slot) as [old|]; [|discriminate].
    injection H as Hpriority Hreturned; subst returned.
    unfold event_wake_state;
      cbn [replace_SchedS replace_EventS replace_TskS SchedState IntrState].
    split; [apply sched_wake_by_status_running_eq|reflexivity].
  - unfold tick_task_step, sched_wake_by_status; cbn zeta;
      repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      split; reflexivity.
Qed.

Lemma kernel_wake_c_segment_control : forall sg entry before input returned after output,
  kernel_wake_c_segment sg entry before input returned after output ->
  kernel_call_control_rely sg entry returned.
Proof.
  intros sg entry before input returned after output Hsegment.
  apply kernel_wake_c_source_control.
  eapply kernel_wake_c_segment_source; exact Hsegment.
Qed.

Lemma task_install_c_step_control :
  forall environment local sg state before input stopped returned after output,
  task_install_c_step environment local sg state before input stopped returned after output ->
  kernel_call_control_rely sg state returned.
Proof.
  intros environment local sg state before input stopped returned after output Hstep.
  destruct Hstep; split; reflexivity.
Qed.

Lemma task_delete_primitive_c_segment_control :
  forall environment critical sg state before input stopped returned after output,
  task_delete_primitive_c_segment environment critical sg
    state before input stopped returned after output ->
  kernel_call_control_rely sg state returned.
Proof.
  intros environment critical sg state before input stopped returned after output Hstep.
  destruct Hstep; split; reflexivity.
Qed.

Lemma flag_pend_task_primitive_c_step_control :
  forall environment critical sg state before input stopped returned after output,
  flag_pend_task_primitive_c_step environment critical sg
    state before input stopped returned after output ->
  kernel_call_control_rely sg state returned.
Proof.
  intros environment critical sg state before input stopped returned after output Hstep.
  destruct Hstep; try (split; reflexivity).
  destruct H; split; reflexivity.
Qed.
End SelectedControlFrames.
