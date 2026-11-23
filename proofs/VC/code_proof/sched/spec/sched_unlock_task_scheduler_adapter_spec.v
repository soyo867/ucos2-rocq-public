Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_callee_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_protocol_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_caller_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_active_control_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_idle_ready.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Import SchedulerCalleePhaseComponent SchedulerPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This is the actual OS_Sched_Task_Return input, with its global C
    address equalities supplied separately by the calling annotation.
    It does not replace the source proof with a stronger opaque Ensure. *)
Definition os_sched_unlock_task_scheduler_pre environment critical local active
  sg call mask state : Assertion :=
  coq_prop (kernel_sched_ready_clients critical /\
    FlagPendActiveProtocol.flag_pend_active_protocol sg active /\
    FlagPendActiveCallerControl.flag_pend_active_requires_control active /\
    state.(SchedState).(isRunning) = true /\ os_sched_active_local_stable active /\
    kernel_tcb_stack_field_layout sg /\ kernel_call_stack_available call state /\
    task_idle_ready sg state.(TskState)) &&
  os_sched_task_call_pre (task_sw_hook_call_environment environment) local active
    sg call mask state.

(** A source-established clear-wait task already provides the existing
    Fresh family. No new protocol constructor, copied task state, extra
    flag node, or non-Idle premise is needed for this adapter. *)
Lemma os_sched_unlock_source_fresh_registration : forall call state node,
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  flag_active_event_clear node -> node.(tcbFlagNode) = 0 ->
  flag_active_fresh_registration call call state.
Proof.
  intros call state node [Horigin [Hactive Hcurrent]] Hnode Hgen Hclear Hflag.
  exists node; split; [|exact Hflag].
  unfold flag_active_task_fields, task_tcb_init_stack_same_call.
  exact (conj (conj eq_refl (conj eq_refl eq_refl))
    (conj Horigin (conj Hnode (conj Hgen (conj Hactive Hclear))))).
Qed.

(** Split the SAME owned continuation map. Only the kernel Flag padding
    moves to the explicit frame. The map's state and local family do not
    change in either direction of this equivalence. *)
Lemma os_sched_unlock_closed_fields_padding : forall environment local sg active call mask state,
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_inv local sg active call mask state --||--
  (kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg active call mask state **
   flag_configured_padding_rep sg state.(FlagState)).
Proof.
  intros; unfold kernel_continuation_call_closed, kernel_continuation_inv.
  rewrite kernel_program_inv_fields_padding.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  split; Intros; entailer!; tauto.
Qed.

Lemma os_sched_unlock_native_fields_padding : forall environment critical saved_local sg call mask state,
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
    unmap_table_rep sg --||--
  (kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv (task_create_continuation_local saved_local)
    sg (task_stack_call_active_key call) call mask state **
   flag_configured_padding_rep sg state.(FlagState)).
Proof.
  intros; rewrite task_tcb_init_continuation_save_input_closed_world.
  apply os_sched_unlock_closed_fields_padding.
Qed.

Lemma os_sched_unlock_configured_closed_world_eq : forall environment resources local sg active call mask state,
  kernel_continuation_call_closed (task_sw_hook_call_environment environment).(task_stack_call_continuations)
    resources local sg active call mask state =
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    resources local sg active call mask state.
Proof. intros; reflexivity. Qed.

(** The current endpoint facts are the actual caller obligation. Idle
    readiness is not inferred from validity, and the outgoing caller is
    not required to be ready: current consistency is the scheduler cache
    binding, while Fresh concerns only this call's clear wait fields. *)
Lemma os_sched_unlock_task_scheduler_fresh_pre : forall environment critical local sg call mask state,
  kernel_sched_ready_clients critical -> kernel_tcb_stack_field_layout sg ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_stack_available call state -> task_idle_ready sg state.(TskState) ->
  os_sched_task_entry_observation call state -> os_sched_call_cut sg call state ->
  flag_active_fresh_registration call call state ->
  kernel_continuation_call_closed (task_sw_hook_call_environment environment).(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state |--
  os_sched_unlock_task_scheduler_pre environment critical local
    (PendPhaseCandidate.flag_pend_fresh_observation call) sg call mask state.
Proof.
  intros environment critical local sg call mask state Hclients Hlayout Hrunning Havailable Hidle
    Hentry Hcut Hfresh.
  pose proof (FlagPendActiveProtocol.flag_pend_active_protocol_fresh sg call) as Hprotocol.
  pose proof (FlagPendActiveProtocol.flag_pend_fresh_observation_prefix_stable call) as Hstable.
  pose proof (FlagPendActiveControl.flag_pend_fresh_observation_not_emp call state) as Hnonempty.
  unfold os_sched_unlock_task_scheduler_pre, os_sched_task_call_pre,
    os_sched_active_call_pre, PendPhaseCandidate.flag_pend_fresh_observation,
    FlagPendActiveCallerControl.flag_pend_active_requires_control.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|]).
  entailer!.
Qed.

Lemma os_sched_unlock_native_fresh_scheduler_pre : forall environment critical saved_local sg call mask state,
  kernel_sched_ready_clients critical -> kernel_tcb_stack_field_layout sg ->
  state.(SchedState).(isRunning) = true ->
  kernel_call_stack_available call state -> task_idle_ready sg state.(TskState) ->
  os_sched_task_entry_observation call state -> os_sched_call_cut sg call state ->
  flag_active_fresh_registration call call state ->
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** unmap_table_rep sg |--
  os_sched_unlock_task_scheduler_pre environment critical (task_create_continuation_local saved_local)
    (PendPhaseCandidate.flag_pend_fresh_observation call) sg call mask state **
  flag_configured_padding_rep sg state.(FlagState).
Proof.
  intros environment critical saved_local sg call mask state Hclients Hlayout Hrunning Havailable Hidle Hentry Hcut Hfresh.
  sep_apply_l_atomic (proj1 (os_sched_unlock_native_fields_padding environment critical saved_local sg call mask state)).
  rewrite <- (os_sched_unlock_configured_closed_world_eq environment kernel_program_fields_inv
    (task_create_continuation_local saved_local) sg (task_stack_call_active_key call) call mask state).
  sep_apply_l_atomic (os_sched_unlock_task_scheduler_fresh_pre environment critical
    (task_create_continuation_local saved_local) sg call mask state
    Hclients Hlayout Hrunning Havailable Hidle Hentry Hcut Hfresh).
  entailer!.
Qed.

(** Consume the actual stronger Scheduler post without erasing its
    ready/normal/control result or identifying next_local with the input
    family. The pure Fresh observation provides the same invocation's
    current clear-wait registration. The supplied frame stays on this heap. *)
Lemma os_sched_unlock_task_scheduler_fresh_return : forall environment critical sg original mask before
  (frame : Assertion),
  os_sched_task_history_return_post (task_sw_hook_call_environment environment) critical
    (PendPhaseCandidate.flag_pend_fresh_observation original) sg original mask before ** frame |--
  EX returned current next_local,
    coq_prop (os_sched_task_call_history (task_sw_hook_call_environment environment) critical
      sg original mask before returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      os_sched_task_current_ready returned current /\
      kernel_call_normal_return original before returned current /\
      kernel_call_control_rely sg before current /\
      flag_active_fresh_registration original returned current) &&
    (kernel_continuation_call_closed (task_sw_hook_call_environment environment).(task_stack_call_continuations)
       kernel_program_fields_inv next_local sg (task_stack_call_active_key returned) returned mask current ** frame).
Proof.
  intros; unfold os_sched_task_history_return_post,
    PendPhaseCandidate.flag_pend_fresh_observation; Intros returned current next_local.
  repeat first [rewrite logic_equiv_sepcon_coq_prop_andp |
    rewrite logic_equiv_coq_prop_andp_sepcon].
  repeat (apply coq_prop_andp_left; intro).
  Exists returned current next_local.
  apply UCOS2_C_Rules._derivable1_andp_intros; [apply derivable1s_coq_prop_r; tauto|].
  entailer!.
Qed.

(** Padding is NOT a single fixed global undef array. Its current map
    domain and optional byte images are observed. This is the existing
    exact criterion for reindexing a supplied padding owner. *)
Lemma os_sched_unlock_padding_projection_equiv : forall sg before after,
  (forall p,
    option_map (fun w => w.(flagWaitImage).(flagNodePadding)) (before.(flagWaitNodes) p) =
    option_map (fun w => w.(flagWaitImage).(flagNodePadding)) (after.(flagWaitNodes) p)) ->
  flag_configured_padding_rep sg before --||-- flag_configured_padding_rep sg after.
Proof.
  intros sg before after Hpadding; unfold flag_configured_padding_rep.
  destruct sg.(osKernelConfig).(cfgFlagEnabled); [apply flag_wait_nodes_padding_rep_equiv; exact Hpadding|].
  split; reflexivity.
Qed.

(** Rebuild a full CURRENT generic world only when its current padding
    has actually been supplied. This theorem changes no saved local and
    makes no claim that an old padding frame satisfies that premise. *)
Lemma os_sched_unlock_current_fields_merge_padding : forall environment local sg active call mask current,
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg active call mask current **
  flag_configured_padding_rep sg current.(FlagState) |--
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_inv local sg active call mask current.
Proof. intros; apply (proj2 (os_sched_unlock_closed_fields_padding environment local sg active call mask current)). Qed.
