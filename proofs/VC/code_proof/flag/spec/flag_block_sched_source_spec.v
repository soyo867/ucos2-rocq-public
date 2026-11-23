Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_execution Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
From SimpleC.SL Require Import Mem ConAssertion.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual OS_FlagBlock transformer obtains the updated node from the
    current-task lookup.  The result below records that lookup and the same
    returned state; it does not assume that the blocked task remains ready. *)
Lemma flag_block_result_state : forall sg before waiter timeout after,
  flag_block_spec.flag_block sg before waiter timeout = Some after ->
  exists slot old flags,
    before.(SchedState).(curTaskID) = Some slot /\
    before.(TskState).(inUsedTaskStates) slot = Some old /\
    flag_block_node sg before.(FlagState) waiter (task_slot_addr sg slot) = Some flags /\
    after = flag_block_spec.flag_block_state sg before slot old
      waiter.(flagNodeAddr) timeout flags.
Proof.
  intros sg before waiter timeout after Hstep.
  unfold flag_block_spec.flag_block in Hstep.
  destruct before.(SchedState).(curTaskID) as [slot|] eqn:Hcurrent; [|discriminate].
  destruct (before.(TskState).(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
  destruct (flag_block_node sg before.(FlagState) waiter (task_slot_addr sg slot))
    as [flags|] eqn:Hflags; [|discriminate].
  injection Hstep as Hafter.
  exists slot, old, flags; exact (conj eq_refl (conj Hold (conj Hflags (eq_sym Hafter)))).
Qed.

Lemma flag_block_task_priority_generation_eq : forall config old node timeout,
  (flag_block_task config old node timeout).(curPrio) = old.(curPrio) /\
  (flag_block_task config old node timeout).(taskGeneration) = old.(taskGeneration).
Proof.
  intros; unfold flag_block_task; destruct config.(cfgTaskDelete); split; reflexivity.
Qed.

Lemma flag_block_preserves_current_consistency : forall sg before waiter timeout after,
  flag_block_spec.flag_block sg before waiter timeout = Some after ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency after.(TskState) after.(SchedState).
Proof.
  intros sg before waiter timeout after Hstep Hconsistent.
  destruct (flag_block_result_state _ _ _ _ _ Hstep)
    as [slot [old [flags [Hcurrent [Hold [Hflags ->]]]]]].
  apply sched_current_consistency_fields_frame with
    (before_tasks := before.(TskState)) (before := before.(SchedState)).
  - reflexivity.
  - reflexivity.
  - intros current node Hslot Hnode.
    assert (current = slot) by congruence; subst current.
    rewrite Hold in Hnode; injection Hnode as Hnode; subst node.
    exists (flag_block_task sg.(osKernelConfig) old waiter.(flagNodeAddr) timeout).
    split.
    + cbn; rewrite Z.eqb_refl; reflexivity.
    + exact (proj1 (flag_block_task_priority_generation_eq _ _ _ _)).
  - exact Hconsistent.
Qed.

Lemma flag_block_preserves_task_source : forall sg before waiter timeout after call,
  flag_block_spec.flag_block sg before waiter timeout = Some after ->
  kernel_call_task_source call before -> kernel_call_task_source call after.
Proof.
  intros sg before waiter timeout after call Hstep [Horigin [Hactive Hcurrent]].
  destruct (flag_block_result_state _ _ _ _ _ Hstep)
    as [slot [old [flags [Hslot [Hold [Hflags ->]]]]]].
  split; [exact Horigin|]. split.
  - eapply glob_task_set_usedtask_preserves_invocation_active.
    + exact Hold.
    + exact (proj2 (flag_block_task_priority_generation_eq _ _ _ _)).
    + exact Hactive.
  - exact Hcurrent.
Qed.

Lemma flag_block_control_rely : forall sg before waiter timeout after,
  flag_block_spec.flag_block sg before waiter timeout = Some after ->
  kernel_call_control_rely sg before after.
Proof.
  intros sg before waiter timeout after Hstep.
  destruct (flag_block_result_state _ _ _ _ _ Hstep)
    as [slot [old [flags [_ [_ [_ ->]]]]]].
  split; reflexivity.
Qed.

Lemma flag_block_normal_return : forall sg before waiter timeout after call,
  flag_block_spec.flag_block sg before waiter timeout = Some after ->
  kernel_call_normal_return call before call after.
Proof.
  intros sg before waiter timeout after call Hstep.
  destruct (flag_block_result_state _ _ _ _ _ Hstep)
    as [slot [old [flags [_ [_ [_ ->]]]]]].
  split; [split; [reflexivity|split; reflexivity]|].
  intro Havailable; exact Havailable.
Qed.

Lemma flag_block_preserves_selection_enabled : forall sg before waiter timeout after,
  flag_block_spec.flag_block sg before waiter timeout = Some after ->
  os_sched_selection_enabled after = os_sched_selection_enabled before.
Proof.
  intros sg before waiter timeout after Hstep.
  destruct (flag_block_result_state _ _ _ _ _ Hstep)
    as [slot [old [flags [_ [_ [_ ->]]]]]].
  reflexivity.
Qed.

(** Consume the actual fields post without copying its heap.  The blocked
    stage and exact transformer outcome remain available alongside the
    task identity, current priority cache, and unchanged scheduling guards.
    Transport across the following Restore is a separate source obligation. *)
Lemma flag_block_call_fields_post_sched_source :
  forall sg before waiter old timeout call,
  kernel_call_task_source call before ->
  sched_current_consistency before.(TskState) before.(SchedState) ->
  os_sched_selection_enabled before = true ->
  flag_block_call_fields_post sg before waiter old timeout |--
  EX flags,
    let after := flag_execution.flag_block_state before waiter flags old timeout in
    coq_prop
      (flag_block_node sg before.(FlagState) waiter (flag_block_call_tcb sg waiter) = Some flags /\
       flag_block_spec.flag_block sg before waiter timeout = Some after /\
       sched_current_blocked_before_schedule after.(TskState) after.(SchedState)
         waiter.(flagTask) (task_prepare_flag_wait old waiter.(flagNodeAddr) timeout) /\
       kernel_call_task_source call after /\
       sched_current_consistency after.(TskState) after.(SchedState) /\
       os_sched_selection_enabled after = true /\
       kernel_call_normal_return call before call after /\
       kernel_call_control_rely sg before after) && UCOS2_fields_inv sg after.
Proof.
  intros sg before waiter old timeout call Hsource Hcurrent Henabled.
  unfold flag_block_call_fields_post.
  intros heap [flags [[Hnode [Hstep Hblocked]] Hfields]].
  exists flags; split; [|exact Hfields].
  split; [exact Hnode|]. split; [exact Hstep|]. split; [exact Hblocked|].
  split; [eapply flag_block_preserves_task_source; eassumption|].
  split; [eapply flag_block_preserves_current_consistency; eassumption|].
  split.
  - rewrite (flag_block_preserves_selection_enabled _ _ _ _ _ Hstep); exact Henabled.
  - split; [eapply flag_block_normal_return|eapply flag_block_control_rely]; exact Hstep.
Qed.
