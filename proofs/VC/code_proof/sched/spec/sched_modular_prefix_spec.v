Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected OS_Sched C prefix starts after Save and stops immediately
    before OSCtxSw or the final Restore. The two existing execution relations
    cover the interrupt-nesting guard, the lock guard, equal priority, and
    unequal priority with the actual selection/cache/counter writes. No C
    test or scheduling call is removed by this branch-indexed interface. *)
Definition os_sched_modular_prefix_execution (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (before after : model) : Prop :=
  if os_sched_requests_switch state
  then os_sched_source_switch_prefix_execution sg before after
  else os_sched_source_nonswitch_prefix_execution sg before after.

(** The sole readiness premise is conditional on the source guards enabling
    selection. The frame is retained only through this masked C prefix;
    this theorem asserts no frame rule across Save, Restore or OSCtxSw. *)
Lemma os_sched_modular_prefix_resources : forall sg state (frame : Assertion) before,
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (UCOS2_inv sg state ** unmap_table_rep sg ** frame) before ->
  exists after,
    os_sched_modular_prefix_execution sg state before after /\
    (os_sched_requests_switch state = true ->
      sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
        (os_sched_prefix_state state).(SchedState)) /\
    (UCOS2_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before Hnonempty Hpre.
  unfold os_sched_modular_prefix_execution.
  destruct (os_sched_requests_switch state) eqn:Hswitch.
  - destruct (proj1 (os_sched_requests_switch_iff state) Hswitch) as [Henabled _].
    destruct (kernel_sched_switch_prefix_frame_source sg state frame before
      Hswitch (Hnonempty Henabled) Hpre) as [after [Hrun [Hhigh Hpost]]].
    exists after; split; [exact Hrun|]. split; [intros _; exact Hhigh|exact Hpost].
  - destruct (os_sched_source_nonswitch_prefix_resources sg state frame before
      Hswitch Hnonempty Hpre) as [after [Hrun Hpost]].
    exists after; split; [exact Hrun|]. split; [discriminate|exact Hpost].
Qed.

(** The Task state, parked keys and descriptors are unchanged by this C
    prefix. Keep the SAME descriptor-indexed local resource map, acquired
    critical-region owner, saved word and current call context throughout.
    Its producer supplies the input ownership; no arbitrary stability law
    or weak-map reconstruction is needed. *)
Lemma os_sched_modular_prefix_continuation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  local critical sg active call saved acquired state before (frame : Assertion),
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (kernel_continuation_call_masked abi kernel_program_inv local critical sg active
    call saved acquired state ** frame) before ->
  exists after,
    os_sched_modular_prefix_execution sg state before after /\
    (os_sched_requests_switch state = true ->
      sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
        (os_sched_prefix_state state).(SchedState)) /\
    (kernel_continuation_call_masked abi kernel_program_inv local critical sg active
      call saved acquired (os_sched_prefix_state state) ** frame) after.
Proof.
  intros external platform port abi local critical sg active call saved acquired state before frame
    Hnonempty Hpre.
  set (prefix_frame :=
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources external call **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** frame).
  assert (Hopen :
    kernel_continuation_call_masked abi kernel_program_inv local critical sg active
      call saved acquired state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) active) &&
    (UCOS2_inv sg state ** unmap_table_rep sg ** prefix_frame)).
  { unfold kernel_continuation_call_masked, kernel_continuation_inv, prefix_frame.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Hphysical].
  destruct (os_sched_modular_prefix_resources sg state prefix_frame before Hnonempty Hphysical)
    as [after [Hrun [Hhigh Hafter]]].
  exists after; split; [exact Hrun|]. split; [exact Hhigh|].
  assert (Hclose :
    UCOS2_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** prefix_frame |--
    kernel_continuation_call_masked abi kernel_program_inv local critical sg active
      call saved acquired (os_sched_prefix_state state) ** frame).
  { unfold kernel_continuation_call_masked, kernel_continuation_inv, prefix_frame.
    rewrite kernel_program_inv_split_unmap.
    change (os_sched_prefix_state state).(TskState) with state.(TskState).
    entailer!. }
  exact (Hclose after Hafter).
Qed.
