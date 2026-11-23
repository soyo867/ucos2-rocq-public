Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The existing physical world and the SAME parked map, retaining the
    source-established local predicate at each descriptor. [local] owns
    no second copy of stack bytes. Its preservation through an OS update
    must be proved by that update's source; no stability law is assumed.
    In particular, a saved-state registration fact is not current liveness.
    Legacy weak worlds remain separate interfaces during migration. *)
Definition kernel_continuation_inv {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  (resources : StableGlobVars -> UCOS2_Verify_State -> Assertion)
  (local : Armv7aContinuation -> Assertion) sg active state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) active) &&
  (resources sg state **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks)).

Definition kernel_continuation_call_closed {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  resources local sg active call mask state : Assertion :=
  kernel_call_execution_owned external platform call mask **
    kernel_continuation_inv abi resources local sg active state.

Definition kernel_continuation_call_masked {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  resources local critical sg active call saved acquired state : Assertion :=
  critical_region_masked platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
    kernel_continuation_inv abi resources local sg active state.

(** Actual uninterrupted MRS/CPSID/DSB/BX: the whole owned map is a frame
    only of these local instructions. The result is not a frame rule for
    an arbitrary interrupt interval and imposes no public input restriction. *)
Lemma kernel_continuation_call_uninterrupted_save : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (save : Armv7aSaveSuffixABI external platform critical arch)
  resources local sg active call state mask registers before final_registers acquired after
  (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_continuation_call_closed abi resources local sg active call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  acquired = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (kernel_continuation_call_masked abi resources local critical sg active call
    final_registers.(kernel_save_r0) state state ** frame) after.
Proof.
  intros external platform port critical arch abi save resources local sg active call state mask registers
    before final_registers acquired after frame Hreturn Hvalid Hmask Hpre Hsuffix.
  assert (Hopen : kernel_continuation_call_closed abi resources local sg active call mask state ** frame |--
    kernel_call_execution_owned external platform call mask **
    (kernel_continuation_inv abi resources local sg active state ** frame)).
  { unfold kernel_continuation_call_closed; entailer!. }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hvalid|reflexivity]. }
  pose proof (Hopen before Hpre) as Howned; rewrite <- Hmask in Howned.
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired after _
    Hsaved Howned Hsuffix) as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  assert (Hrun : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsuffix). }
  split; [exact Hstate|]. split; [exact Hr0|]. split; [exact Hrun|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold kernel_continuation_call_masked; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Actual uninterrupted C Restore retains the very same local map. A
    subsequent public caller can consume this returned world directly;
    no weak-map projection or duplicated dormant authority intervenes. *)
Lemma kernel_continuation_call_uninterrupted_restore : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  resources local sg active call saved acquired state cursor before written middle final_cursor after
  (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (kernel_continuation_call_masked abi resources local critical sg active call saved acquired state ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (kernel_continuation_call_closed abi resources local sg active call (armv7a_irq_fiq_mask saved) state ** frame) after.
Proof.
  intros external platform port critical arch abi restore resources local sg active call saved acquired state
    cursor before written middle final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix.
  assert (Hopen : kernel_continuation_call_masked abi resources local critical sg active call saved acquired state ** frame |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources external call ** (kernel_continuation_inv abi resources local sg active state ** frame)).
  { unfold kernel_continuation_call_masked; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch restore
    sg call saved acquired cursor before written middle final_cursor after _ Hr0 Hmask
    (Hopen before Hpre) Hprefix Hsuffix) as [Hsource [Hreturn [Hmemory Hafter]]].
  split; [exact Hsource|]. split; [exact Hreturn|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold kernel_continuation_call_closed; entailer!. }
  exact (Hclose after Hafter).
Qed.
