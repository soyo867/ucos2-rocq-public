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
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual final CPSID/DSB/BX suffix consumes the whole SOURCE world.
    The earlier source history must come from its actual prefix/return
    proof; the ABI supplies neither that history nor kernel invariants.
    Boot/no-current and full-profile owners remain valid parameters. *)
Lemma kernel_stack_call_save_suffix : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  resources sg active original returned mask before state registers heap
  final_registers final_state after (frame : Assertion),
  kernel_call_save_source external port critical sg original returned mask
    registers.(kernel_save_r0) before state ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  (kernel_stack_call_closed abi resources sg active returned
    (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state ** frame) heap ->
  armv7a_save_suffix_transition suffix registers state heap final_registers final_state after ->
  final_state = state /\ final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  (kernel_stack_call_save_post abi resources critical sg active original mask
    final_registers.(kernel_save_r0) before ** frame) after.
Proof.
  intros external platform port critical arch abi suffix resources sg active original returned mask before state
    registers heap final_registers final_state after frame Hsource Hsaved Hpre Hrun.
  assert (Hopen : kernel_stack_call_closed abi resources sg active returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state ** frame |--
    kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
      (kernel_stack_inv abi resources sg active state ** frame)).
  { unfold kernel_stack_call_closed; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg returned registers
    state heap final_registers final_state after _ Hsaved (Hopen heap Hpre) Hrun)
    as [Hstate [Hmemory [Hreturn [Hr0 Hpost]]]].
  split; [exact Hstate|]. split; [exact Hreturn|]. subst final_state.
  assert (Hclose : critical_region_masked platform critical sg returned.(os_sched_call_invocation)
      returned.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
      os_sched_context_resources external returned ** (kernel_stack_inv abi resources sg active state ** frame) |--
    kernel_stack_call_save_post abi resources critical sg active original mask final_registers.(kernel_save_r0) before ** frame).
  { unfold kernel_stack_call_save_post; Exists returned state.
    unfold kernel_stack_call_masked; rewrite Hr0; entailer!. }
  exact (Hclose after Hpost).
Qed.

(** Complete UNINTERRUPTED Save source branch, including its observed MRS.
    The source history is constructed here (reflexive), not a new caller
    precondition. The other branches are not excluded by this theorem. *)
Lemma kernel_stack_call_uninterrupted_save : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  resources sg active call state mask registers before final_registers acquired after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_stack_call_closed abi resources sg active call mask state ** frame) before ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) state before final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (kernel_stack_call_save_post abi resources critical sg active call mask final_registers.(kernel_save_r0) state ** frame) after.
Proof.
  intros external platform port critical arch abi suffix resources sg active call state mask registers before
    final_registers acquired after frame Hreturn Hvalid Hmask Hpre Hsuffix.
  assert (Hrun : kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hsuffix). }
  assert (Hsource : kernel_call_save_source external port critical sg call call mask
      (kernel_save_read_cpsr registers).(kernel_save_r0) state state).
  { split; [constructor|]. repeat (split; [reflexivity|]).
    split; [exact Hvalid|exact Hmask]. }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hvalid|reflexivity]. }
  rewrite <- Hmask in Hpre.
  destruct (kernel_stack_call_save_suffix external platform port critical arch abi suffix resources sg active
    call call mask state state (kernel_save_read_cpsr registers) before final_registers acquired after frame
    Hsource Hsaved Hpre Hsuffix) as [_ [_ Hpost]].
  split; assumption.
Qed.

(** This is exactly the DSB/MSR prefix. Re-enabling IRQ/FIQ does not yet
    claim C return, and the following handler interval must obtain its
    current world from its own actual source producer. *)
Lemma kernel_stack_call_restore_prefix : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  resources sg active call saved acquired state cursor before written_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (kernel_stack_call_masked abi resources critical sg active call saved acquired state ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor after ->
  written_cursor = kernel_restore_write_cpsr cursor /\ after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_stack_call_closed abi resources sg active call (armv7a_irq_fiq_mask saved) state ** frame) after.
Proof.
  intros external platform port critical arch abi restore resources sg active call saved acquired state cursor
    before written_cursor after frame Hr0 Hmask Hpre Hrun.
  assert (Hopen : kernel_stack_call_masked abi resources critical sg active call saved acquired state ** frame |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources external call ** (kernel_stack_inv abi resources sg active state ** frame)).
  { unfold kernel_stack_call_masked; entailer!. }
  destruct (armv7a_restore_prefix_releases_critical_region external platform critical arch restore sg call saved acquired
    cursor before written_cursor after _ Hr0 Hmask (Hopen before Hpre) Hrun) as [Hcursor [Hmemory Hpost]].
  split; [exact Hcursor|]. split; [exact Hmemory|].
  assert (Hclose : kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask saved) **
    (kernel_stack_inv abi resources sg active state ** frame) |--
    kernel_stack_call_closed abi resources sg active call (armv7a_irq_fiq_mask saved) state ** frame).
  { unfold kernel_stack_call_closed; entailer!. }
  exact (Hclose after Hpost).
Qed.

(** The last BX suffix consumes the world established at THIS endpoint.
    The supplied source relation is pure history from the actual preceding
    prefix/handler chain; it supplies no spatial resources by itself. *)
Lemma kernel_stack_call_restore_suffix : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  resources sg active original released returned state written cursor before final_cursor after (frame : Assertion),
  kernel_stack_call_return_source external port critical sg original released returned state ->
  cursor.(kernel_restore_msr_word) = Some written ->
  (kernel_stack_call_closed abi resources sg active returned (armv7a_irq_fiq_mask written) state ** frame) before ->
  armv7a_restore_suffix_transition restore cursor before final_cursor after ->
  final_cursor = kernel_restore_branch_lr cursor /\ after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_stack_call_restore_post abi resources critical sg active original (armv7a_irq_fiq_mask written) released ** frame) after.
Proof.
  intros external platform port critical arch abi restore resources sg active original released returned state written cursor
    before final_cursor after frame Hsource Hword Hpre Hrun.
  assert (Hopen : kernel_stack_call_closed abi resources sg active returned (armv7a_irq_fiq_mask written) state ** frame |--
    kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask written) **
      (kernel_stack_inv abi resources sg active state ** frame)).
  { unfold kernel_stack_call_closed; entailer!. }
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch restore returned written cursor
    before final_cursor after _ Hword (Hopen before Hpre) Hrun) as [Hcursor [Hmemory Hpost]].
  split; [exact Hcursor|]. split; [exact Hmemory|].
  assert (Hclose : kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask written) **
      (kernel_stack_inv abi resources sg active state ** frame) |--
    kernel_stack_call_restore_post abi resources critical sg active original (armv7a_irq_fiq_mask written) released ** frame).
  { unfold kernel_stack_call_restore_post; Exists returned state; unfold kernel_stack_call_closed; entailer!. }
  exact (Hclose after Hpost).
Qed.

Lemma kernel_stack_call_uninterrupted_restore : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  resources sg active call saved acquired state cursor before written_cursor middle final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (kernel_stack_call_masked abi resources critical sg active call saved acquired state ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (kernel_stack_call_restore_post abi resources critical sg active call (armv7a_irq_fiq_mask saved) state ** frame) after.
Proof.
  intros external platform port critical arch abi restore resources sg active call saved acquired state cursor
    before written_cursor middle final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix.
  assert (Hopen : kernel_stack_call_masked abi resources critical sg active call saved acquired state ** frame |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources external call ** (kernel_stack_inv abi resources sg active state ** frame)).
  { unfold kernel_stack_call_masked; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch restore sg call saved
    acquired cursor before written_cursor middle final_cursor after _ Hr0 Hmask (Hopen before Hpre) Hprefix Hsuffix)
    as [Hsource [Hreturn [Hmemory Hpost]]].
  assert (Hhistory : kernel_stack_call_return_source external port critical sg call state call state).
  { split; [constructor|]; auto. }
  split; [exact Hsource|]. split; [exact Hreturn|].
  assert (Hclose : kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask saved) **
      (kernel_stack_inv abi resources sg active state ** frame) |--
    kernel_stack_call_restore_post abi resources critical sg active call (armv7a_irq_fiq_mask saved) state ** frame).
  { unfold kernel_stack_call_restore_post; Exists call state; unfold kernel_stack_call_closed; entailer!. }
  exact (Hclose after Hpost).
Qed.
