Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.

(** Pinned ARMv7-A/GNU non-VFP OS_CPU_SR_Restore, lines 157--161:
    DSB; MSR CPSR_c,R0; BX LR. This relation describes a LOCAL instruction
    projection with no intervening interrupt. It is neither an execution
    permission nor a specification for every complete public Restore call.

    [kernel_restore_msr_word] records the value written at the MSR cut,
    not the final CPSR after BX interworking. [kernel_restore_return_word]
    is the raw LR branch operand, not an aligned PC or an ARM-only return.
    The existing A32 specialization bounds the MSR observation. No OS-state
    index, ready/current fact, shared-table owner or CPU resource is added. *)
Record KernelRestoreCursor : Type := {
  kernel_restore_current_cpsr : Z;
  kernel_restore_r0 : Z;
  kernel_restore_lr : Z;
  kernel_restore_msr_word : option Z;
  kernel_restore_return_word : option Z
}.

Inductive KernelRestoreInstruction : Type :=
| RestoreDataBarrier | RestoreWriteCPSR | RestoreBranchLR.

Definition kernel_restore_write_cpsr (cursor : KernelRestoreCursor)
  : KernelRestoreCursor :=
  {| kernel_restore_current_cpsr := cursor.(kernel_restore_current_cpsr);
     kernel_restore_r0 := cursor.(kernel_restore_r0);
     kernel_restore_lr := cursor.(kernel_restore_lr);
     kernel_restore_msr_word := Some (armv7a_cpsr_restore_direct
       cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0));
     kernel_restore_return_word := None |}.

Definition kernel_restore_branch_lr (cursor : KernelRestoreCursor)
  : KernelRestoreCursor :=
  {| kernel_restore_current_cpsr := cursor.(kernel_restore_current_cpsr);
     kernel_restore_r0 := cursor.(kernel_restore_r0);
     kernel_restore_lr := cursor.(kernel_restore_lr);
     kernel_restore_msr_word := cursor.(kernel_restore_msr_word);
     kernel_restore_return_word := Some cursor.(kernel_restore_lr) |}.

Inductive kernel_call_restore_instruction_step (arch : A32InterruptContext)
  : KernelRestoreInstruction -> KernelRestoreCursor -> model ->
    KernelRestoreCursor -> model -> Prop :=
| KernelRestoreDataBarrier : forall cursor before after,
    cursor.(kernel_restore_msr_word) = None ->
    cursor.(kernel_restore_return_word) = None ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    kernel_call_restore_instruction_step arch RestoreDataBarrier
      cursor before cursor after
| KernelRestoreWriteCPSR : forall cursor before after,
    cursor.(kernel_restore_msr_word) = None ->
    cursor.(kernel_restore_return_word) = None ->
    a32_maskable_context arch cursor.(kernel_restore_current_cpsr) ->
    a32_maskable_context arch cursor.(kernel_restore_r0) ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    kernel_call_restore_instruction_step arch RestoreWriteCPSR
      cursor before (kernel_restore_write_cpsr cursor) after
| KernelRestoreBranchLR : forall cursor written before after,
    cursor.(kernel_restore_msr_word) = Some written ->
    cursor.(kernel_restore_return_word) = None ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) ->
    kernel_call_restore_instruction_step arch RestoreBranchLR
      cursor before (kernel_restore_branch_lr cursor) after.

Inductive kernel_call_restore_instruction_execution (arch : A32InterruptContext)
  : list KernelRestoreInstruction -> KernelRestoreCursor -> model ->
    KernelRestoreCursor -> model -> Prop :=
| KernelRestoreExecutionNil : forall cursor heap,
    kernel_call_restore_instruction_execution arch [] cursor heap cursor heap
| KernelRestoreExecutionCons : forall instruction instructions cursor before
    middle_cursor middle final_cursor after,
    kernel_call_restore_instruction_step arch instruction cursor before middle_cursor middle ->
    kernel_call_restore_instruction_execution arch instructions middle_cursor middle final_cursor after ->
    kernel_call_restore_instruction_execution arch (instruction :: instructions)
      cursor before final_cursor after.

Definition kernel_call_restore_uninterrupted_execution arch cursor before
  final_cursor after : Prop :=
  kernel_call_restore_instruction_execution arch
    [RestoreDataBarrier; RestoreWriteCPSR; RestoreBranchLR]
    cursor before final_cursor after.

(** The CPU/CSL release belongs at MSR. An interrupt between MSR and BX
    must resume the BX cursor without consuming the saved token a second
    time. These two cuts share the same instruction relation. *)
Definition kernel_call_restore_prefix_execution arch cursor before
  final_cursor after : Prop :=
  kernel_call_restore_instruction_execution arch
    [RestoreDataBarrier; RestoreWriteCPSR] cursor before final_cursor after.

Definition kernel_call_restore_suffix_execution arch cursor before
  final_cursor after : Prop :=
  kernel_call_restore_instruction_execution arch
    [RestoreBranchLR] cursor before final_cursor after.

Lemma kernel_call_restore_instruction_execution_app :
  forall arch first cursor before middle_cursor middle second final_cursor after,
  kernel_call_restore_instruction_execution arch first cursor before middle_cursor middle ->
  kernel_call_restore_instruction_execution arch second middle_cursor middle final_cursor after ->
  kernel_call_restore_instruction_execution arch (first ++ second) cursor before final_cursor after.
Proof.
  intros arch first cursor before middle_cursor middle second final_cursor after Hfirst Hsecond.
  induction Hfirst; simpl; [exact Hsecond|].
  econstructor; [exact H|exact (IHHfirst Hsecond)].
Qed.

Lemma kernel_call_restore_prefix_suffix :
  forall arch cursor before middle_cursor middle final_cursor after,
  kernel_call_restore_prefix_execution arch cursor before middle_cursor middle ->
  kernel_call_restore_suffix_execution arch middle_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after.
Proof.
  intros arch cursor before middle_cursor middle final_cursor after Hprefix Hsuffix.
  exact (kernel_call_restore_instruction_execution_app arch
    [RestoreDataBarrier; RestoreWriteCPSR] cursor before middle_cursor middle
    [RestoreBranchLR] final_cursor after Hprefix Hsuffix).
Qed.

Lemma kernel_call_restore_instruction_preserves_memory :
  forall arch instruction cursor before final_cursor after,
  kernel_call_restore_instruction_step arch instruction cursor before final_cursor after ->
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem).
Proof. intros; destruct H; assumption. Qed.

Lemma kernel_call_restore_instructions_preserve_memory :
  forall arch instructions cursor before final_cursor after,
  kernel_call_restore_instruction_execution arch instructions cursor before final_cursor after ->
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem).
Proof.
  intros arch instructions cursor before final_cursor after Hrun.
  induction Hrun as [cursor heap|instruction instructions cursor before
    middle_cursor middle final_cursor after Hstep Htail IH].
  - reflexivity.
  - pose proof (kernel_call_restore_instruction_preserves_memory _ _ _ _ _ _ Hstep).
    congruence.
Qed.

(** This constructs an inhabitant of the local projection, not a hardware
    execution or an assertion that all public calls follow this branch. *)
Lemma kernel_call_restore_uninterrupted_projection : forall arch cursor heap,
  cursor.(kernel_restore_msr_word) = None ->
  cursor.(kernel_restore_return_word) = None ->
  a32_maskable_context arch cursor.(kernel_restore_current_cpsr) ->
  a32_maskable_context arch cursor.(kernel_restore_r0) ->
  kernel_call_restore_uninterrupted_execution arch cursor heap
    (kernel_restore_branch_lr (kernel_restore_write_cpsr cursor)) heap.
Proof.
  intros arch cursor heap Hmsr Hreturn Hcurrent Hsaved.
  unfold kernel_call_restore_uninterrupted_execution.
  econstructor; [constructor; [exact Hmsr|exact Hreturn|reflexivity]|].
  econstructor; [constructor; [exact Hmsr|exact Hreturn|exact Hcurrent|exact Hsaved|reflexivity]|].
  econstructor; [econstructor; reflexivity|constructor].
Qed.

Lemma kernel_call_restore_uninterrupted_observations :
  forall arch cursor before final_cursor after,
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after ->
  final_cursor = kernel_restore_branch_lr (kernel_restore_write_cpsr cursor) /\
  a32_sr_restore_source_specialization arch cursor.(kernel_restore_current_cpsr)
    cursor.(kernel_restore_r0)
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
Proof.
  intros arch cursor before final_cursor after Hrun.
  unfold kernel_call_restore_uninterrupted_execution in Hrun.
  repeat match goal with
  | H : kernel_call_restore_instruction_execution _ (_ :: _) _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_restore_instruction_step _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_restore_instruction_execution _ [] _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end.
  split; [reflexivity|].
  unfold a32_sr_restore_source_specialization.
  split; [assumption|]. split; [assumption|reflexivity].
Qed.

Lemma kernel_call_restore_uninterrupted_return_values :
  forall arch cursor before final_cursor after,
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after ->
  final_cursor.(kernel_restore_msr_word) = Some
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  Z.testbit (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
    cursor.(kernel_restore_r0)) 7 = Z.testbit cursor.(kernel_restore_r0) 7 /\
  Z.testbit (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
    cursor.(kernel_restore_r0)) 6 = Z.testbit cursor.(kernel_restore_r0) 6.
Proof.
  intros arch cursor before final_cursor after Hrun.
  destruct (kernel_call_restore_uninterrupted_observations _ _ _ _ _ Hrun) as [Hcursor _].
  rewrite Hcursor; split; [reflexivity|]. split; [reflexivity|].
  apply armv7a_cpsr_restore_irq_fiq_exact.
Qed.
