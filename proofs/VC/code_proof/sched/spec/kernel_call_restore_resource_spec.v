Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The existing MSR specialization changes the I/F bits to the supplied
    word. This equality concerns only that mask, not the final CPSR after
    BX interworking. *)
Lemma armv7a_cpsr_restore_mask_eq : forall current saved,
  armv7a_irq_fiq_mask (armv7a_cpsr_restore_direct current saved) =
  armv7a_irq_fiq_mask saved.
Proof.
  intros; unfold armv7a_irq_fiq_mask, armv7a_cpsr_restore_direct.
  rewrite Z.land_lor_distr_l, <- !Z.land_assoc.
  change (Z.lor (Z.land current 0) (Z.land saved 192) = Z.land saved 192).
  rewrite Z.land_0_r, Z.lor_0_l; reflexivity.
Qed.

Lemma kernel_call_restore_prefix_cursor : forall arch cursor before written_cursor after,
  kernel_call_restore_prefix_execution arch cursor before written_cursor after ->
  written_cursor = kernel_restore_write_cpsr cursor.
Proof.
  intros arch cursor before written_cursor after Hrun.
  unfold kernel_call_restore_prefix_execution in Hrun.
  repeat match goal with
  | H : kernel_call_restore_instruction_execution _ (_ :: _) _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_restore_instruction_step _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_restore_instruction_execution _ nil _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end; reflexivity.
Qed.

Lemma kernel_call_restore_suffix_cursor : forall arch cursor before final_cursor after,
  kernel_call_restore_suffix_execution arch cursor before final_cursor after ->
  final_cursor = kernel_restore_branch_lr cursor.
Proof.
  intros arch cursor before final_cursor after Hrun.
  unfold kernel_call_restore_suffix_execution in Hrun.
  repeat match goal with
  | H : kernel_call_restore_instruction_execution _ (_ :: _) _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_restore_instruction_step _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H : kernel_call_restore_instruction_execution _ nil _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end; reflexivity.
Qed.

(** Explicit MSR-direction EXTERNAL resource refinement. These fields are
    additional parameters of a compatible CPU/CSL interpretation, not
    consequences of arbitrary resource records or a proved ARM/BSP instance.

    Only the real local DSB/MSR and BX projections are permitted. Saved and
    inside resources are consumed at MSR, never a second time after an IRQ.
    No OS state, table, current/ready, outside handle, caller-PC binding or
    progress assertion occurs in this interface. [frame] describes the same
    disjoint resource through ONE local transition, not arbitrary IRQ work. *)
Record Armv7aRestoreResourceABI (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (arch : A32InterruptContext) : Type := {
  armv7a_restore_prefix_transition : KernelRestoreCursor -> model ->
    KernelRestoreCursor -> model -> Prop;
  armv7a_restore_suffix_transition : KernelRestoreCursor -> model ->
    KernelRestoreCursor -> model -> Prop;
  armv7a_restore_prefix_source : forall cursor before written_cursor after,
    armv7a_restore_prefix_transition cursor before written_cursor after ->
    kernel_call_restore_prefix_execution arch cursor before written_cursor after;
  armv7a_restore_suffix_source : forall cursor before final_cursor after,
    armv7a_restore_suffix_transition cursor before final_cursor after ->
    kernel_call_restore_suffix_execution arch cursor before final_cursor after;
  armv7a_restore_prefix_resources : forall sg call saved entry cursor before
      written_cursor after (frame : Assertion),
    cursor.(kernel_restore_r0) = saved ->
    armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved entry **
     os_sched_context_resources external call ** frame) before ->
    armv7a_restore_prefix_transition cursor before written_cursor after ->
    (kernel_call_execution_owned external platform call
       (armv7a_irq_fiq_mask (armv7a_cpsr_restore_direct
         cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))) ** frame) after;
  armv7a_restore_suffix_resources : forall call written cursor before final_cursor after
      (frame : Assertion),
    cursor.(kernel_restore_msr_word) = Some written ->
    (kernel_call_execution_owned external platform call
       (armv7a_irq_fiq_mask written) ** frame) before ->
    armv7a_restore_suffix_transition cursor before final_cursor after ->
    (kernel_call_execution_owned external platform call
       (armv7a_irq_fiq_mask written) ** frame) after
}.

Arguments armv7a_restore_prefix_transition {external platform critical arch} _ _ _ _ _.
Arguments armv7a_restore_suffix_transition {external platform critical arch} _ _ _ _ _.

(** The resource result is on the SUPPLIED actual endpoint, with an
    explicit R0/saved-token and current-mask/CPU join. These source bindings
    are not inferred from an unconstrained ghost integer. *)
Lemma armv7a_restore_prefix_releases_critical_region : forall external platform critical arch
  (abi : Armv7aRestoreResourceABI external platform critical arch)
  sg call saved entry cursor before written_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry **
   os_sched_context_resources external call ** frame) before ->
  armv7a_restore_prefix_transition abi cursor before written_cursor after ->
  written_cursor = kernel_restore_write_cpsr cursor /\
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_call_execution_owned external platform call
     (armv7a_irq_fiq_mask saved) ** frame) after.
Proof.
  intros external platform critical arch abi sg call saved entry cursor before
    written_cursor after frame Hr0 Hmask Hpre Hrun.
  pose proof (armv7a_restore_prefix_source _ _ _ _ abi _ _ _ _ Hrun) as Hsource.
  split; [eapply kernel_call_restore_prefix_cursor; exact Hsource|].
  split; [eapply kernel_call_restore_instructions_preserve_memory; exact Hsource|].
  pose proof (armv7a_restore_prefix_resources _ _ _ _ abi sg call saved entry cursor
    before written_cursor after frame Hr0 Hmask Hpre Hrun) as Hpost.
  rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hpost; exact Hpost.
Qed.

Lemma armv7a_restore_suffix_transports_owned_execution : forall external platform critical arch
  (abi : Armv7aRestoreResourceABI external platform critical arch)
  call written cursor before final_cursor after (frame : Assertion),
  cursor.(kernel_restore_msr_word) = Some written ->
  (kernel_call_execution_owned external platform call
     (armv7a_irq_fiq_mask written) ** frame) before ->
  armv7a_restore_suffix_transition abi cursor before final_cursor after ->
  final_cursor = kernel_restore_branch_lr cursor /\
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_call_execution_owned external platform call
     (armv7a_irq_fiq_mask written) ** frame) after.
Proof.
  intros external platform critical arch abi call written cursor before final_cursor
    after frame Hword Hpre Hrun.
  pose proof (armv7a_restore_suffix_source _ _ _ _ abi _ _ _ _ Hrun) as Hsource.
  split; [eapply kernel_call_restore_suffix_cursor; exact Hsource|].
  split; [eapply kernel_call_restore_instructions_preserve_memory; exact Hsource|].
  eapply armv7a_restore_suffix_resources; eassumption.
Qed.

(** Consumer of two real local transitions meeting on the SAME model.
    An interrupt in the middle is not a case of this theorem. There is no
    assertion that these transitions exist or that a public call returns. *)
Lemma armv7a_restore_uninterrupted_transports_owned_execution :
  forall external platform critical arch
    (abi : Armv7aRestoreResourceABI external platform critical arch)
    sg call saved entry cursor before written_cursor middle final_cursor after
    (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry **
   os_sched_context_resources external call ** frame) before ->
  armv7a_restore_prefix_transition abi cursor before written_cursor middle ->
  armv7a_restore_suffix_transition abi written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_call_execution_owned external platform call
     (armv7a_irq_fiq_mask saved) ** frame) after.
Proof.
  intros external platform critical arch abi sg call saved entry cursor before
    written_cursor middle final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix.
  pose proof (armv7a_restore_prefix_source _ _ _ _ abi _ _ _ _ Hprefix) as Hprefix_source.
  pose proof (armv7a_restore_suffix_source _ _ _ _ abi _ _ _ _ Hsuffix) as Hsuffix_source.
  pose proof (kernel_call_restore_prefix_suffix arch cursor before written_cursor middle
    final_cursor after Hprefix_source Hsuffix_source) as Hsource.
  destruct (armv7a_restore_prefix_releases_critical_region external platform critical arch
    abi sg call saved entry cursor before written_cursor middle frame Hr0 Hmask Hpre Hprefix)
    as [Hcursor [Hmemory Howned]].
  assert (Hword : written_cursor.(kernel_restore_msr_word) =
    Some (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
      cursor.(kernel_restore_r0))) by (rewrite Hcursor; reflexivity).
  assert (Hinput : (kernel_call_execution_owned external platform call
    (armv7a_irq_fiq_mask (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
       cursor.(kernel_restore_r0))) ** frame) middle).
  { rewrite armv7a_cpsr_restore_mask_eq, Hr0; exact Howned. }
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch
    abi call _ written_cursor middle final_cursor after frame Hword Hinput Hsuffix)
    as [Hfinal [Hmemory_final Hpost]].
  split; [exact Hsource|].
  split.
  - rewrite Hfinal, Hcursor; reflexivity.
  - split; [congruence|].
    rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hpost; exact Hpost.
Qed.
