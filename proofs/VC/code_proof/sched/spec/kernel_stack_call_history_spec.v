Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source history is an explicit parameter, NOT an erased region trace.
    In particular actual IRQ deposit writes the TCB SP and final take
    removes the stored continuation. A complete source producer records
    those edges around its SAME heap/state/client trace. It must not claim
    they disappear into the older released-to-current interval.

    Existing selected segmented histories and separately proved full92
    histories instantiate this relation. Neither a relation nor call
    identity creates a spatial owner. No ABI field or new axiom is added. *)
Definition kernel_stack_call_same_call (returned original : OsSchedCallContext) : Prop :=
  returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = original.(os_sched_call_stack).

Definition kernel_stack_call_history_save_post {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources critical sg active
  (history : OsSchedCallContext -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
  original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (history original before returned acquired /\
      kernel_stack_call_same_call returned original /\ interrupt_saved_value mask saved) &&
    kernel_stack_call_masked abi resources critical sg active returned saved acquired acquired.

Definition kernel_stack_call_history_restore_post {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources sg active
  (history : OsSchedCallContext -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
  original mask released : Assertion :=
  EX returned current,
    coq_prop (history original released returned current /\ kernel_stack_call_same_call returned original) &&
    kernel_stack_call_closed abi resources sg active returned mask current.

(** A source suffix consumes BOTH prior actual history and the actual
    current world. The world is framed only through this CPSID/DSB/BX
    transition, not through the earlier arbitrary IRQ/client interval.
    A full call theorem must construct [history] from that actual path. *)
Lemma kernel_stack_call_history_save_suffix : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  resources sg active history original returned mask before state registers heap
  final_registers final_state after (frame : Assertion),
  history original before returned state -> kernel_stack_call_same_call returned original ->
  interrupt_saved_value mask registers.(kernel_save_r0) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  (kernel_stack_call_closed abi resources sg active returned
    (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state ** frame) heap ->
  armv7a_save_suffix_transition suffix registers state heap final_registers final_state after ->
  final_state = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  (kernel_stack_call_masked abi resources critical sg active returned
    final_registers.(kernel_save_r0) final_state final_state ** frame) after /\
  (kernel_stack_call_history_save_post abi resources critical sg active history original mask
    final_registers.(kernel_save_r0) before ** frame) after.
Proof.
  intros external platform port critical arch abi suffix resources sg active history original returned mask before state
    registers heap final_registers final_state after frame Hhistory Hsame Hsaved_input Hsaved Hpre Hrun.
  assert (Hopen : kernel_stack_call_closed abi resources sg active returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state ** frame |--
    kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
      (kernel_stack_inv abi resources sg active state ** frame)).
  { unfold kernel_stack_call_closed; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg returned registers
    state heap final_registers final_state after _ Hsaved (Hopen heap Hpre) Hrun)
    as [Hstate [Hmemory [Hreturn [Hr0 Hpost]]]].
  split; [exact Hstate|]. split; [exact Hr0|]. split; [exact Hreturn|]. subst final_state.
  split.
  - unfold kernel_stack_call_masked.
    match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hconcrete : P |-- Q) by entailer! end end.
    exact (Hconcrete after Hpost).
  -
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold kernel_stack_call_history_save_post; Exists returned state.
    unfold kernel_stack_call_masked; rewrite Hr0; entailer!. }
  exact (Hclose after Hpost).
Qed.

(** The final BX preserves the already re-established owner at current.
    [history] may record the full actual segmented path (including this
    known transition); it is never converted to an unsupported old trace. *)
Lemma kernel_stack_call_history_restore_suffix : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  resources sg active history original released returned state written cursor before final_cursor after (frame : Assertion),
  history original released returned state -> kernel_stack_call_same_call returned original ->
  cursor.(kernel_restore_msr_word) = Some written ->
  (kernel_stack_call_closed abi resources sg active returned (armv7a_irq_fiq_mask written) state ** frame) before ->
  armv7a_restore_suffix_transition restore cursor before final_cursor after ->
  final_cursor = kernel_restore_branch_lr cursor /\ after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_stack_call_closed abi resources sg active returned (armv7a_irq_fiq_mask written) state ** frame) after /\
  (kernel_stack_call_history_restore_post abi resources sg active history original
    (armv7a_irq_fiq_mask written) released ** frame) after.
Proof.
  intros external platform port critical arch abi restore resources sg active history original released returned state written cursor
    before final_cursor after frame Hhistory Hsame Hword Hpre Hrun.
  assert (Hopen : kernel_stack_call_closed abi resources sg active returned (armv7a_irq_fiq_mask written) state ** frame |--
    kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask written) **
      (kernel_stack_inv abi resources sg active state ** frame)).
  { unfold kernel_stack_call_closed; entailer!. }
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch restore returned written cursor
    before final_cursor after _ Hword (Hopen before Hpre) Hrun) as [Hcursor [Hmemory Hpost]].
  split; [exact Hcursor|]. split; [exact Hmemory|].
  split.
  - unfold kernel_stack_call_closed.
    match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hconcrete : P |-- Q) by entailer! end end.
    exact (Hconcrete after Hpost).
  -
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold kernel_stack_call_history_restore_post; Exists returned state; unfold kernel_stack_call_closed; entailer!. }
  exact (Hclose after Hpost).
Qed.
