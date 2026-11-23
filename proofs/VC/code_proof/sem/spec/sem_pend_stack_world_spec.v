Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The task branch at an actual source cut. This is NOT a replacement
    public Require: early errors and the nonblocking Boot branch remain
    in sem_pend_call_admission. The current strong map is carried to the
    next Save, rather than forgotten after the preceding restore. *)
Definition sem_pend_task_stack_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources sg call mask state : Assertion :=
  coq_prop (sem_pend_task_call_stage sg call state) &&
  (kernel_call_execution_owned external platform call mask **
   kernel_stack_inv abi resources sg (Some (task_stack_key call.(os_sched_call_stack))) state).

(** The actual selector/restore producer establishes this entry. Earlier
    source clients supply liveness and the no-wait fields; they do not
    assert that the original task remained current throughout the trace. *)
Lemma sem_pend_selected_source_stack_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg original pc lr incoming selected node state,
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) state ->
  task_stack_key incoming = task_stack_key original.(os_sched_call_stack) ->
  os_sched_source_selected_post external platform port abi sg
    (armv7a_call_focus original pc lr) incoming selected node state |--
  coq_prop (selected.(armv7a_continuation_call) = Some original /\
    selected.(armv7a_continuation_pc) = pc /\ selected.(armv7a_continuation_lr) = lr) &&
  sem_pend_task_stack_resources abi UCOS2_inv sg
    (armv7a_continuation_resumed_call selected original)
    (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) state.
Proof.
  intros external platform port abi sg original pc lr incoming selected node state
    Horigin Hactive Hfields Hkey.
  sep_apply_l_atomic (sem_pend_selected_source_call_stage external platform port abi sg
    original pc lr incoming selected node state Horigin Hactive Hfields Hkey).
  Intros; unfold sem_pend_task_stack_resources, kernel_stack_inv.
  sep_apply_l_atomic (armv7a_task_call_stacks_forget external platform port abi state.(TskState)
    (armv7a_call_focus original pc lr) state.(TskState).(parkedTaskStacks)); entailer!.
Qed.

(** At CPSID/DSB/BX there is no kernel-memory write. Thus the actual
    current world, including any supplied extra owner, survives this
    suffix on the same heap. This does not frame such an owner across an
    earlier IRQ, scheduler handoff, or unmasked Restore interval. *)
Lemma sem_pend_save_suffix_keeps_stack_resources : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  resources sg call state registers before final_registers acquired after (frame : Assertion),
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  (sem_pend_task_stack_resources abi resources sg call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state ** frame) before ->
  armv7a_save_suffix_transition suffix registers state before final_registers acquired after ->
  acquired = state /\ after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  kernel_save_after_mrs_execution arch registers state before final_registers acquired after /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  sem_pend_task_call_stage sg call acquired /\
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
   os_sched_context_resources external call **
   kernel_stack_inv abi resources sg (Some (task_stack_key call.(os_sched_call_stack))) acquired ** frame) after.
Proof.
  intros external platform port critical arch abi suffix resources sg call state registers before
    final_registers acquired after frame Hsaved Hpre Hrun.
  assert (Hopen : sem_pend_task_stack_resources abi resources sg call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state ** frame |--
    coq_prop (sem_pend_task_call_stage sg call state) &&
    (kernel_call_execution_owned external platform call
       (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
     (kernel_stack_inv abi resources sg (Some (task_stack_key call.(os_sched_call_stack))) state ** frame))).
  { unfold sem_pend_task_stack_resources; entailer!. }
  destruct (Hopen before Hpre) as [Hstage Howned].
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg call
    registers state before final_registers acquired after _ Hsaved Howned Hrun)
    as [Hstate [Hmemory [Hreturn [Hvalue Hpost]]]].
  subst acquired; split; [reflexivity|]. split; [exact Hmemory|]. split.
  - exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hrun).
  - split; [exact Hreturn|]. split; [exact Hvalue|]. split; [exact Hstage|].
    match type of Hpost with ?P after => assert (Hclose : P |--
      critical_region_masked platform critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
      os_sched_context_resources external call **
      kernel_stack_inv abi resources sg (Some (task_stack_key call.(os_sched_call_stack))) state ** frame)
      by entailer!
    end.
    exact (Hclose after Hpost).
Qed.
