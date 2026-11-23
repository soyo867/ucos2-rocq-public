Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_repeated_irq_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Section SaveIRQResources.
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (abi : Armv7aContinuationABI external platform port)
  (registers_source : Armv7aIRQRegisterSave external platform port abi)
  (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

(** Exact property of the existing counter-only source family. It is not
    a frame condition on arbitrary configured clients or interrupt paths. *)
Lemma mutex_del_counter_irqs_event_eq : forall mask pc lr call state before returned final after,
  mutex_del_restore_irqs_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments mask pc lr call state before returned final after ->
  final.(EventState) = state.(EventState).
Proof.
  intros mask pc lr call state before returned final after Hrun; induction Hrun.
  - reflexivity.
  - rewrite IHHrun.
    destruct H as [state handler saved node publication clients kind before saved_heap handler_heap handler_cursor
      returned_cursor returned_heap exit_cursor exit_heap exited_heap irq_after Hsafe Hpc Hmask Hlr Hstack Hfragments
      Hsave Hentry Hreturn Hsame Hreturn_pc Htrace Hwrapper Hexit Hreads Hrestore].
    exact (proj2 (mutex_del_restore_irq_tasks_event_eq sg state handler saved node publication clients kind Hsafe)).
Qed.

(** One actual MRS, the existing register-indexed IRQ source at Save+4,
    and the restored CPSID/DSB/BX suffix. The resource producer consumes
    that SAME finite execution, rather than framing a stale world across
    it. Only R0/LR and CPSR's mask are transported from the old indexed
    source. The suffix's full CPSR is computed from its actual resumed
    cursor, not asserted equal to the original CPSR. *)
Lemma mutex_del_stack_irq_save_resources : forall critical arch
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  active call state registers before returned_registers returned acquired resumed
  final_registers final_state after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  (kernel_stack_call_closed abi mutex_del_stack_resources sg active call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  mutex_del_irq_registers_execution external platform port abi registers_source sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_save_entry_address suffix + 4)
    (kernel_save_read_cpsr registers) call state before returned_registers returned acquired resumed ->
  armv7a_save_suffix_transition suffix returned_registers acquired resumed final_registers final_state after ->
  kernel_call_save_instruction_step arch SaveReadCPSR registers state before
    (kernel_save_read_cpsr registers) state before /\
  kernel_save_after_mrs_execution arch returned_registers acquired resumed final_registers final_state after /\
  final_state = acquired /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_cpsr) = Z.lor returned_registers.(kernel_save_cpsr) 192 /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  kernel_stack_call_same_call returned call /\ acquired.(EventState) = state.(EventState) /\
  (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active returned
     final_registers.(kernel_save_r0) acquired acquired **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros critical arch suffix active call state registers before returned_registers returned acquired resumed
    final_registers final_state after frame Hnone Hvalid Hpre Hirqs Hsuffix.
  destruct (mutex_del_irq_registers_execution_refinement external platform port abi registers_source sg Local
    local_step normal_return handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hirqs)
    as [Hr0 [Hlr [Hmask Hsource]]].
  cbn [kernel_save_read_cpsr] in Hr0, Hlr, Hmask.
  pose proof (mutex_del_counter_irqs_event_eq _ _ _ _ _ _ _ _ _ Hsource) as Hevents.
  destruct (mutex_del_restore_irqs_execution_stack_resources external platform port abi sg Local
    local_step normal_return handler_contract handler_stack handler_fragments active _ _ _ _ _ _ _ _ _ _
    Hsource Hpre) as [Hi [Ho [Hs Hresumed]]].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask returned_registers.(kernel_save_cpsr)) returned_registers.(kernel_save_r0)).
  { unfold interrupt_saved_value; rewrite Hr0, Hmask; split; [exact Hvalid|reflexivity]. }
  assert (Hopen : kernel_stack_call_closed abi mutex_del_stack_resources sg active returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) acquired **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask returned_registers.(kernel_save_cpsr)) **
      (kernel_stack_inv abi mutex_del_stack_resources sg active acquired **
       (task_stack_fragments_rep handler_stack handler_fragments ** frame))).
  { unfold kernel_stack_call_closed; rewrite Hmask; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg returned
    returned_registers acquired resumed final_registers final_state after _ Hsaved (Hopen resumed Hresumed) Hsuffix)
    as [Hstate [Hmemory [Hreturn [Hvalue Hmasked]]]].
  pose proof (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hsuffix) as Hsuffix_source.
  destruct (kernel_save_after_mrs_return_values _ _ _ _ _ _ _ Hsuffix_source) as [_ [Hcpsr _]].
  split; [constructor; [exact Hnone|reflexivity]|].
  split; [exact Hsuffix_source|]. split; [exact Hstate|].
  split; [rewrite Hvalue; exact Hr0|]. split; [exact Hcpsr|].
  split; [rewrite Hreturn, Hlr; reflexivity|].
  split; [unfold kernel_stack_call_same_call; auto|]. split; [exact Hevents|].
  match type of Hmasked with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold kernel_stack_call_masked; entailer!. }
  exact (Hclose after Hmasked).
Qed.
End SaveIRQResources.
