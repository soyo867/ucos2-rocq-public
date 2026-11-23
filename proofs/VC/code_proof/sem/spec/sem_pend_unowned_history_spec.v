Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** BreakNothing's eight-byte aligned call frame is separate from the
    sixteen-word interrupted register image. These are the literal STMFD
    addresses; the later LDMIA reads the same words before SP is restored.
    No scratch ownership follows merely from a stack lease. *)
Definition sem_pend_boot_handler_sp (sp : Z) : Z := sp - Z.land sp 4 - 8.

Definition sem_pend_boot_handler_push (sp lr : Z) : list (addr * Mem.byte) :=
  pointer_store_writes (sem_pend_boot_handler_sp sp) (Z.land sp 4) ++
  pointer_store_writes (sem_pend_boot_handler_sp sp + 4) lr.

Definition sem_pend_boot_handler_pop (sp lr : Z) (heap : model) : Prop :=
  pointer_load (sem_pend_boot_handler_sp sp) (Z.land sp 4) heap /\
  pointer_load (sem_pend_boot_handler_sp sp + 4) lr heap.

(** A bounded SOURCE history for the no-Task-capsule domain. The CPU and
    BSP witnesses are indexed by the external/platform parameters of THIS
    call. The IRQ arm records the actual saved descriptor, both wrapper
    stack accesses, the same matched handler trace and the same restore
    heaps. It cannot manufacture a returned fragment image from same_call.

    The selected handler registry is exactly RestoreHandlerClientKind;
    no arbitrary extra_effect or SemPost deployment is quantified here.
    Kernel effects are its proved, fixed source transformers. On the Boot
    branch these particular counters are inactive, but this is a source
    fact to prove, not an equality required of every possible None call.

    The remask edge carries both its concrete MSR projection and an actual
    local resource step of the already supplied handler contract. Providing
    that edge, the scratch owner and the full BL binding is a remaining
    source-composition obligation; this datatype is not an extra platform
    law, a termination theorem, or coverage of arbitrary/nested IRQs. *)
Inductive sem_pend_unowned_restore_history
  (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) :
  OsSchedCallContext -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop :=
| SemPendUnownedRestoreUninterrupted : forall arch
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    call state cursor before written middle final_cursor after,
    armv7a_restore_prefix_transition restore cursor before written middle ->
    armv7a_restore_suffix_transition restore written middle final_cursor after ->
    sem_pend_unowned_restore_history external platform critical sg call state call state
| SemPendUnownedRestoreBootIRQ : forall port arch
    (abi : Armv7aContinuationABI external platform port)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    (private : RestoreHandlerCall -> (KernelRestoreCursor * Z) -> Assertion) local_step normal_return
    (bsp : RestoreHandlerContract private local_step normal_return)
    original checkpoint handler suspended cursor before written written_word irq_input saved_heap
    handler_cursor handler_heap returned_cursor returned_heap clients handler_entry_pc handler_bl_pc
    remask_cursor remasked_cursor remasked_heap remask_word
    irq_return resume_cursor final_cursor after,
    handler.(os_int_exit_interrupted_call) = original ->
    original.(os_sched_call_origin) = BootInvocation ->
    checkpoint.(SchedState).(isRunning) = false ->
    handler.(os_int_exit_handler_stack) = original.(os_sched_call_stack).(stackLeaseRegion) ->
    armv7a_restore_prefix_transition restore cursor before written irq_input ->
    written.(kernel_restore_msr_word) = Some written_word ->
    handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask written_word ->
    armv7a_save_transition abi handler suspended irq_input saved_heap ->
    suspended.(armv7a_continuation_call) = Some original ->
    armv7a_continuation_binding suspended ->
    suspended.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) ->
    suspended.(armv7a_continuation_lr) = cursor.(kernel_restore_lr) ->
    uchar_load sg.(g_OSRunning) 0 saved_heap ->
    kernel_heap_execution
      (sem_pend_boot_handler_push suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_lr)) saved_heap handler_heap ->
    handler_cursor.(restore_handler_pc) = handler_entry_pc ->
    handler_cursor.(restore_handler_current_call).(restore_handler_return_word) = handler_bl_pc + 4 ->
    snd handler_cursor.(restore_handler_local) =
      sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp) ->
    (fst handler_cursor.(restore_handler_local)).(kernel_restore_lr) = handler_bl_pc + 4 ->
    normal_return sg handler_cursor handler_heap returned_cursor returned_heap ->
    mutex_del_restore_handler_trace local_step sg clients
      handler_cursor handler_heap returned_cursor returned_heap ->
    sem_pend_boot_handler_pop suspended.(armv7a_continuation_sp)
      suspended.(armv7a_continuation_lr) returned_heap ->
    snd returned_cursor.(restore_handler_local) =
      sem_pend_boot_handler_sp suspended.(armv7a_continuation_sp) ->
    local_step returned_cursor returned_heap remasked_cursor remasked_heap ->
    remask_cursor =
      {| kernel_restore_current_cpsr :=
           (fst returned_cursor.(restore_handler_local)).(kernel_restore_current_cpsr);
         kernel_restore_r0 := 211;
         kernel_restore_lr := suspended.(armv7a_continuation_lr);
         kernel_restore_msr_word := None; kernel_restore_return_word := None |} ->
    snd remasked_cursor.(restore_handler_local) = suspended.(armv7a_continuation_sp) ->
    remasked_cursor.(restore_handler_pc) = handler_bl_pc + 16 ->
    (fst remasked_cursor.(restore_handler_local)).(kernel_restore_current_cpsr) =
      armv7a_cpsr_restore_direct remask_cursor.(kernel_restore_current_cpsr) 211 ->
    (fst remasked_cursor.(restore_handler_local)).(kernel_restore_lr) =
      suspended.(armv7a_continuation_lr) ->
    kernel_call_restore_instruction_step arch RestoreWriteCPSR remask_cursor returned_heap
      remask_word remasked_heap ->
    armv7a_continuation_restore_reads suspended remasked_heap ->
    armv7a_restore_transition abi handler suspended remasked_heap irq_return ->
    resume_cursor.(kernel_restore_current_cpsr) = suspended.(armv7a_continuation_cpsr) ->
    resume_cursor.(kernel_restore_msr_word) = written.(kernel_restore_msr_word) ->
    resume_cursor.(kernel_restore_lr) = suspended.(armv7a_continuation_lr) ->
    armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
    sem_pend_unowned_restore_history external platform critical sg original checkpoint
      (armv7a_continuation_resumed_call suspended original)
      (mutex_del_restore_clients_state clients checkpoint).

Lemma sem_pend_unowned_restore_history_same_call : forall external platform critical sg
  original checkpoint returned current,
  sem_pend_unowned_restore_history external platform critical sg original checkpoint returned current ->
  kernel_stack_call_same_call returned original.
Proof.
  intros external platform critical sg original checkpoint returned current Hhistory.
  destruct Hhistory.
  - unfold kernel_stack_call_same_call; repeat split; reflexivity.
  - match goal with
    | Hbinding : armv7a_continuation_binding ?saved,
      Hcall : armv7a_continuation_call ?saved = Some ?call |- _ =>
        pose proof (proj2 Hbinding) as Hstack; rewrite Hcall in Hstack
    end.
    unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call; cbn; auto.
Qed.

Lemma sem_pend_unowned_restore_history_preserves_task_source : forall external platform critical sg
  original checkpoint returned current,
  sem_pend_unowned_restore_history external platform critical sg original checkpoint returned current ->
  kernel_call_task_source original checkpoint -> kernel_call_task_source returned current.
Proof.
  intros external platform critical sg original checkpoint returned current Hhistory Hsource.
  destruct Hhistory; [exact Hsource|].
  destruct Hsource as [Horigin _]; congruence.
Qed.
