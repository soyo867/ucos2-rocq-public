Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** APPROVED additional external register observation, for the pinned
    non-VFP IRQ wrapper interrupting its supported SVC caller. The source
    relation is NOT a classifier of every ARM exception or every IRQ.
    Instantiating it for an actual execution remains an explicit platform
    refinement obligation. In particular it makes no claim about nested
    IRQ/FIQ, another processor mode, or a floating-point wrapper.

    [live_r0] is the working R0 saved by STMFD SP!,{R0-R3}, before the
    exception ID overwrites R0. [live_lr] is the interrupted SVC caller's
    banked LR, saved after the mode switch; it is NOT the IRQ return-PC LR.
    These two observations augment the OLD save source relation on the
    SAME heaps and descriptor. They add no resource exchange, OS state,
    table, ready/current fact, normal-return existence or termination law.
    Actual frame writes/reads and linear ownership remain the old ABI's
    responsibility. No old ABI record or frozen proof is changed. *)
Record Armv7aIRQRegisterSave external platform port
  (abi : Armv7aContinuationABI external platform port) : Type := {
  armv7a_irq_register_save :
    Z -> Z -> OsIntExitCallContext -> Armv7aContinuation -> model -> model -> Prop;
  armv7a_irq_register_save_refinement :
    forall live_r0 live_lr context saved before after,
      armv7a_irq_register_save live_r0 live_lr context saved before after ->
      armv7a_save_transition abi context saved before after /\
      nth 0 saved.(armv7a_continuation_registers) 0 = live_r0 /\
      saved.(armv7a_continuation_lr) = live_lr
}.

Arguments armv7a_irq_register_save {external platform port abi} _ _ _ _ _ _ _.

(** Observation of the descriptor restored by the existing sixteen-load
    source/heap consumer. This is only a register cursor, never CPU or
    stack permission. Its source binding is proved at each actual IRQ. *)
Definition mutex_del_irq_restored_registers (saved : Armv7aContinuation) : KernelSaveRegisters :=
  {| kernel_save_cpsr := saved.(armv7a_continuation_cpsr);
     kernel_save_r0 := nth 0 saved.(armv7a_continuation_registers) 0;
     kernel_save_lr := saved.(armv7a_continuation_lr);
     kernel_save_return_word := None |}.

Lemma mutex_del_irq_register_save_observations : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (registers_source : Armv7aIRQRegisterSave external platform port abi)
  registers handler saved before after,
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
  armv7a_irq_register_save registers_source registers.(kernel_save_r0) registers.(kernel_save_lr)
    handler saved before after ->
  armv7a_save_transition abi handler saved before after /\
  (mutex_del_irq_restored_registers saved).(kernel_save_r0) = registers.(kernel_save_r0) /\
  (mutex_del_irq_restored_registers saved).(kernel_save_lr) = registers.(kernel_save_lr) /\
  armv7a_irq_fiq_mask (mutex_del_irq_restored_registers saved).(kernel_save_cpsr) =
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr).
Proof.
  intros external platform port abi registers_source registers handler saved before after Hmask Hsource.
  destruct (armv7a_irq_register_save_refinement _ _ _ _ registers_source _ _ _ _ _ _ Hsource)
    as [Hsave [Hr0 Hlr]].
  destruct (armv7a_save_transition_observations _ _ _ abi _ _ _ _ Hsave)
    as [_ [_ [_ [Hsaved_mask _]]]].
  split; [exact Hsave|]. split; [exact Hr0|]. split; [exact Hlr|].
  change (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) =
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr)).
  rewrite Hsaved_mask; exact Hmask.
Qed.

Section RegisterIRQComposition.
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

(** One source event, not two independently chosen IRQ descriptions. The
    indexed save, actual writes, SAME normal-return handler trace, actual
    wrapper exit, sixteen frame reads and restore share all their heaps.
    The existing small kernel-client registry is explicit; this relation
    does not claim that it covers arbitrary BSP clients or switching. *)
Inductive mutex_del_irq_register_execution (pc : Z)
  : KernelSaveRegisters -> OsSchedCallContext -> UCOS2_Verify_State -> model ->
    KernelSaveRegisters -> OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| MutexDelIRQRegisterExecution : forall registers state handler saved node publication clients kind
    before saved_heap handler_heap handler_cursor returned_cursor returned_heap exit_cursor exit_heap exited_heap after,
    mutex_del_restore_irq_input sg state handler saved node publication kind ->
    handler.(os_int_exit_interrupted_pc) = pc ->
    handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
    handler.(os_int_exit_handler_stack) = handler_stack ->
    handler.(os_int_exit_handler_fragments) = handler_fragments ->
    armv7a_irq_register_save registers_source registers.(kernel_save_r0) registers.(kernel_save_lr)
      handler saved before saved_heap ->
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg state handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp)) saved_heap handler_heap ->
    normal_return handler sg handler_cursor handler_heap returned_cursor returned_heap ->
    returned_cursor.(restore_handler_current_call) = handler_cursor.(restore_handler_current_call) ->
    returned_cursor.(restore_handler_pc) =
      handler_cursor.(restore_handler_current_call).(restore_handler_return_word) ->
    mutex_del_restore_handler_trace (local_step handler) sg clients
      handler_cursor handler_heap returned_cursor returned_heap ->
    local_step handler returned_cursor returned_heap exit_cursor exit_heap ->
    mutex_del_restore_exit_execution sg kind exit_heap exited_heap ->
    armv7a_continuation_restore_reads saved exited_heap ->
    armv7a_restore_transition abi handler saved exited_heap after ->
    mutex_del_irq_register_execution pc registers handler.(os_int_exit_interrupted_call) state before
      (mutex_del_irq_restored_registers saved)
      (armv7a_continuation_resumed_call saved handler.(os_int_exit_interrupted_call))
      (mutex_del_restore_irq_state state handler saved clients kind) after.

(** A supplied finite sequence, NOT a bound on interrupts or a promise of
    eventual return. Each iteration may change the kernel state. Only the
    actual caller register values and the linked instruction cut persist. *)
Inductive mutex_del_irq_registers_execution (pc : Z)
  : KernelSaveRegisters -> OsSchedCallContext -> UCOS2_Verify_State -> model ->
    KernelSaveRegisters -> OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| MutexDelIRQRegistersDone : forall registers call state heap,
    mutex_del_irq_registers_execution pc registers call state heap registers call state heap
| MutexDelIRQRegistersNext : forall registers call state before middle_registers middle_call middle_state middle
    returned_registers returned final after,
    mutex_del_irq_register_execution pc registers call state before middle_registers middle_call middle_state middle ->
    mutex_del_irq_registers_execution pc middle_registers middle_call middle_state middle
      returned_registers returned final after ->
    mutex_del_irq_registers_execution pc registers call state before returned_registers returned final after.

Lemma mutex_del_irq_register_execution_refinement : forall pc registers call state before
  returned_registers returned final after,
  mutex_del_irq_register_execution pc registers call state before returned_registers returned final after ->
  returned_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  returned_registers.(kernel_save_lr) = registers.(kernel_save_lr) /\
  armv7a_irq_fiq_mask returned_registers.(kernel_save_cpsr) =
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) /\
  mutex_del_restore_irq_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) pc
    registers.(kernel_save_lr) call state before returned final after.
Proof.
  intros pc registers call state before returned_registers returned final after Hrun.
  destruct Hrun as [registers state handler saved node publication clients kind before saved_heap handler_heap
    handler_cursor returned_cursor returned_heap exit_cursor exit_heap exited_heap after
    Hsafe Hpc Hmask Hstack Hfragments Hsave Hentry Hreturn Hsame Hreturn_pc Htrace Hwrapper Hexit Hreads Hrestore].
  destruct (mutex_del_irq_register_save_observations external platform port abi registers_source
    registers handler saved before saved_heap Hmask Hsave) as [Hsource [Hr0 [Hlr Hsaved_mask]]].
  split; [exact Hr0|]. split; [exact Hlr|]. split; [exact Hsaved_mask|].
  cbn [mutex_del_irq_restored_registers] in Hlr.
  econstructor; eassumption.
Qed.

(** This producer obtains the labelled trace from the supplied SAME BSP
    normal return. Neither a desired state nor a trace witness is added
    to the external register law. *)
Lemma mutex_del_irq_register_normal_return : forall pc registers state handler saved node publication kind
  before saved_heap handler_heap handler_cursor returned_cursor returned_heap exit_cursor exit_heap exited_heap after,
  mutex_del_restore_irq_input sg state handler saved node publication kind ->
  handler.(os_int_exit_interrupted_pc) = pc ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask registers.(kernel_save_cpsr) ->
  handler.(os_int_exit_handler_stack) = handler_stack ->
  handler.(os_int_exit_handler_fragments) = handler_fragments ->
  armv7a_irq_register_save registers_source registers.(kernel_save_r0) registers.(kernel_save_lr)
    handler saved before saved_heap ->
  kernel_heap_execution
    (armv7a_irq_live_entry_writes sg state handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_sp)) saved_heap handler_heap ->
  normal_return handler sg handler_cursor handler_heap returned_cursor returned_heap ->
  local_step handler returned_cursor returned_heap exit_cursor exit_heap ->
  mutex_del_restore_exit_execution sg kind exit_heap exited_heap ->
  armv7a_continuation_restore_reads saved exited_heap ->
  armv7a_restore_transition abi handler saved exited_heap after ->
  exists clients,
    mutex_del_irq_register_execution pc registers handler.(os_int_exit_interrupted_call) state before
      (mutex_del_irq_restored_registers saved)
      (armv7a_continuation_resumed_call saved handler.(os_int_exit_interrupted_call))
      (mutex_del_restore_irq_state state handler saved clients kind) after.
Proof.
  intros pc registers state handler saved node publication kind before saved_heap handler_heap handler_cursor
    returned_cursor returned_heap exit_cursor exit_heap exited_heap after
    Hsafe Hpc Hmask Hstack Hfragments Hsave Hentry Hreturn Hwrapper Hexit Hreads Hrestore.
  destruct (mutex_del_restore_handler_normal_return_trace Local
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    (local_step handler) (normal_return handler) (handler_contract handler) sg handler_cursor handler_heap
    returned_cursor returned_heap Hreturn) as [clients [Hsame [Hreturn_pc Htrace]]].
  exists clients; econstructor; eassumption.
Qed.

Lemma mutex_del_irq_registers_execution_refinement : forall pc registers call state before
  returned_registers returned final after,
  mutex_del_irq_registers_execution pc registers call state before returned_registers returned final after ->
  returned_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  returned_registers.(kernel_save_lr) = registers.(kernel_save_lr) /\
  armv7a_irq_fiq_mask returned_registers.(kernel_save_cpsr) =
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) /\
  mutex_del_restore_irqs_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) pc
    registers.(kernel_save_lr) call state before returned final after.
Proof.
  intros pc registers call state before returned_registers returned final after Hrun; induction Hrun.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|constructor].
  - destruct (mutex_del_irq_register_execution_refinement _ _ _ _ _ _ _ _ _ H)
      as [Hr0 [Hlr [Hmask Hstep]]].
    destruct IHHrun as [Hr0' [Hlr' [Hmask' Htail]]].
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    rewrite Hmask, Hlr in Htail; econstructor; eassumption.
Qed.

(** The actual source event is immediately consumed by the already proved
    entry/deposit -> BSP/client -> take/read/restore resource chain. The
    table is carried ONCE by that chain's program world, not by this new
    ABI. Foreign parked continuations retain their original ABI owners. *)
Lemma mutex_del_irq_registers_execution_resources : forall pc registers call state before
  returned_registers returned final after (frame : Assertion),
  mutex_del_irq_registers_execution pc registers call state before returned_registers returned final after ->
  (kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
    (kernel_program_inv sg state ** task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  returned_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  returned_registers.(kernel_save_lr) = registers.(kernel_save_lr) /\
  armv7a_irq_fiq_mask returned_registers.(kernel_save_cpsr) =
    armv7a_irq_fiq_mask registers.(kernel_save_cpsr) /\
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  (kernel_call_execution_owned external platform returned
      (armv7a_irq_fiq_mask returned_registers.(kernel_save_cpsr)) **
    (kernel_program_inv sg final ** task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros pc registers call state before returned_registers returned final after frame Hrun Hpre.
  destruct (mutex_del_irq_registers_execution_refinement _ _ _ _ _ _ _ _ _ Hrun)
    as [Hr0 [Hlr [Hmask Hsource]]].
  destruct (mutex_del_restore_irqs_execution_resources external platform port abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments _ _ _ _ _ _ _ _ _ frame Hsource Hpre)
    as [Hi [Ho [Hs Hpost]]].
  split; [exact Hr0|]. split; [exact Hlr|]. split; [exact Hmask|].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|].
  rewrite Hmask; exact Hpost.
Qed.

(** The Save+4 consumer begins at MRS's real value cut, allows finitely
    many actual ordinary IRQ returns, then consumes CPSID/DSB/BX and Del's
    physical cpu_sr assignment. R0/LR joins are conclusions of the indexed
    source chain above, not caller premises. [acquired] is the actual state
    at CPSID and is not equated with the pre-interrupt state. The owned
    cpu_sr cell is a disjoint borrowed local, not allocated by its address. *)
Lemma mutex_del_call_irq_save_store : forall critical arch
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  call state registers before returned_registers returned acquired resumed
  final_registers final_state saved_heap cpu_sr after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  (mutex_del_call_owned external platform sg call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
    task_stack_fragments_rep handler_stack handler_fragments ** (cpu_sr # UInt |->_) ** frame) before ->
  mutex_del_irq_registers_execution (armv7a_save_entry_address suffix + 4)
    (kernel_save_read_cpsr registers) call state before returned_registers returned acquired resumed ->
  armv7a_save_suffix_transition suffix returned_registers acquired resumed final_registers final_state saved_heap ->
  kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) saved_heap after ->
  kernel_call_save_instruction_step arch SaveReadCPSR registers state before
    (kernel_save_read_cpsr registers) state before /\
  kernel_save_after_mrs_execution arch returned_registers acquired resumed final_registers final_state saved_heap /\
  final_state = acquired /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  (mutex_del_call_masked external platform critical sg returned final_registers.(kernel_save_r0)
     acquired acquired ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
   task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros critical arch suffix call state registers before returned_registers returned acquired resumed
    final_registers final_state saved_heap cpu_sr after frame Hnone Hvalid Hpre Hirqs Hsuffix Hstore.
  assert (Hopen : mutex_del_call_owned external platform sg call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      task_stack_fragments_rep handler_stack handler_fragments ** (cpu_sr # UInt |->_) ** frame |--
    kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
      (kernel_program_inv sg state ** task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** frame))).
  { change (mutex_del_call_owned external platform sg call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      task_stack_fragments_rep handler_stack handler_fragments ** (cpu_sr # UInt |->_) ** frame |--
    kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
      (kernel_program_inv sg state ** task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** frame))).
    unfold mutex_del_call_owned; entailer!. }
  destruct (mutex_del_irq_registers_execution_resources _ _ _ _ _ _ _ _ _ _ Hirqs (Hopen before Hpre))
    as [Hr0 [Hlr [Hmask [Hi [Ho [Hs Hresumed]]]]]].
  cbn [kernel_save_read_cpsr] in Hr0, Hlr, Hmask.
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask returned_registers.(kernel_save_cpsr)) returned_registers.(kernel_save_r0)).
  { unfold interrupt_saved_value; rewrite Hr0, Hmask; split; [exact Hvalid|reflexivity]. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg returned
    returned_registers acquired resumed final_registers final_state saved_heap _ Hsaved Hresumed Hsuffix)
    as [Hstate [Hmemory [Hreturn [Hvalue Hsaved_heap]]]].
  assert (Hfinal_value : final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr)).
  { rewrite Hvalue; exact Hr0. }
  assert (Hstore_order : critical_region_masked platform critical sg returned.(os_sched_call_invocation)
      returned.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
      os_sched_context_resources external returned **
      (kernel_program_inv sg acquired ** task_stack_fragments_rep handler_stack handler_fragments **
       ((cpu_sr # UInt |->_) ** frame)) |--
    mutex_del_call_masked external platform critical sg returned final_registers.(kernel_save_r0)
      acquired acquired ** (cpu_sr # UInt |->_) **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame)).
  { unfold mutex_del_call_masked; entailer!. }
  pose proof (mutex_del_call_saved_return_store external platform critical sg returned
    final_registers.(kernel_save_r0) acquired acquired cpu_sr saved_heap after _
    ltac:(rewrite Hfinal_value; exact Hvalid) (Hstore_order saved_heap Hsaved_heap) Hstore) as Hpost.
  split; [constructor; [exact Hnone|reflexivity]|].
  split; [exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hsuffix)|].
  split; [exact Hstate|]. split; [exact Hfinal_value|]. split; [rewrite Hreturn, Hlr; reflexivity|].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|].
  assert (Hclose : mutex_del_call_masked external platform critical sg returned final_registers.(kernel_save_r0)
      acquired acquired ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    mutex_del_call_masked external platform critical sg returned final_registers.(kernel_save_r0)
      acquired acquired ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame) by entailer!.
  exact (Hclose after Hpost).
Qed.

(** The approved C prefix now feeds the interrupted Save producer and the
    actual cpu_sr assignment. The old NULL/type/ISR branches remain in
    mutex_del_call_prefix_execution; this is precisely its continuation
    branch. No acquired public-slot or stable pre-Save type is assumed:
    the following protected type read must use the acquired state's real
    public/private resource branch. That separate lifetime issue is _6. *)
Lemma mutex_del_call_prefix_irq_save_store : forall critical arch
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  call state registers pe eid observed perr old_error cpu_sr before prefix_heap
  returned_registers returned acquired resumed final_registers final_state saved_heap after (frame : Assertion),
  mutex_del_call_pointer_domain sg state pe eid observed ->
  (mutex_del_call_owned external platform sg call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_call_prefix_execution sg pe perr before None prefix_heap ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  mutex_del_irq_registers_execution (armv7a_save_entry_address suffix + 4)
    (kernel_save_read_cpsr registers) call state prefix_heap returned_registers returned acquired resumed ->
  armv7a_save_suffix_transition suffix returned_registers acquired resumed final_registers final_state saved_heap ->
  kernel_heap_execution (pointer_store_writes cpu_sr final_registers.(kernel_save_r0)) saved_heap after ->
  final_state = acquired /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  (mutex_del_call_masked external platform critical sg returned final_registers.(kernel_save_r0)
     acquired acquired ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
   (perr # UChar |-> old_error) ** task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros critical arch suffix call state registers pe eid observed perr old_error cpu_sr before prefix_heap
    returned_registers returned acquired resumed final_registers final_state saved_heap after frame
    Hdomain Hpre Hprefix Hnone Hvalid Hirqs Hsuffix Hstore.
  assert (Hopen : mutex_del_call_owned external platform sg call
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
       (cpu_sr # UInt |->_) ** task_stack_fragments_rep handler_stack handler_fragments ** frame)).
  { unfold mutex_del_call_owned; entailer!. }
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error before None prefix_heap _
    Hdomain (Hopen before Hpre) Hprefix) as [Hguards Hguarded].
  assert (Hsave_order : kernel_program_inv sg state ** (perr # UChar |-> old_error) **
      (kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
       (cpu_sr # UInt |->_) ** task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    mutex_del_call_owned external platform sg call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
      task_stack_fragments_rep handler_stack handler_fragments ** (cpu_sr # UInt |->_) **
      ((perr # UChar |-> old_error) ** frame)).
  { unfold mutex_del_call_owned; entailer!. }
  destruct (mutex_del_call_irq_save_store critical arch suffix call state registers prefix_heap
    returned_registers returned acquired resumed final_registers final_state saved_heap cpu_sr after _
    Hnone Hvalid (Hsave_order prefix_heap Hguarded) Hirqs Hsuffix Hstore)
    as [Hmrs [Hsuffix_source [Hstate [Hr0 [Hlr [Hi [Ho [Hs Hpost]]]]]]]].
  split; [exact Hstate|]. split; [exact Hr0|]. split; [exact Hlr|].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|].
  assert (Hclose : mutex_del_call_masked external platform critical sg returned final_registers.(kernel_save_r0)
      acquired acquired ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      task_stack_fragments_rep handler_stack handler_fragments ** ((perr # UChar |-> old_error) ** frame) |--
    mutex_del_call_masked external platform critical sg returned final_registers.(kernel_save_r0)
      acquired acquired ** (cpu_sr # UInt |-> final_registers.(kernel_save_r0)) **
      (perr # UChar |-> old_error) ** task_stack_fragments_rep handler_stack handler_fragments ** frame) by entailer!.
  exact (Hclose after Hpost).
Qed.

(** Register observation immediately after the one actual MSR prefix. The
    CPSR field here is the MSR-written word, not the older current-CPSR
    observation stored in KernelRestoreCursor. *)
Definition mutex_del_restore_written_registers (cursor : KernelRestoreCursor) : KernelSaveRegisters :=
  {| kernel_save_cpsr := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0);
     kernel_save_r0 := cursor.(kernel_restore_r0);
     kernel_save_lr := cursor.(kernel_restore_lr);
     kernel_save_return_word := None |}.

(** BX uses the values restored by the last actual IRQ. The MSR field is
    the original cut observation; it is not a claim that the complete CPSR
    stayed equal during interrupts. Register transport will prove this
    cursor equals the prefix's BX cursor before the suffix is consumed. *)
Definition mutex_del_restore_resumed_cursor (cursor : KernelRestoreCursor)
  (registers : KernelSaveRegisters) : KernelRestoreCursor :=
  {| kernel_restore_current_cpsr := cursor.(kernel_restore_current_cpsr);
     kernel_restore_r0 := registers.(kernel_save_r0);
     kernel_restore_lr := registers.(kernel_save_lr);
     kernel_restore_msr_word := Some
       (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0));
     kernel_restore_return_word := None |}.

(** One real prefix, finite register-indexed IRQ returns at Restore+8,
    then BX of the ACTUALLY restored LR. This removes the former naked LR
    equality from this source-facing consumer, without weakening the old
    resource ABI or putting the table in the new observation contract. *)
Lemma mutex_del_call_irq_restore : forall critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  call saved entry checkpoint restore_entry cursor before written_cursor released
  returned_registers returned final resumed final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (mutex_del_call_masked external platform critical sg call saved entry checkpoint **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor released ->
  mutex_del_irq_registers_execution (restore_entry + 8)
    (mutex_del_restore_written_registers cursor) call checkpoint released
    returned_registers returned final resumed ->
  armv7a_restore_suffix_transition restore (mutex_del_restore_resumed_cursor cursor returned_registers)
    resumed final_cursor after ->
  mutex_del_restore_resumed_cursor cursor returned_registers = written_cursor /\
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (kernel_program_closed platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) final **
   os_sched_context_resources external returned **
   task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros critical arch restore call saved entry checkpoint restore_entry cursor before written_cursor released
    returned_registers returned final resumed final_cursor after frame Hr0 Hmask Hpre Hprefix Hirqs Hsuffix.
  destruct (mutex_del_irq_registers_execution_refinement _ _ _ _ _ _ _ _ _ Hirqs)
    as [Hrestored_r0 [Hrestored_lr [Hrestored_mask Hsource]]].
  change (returned_registers.(kernel_save_r0) = cursor.(kernel_restore_r0)) in Hrestored_r0.
  change (returned_registers.(kernel_save_lr) = cursor.(kernel_restore_lr)) in Hrestored_lr.
  change (mutex_del_restore_irqs_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments
    (armv7a_irq_fiq_mask (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
      cursor.(kernel_restore_r0))) (restore_entry + 8) cursor.(kernel_restore_lr)
    call checkpoint released returned final resumed) in Hsource.
  pose proof (armv7a_restore_prefix_source _ _ _ _ restore _ _ _ _ Hprefix) as Hprefix_source.
  pose proof (kernel_call_restore_prefix_cursor _ _ _ _ _ Hprefix_source) as Hwritten.
  assert (Hcursor : mutex_del_restore_resumed_cursor cursor returned_registers = written_cursor).
  { rewrite Hwritten; unfold mutex_del_restore_resumed_cursor, kernel_restore_write_cpsr.
    rewrite Hrestored_r0, Hrestored_lr; reflexivity. }
  rewrite armv7a_cpsr_restore_mask_eq, Hr0 in Hsource.
  rewrite Hcursor in Hsuffix.
  assert (Hopen : mutex_del_call_masked external platform critical sg call saved entry checkpoint **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved entry ** os_sched_context_resources external call **
      (kernel_program_inv sg checkpoint ** task_stack_fragments_rep handler_stack handler_fragments ** frame)).
  { unfold mutex_del_call_masked; entailer!. }
  split; [exact Hcursor|].
  exact (mutex_del_restore_call_normal_return external platform port abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch restore call saved entry checkpoint
    restore_entry cursor before written_cursor released returned final resumed final_cursor after frame
    Hr0 Hmask (Hopen before Hpre) Hprefix Hsource Hsuffix).
Qed.

(** The source-facing Restore consumer supplies an actual following Del
    entry owner and borrowed locals on its real return heap. The original
    prefix still includes all three early errors. The parameter-domain
    condition belongs to THIS next Del call, not the old mutex or a promise
    that the previous interrupt preserved an ECB lifetime. This is the
    C-source handoff; arbitrary compiled BL/argument setup is not proved. *)
Lemma mutex_del_call_prefix_after_irq_restore : forall critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  original saved entry checkpoint restore_entry cursor before written_cursor released
  returned_registers returned final resumed final_cursor after pe eid observed perr old_error cpu_sr (frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (mutex_del_call_masked external platform critical sg original saved entry checkpoint **
    task_stack_fragments_rep handler_stack handler_fragments **
    ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor released ->
  mutex_del_irq_registers_execution (restore_entry + 8)
    (mutex_del_restore_written_registers cursor) original checkpoint released
    returned_registers returned final resumed ->
  armv7a_restore_suffix_transition restore (mutex_del_restore_resumed_cursor cursor returned_registers)
    resumed final_cursor after ->
  mutex_del_call_pointer_domain sg final pe eid observed ->
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
  exists initialized result prefix_after,
    kernel_heap_execution (pointer_store_writes cpu_sr 0) after initialized /\
    mutex_del_call_prefix_execution sg pe perr initialized result prefix_after /\
    mutex_del_call_prefix_post sg final pe eid perr old_error result
      ((cpu_sr # UInt |-> 0) **
       (kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask saved) **
        task_stack_fragments_rep handler_stack handler_fragments ** frame)) prefix_after.
Proof.
  intros critical arch restore original saved entry checkpoint restore_entry cursor before written_cursor released
    returned_registers returned final resumed final_cursor after pe eid observed perr old_error cpu_sr frame
    Hr0 Hmask Hpre Hprefix Hirqs Hsuffix Hdomain.
  destruct (mutex_del_call_irq_restore critical arch restore original saved entry checkpoint
    restore_entry cursor before written_cursor released returned_registers returned final resumed final_cursor after
    ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame) Hr0 Hmask Hpre Hprefix Hirqs Hsuffix)
    as [Hcursor [Hi [Ho [Hs [Hlr Hreturned]]]]].
  assert (Hopen : kernel_program_closed platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) final **
      os_sched_context_resources external returned ** task_stack_fragments_rep handler_stack handler_fragments **
      ((perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) ** frame) |--
    kernel_program_inv sg final ** (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      (kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask saved) **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)).
  { rewrite kernel_program_closed_equiv; unfold kernel_call_execution_owned; rewrite Hi, Ho; entailer!. }
  split; [exact Hlr|]. split; [exact Hi|]. split; [exact Ho|].
  eapply mutex_del_call_entry_prefix_source; [exact Hdomain|exact (Hopen after Hreturned)].
Qed.

End RegisterIRQComposition.
