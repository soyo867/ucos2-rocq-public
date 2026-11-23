Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac_scope.

(** Fresh registration changes the call label, not the current task or its
    waiting fields. This is the already approved ordinary task protocol;
    the separate early-error and nonblocking admission alternatives remain
    unchanged. In particular Boot is not required to satisfy this lemma. *)
Lemma sem_pend_sequential_call_stage : forall sg previous state,
  sem_pend_task_call_stage sg previous state ->
  sem_pend_task_call_stage sg
    (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation))
    (replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state).
Proof.
  intros sg previous state [[Horigin [Hactive Hcurrent]] [Hrunning Hnode]].
  unfold sem_pend_task_call_stage, kernel_call_task_source.
  cbn [kernel_sequential_call os_sched_call_origin os_sched_call_invocation os_sched_call_stack].
  split.
  - split; [exact Horigin|]. split; [|exact Hcurrent].
    apply task_begin_invocation_active; exact (proj2 (proj2 Hactive)).
  - split; [exact Hrunning|exact Hnode].
Qed.

(** Consume the actual current execution at a source-bound subsequent
    entry, register its fresh invocation and return the SAME strong world
    expected by the first-Save producer. The ABI exchanges execution only;
    the existing task protocol and kernel ghost-update lemmas establish
    every OS fact. The caller's other resources remain in the real frame. *)
Lemma sem_pend_sequential_entry_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (boundary : KernelSequentialCallABI external platform)
  sg previous mask state before after (frame : Assertion),
  kernel_sequential_call_source boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) before after ->
  (sem_pend_task_stack_resources abi kernel_program_inv sg previous mask state ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := replace_TskS
    (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (sem_pend_task_stack_resources abi kernel_program_inv sg call mask registered ** frame) after.
Proof.
  intros external platform port abi boundary sg previous mask state before after frame
    Hsource Hbefore call registered.
  assert (Hopen : sem_pend_task_stack_resources abi kernel_program_inv sg previous mask state ** frame |--
    coq_prop (sem_pend_task_call_stage sg previous state) &&
    (kernel_call_execution_owned external platform previous mask **
     (kernel_stack_inv abi kernel_program_inv sg
       (Some (task_stack_key previous.(os_sched_call_stack))) state ** frame)))
    by (unfold sem_pend_task_stack_resources; entailer!).
  destruct (Hopen before Hbefore) as [Hstage Howned].
  destruct (kernel_sequential_call_owned_entry external platform boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _ Hsource Howned)
    as [Hmemory Hreturned].
  fold call in Hreturned; split; [exact Hmemory|].
  pose proof (sem_pend_sequential_call_stage sg previous state Hstage) as Hregistered_stage.
  change (sem_pend_task_call_stage sg call registered) in Hregistered_stage.
  assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin)).
  { destruct Hstage as [[_ [[_ [_ Hlive]] _]] _]; exact Hlive. }
  match type of Hreturned with ?P after => match goal with |- ?Q after =>
    assert (Hregister : P |-- Q) end end.
  { unfold sem_pend_task_stack_resources, kernel_stack_inv; rewrite !kernel_program_inv_split_unmap.
    Intros.
    sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state previous.(os_sched_call_origin) Hlive).
    change (armv7a_task_stack_continuations abi registered.(TskState)
      registered.(TskState).(parkedTaskStacks)) with
      (armv7a_task_stack_continuations abi state.(TskState) state.(TskState).(parkedTaskStacks)).
    entailer!. }
  exact (Hregister after Hreturned).
Qed.

(** The actual MRS/CPSID/DSB/BX branch after that entry. This consumes the
    entry heap produced above, not a newly assumed acquired task stage.
    Interrupting executions require the separate IRQ/source-return chain;
    they are not excluded from the public SemPend contract. *)
Lemma sem_pend_sequential_entry_uninterrupted_save : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (boundary : KernelSequentialCallABI external platform)
  (suffix : Armv7aSaveSuffixABI external platform critical arch)
  sg previous mask state before entered registers final_registers acquired after (frame : Assertion),
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := replace_TskS
    (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  kernel_sequential_call_source boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) before entered ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_task_stack_resources abi kernel_program_inv sg previous mask state ** frame) before ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) registered entered
    final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers registered entered final_registers acquired after /\
  acquired = registered /\ sem_pend_task_call_stage sg call acquired /\
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) final_registers.(kernel_save_r0) acquired **
   os_sched_context_resources external call **
   kernel_stack_inv abi kernel_program_inv sg (Some (task_stack_key call.(os_sched_call_stack))) acquired **
   frame) after.
Proof.
  intros external platform port critical arch abi boundary suffix sg previous mask state before entered
    registers final_registers acquired after frame call registered Hentry Hreturn Hcpsr Hmask Hbefore Hsave.
  destruct (sem_pend_sequential_entry_resources external platform port abi boundary sg previous mask state
    before entered frame Hentry Hbefore) as [Hmemory Hentered].
  fold call registered in Hentered.
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  rewrite <- Hmask in Hentered.
  destruct (sem_pend_save_suffix_keeps_stack_resources external platform port critical arch abi suffix
    kernel_program_inv sg call registered (kernel_save_read_cpsr registers) entered final_registers
    acquired after frame Hsaved Hentered Hsave)
    as [Hstate [Hsame [Hrun [Hreturned [Hvalue [Hstage Howned]]]]]].
  split.
  - unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|exact Hrun].
  - exact (conj Hstate (conj Hstage Howned)).
Qed.
