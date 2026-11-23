Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_save_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_readonly_irq_save_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Section RuntimeSources.
Context (environment : MutexDelCallEnvironment) (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) =>
      mutex_del_restore_handler_owner environment.(mutex_del_call_platform)
        environment.(mutex_del_call_port) handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

(** A projection of the ALREADY defined physical counter execution, not
    a new IRQ grammar or a frame rule for arbitrary configured handlers. *)
Lemma mutex_del_counter_irqs_owner_history : forall mask pc lr call state before returned current after,
  mutex_del_restore_irqs_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) sg Local local_step normal_return
    handler_stack handler_fragments mask pc lr call state before returned current after ->
  mutex_owner_source_history sg state current.
Proof.
  intros mask pc lr call state before returned current after Hrun; induction Hrun.
  - constructor.
  - eapply mutex_owner_source_history_trans; [|exact IHHrun].
    destruct H as [state handler saved node publication clients kind before saved_heap handler_heap handler_cursor
      returned_cursor returned_heap exit_cursor exit_heap exited_heap irq_after Hsafe Hpc Hmask Hlr Hstack Hfragments
      Hsave Hentry Hreturn Hsame Hreturn_pc Htrace Hwrapper Hexit Hreads Hrestore].
    destruct (mutex_del_restore_irq_tasks_event_eq sg state handler saved node publication clients kind Hsafe)
      as [Htasks Hevents].
    destruct Hsafe as [Hrunning [Hnest [Hcurrent [Hnode Hrest]]]].
    eapply mutex_program_task_fields_source with
      (tid := handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot))
      (old := node) (new := task_set_saved_sp node saved.(armv7a_continuation_sp));
      [exact Hnode|reflexivity|reflexivity|rewrite Htasks; reflexivity|rewrite Hevents; reflexivity].
Qed.

(** This establishes the actual modular Save post consumed by the new C
    carrier for the existing MRS+4 family. All CPSR/R0/LR observations still
    come from that source; mask equality is never promoted to full CPSR
    equality. Missing other returning source families remain separate. *)
Lemma mutex_del_runtime_irq_save_post : forall critical arch
  (suffix : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (registers_source : Armv7aIRQRegisterSave environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  call state registers before returned_registers returned acquired resumed final_registers final_state after
  (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  (kernel_stack_call_closed environment.(mutex_del_call_continuations) mutex_del_stack_resources sg
     (task_stack_call_active_key call) call (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  mutex_del_irq_registers_execution environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_save_entry_address suffix + 4)
    (kernel_save_read_cpsr registers) call state before returned_registers returned acquired resumed ->
  armv7a_save_suffix_transition suffix returned_registers acquired resumed final_registers final_state after ->
  final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_cpsr) = Z.lor returned_registers.(kernel_save_cpsr) 192 /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  (mutex_del_runtime_save_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) critical sg call
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0) state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros critical arch suffix registers_source call state registers before returned_registers returned acquired resumed
    final_registers final_state after frame Hnone Hvalid Hpre Hirqs Hsuffix.
  destruct (mutex_del_stack_irq_save_resources environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
    handler_contract handler_stack handler_fragments critical arch suffix
    (task_stack_call_active_key call) call state registers before returned_registers returned acquired resumed
    final_registers final_state after frame Hnone Hvalid Hpre Hirqs Hsuffix)
    as [Hmrs [Hsource [Hstate [Hr0 [Hcpsr [Hlr [Hsame [Hevents Hpost]]]]]]]].
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations) registers_source sg Local local_step normal_return
    handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hirqs) as [_ [_ [_ Hcounter]]].
  pose proof (mutex_del_counter_irqs_owner_history _ _ _ _ _ _ _ _ _ Hcounter) as Hhistory.
  assert (Hsaved : interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
    final_registers.(kernel_save_r0)).
  { unfold interrupt_saved_value; rewrite Hr0; auto. }
  split; [exact Hr0|]. split; [exact Hcpsr|]. split; [exact Hlr|].
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (mutex_del_runtime_save_post_from_masked environment environment critical sg call returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0)
      state acquired eq_refl Hhistory Hsame Hsaved); entailer!. }
  exact (Hclose after Hpost).
Qed.

(** The existing continuous physical error execution now consumes and
    establishes the SAME entry/public post used by the canonical C caller.
    Its old finite counter-source boundary is retained verbatim; this is
    neither total Save/Restore coverage nor an assembly/BSP linking claim. *)
Lemma mutex_del_runtime_readonly_irq_source_post : forall critical arch
  (save : Armv7aSaveSuffixABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) critical arch)
  (registers_source : Armv7aIRQRegisterSave environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port)
    environment.(mutex_del_call_continuations))
  restore_entry call state mask registers pe eid observed option perr old_error cpu_sr code saved_word
  before entered acquired returned final after (frame : Assertion),
  mutex_del_parent_input sg pe state eid observed ->
  (mutex_del_runtime_entry environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state **
    (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) before ->
  mutex_del_readonly_error_irq_save_execution environment critical arch sg Local save restore
    registers_source local_step normal_return handler_stack handler_fragments restore_entry
    call state mask registers pe option perr cpu_sr code saved_word
    before entered acquired returned final after ->
  saved_word = registers.(kernel_save_cpsr) /\
  (mutex_del_runtime_post environment environment.(mutex_del_call_external)
     environment.(mutex_del_call_platform) sg call mask state pe option eid pe (encode_os_err_code code) **
    (perr # UChar |-> encode_os_err_code code) ** (cpu_sr # UInt |-> saved_word) **
    task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros critical arch save restore registers_source restore_entry call state mask registers pe eid observed
    option perr old_error cpu_sr code saved_word before entered acquired returned final after frame
    Hdomain Hpre Hrun.
  set (abi := environment.(mutex_del_call_continuations)).
  assert (Hopen : mutex_del_runtime_entry environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state |--
    kernel_stack_call_closed abi mutex_del_stack_resources sg (task_stack_call_active_key call) call mask state).
  { unfold mutex_del_runtime_entry; Intros same_environment.
    destruct H as [Henv ->]; reflexivity. }
  assert (Howned : (kernel_stack_call_closed abi mutex_del_stack_resources sg
      (task_stack_call_active_key call) call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Horder : P |-- Q) end end.
    { sep_apply_l_atomic Hopen; entailer!. }
    exact (Horder before Hpre). }
  destruct (mutex_del_readonly_error_irq_save_post environment critical arch sg Local save restore
    registers_source local_step normal_return handler_contract handler_stack handler_fragments
    restore_entry (task_stack_call_active_key call) call state mask registers pe eid observed option perr old_error
    cpu_sr code saved_word before entered acquired returned final after frame Hdomain Howned Hrun)
    as [Hsaved [Hentered [Hreturned [Hobservation [Hexecution Hafter]]]]].
  destruct Hrun as (initialized & prefix_heap & returned_registers & resumed & final_registers & final_state &
    saved_heap & body_heap & middle & restored & returned_heap & cursor & written & final_cursor & group &
    Hinit & Hprefix & Hnone & Hvalid & Hmask & Hsave_irqs & Hsave_suffix & Hsaved_word & Hrest).
  destruct (mutex_del_irq_registers_execution_refinement environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) environment.(mutex_del_call_port) abi registers_source sg Local
    local_step normal_return handler_stack handler_fragments _ _ _ _ _ _ _ _ _ Hsave_irqs)
    as [_ [_ [_ Hcounter]]].
  pose proof (mutex_del_counter_irqs_owner_history _ _ _ _ _ _ _ _ _ Hcounter) as Hhistory.
  set (residual := kernel_call_execution_owned environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) call mask **
    mutex_del_stack_critical_frame abi sg (task_stack_call_active_key call) state **
    task_stack_fragments_rep handler_stack handler_fragments ** frame).
  assert (Horder : kernel_stack_call_closed abi mutex_del_stack_resources sg
      (task_stack_call_active_key call) call mask state **
      (perr # UChar |-> old_error) ** (cpu_sr # UInt |->_) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame |--
    (cpu_sr # UInt |->_) ** (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** residual)).
  { unfold kernel_stack_call_closed, residual.
    rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (task_stack_uint_store_execution cpu_sr 0 _ before ltac:(lia) (Horder before Howned))
    as [produced [Hwrite Hinitialized]].
  assert (produced = initialized) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hprefix_order : (cpu_sr # UInt |-> 0) **
      (kernel_program_inv sg state ** (perr # UChar |-> old_error) ** residual) |--
    kernel_program_inv sg state ** (perr # UChar |-> old_error) ** ((cpu_sr # UInt |-> 0) ** residual)) by entailer!.
  destruct (mutex_del_call_prefix_resources sg state pe eid observed perr old_error initialized None prefix_heap
    _ Hdomain (Hprefix_order initialized Hinitialized) Hprefix) as [Hprefix_facts Hprefix_owned].
  destruct Hprefix_facts as [Hnonnull [Htype Hnest]].
  assert (Hprefix_ok : mutex_del_parent_prefix_ok pe state eid).
  { unfold mutex_del_parent_prefix_ok; apply mutex_del_before_save_continues_iff;
    [rewrite Hnest; lia|auto]. }
  split; [exact Hsaved|].
  assert (Hresult : kernel_stack_call_closed abi mutex_del_stack_resources sg
      (task_stack_call_active_key call) returned mask final |--
    mutex_del_runtime_post environment environment.(mutex_del_call_external)
      environment.(mutex_del_call_platform) sg call mask state pe option eid pe (encode_os_err_code code)).
  { unfold mutex_del_runtime_post; Left; Right; Exists acquired acquired 0.
    apply _derivable1_andp_intros; [entailer!|].
    unfold mutex_del_runtime_return, mutex_del_runtime_return_at; Exists returned final environment.
    unfold mutex_del_callsite_environment; entailer!. }
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold abi in Hresult; sep_apply_l_atomic Hresult; entailer!. }
  exact (Hclose after Hafter).
Qed.
End RuntimeSources.
