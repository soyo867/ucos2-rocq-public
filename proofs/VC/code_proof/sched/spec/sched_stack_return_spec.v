Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A SOURCE history, not an ABI field or ownership assertion. The IRQ
    constructor deliberately keeps the three different OS snapshots:
    released, deposited/parked, and wrapper-restored current. In particular
    it does not fabricate a critical_region_interval from released to
    current by forgetting the entry stores and final take.

    The concrete and state registry traces must be produced together by
    the registered-source resource proof; the constructor does not itself
    prove preservation or recover a spatial owner. Resource postconditions
    below are separate and are established on the actual final heap.
    The IRQ suffix retains the actual MSR control word computed from
    current CPSR and R0. Only its I/F mask equals the saved mask; equality
    of the entire computed word and saved R0 is not assumed.
    These constructors describe the checked returning branches only, not
    a claim that every execution returns or that all source branches have
    already been integrated into a public callee theorem. *)
Inductive kernel_call_restore_history environment critical sg :
  OsSchedCallContext -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop :=
| KernelCallRestoreUninterrupted : forall arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    call released cursor before written middle final_cursor after,
    armv7a_restore_prefix_transition restore cursor before written middle ->
    armv7a_restore_suffix_transition restore written middle final_cursor after ->
    kernel_call_restore_history environment critical sg call released call released
| KernelCallRestoreIRQ : forall arch Extra
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
      KernelClientHeapCut Extra -> model -> Prop)
    (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
      KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
    call released handler suspended selected cursor before written irq_input saved_heap
    registry_heap closed_heap returned stopped returned_origin irq_return resume_cursor final_cursor after,
    handler.(os_int_exit_interrupted_call) = call ->
    armv7a_restore_prefix_transition restore cursor before written irq_input ->
    armv7a_save_transition environment.(task_stack_call_continuations)
      handler suspended irq_input saved_heap ->
    kernel_heap_execution (armv7a_irq_live_entry_writes sg released
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
      saved_heap registry_heap ->
    kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
      KernelClientHeapClosed closed_heap ->
    kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed
      (armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments)) KernelClientHeapClosed returned ->
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      call.(os_sched_call_invocation) None call.(os_sched_call_origin)
      (armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments)) stopped returned_origin returned ->
    armv7a_irq_restore_pointer_reads sg closed_heap
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) ->
    armv7a_continuation_focus_binding (armv7a_call_focus call suspended.(armv7a_continuation_pc)
      suspended.(armv7a_continuation_lr)) selected ->
    selected.(armv7a_continuation_stack) = call.(os_sched_call_stack) ->
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) ->
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) ->
    armv7a_restore_transition environment.(task_stack_call_continuations)
      handler selected closed_heap irq_return ->
    resume_cursor.(kernel_restore_msr_word) = Some
      (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
        cursor.(kernel_restore_r0)) ->
    resume_cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
    armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
    kernel_call_restore_history environment critical sg call released
      (armv7a_continuation_resumed_call selected call)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))
| KernelCallRestoreIRQSamePriority : forall arch Extra
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
      KernelClientHeapCut Extra -> model -> Prop)
    (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
      KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
    call released handler suspended selected cursor before written irq_input saved_heap
    registry_heap closed_heap returned stopped returned_origin exit_heap irq_return
    resume_cursor final_cursor after,
    handler.(os_int_exit_interrupted_call) = call ->
    armv7a_restore_prefix_transition restore cursor before written irq_input ->
    armv7a_save_transition environment.(task_stack_call_continuations)
      handler suspended irq_input saved_heap ->
    kernel_heap_execution (armv7a_irq_live_entry_writes sg released
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
      saved_heap registry_heap ->
    kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
      KernelClientHeapClosed closed_heap ->
    kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed
      (armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments)) KernelClientHeapClosed returned ->
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      call.(os_sched_call_invocation) None call.(os_sched_call_origin)
      (armv7a_irq_live_parked_state released call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments)) stopped returned_origin returned ->
    os_int_exit_masked_same_priority_fragment sg closed_heap exit_heap ->
    armv7a_irq_restore_pointer_reads sg exit_heap
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) ->
    armv7a_continuation_focus_binding (armv7a_call_focus call suspended.(armv7a_continuation_pc)
      suspended.(armv7a_continuation_lr)) selected ->
    selected.(armv7a_continuation_stack) = call.(os_sched_call_stack) ->
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) ->
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) ->
    armv7a_restore_transition environment.(task_stack_call_continuations)
      handler selected exit_heap irq_return ->
    resume_cursor.(kernel_restore_msr_word) = Some
      (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr)
        cursor.(kernel_restore_r0)) ->
    resume_cursor.(kernel_restore_lr) = selected.(armv7a_continuation_lr) ->
    armv7a_restore_suffix_transition restore resume_cursor irq_return final_cursor after ->
    kernel_call_restore_history environment critical sg call released
      (armv7a_continuation_resumed_call selected call)
      (os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state returned)
        call.(os_sched_call_stack)).

(** Kernel-state history of the checked Save branches. The IRQ branch is
    specifically an interruption at the instruction after MRS (+4), then
    the real deposit, ONE registered heap/state/source trace, wrapper take
    and restored CPSID/DSB/BX suffix. It keeps the parked/current snapshots
    rather than asserting a flat before-to-acquired interval.

    This is not a completeness theorem for all Save executions: IRQ before
    MRS, nested/repeated entry outside the supplied registry trace and
    other restore routes need their own actual source composition. These
    constructors contain no ready predicate and no spatial postcondition.
    Resource/stage producers must separately supply their actual owners
    and observations on the SAME heap/state path. *)
Inductive kernel_call_save_history environment critical sg :
  OsSchedCallContext -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop :=
| KernelCallSaveUninterrupted : forall arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    call state registers before final_registers after,
    registers.(kernel_save_return_word) = None ->
    armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
      final_registers state after ->
    kernel_call_save_history environment critical sg call state call state
| KernelCallSaveIRQ : forall arch Extra
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
      KernelClientHeapCut Extra -> model -> Prop)
    (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
      KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
    call state handler suspended selected registers before irq_input saved_heap
    registry_heap closed_heap returned stopped returned_origin restored resume_registers final_registers after,
    handler.(os_int_exit_interrupted_call) = call ->
    kernel_call_save_instruction_step arch SaveReadCPSR registers state before
      (kernel_save_read_cpsr registers) state irq_input ->
    suspended.(armv7a_continuation_pc) = armv7a_save_entry_address save + 4 ->
    armv7a_save_transition environment.(task_stack_call_continuations)
      handler suspended irq_input saved_heap ->
    kernel_heap_execution (armv7a_irq_live_entry_writes sg state
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
      saved_heap registry_heap ->
    kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
      KernelClientHeapClosed closed_heap ->
    kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed
      (armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments)) KernelClientHeapClosed returned ->
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      call.(os_sched_call_invocation) None call.(os_sched_call_origin)
      (armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments)) stopped returned_origin returned ->
    armv7a_irq_restore_pointer_reads sg closed_heap
      (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) ->
    armv7a_continuation_focus_binding (armv7a_call_focus call suspended.(armv7a_continuation_pc)
      suspended.(armv7a_continuation_lr)) selected ->
    selected.(armv7a_continuation_stack) = call.(os_sched_call_stack) ->
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) ->
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) ->
    armv7a_restore_transition environment.(task_stack_call_continuations)
      handler selected closed_heap restored ->
    resume_registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
    resume_registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
    resume_registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
    armv7a_save_suffix_transition save resume_registers
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) restored
      final_registers (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)) after ->
    kernel_call_save_history environment critical sg call state
      (armv7a_continuation_resumed_call selected call)
      (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))
| KernelCallSaveScheduled : forall arch Extra
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
      KernelClientHeapCut Extra -> model -> Prop)
    (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
      KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
    call state handler suspended selected registers before irq_input saved_heap
    registry_heap entry_heap entry stopped returned_origin checkpoint
    outgoing old_sp cpsr task_registers lr saved incoming restored
    resume_registers final_registers after,
    handler.(os_int_exit_interrupted_call) = call ->
    kernel_call_save_instruction_step arch SaveReadCPSR registers state before
      (kernel_save_read_cpsr registers) state irq_input ->
    suspended.(armv7a_continuation_pc) = armv7a_save_entry_address save + 4 ->
    armv7a_save_transition environment.(task_stack_call_continuations)
      handler suspended irq_input saved_heap ->
    kernel_heap_execution (armv7a_irq_live_entry_writes sg state
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
      saved_heap registry_heap ->
    kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
      KernelClientHeapClosed entry_heap ->
    kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed
      (armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments)) KernelClientHeapClosed entry ->
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      call.(os_sched_call_invocation) None call.(os_sched_call_origin)
      (armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
        suspended.(armv7a_continuation_fragments)) stopped returned_origin entry ->
    os_sched_source_switch_prefix_execution sg entry_heap checkpoint ->
    os_sched_source_switch_execution environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) task_abi sg (os_sched_prefix_state entry)
      outgoing old_sp cpsr task_registers lr saved incoming selected checkpoint restored ->
    armv7a_continuation_focus_binding (armv7a_call_focus call
      (armv7a_save_entry_address save + 4) suspended.(armv7a_continuation_lr)) selected ->
    selected.(armv7a_continuation_stack) = call.(os_sched_call_stack) ->
    resume_registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
    resume_registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
    resume_registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
    let acquired := os_sched_install_context outgoing saved.(armv7a_continuation_fragments) incoming
      (os_sched_save_current_sp (os_sched_prefix_state entry)
        outgoing.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp)) in
    armv7a_save_suffix_transition save resume_registers acquired restored final_registers acquired after ->
    kernel_call_save_history environment critical sg call state
      (armv7a_continuation_resumed_call selected call) acquired.

Lemma kernel_call_save_history_same_call : forall environment critical sg original before returned acquired,
  kernel_call_save_history environment critical sg original before returned acquired ->
  kernel_stack_call_same_call returned original.
Proof.
  intros environment critical sg original before returned acquired Hhistory; destruct Hhistory.
  - unfold kernel_stack_call_same_call; repeat split; reflexivity.
  - unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    repeat split; assumption || reflexivity.
  - unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    repeat split; assumption || reflexivity.
Qed.

(** The returned snapshot and its stack map are owned together. This is a
    target C-facing boundary, not an unproved replacement Ensure. A caller
    may use it only after the corresponding complete source branch proof;
    it cannot be inferred from an old weak os_sched_post. *)
Definition os_sched_source_return_post environment critical sg original mask released : Assertion :=
  EX returned current,
    coq_prop (kernel_call_restore_history environment critical sg original released returned current) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) returned mask **
     kernel_stack_inv environment.(task_stack_call_continuations) UCOS2_inv sg
       (task_stack_call_active_key returned) current ** unmap_table_rep sg).

Lemma kernel_call_restore_history_same_call : forall environment critical sg original released returned current,
  kernel_call_restore_history environment critical sg original released returned current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros environment critical sg original released returned current Hhistory.
  destruct Hhistory.
  - unfold task_tcb_init_stack_same_call; repeat split; reflexivity.
  - unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    repeat split; assumption || reflexivity.
  - unfold task_tcb_init_stack_same_call, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    repeat split; assumption || reflexivity.
Qed.

(** The three cuts of a returning OS_Sched call remain distinct. The Save
    source produces the acquired context/state, the C body may restore a
    changed incarnation of that same call, and the final MSR/BX may itself
    be interrupted. In particular [current] is NOT identified with the
    pre-Restore [released] state. This is past source history, not a safety
    requirement on every future critical interval or opaque save value. *)
Definition os_sched_call_history environment critical sg
  (acquire_history : OsSchedCallContext -> UCOS2_Verify_State ->
    OsSchedCallContext -> UCOS2_Verify_State -> Prop)
  original before returned current : Prop :=
  exists entered entry resumed released,
    acquire_history original before entered entry /\
    kernel_stack_call_same_call entered original /\
    os_sched_c_return environment.(task_stack_call_external) critical sg entry entered resumed released /\
    kernel_call_restore_history environment critical sg resumed released returned current.

(** Public resource domain for the source-based scheduler interface. The
    entire current world is transferred to the callee. This assertion
    alone is NOT a theorem that arbitrary kernel states are safe scheduler
    entries: source-stage/selector and actual save obligations remain in
    the callee source proof, never in a caller's future-safety forall. *)
Definition os_sched_stack_pre environment resources sg original mask before : Assertion :=
  kernel_stack_call_closed environment.(task_stack_call_continuations) resources sg
    (task_stack_call_active_key original) original mask before.

Definition os_sched_stack_post environment resources critical sg acquire_history original mask before : Assertion :=
  kernel_stack_call_history_restore_post environment.(task_stack_call_continuations)
    resources sg (task_stack_call_active_key original)
    (os_sched_call_history environment critical sg acquire_history) original mask before.

(** The callable return observation does not require a flat trace across
    physical install/take stores. The ordinary invocation source is
    transported only if it was present at entry; neither readiness nor a
    wait-registration fact is introduced here. The resource owner is the
    CURRENT returned world, with the same invocation/origin/stack key.

    Actual complete branch producers must establish this assertion. Its
    use as a modular C contract is not a proof of total callee coverage. *)
Definition os_sched_stack_return_post environment resources sg original mask before : Assertion :=
  kernel_stack_call_history_restore_post environment.(task_stack_call_continuations)
    resources sg (task_stack_call_active_key original)
    (fun entered entry returned current =>
      kernel_call_task_source entered entry -> kernel_call_task_source returned current)
    original mask before.

Lemma task_create_stack_running_sched_pre : forall environment critical sg call mask state,
  UCOS2_state_inv sg state ->
  sg.(g_OSRunning) # UChar |-> task_create_stack_running state **
  task_create_stack_without_running environment critical sg call mask state ** unmap_table_rep sg |--
  os_sched_stack_pre environment kernel_program_inv sg call mask state.
Proof.
  intros environment critical sg call mask state Hvalid.
  unfold os_sched_stack_pre, kernel_stack_call_closed, kernel_stack_inv,
    task_create_stack_without_running, task_tcb_init_stack_capsules, task_create_stack_running.
  rewrite kernel_program_inv_split_unmap, critical_region_outside_without_running_rep,
    UCOS2_inv_split_running; entailer!.
Qed.

Lemma os_sched_stack_return_post_returns_create : forall environment critical sg
  original scheduled mask before region args task_return lower old_frame upper,
  task_tcb_init_stack_same_call scheduled original ->
  os_sched_stack_return_post environment kernel_program_inv sg scheduled mask before |--
  task_create_stack_post environment critical sg region args task_return lower old_frame upper original mask 0.
Proof.
  intros environment critical sg original scheduled mask before region args task_return lower old_frame upper Hsame.
  unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post; Intros returned current.
  assert (Hreturned : kernel_stack_call_same_call returned scheduled) by tauto.
  assert (Hactive : task_stack_call_active_key scheduled = task_stack_call_active_key returned).
  { unfold task_stack_call_active_key; unfold kernel_stack_call_same_call in Hreturned.
    destruct Hreturned as [Hi [Ho Hs]]; rewrite Ho; reflexivity. }
  rewrite Hactive, <- task_tcb_init_stack_save_input_closed_world.
  unfold task_create_stack_post; Exists returned current.
  destruct (Z.eq_dec 0 0); [|contradiction].
  unfold task_tcb_init_stack_save_input.
  unfold task_tcb_init_stack_same_call, kernel_stack_call_same_call in *; entailer!; intuition congruence.
Qed.

Lemma os_sched_call_history_same_call :
  forall environment critical sg acquire_history original before returned current,
  os_sched_call_history environment critical sg acquire_history original before returned current ->
  kernel_stack_call_same_call returned original.
Proof.
  intros environment critical sg acquire_history original before returned current
    [entered [entry [resumed [released [Hsave [Hsame [Hbody Hrestore]]]]]]].
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hbody_same.
  pose proof (kernel_call_restore_history_same_call _ _ _ _ _ _ _ Hrestore) as Hrestore_same.
  unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
Qed.

(** This join consumes the actual Restore producer's current world. It
    does not frame the acquired map across the C body or an IRQ. Resources
    can include a configured private ECB pool, so Del need not erase it. *)
Lemma os_sched_stack_post_from_restore : forall environment resources critical sg acquire_history
  original mask before entered entry resumed released,
  acquire_history original before entered entry ->
  kernel_stack_call_same_call entered original ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry entered resumed released ->
  kernel_stack_call_history_restore_post environment.(task_stack_call_continuations)
    resources sg (task_stack_call_active_key original)
    (kernel_call_restore_history environment critical sg) resumed mask released |--
  os_sched_stack_post environment resources critical sg acquire_history original mask before.
Proof.
  intros environment resources critical sg acquire_history original mask before entered entry resumed released
    Hsave Hentered Hbody.
  unfold kernel_stack_call_history_restore_post; Intros returned current.
  assert (Hrestore : kernel_call_restore_history environment critical sg resumed released returned current)
    by tauto.
  assert (Hhistory : os_sched_call_history environment critical sg acquire_history original before returned current).
  { exists entered, entry, resumed, released; auto. }
  pose proof (os_sched_call_history_same_call _ _ _ _ _ _ _ _ Hhistory) as Hsame.
  unfold os_sched_stack_post, kernel_stack_call_history_restore_post; Exists returned current; entailer!.
Qed.

(** The final uninterrupted Restore is a real producer of the public
    boundary. Its input is the masked current world established by the C
    body (which may already have switched), not the desired postcondition.
    The prefix and suffix are the unchanged task-domain architecture ABI. *)
Lemma os_sched_stack_uninterrupted_restore : forall environment resources critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg acquire_history original mask before entered entry saved resumed released cursor heap
  written middle final_cursor after (frame : Assertion),
  acquire_history original before entered entry ->
  kernel_stack_call_same_call entered original ->
  interrupt_saved_value mask saved ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry entered resumed released ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) resources critical sg
    (task_stack_call_active_key original) resumed saved entry released ** frame) heap ->
  armv7a_restore_prefix_transition restore cursor heap written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor heap final_cursor after /\
  (os_sched_stack_post environment resources critical sg acquire_history original mask before ** frame) after.
Proof.
  intros environment resources critical arch restore sg acquire_history original mask before entered entry saved resumed released
    cursor heap written middle final_cursor after frame Hsave Hentered Hsaved Hbody Hr0 Hmask Hpre Hprefix Hsuffix.
  assert (Hsaved_mask : armv7a_irq_fiq_mask saved = mask) by exact (proj2 Hsaved).
  destruct (kernel_stack_call_restore_prefix _ _ _ _ _ environment.(task_stack_call_continuations)
    restore resources sg (task_stack_call_active_key original) resumed saved entry released cursor heap
    written middle frame Hr0 Hmask Hpre Hprefix) as [Hwritten [Hmemory Hclosed]].
  assert (Hhistory : kernel_call_restore_history environment critical sg resumed released resumed released)
    by (eapply KernelCallRestoreUninterrupted; eassumption).
  assert (Hsame : kernel_stack_call_same_call resumed resumed) by (repeat split; reflexivity).
  assert (Hword : written.(kernel_restore_msr_word) =
    Some (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0))).
  { rewrite Hwritten; reflexivity. }
  assert (Hword_mask : armv7a_irq_fiq_mask
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) = mask).
  { rewrite armv7a_cpsr_restore_mask_eq, Hr0; exact Hsaved_mask. }
  rewrite Hsaved_mask in Hclosed.
  rewrite <- Hword_mask in Hclosed.
  destruct (kernel_stack_call_history_restore_suffix _ _ _ _ _ environment.(task_stack_call_continuations)
    restore resources sg (task_stack_call_active_key original)
    (kernel_call_restore_history environment critical sg) resumed released resumed released
    (armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)) written middle
    final_cursor after frame Hhistory Hsame Hword Hclosed Hsuffix)
    as [Hcursor [Hafter_memory [Hafter_closed Hpost]]].
  rewrite Hword_mask in Hpost.
  split.
  - eapply kernel_call_restore_prefix_suffix.
    + exact (armv7a_restore_prefix_source _ _ _ _ restore _ _ _ _ Hprefix).
    + exact (armv7a_restore_suffix_source _ _ _ _ restore _ _ _ _ Hsuffix).
  - match type of Hpost with ?P after => assert (Hclose : P |--
      os_sched_stack_post environment resources critical sg acquire_history original mask before ** frame) end.
    { sep_apply_l_atomic (os_sched_stack_post_from_restore environment resources critical sg acquire_history original
        mask before entered entry resumed released Hsave Hentered Hbody); entailer!. }
    exact (Hclose after Hpost).
Qed.

Lemma os_sched_stack_post_returns_create : forall environment critical sg acquire_history original scheduled mask before
  region args task_return lower old_frame upper,
  task_tcb_init_stack_same_call scheduled original ->
  os_sched_stack_post environment kernel_program_inv critical sg acquire_history scheduled mask before |--
  task_create_stack_post environment critical sg region args task_return lower old_frame upper original mask 0.
Proof.
  intros environment critical sg acquire_history original scheduled mask before region args task_return lower old_frame upper Hsame.
  unfold os_sched_stack_post, kernel_stack_call_history_restore_post; Intros returned current.
  assert (Hreturned : kernel_stack_call_same_call returned scheduled) by tauto.
  assert (Hactive : task_stack_call_active_key scheduled = task_stack_call_active_key returned).
  { unfold task_stack_call_active_key; unfold kernel_stack_call_same_call in Hreturned.
    destruct Hreturned as [Hi [Ho Hs]]; rewrite Ho; reflexivity. }
  rewrite Hactive, <- task_tcb_init_stack_save_input_closed_world.
  unfold task_create_stack_post; Exists returned current.
  destruct (Z.eq_dec 0 0); [|contradiction].
  unfold task_tcb_init_stack_save_input.
  unfold task_tcb_init_stack_same_call, kernel_stack_call_same_call in *; entailer!; intuition congruence.
Qed.

(** A complete actual no-IRQ/no-switch call produces the callable current
    world and ordinary-source transport. The ready-list premise is at the actual
    selector state and the existing source caller establishes it. This
    theorem does not grant it for arbitrary public resource inputs. *)
Lemma os_sched_stack_uninterrupted_nonswitch_call : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call mask state registers before final_registers acquired saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (os_sched_stack_pre environment kernel_program_inv sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (os_sched_stack_return_post environment kernel_program_inv sg call mask state ** frame) after).
Proof.
  intros environment critical arch save restore sg call mask state registers before final_registers acquired
    saved_heap frame Hreturn Hvalid Hmask Hnoswitch Hnonempty Hpre Hsave.
  assert (Hinput : (task_tcb_init_stack_covered_save_input environment critical sg call mask state **
    unmap_table_rep sg ** frame) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Hopen : P |-- Q) end end.
    { unfold os_sched_stack_pre; rewrite <- task_tcb_init_stack_save_input_closed_world.
      unfold task_tcb_init_stack_covered_save_input, task_tcb_init_stack_covered_capsules,
        task_tcb_init_stack_save_input, task_tcb_init_stack_capsules; reflexivity. }
    exact (Hopen before Hpre). }
  destruct (os_sched_source_uninterrupted_nonswitch_call_resources environment critical arch save restore
    sg call mask state registers before final_registers acquired saved_heap frame Hreturn Hvalid Hmask
    Hnoswitch Hnonempty Hinput Hsave) as [Hsave_run [Hstate [prefix_heap [Hprefix Hrestore]]]].
  split; [exact Hsave_run|]. split; [exact Hstate|]. exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix.
  destruct (Hrestore cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix)
    as [Hrestore_run Hafter].
  assert (Hsource : kernel_call_task_source call state ->
    kernel_call_task_source call (os_sched_prefix_state state))
    by (apply os_sched_prefix_preserves_task_source).
  split; [exact Hrestore_run|].
  match type of Hafter with ?P after => assert (Hclose : P |--
    os_sched_stack_return_post environment kernel_program_inv sg call mask state ** frame) end.
  { unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post; Exists call (os_sched_prefix_state state).
    rewrite <- task_tcb_init_stack_save_input_closed_world.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_covered_save_input,
      task_tcb_init_stack_covered_capsules, task_tcb_init_stack_save_input, task_tcb_init_stack_capsules;
      entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma os_sched_source_return_creates_success : forall environment critical sg original mask released,
  os_sched_source_return_post environment critical sg original mask released |--
  task_create_stack_covered_success_post environment critical sg original mask.
Proof.
  intros; unfold os_sched_source_return_post; Intros returned current.
  assert (Hhistory : kernel_call_restore_history environment critical sg original released returned current)
    by assumption.
  pose proof (kernel_call_restore_history_same_call environment critical sg original released returned current
    Hhistory) as Hsame.
  unfold task_create_stack_covered_success_post; Exists returned current.
  unfold kernel_stack_inv, task_tcb_init_stack_covered_save_input, task_tcb_init_stack_covered_capsules,
    critical_region_outside.
  rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
  unfold UCOS2_inv; entailer!.
Qed.

Lemma os_sched_source_return_creates_same_call_success :
  forall environment critical sg original call mask released,
  task_tcb_init_stack_same_call call original ->
  os_sched_source_return_post environment critical sg call mask released |--
  task_create_stack_covered_success_post environment critical sg original mask.
Proof.
  intros environment critical sg original call mask released Hsame.
  sep_apply_l_atomic (os_sched_source_return_creates_success environment critical sg call mask released).
  unfold task_create_stack_covered_success_post; Intros returned current.
  Exists returned current; unfold task_tcb_init_stack_same_call in *; entailer!; intuition congruence.
Qed.

(** The uninterrupted branch produces the same new return boundary from
    real MSR/BX transitions. The disjoint frame passes through these local
    instructions only; the IRQ producer handles its own current world. *)
Lemma os_sched_source_uninterrupted_return_post :
  forall environment critical arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call saved entry released cursor before written middle final_cursor after (frame : Assertion),
  task_stack_live_coverage released.(TskState) (task_stack_call_active_key call) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   task_tcb_init_stack_context environment call ** UCOS2_inv sg released **
   task_tcb_init_stack_covered_capsules environment released ** unmap_table_rep sg ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  (os_sched_source_return_post environment critical sg call (armv7a_irq_fiq_mask saved) released ** frame) after.
Proof.
  intros environment critical arch restore sg call saved entry released cursor before written middle
    final_cursor after frame Hcoverage Hr0 Hmask Hpre Hprefix Hsuffix.
  match type of Hpre with ?P before => assert (Horder : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
    task_tcb_init_stack_context environment call ** UCOS2_inv sg released **
    task_tcb_init_stack_covered_capsules environment released ** (unmap_table_rep sg ** frame))
    by entailer! end.
  destruct (task_tcb_init_stack_covered_uninterrupted_restore environment critical arch restore sg call
    saved entry released cursor before written middle final_cursor after _ Hcoverage Hr0 Hmask
    (Horder before Hpre) Hprefix Hsuffix) as [Hrun [Hreturn Hpost]].
  assert (Hhistory : kernel_call_restore_history environment critical sg call released call released).
  { eapply KernelCallRestoreUninterrupted; eassumption. }
  split; [exact Hrun|].
  match type of Hpost with ?P after => assert (Hclose : P |--
    os_sched_source_return_post environment critical sg call (armv7a_irq_fiq_mask saved) released ** frame) end.
  { unfold os_sched_source_return_post; Exists call released.
    unfold task_tcb_init_stack_covered_save_input, task_tcb_init_stack_covered_capsules,
      critical_region_outside, kernel_stack_inv.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  exact (Hclose after Hpost).
Qed.
