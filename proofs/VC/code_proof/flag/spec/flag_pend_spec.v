(** Report-only ordinary module extracted from the frozen checked C context.
    The original proof bodies are retained under the recorded shared-reference map. *)
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import SimpleC.SL.Mem.
Require Import SimpleC.SL.ConAssertion.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import ArrayLib.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import AUXLib.ListLib.
From MonadLib Require Import Monad.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_change_prio_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_always_nonswitch_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_nontimer_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_fields_local_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.field_storage.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_environment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_irq_source_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_current_client_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_accept_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_api_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Export Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.lib.flag_node_fields.
Require Export Ucos2Verify.VC.code.flag.spec.flag_block_call_fields_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_fields_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_api_entry_source_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_idle_ready_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_delete_source_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_phase_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_task_return_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.


Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Instantiate the TaskDel composite with the concrete program union.
    Both syntactic inclusions are discharged by its actual constructors.
    The original two captured sources, local frames and five heaps remain
    those of the checked body producer. *)
Import DeleteComponent CriticalComponent.

(** This is a fixed C interpretation, not a law asserted about an arbitrary
    old linked predicate.  Its producer must supply the same actual C run;
    the raw endpoint observations are part of that run's original output. *)
Import CriticalComponent PrimitiveComponent.

(** The selected source has a concrete interpretation for each original
    caller kind.  Task execution uses the proved C program.  IRQ execution
    additionally admits the already explicit view primitive contract; that
    contract is not promoted to a Task cache-preservation law. *)
Import CriticalComponent PrimitiveComponent.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Sources decorate the original C completion proof.  They retain the
    invocation/allocation from that completion; no constructor assumes any
    creation-frame, cache, ready or future-return conclusion. *)
Import EventStateDef.
Import EventStateDef.












(** Provenance follows the existing execution proof.  An atomic marker is
    supplied by that C module's actual call/allocation protocol.  In
    particular, it may retain a foreign invocation condition; it is not a
    second execution picked for its endpoints. *)
Import CriticalComponent.



(** A selected environment is an actual sequence of the fixed C program.
    Its existing return owner contains the original C endpoint contract.
    The ABI suffix/prefix below is composed with that very sequence; there
    is no independently supplied old source or endpoint-equal replacement
    tree.  State, caller, local resources and heaps may all change in the
    environment.  Its stopped bit is retained, not assumed false. *)
Import PrimitiveComponent.

Module PendPhaseCandidate.
Import FlagPendSchedulerResources KernelHeapObservation KernelHeapStorage.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations Monad MonadNotation.
Import PrimitiveComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.
Local Open Scope monad_scope.

(** Source program components. Save, Scheduler and Restore retain their
    existing same-invocation source histories. Their fields-resource C
    interfaces are separate obligations; these definitions do not certify
    that the full-byte Scheduler contract can consume a local six-field node. *)
Definition flag_pend_task_set_ready_flags (old : TaskAbstractState) (ready : Z) : TaskAbstractState :=
  {|
    taskID := old.(taskID);
    taskGeneration := old.(taskGeneration);
    tcbStkPtr := old.(tcbStkPtr);
    tcbExtPtr := old.(tcbExtPtr);
    tcbStkBottom := old.(tcbStkBottom);
    tcbStkSize := old.(tcbStkSize);
    tcbOpt := old.(tcbOpt);
    tcbPublicId := old.(tcbPublicId);
    tcbFlagNode := old.(tcbFlagNode);
    tcbFlagsRdy := ready;
    tcbTaskName := old.(tcbTaskName);
    tcbReg0 := old.(tcbReg0);
    tcbCtxSwCtr := old.(tcbCtxSwCtr);
    tcbCyclesTot := old.(tcbCyclesTot);
    tcbCyclesStart := old.(tcbCyclesStart);
    tcbStkBase := old.(tcbStkBase);
    tcbStkUsed := old.(tcbStkUsed);
    tcbPadding42 := old.(tcbPadding42);
    tcbPadding43 := old.(tcbPadding43);
    tcbEventMultiPtr := old.(tcbEventMultiPtr);
    curPrio := old.(curPrio);
    stat := old.(stat);
    statPend := old.(statPend);
    dly := old.(dly);
    eventPtr := old.(eventPtr);
    eventMultiWaitEvents := old.(eventMultiWaitEvents);
    eventMultiRdy := old.(eventMultiRdy);
    msg := old.(msg);
    nextTCB := old.(nextTCB);
    prevTCB := old.(prevTCB);
    delReq := old.(delReq) |}.

Definition flag_pend_update_task (s : UCOS2_Verify_State) (tid : TaskID)
  (current : TaskAbstractState) : UCOS2_Verify_State :=
  replace_TskS (glob_task_set_usedtask s.(TskState) tid current) s.

(** The delayed consume writes the acquired pool image even when the
    original group was deleted.  It never allocates a group or fixes a
    generation across Save/Restore/Sched. *)
Definition flag_pend_pool_set_bits (s : GlobFlagState) (i : FlagID)
  (image : FlagGroupImage) (bits : Z) : GlobFlagState :=
  {| flagUsed := match s.(flagUsed) i with
       | Some group => kernel_map_set s.(flagUsed) i (Some (flag_group_set_bits group bits))
       | None => s.(flagUsed) end;
     flagFree := s.(flagFree);
     flagImages := kernel_map_set s.(flagImages) i (Some (flag_image_set_bits image bits));
     flagWaitNodes := s.(flagWaitNodes); flagNextGeneration := s.(flagNextGeneration) |}.

Definition flag_pend_argument_error (pgrp nesting locked ty : Z) : option Z :=
  if Z.eqb pgrp 0 then Some 110 else
  if Z.ltb 0 nesting then Some 2 else
  if Z.ltb 0 locked then Some 13 else
  if negb (Z.eqb ty 5) then Some 1 else None.

Definition flag_pend_resume_error (status : Z) : Z :=
  if Z.eqb status 2 then 14 else 10.

Inductive FlagPendPhase :=
| FlagPendReturn (ready error : Z)
| FlagPendWaiting (node : addr).

Definition flag_pend_first_critical (sg : StableGlobVars) (i : FlagID)
  (requested wait_type timeout : Z) : program UCOS2_Verify_State FlagPendPhase :=
  fun acquired result released =>
  match decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) with
  | None => result = FlagPendReturn 0 111 /\ released = acquired
  | Some mode => exists image, acquired.(FlagState).(flagImages) i = Some image /\
      if negb (Z.eqb image.(flagImageType) 5)
      then result = FlagPendReturn 0 1 /\ released = acquired
      else let ready := flag_ready_bits sg.(osKernelConfig) image.(flagImageBits) requested mode in
        if flag_wait_satisfied mode ready requested then
          exists tid old,
            acquired.(SchedState).(curTaskID) = Some tid /\
            acquired.(TskState).(inUsedTaskStates) tid = Some old /\
            result = FlagPendReturn ready 0 /\
            released = flag_pend_update_task
              (if Z.testbit wait_type 7 then
                replace_FlagS (flag_pend_pool_set_bits acquired.(FlagState) i image
                  (flag_consume_bits sg.(osKernelConfig) image.(flagImageBits) ready mode)) acquired
               else acquired) tid (flag_pend_task_set_ready_flags old ready)
        else exists waiter old group blocked,
          flag_block_call_protocol sg acquired waiter old group image timeout /\
          waiter.(flagGroup) = i /\ waiter.(flagMask) = requested /\
          waiter.(flagWaitMode) = mode /\
          flag_block sg acquired waiter timeout = Some blocked /\
          result = FlagPendWaiting waiter.(flagNodeAddr) /\ released = blocked
  end.

Definition flag_pend_resume_critical (sg : StableGlobVars) (i : FlagID)
  (node wait_type : Z) : program UCOS2_Verify_State (Z * Z) :=
  fun acquired result released => exists tid old,
    acquired.(SchedState).(curTaskID) = Some tid /\
    acquired.(TskState).(inUsedTaskStates) tid = Some old /\
    let status := encode_pend_status old.(statPend) in
    if negb (Z.eqb status 0) then
      result = (0, flag_pend_resume_error status) /\
      if Z.eqb status 2
      then released = flag_pend_update_task acquired tid (task_clear_pend_status false old)
      else exists waiter flags,
        flag_unlink_node acquired.(FlagState) node = Some (waiter, flags) /\
        released = flag_pend_update_task (replace_FlagS flags acquired) tid
          (task_set_flag_node (task_clear_pend_status false old) 0)
    else let ready := old.(tcbFlagsRdy) in
      if Z.testbit wait_type 7 then
        match decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) with
        | None => result = (0, 111) /\ released = acquired
        | Some mode => exists image,
            acquired.(FlagState).(flagImages) i = Some image /\ result = (ready, 0) /\
            released = replace_FlagS
              (flag_pend_pool_set_bits acquired.(FlagState) i image
                (flag_consume_bits sg.(osKernelConfig) image.(flagImageBits) ready mode)) acquired
        end
      else result = (ready, 0) /\ released = acquired.

Definition flag_pend_restored_return environment critical sg call (ready error : Z) :
  program UCOS2_Verify_State (Z * Z) :=
  StateRelMonad.bind (ContinuationPhaseEffects.os_sched_continuation_phase_restore_program environment critical sg call)
    (fun _ => StateRelMonad.ret (ready, error)).

Definition flag_pend_after_schedule environment critical sg call mask i node wait_type :
  program UCOS2_Verify_State (Z * Z) :=
  StateRelMonad.bind (SchedulerPhaseCandidate.os_sched_task_program environment critical sg call mask)
    (fun resumed => StateRelMonad.bind
      (ContinuationPhaseEffects.os_sched_continuation_phase_save_program environment critical sg resumed mask)
      (fun entered => StateRelMonad.bind (flag_pend_resume_critical sg i node wait_type)
        (fun result => flag_pend_restored_return environment critical sg (fst entered)
          (fst result) (snd result)))).

Definition flag_pend_protected_program environment critical sg call mask i requested wait_type timeout :
  program UCOS2_Verify_State (Z * Z) :=
  StateRelMonad.bind (ContinuationPhaseEffects.os_sched_continuation_phase_save_program environment critical sg call mask)
    (fun entered => StateRelMonad.bind (flag_pend_first_critical sg i requested wait_type timeout)
      (fun phase => match phase with
       | FlagPendReturn ready error =>
           flag_pend_restored_return environment critical sg (fst entered) ready error
       | FlagPendWaiting node =>
           StateRelMonad.bind
             (ContinuationPhaseEffects.os_sched_continuation_phase_restore_program environment critical sg (fst entered))
             (fun restored => flag_pend_after_schedule environment critical sg restored mask i node wait_type)
       end)).

(** The initial scalar observations precede the first acquisition.  The
    image tested inside the first critical section is looked up afresh. *)
Definition flag_pend_program environment critical sg call mask (i pgrp requested wait_type timeout : Z) :
  program UCOS2_Verify_State (Z * Z) :=
  fun before result current =>
    if Z.eqb pgrp 0 then result = (0, 110) /\ current = before else
    if Z.ltb 0 before.(IntrState).(intNesting) then result = (0, 2) /\ current = before else
    if Z.ltb 0 before.(IntrState).(lockNesting) then result = (0, 13) /\ current = before else
    exists observed, before.(FlagState).(flagImages) i = Some observed /\
      if negb (Z.eqb observed.(flagImageType) 5)
      then result = (0, 1) /\ current = before
      else flag_pend_protected_program environment critical sg call mask i requested wait_type timeout
             before result current.

Definition flag_pend_safe environment critical sg call mask i pgrp requested wait_type timeout before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun s => s = before)
    (flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout)
    (fun result current => X (fst result) (snd result) current).

Definition flag_pend_return_safe ready error current (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret (ready, error))
    (fun result state => X (fst result) (snd result) state).


Lemma flag_pend_argument_null_first : forall nesting locked ty,
  flag_pend_argument_error 0 nesting locked ty = Some 110.
Proof. reflexivity. Qed.

Lemma flag_pend_resume_abort_error : flag_pend_resume_error 2 = 14.
Proof. reflexivity. Qed.

Lemma flag_pend_resume_default_error : forall status,
  status <> 2 -> flag_pend_resume_error status = 10.
Proof.
  intros status Hne; unfold flag_pend_resume_error;
  rewrite (proj2 (Z.eqb_neq _ _) Hne); reflexivity.
Qed.

Lemma flag_pend_safe_return : forall environment critical sg call mask i pgrp requested wait_type timeout
  before ready error current X,
  flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout
    before (ready, error) current ->
  flag_pend_safe environment critical sg call mask i pgrp requested wait_type timeout before X ->
  flag_pend_return_safe ready error current X.
Proof.
  intros environment critical sg call mask i pgrp requested wait_type timeout before ready error current X Hstep Hsafe.
  unfold flag_pend_safe in Hsafe; unfold flag_pend_return_safe.
  eapply (highstependret_derive
    (flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout)
    (fun s => s = before) (ready, error) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma flag_pend_program_null : forall environment critical sg call mask i requested wait_type timeout before,
  flag_pend_program environment critical sg call mask i 0 requested wait_type timeout
    before (0, 110) before.
Proof. intros; unfold flag_pend_program; cbn; auto. Qed.

Lemma flag_pend_program_isr : forall environment critical sg call mask i pgrp requested wait_type timeout before,
  pgrp <> 0 -> 0 < before.(IntrState).(intNesting) ->
  flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout before (0, 2) before.
Proof.
  intros; unfold flag_pend_program; rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.ltb_lt _ _) H0); auto.
Qed.

Lemma flag_pend_program_locked : forall environment critical sg call mask i pgrp requested wait_type timeout before,
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 -> 0 < before.(IntrState).(lockNesting) ->
  flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout before (0, 13) before.
Proof.
  intros; unfold flag_pend_program; rewrite (proj2 (Z.eqb_neq _ _) H),
    (proj2 (Z.ltb_ge _ _) H0), (proj2 (Z.ltb_lt _ _) H1); auto.
Qed.

Lemma flag_pend_first_invalid_mode : forall sg i requested wait_type timeout acquired,
  decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) = None ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn 0 111) acquired.
Proof. intros; unfold flag_pend_first_critical; rewrite H; auto. Qed.

Lemma flag_pend_pool_set_bits_image : forall flags i image bits,
  (flag_pend_pool_set_bits flags i image bits).(flagImages) i = Some (flag_image_set_bits image bits).
Proof. intros; apply kernel_map_set_same. Qed.

Lemma flag_pend_pool_set_bits_free_remains_free : forall flags i image bits,
  flags.(flagUsed) i = None -> (flag_pend_pool_set_bits flags i image bits).(flagUsed) i = None.
Proof. intros; unfold flag_pend_pool_set_bits; cbn; rewrite H; exact H. Qed.

Lemma flag_pend_pool_set_bits_waiters : forall flags i image bits,
  (flag_pend_pool_set_bits flags i image bits).(flagWaitNodes) = flags.(flagWaitNodes).
Proof. reflexivity. Qed.

(** Admission records the source application stage before invocation
    registration. Clean registration is an API/source guarantee, not an
    invariant consequence of ready-list membership or a CPU ABI law. *)
Definition flag_pend_registration_clean (node : TaskAbstractState) : Prop :=
  node.(tcbFlagNode) = 0 /\ node.(eventPtr) = None /\
  node.(eventMultiWaitEvents) = [] /\ node.(tcbEventMultiPtr) = 0.

Definition flag_pend_task_stage (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  call.(os_sched_call_origin) =
    RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
      call.(os_sched_call_stack).(stackLeaseGeneration) /\
  state.(SchedState).(isRunning) = true /\
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
  exists node,
    sched_current_ready_at state.(TskState) state.(SchedState)
      call.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
    flag_pend_registration_clean node.

Definition flag_pend_task_entry (call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Prop :=
  flag_pend_task_stage call state /\
  task_invocation_active state.(TskState) call.(os_sched_call_invocation)
    call.(os_sched_call_origin).

(** Early guards do not require a clean interrupted task or ready current
    task. In those branches the caller's actual execution/parent view is a
    frame; no Save, Block or Scheduler source claim is made. *)
Definition flag_pend_source_entry (call : OsSchedCallContext) (pgrp : Z)
  (state : UCOS2_Verify_State) : Prop :=
  pgrp <> 0 -> state.(IntrState).(intNesting) <= 0 ->
  state.(IntrState).(lockNesting) <= 0 -> flag_pend_task_entry call state.

Lemma flag_pend_source_entry_null : forall call state,
  flag_pend_source_entry call 0 state.
Proof. unfold flag_pend_source_entry; intuition. Qed.

Lemma flag_pend_source_entry_isr : forall call pgrp state,
  0 < state.(IntrState).(intNesting) -> flag_pend_source_entry call pgrp state.
Proof. unfold flag_pend_source_entry; intros; lia. Qed.

Lemma flag_pend_source_entry_locked : forall call pgrp state,
  0 < state.(IntrState).(lockNesting) -> flag_pend_source_entry call pgrp state.
Proof. unfold flag_pend_source_entry; intros; lia. Qed.

Lemma flag_pend_task_entry_source_entry : forall call pgrp state,
  flag_pend_task_entry call state -> flag_pend_source_entry call pgrp state.
Proof. unfold flag_pend_source_entry; auto. Qed.

Lemma flag_pend_task_stage_current : forall call state,
  flag_pend_task_stage call state ->
  task_current_at state call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration).
Proof.
  intros call state [_ [_ [_ [node [Hready [Hgen Hclean]]]]]].
  split; [exact (proj1 (proj2 Hready))|].
  exists node; split; [exact (proj1 Hready)|exact Hgen].
Qed.

Lemma flag_pend_task_entry_call_source : forall call state,
  flag_pend_task_entry call state -> kernel_call_task_source call state.
Proof.
  intros call state [Hstage Hactive].
  pose proof (flag_pend_task_stage_current call state Hstage) as Hcurrent.
  destruct Hstage as [Horigin _].
  unfold kernel_call_task_source; split; [exact Horigin|].
  split; [exact Hactive|].
  unfold task_execution_current; rewrite Horigin; exact (proj1 Hcurrent).
Qed.

Lemma flag_pend_tcb_init_commit_registration_clean : forall args acquired slot image,
  flag_pend_registration_clean (task_tcb_init_commit_node args acquired slot image).
Proof. intros; repeat split; reflexivity. Qed.

Lemma flag_pend_task_stage_register : forall call state,
  flag_pend_task_stage call state ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  flag_pend_task_entry call
    (replace_TskS (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state).
Proof.
  intros call state Hstage Hinv.
  split; [exact Hstage|].
  pose proof (flag_pend_task_stage_current call state Hstage) as Hcurrent.
  destruct Hstage as [Horigin _].
  rewrite Hinv; apply task_begin_invocation_active.
  rewrite Horigin; exact (proj2 Hcurrent).
Qed.

(** The initial producer uses the actual initialized node, selected current
    ready endpoint and taken parked key. The initialization equality is
    necessary: a generic installed task alone need not have clean registration. *)
Lemma flag_pend_selected_initial_entry : forall selected state node args acquired image next prev,
  state.(SchedState).(isRunning) = true ->
  state.(TskState).(parkedTaskStacks) (task_stack_key selected.(armv7a_continuation_stack)) = None ->
  sched_current_ready_at state.(TskState) state.(SchedState)
    selected.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  node = task_set_links (task_tcb_init_commit_node args acquired
    selected.(armv7a_continuation_stack).(stackLeaseSlot) image) next prev ->
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  flag_pend_task_entry call (armv7a_initial_call_registered selected state).
Proof.
  intros selected state node args acquired image next prev Hrunning Habsent Hready Hgen Hinit call.
  apply (flag_pend_task_stage_register call state); [|reflexivity].
  unfold flag_pend_task_stage, call, armv7a_initial_call; cbn.
  split; [reflexivity|]. split; [exact Hrunning|]. split; [exact Habsent|].
  exists node; split; [exact Hready|]. split; [exact Hgen|].
  rewrite Hinit; repeat split; reflexivity.
Qed.

(** A sequential stage must come from the preceding API's actual guarantee.
    This lemma only registers the next invocation; it does not create that
    guarantee and makes no assertion that an interrupted call eventually returns. *)
Lemma flag_pend_sequential_entry : forall previous state,
  flag_pend_task_stage previous state ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  flag_pend_task_entry call
    (replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state).
Proof.
  intros previous state Hstage call.
  apply (flag_pend_task_stage_register call state); [exact Hstage|reflexivity].
Qed.

Definition flag_pend_fields_world environment saved_local sg call mask state : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv (task_create_continuation_local saved_local)
    sg (task_stack_call_active_key call) call mask state.

(** This observed next-entry consumes exactly one returned execution owner.
    The old API's source stage is retained independently of the ABI event. *)
Lemma flag_pend_sequential_entry_resources : forall environment
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  saved_local sg previous mask state before after (frame : Assertion),
  flag_pend_task_stage previous state ->
  kernel_sequential_call_source boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) before after ->
  (flag_pend_fields_world environment saved_local sg previous mask state ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (coq_prop (flag_pend_task_stage call state) &&
    (flag_pend_fields_world environment saved_local sg call mask state ** frame)) after.
Proof.
  intros environment boundary saved_local sg previous mask state before after frame
    Hstage Hsource Hpre call.
  assert (Hopen : flag_pend_fields_world environment saved_local sg previous mask state ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) previous mask **
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      kernel_program_fields_inv (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key previous) state ** frame)).
  { unfold flag_pend_fields_world, kernel_continuation_call_closed; entailer!. }
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _
    Hsource (Hopen before Hpre)) as [Hmemory Hafter].
  split; [exact Hmemory|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold flag_pend_fields_world, kernel_continuation_call_closed.
    change (task_stack_call_active_key call) with (task_stack_call_active_key previous).
    assert (Hstage_new : flag_pend_task_stage call state) by exact Hstage.
    entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Local QCP allocation owns these six typed cells, including no padding.
    Actual dot/arrow address equalities remain source-generation obligations. *)
Definition flag_pend_node_fields (p : addr) : Assertion :=
  flag_node_fields_uninit_rep selected_kernel_configuration p.

Lemma flag_pend_node_fields_not_registered : forall sg nodes p,
  flag_wait_nodes_fields_rep sg nodes ** flag_pend_node_fields p |--
  coq_prop (nodes p = None) &&
    (flag_wait_nodes_fields_rep sg nodes ** flag_pend_node_fields p).
Proof.
  intros sg nodes p; destruct (nodes p) as [waiter|] eqn:Hnode.
  - assert (Hfalse : flag_wait_nodes_fields_rep sg nodes ** flag_pend_node_fields p |-- coq_prop False).
    { sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_next sg nodes p waiter Hnode).
      unfold flag_pend_node_fields, flag_node_fields_uninit_rep.
      sep_apply_l_atomic (store_ptr_undef_store_ptr p waiter.(flagWaitImage).(flagNodeNext)).
      sep_apply_l_atomic (dup_undef_store_ptr p); entailer!. }
    intros heap Hheap; exfalso; exact (Hfalse heap Hheap).
  - entailer!.
Qed.

Lemma flag_pend_return_loan_to_local_fields : forall waiter,
  flag_node_fields_return_loan selected_kernel_configuration waiter |--
    flag_pend_node_fields waiter.(flagNodeAddr).
Proof. intros; apply flag_node_fields_return_loan_to_uninit. Qed.

Lemma flag_pend_detached_receipt_to_local_fields : forall sg state node,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  state.(FlagState).(flagWaitNodes) node = None ->
  flag_pend_sched_node_fields_rep sg node state |-- flag_pend_node_fields node.
Proof.
  intros sg state node Hconfig Hnone.
  unfold flag_pend_sched_node_fields_rep; rewrite Hnone; Intros image.
  rewrite Hconfig; apply flag_node_fields_rep_to_uninit.
Qed.

(** All source protocol facts for Block are exposed, including the current
    ready witness and clean registration. Node absence is established by
    the disjoint six-field allocation lemma, not by a fresh-address axiom. *)
Lemma flag_pend_stage_block_protocol : forall sg state call waiter old group image timeout,
  flag_pend_task_stage call state ->
  waiter.(flagTask) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) waiter.(flagTask) = Some old ->
  waiter.(flagTaskGeneration) = old.(taskGeneration) ->
  waiter.(flagNodeAddr) <> 0 -> state.(FlagState).(flagWaitNodes) waiter.(flagNodeAddr) = None ->
  state.(FlagState).(flagUsed) waiter.(flagGroup) = Some group ->
  waiter.(flagGroupGeneration) = group.(flagGeneration) ->
  state.(FlagState).(flagImages) waiter.(flagGroup) = Some image ->
  flag_word_in_range sg.(osKernelConfig) waiter.(flagMask) ->
  waiter.(flagWaitImage).(flagNodePadding) = [None] -> 0 <= timeout <= 4294967295 ->
  flag_block_call_protocol sg state waiter old group image timeout.
Proof.
  intros sg state call waiter old group image timeout
    [_ [_ [_ [node [Hready [Hgen Hclean]]]]]] Htask Hold Hwaitgen
    Haddr Habsent Hgroup Hgroupgen Himage Hmask Hpadding Htimeout.
  destruct Hready as [Hnode [Hcur [Hprio [Hin Hstatus]]]].
  rewrite <- Htask in Hnode, Hcur, Hin; rewrite Hold in Hnode; inversion Hnode; subst node.
  unfold flag_pend_registration_clean in Hclean.
  unfold flag_block_call_protocol; intuition.
Qed.

Lemma flag_pend_program_bad_type : forall environment critical sg call mask i pgrp requested wait_type timeout before image,
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 ->
  before.(IntrState).(lockNesting) <= 0 -> before.(FlagState).(flagImages) i = Some image ->
  image.(flagImageType) <> 5 ->
  flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout before (0, 1) before.
Proof.
  intros; unfold flag_pend_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.ltb_ge _ _) H0),
    (proj2 (Z.ltb_ge _ _) H1).
  exists image; split; [exact H2|]. rewrite (proj2 (Z.eqb_neq _ _) H3); cbn; split; reflexivity.
Qed.

Lemma flag_pend_first_revalidated_type : forall sg i requested wait_type timeout acquired mode image,
  decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) = Some mode ->
  acquired.(FlagState).(flagImages) i = Some image -> image.(flagImageType) <> 5 ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn 0 1) acquired.
Proof.
  intros; unfold flag_pend_first_critical; rewrite H; exists image; split; [exact H0|].
  rewrite (proj2 (Z.eqb_neq _ _) H1); cbn; split; reflexivity.
Qed.

Lemma flag_pend_first_ready : forall sg i requested wait_type timeout acquired mode image tid old,
  decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) = Some mode ->
  acquired.(FlagState).(flagImages) i = Some image -> image.(flagImageType) = 5 ->
  let ready := flag_ready_bits sg.(osKernelConfig) image.(flagImageBits) requested mode in
  flag_wait_satisfied mode ready requested = true ->
  acquired.(SchedState).(curTaskID) = Some tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some old ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn ready 0)
    (flag_pend_update_task
      (if Z.testbit wait_type 7 then replace_FlagS
        (flag_pend_pool_set_bits acquired.(FlagState) i image
          (flag_consume_bits sg.(osKernelConfig) image.(flagImageBits) ready mode)) acquired
       else acquired) tid (flag_pend_task_set_ready_flags old ready)).
Proof.
  intros sg i requested wait_type timeout acquired mode image tid old Hmode Himage Htype
    ready Hsatisfied Hcur Hold.
  unfold flag_pend_first_critical; rewrite Hmode; exists image; split; [exact Himage|].
  rewrite Htype; cbn; fold ready; rewrite Hsatisfied; exists tid, old; auto.
Qed.

Lemma flag_pend_first_block : forall sg i requested wait_type timeout acquired mode image waiter old group blocked,
  decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) = Some mode ->
  acquired.(FlagState).(flagImages) i = Some image -> image.(flagImageType) = 5 ->
  flag_wait_satisfied mode (flag_ready_bits sg.(osKernelConfig) image.(flagImageBits) requested mode) requested = false ->
  flag_block_call_protocol sg acquired waiter old group image timeout ->
  waiter.(flagGroup) = i -> waiter.(flagMask) = requested -> waiter.(flagWaitMode) = mode ->
  flag_block sg acquired waiter timeout = Some blocked ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendWaiting waiter.(flagNodeAddr)) blocked.
Proof.
  intros; unfold flag_pend_first_critical; rewrite H; exists image; split; [exact H0|].
  rewrite H1; cbn; rewrite H2; exists waiter, old, group, blocked; repeat first [assumption | reflexivity | split].
Qed.

Lemma flag_pend_resume_abort : forall sg i node wait_type acquired tid old,
  acquired.(SchedState).(curTaskID) = Some tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some old -> encode_pend_status old.(statPend) = 2 ->
  flag_pend_resume_critical sg i node wait_type acquired (0, 14)
    (flag_pend_update_task acquired tid (task_clear_pend_status false old)).
Proof.
  intros; unfold flag_pend_resume_critical; exists tid, old; split; [exact H|].
  split; [exact H0|]. rewrite H1; cbn; auto.
Qed.

Lemma flag_pend_resume_timeout : forall sg i node wait_type acquired tid old waiter flags,
  acquired.(SchedState).(curTaskID) = Some tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some old ->
  encode_pend_status old.(statPend) <> 0 -> encode_pend_status old.(statPend) <> 2 ->
  flag_unlink_node acquired.(FlagState) node = Some (waiter, flags) ->
  flag_pend_resume_critical sg i node wait_type acquired (0, 10)
    (flag_pend_update_task (replace_FlagS flags acquired) tid
      (task_set_flag_node (task_clear_pend_status false old) 0)).
Proof.
  intros; unfold flag_pend_resume_critical; exists tid, old; split; [exact H|].
  split; [exact H0|]. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2).
  split; [unfold flag_pend_resume_error; rewrite (proj2 (Z.eqb_neq _ _) H2); reflexivity|].
  exists waiter, flags; auto.
Qed.

Lemma flag_pend_resume_ready : forall sg i node wait_type acquired tid old,
  acquired.(SchedState).(curTaskID) = Some tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some old -> encode_pend_status old.(statPend) = 0 ->
  Z.testbit wait_type 7 = false ->
  flag_pend_resume_critical sg i node wait_type acquired (old.(tcbFlagsRdy), 0) acquired.
Proof.
  intros; unfold flag_pend_resume_critical; exists tid, old; split; [exact H|].
  split; [exact H0|]. rewrite H1, H2; cbn; auto.
Qed.

Lemma flag_pend_resume_ready_consume : forall sg i node wait_type acquired tid old mode image,
  acquired.(SchedState).(curTaskID) = Some tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some old -> encode_pend_status old.(statPend) = 0 ->
  Z.testbit wait_type 7 = true ->
  decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) = Some mode ->
  acquired.(FlagState).(flagImages) i = Some image ->
  flag_pend_resume_critical sg i node wait_type acquired (old.(tcbFlagsRdy), 0)
    (replace_FlagS (flag_pend_pool_set_bits acquired.(FlagState) i image
      (flag_consume_bits sg.(osKernelConfig) image.(flagImageBits) old.(tcbFlagsRdy) mode)) acquired).
Proof.
  intros; unfold flag_pend_resume_critical; exists tid, old; split; [exact H|].
  split; [exact H0|]. rewrite H1, H2, H3; exists image; auto.
Qed.

Lemma flag_pend_resume_invalid_mode : forall sg i node wait_type acquired tid old,
  acquired.(SchedState).(curTaskID) = Some tid ->
  acquired.(TskState).(inUsedTaskStates) tid = Some old -> encode_pend_status old.(statPend) = 0 ->
  Z.testbit wait_type 7 = true ->
  decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) = None ->
  flag_pend_resume_critical sg i node wait_type acquired (0, 111) acquired.
Proof.
  intros; unfold flag_pend_resume_critical; exists tid, old; split; [exact H|].
  split; [exact H0|]. rewrite H1, H2, H3; cbn; auto.
Qed.

(** Invocation registration changes only the ghost ledger. It preserves
    every physical field, parked descriptor and other saved local owner. *)
Lemma flag_pend_fields_raw_register_eq : forall sg state origin,
  UCOS2_fields_raw_rep sg state =
  UCOS2_fields_raw_rep sg
    (replace_TskS (task_begin_invocation origin state.(TskState)) state).
Proof.
  intros sg state origin.
  unfold UCOS2_fields_raw_rep, UCOS2_raw_rep_missing_flag,
    UCOS2_raw_rep_missing_module, UCOS2_selected_rep, UCOS2_module_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect replace_TskS
    TskState SchedState IntrState EventState TickState FlagState MemoryState
    TimerState StatsState ControlState NameState].
  rewrite (sched_raw_rep_change_task_index sg state.(TskState)
    (task_begin_invocation origin state.(TskState)) state.(SchedState) eq_refl).
  rewrite (event_raw_rep_change_task_index sg state.(TskState)
    (task_begin_invocation origin state.(TskState)) state.(EventState)); [reflexivity|].
  apply event_wait_priority_agreement_encodes; intros eid event tid Hlookup Hin; reflexivity.
Qed.

Lemma flag_pend_fields_inv_register : forall sg state origin,
  task_invocation_origin_live state.(TskState) origin ->
  kernel_program_fields_inv sg state |--
  kernel_program_fields_inv sg
    (replace_TskS (task_begin_invocation origin state.(TskState)) state).
Proof.
  intros sg state origin Hlive.
  unfold kernel_program_fields_inv, kernel_program_fields_rep; Intros.
  pose proof (UCOS2_begin_task_invocation_preserves_validity sg state origin H Hlive).
  rewrite <- flag_pend_fields_raw_register_eq; entailer!.
Qed.

Lemma flag_pend_fields_world_register_entry : forall environment saved_local sg call mask state,
  flag_pend_task_stage call state ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  flag_pend_fields_world environment saved_local sg call mask state |--
  let registered := replace_TskS
    (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state in
  coq_prop (flag_pend_task_entry call registered) &&
    flag_pend_fields_world environment saved_local sg call mask registered.
Proof.
  intros environment saved_local sg call mask state Hstage Hinv; cbv zeta.
  pose proof (flag_pend_task_stage_register call state Hstage Hinv) as Hentry.
  pose proof (flag_pend_task_stage_current call state Hstage) as Hcurrent.
  assert (Hlive : task_invocation_origin_live state.(TskState) call.(os_sched_call_origin)).
  { rewrite (proj1 Hstage); exact (proj2 Hcurrent). }
  unfold flag_pend_fields_world, kernel_continuation_call_closed, kernel_continuation_inv; Intros.
  sep_apply_l_atomic (flag_pend_fields_inv_register sg state call.(os_sched_call_origin) Hlive).
  sep_apply_l_atomic (kernel_saved_continuation_map_used_map_eq
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) environment.(task_stack_call_continuations)
    state.(TskState) (task_begin_invocation call.(os_sched_call_origin) state.(TskState))
    (task_create_continuation_local saved_local) state.(TskState).(parkedTaskStacks) eq_refl).
  entailer!.
Qed.

(** The C acquire/release rely is stated separately from CPU/architecture
    interfaces. Every endpoint has both its existing source effect and the
    matching fields resource transfer on that very heap. The current local
    interpretation is supplied by the source phase; publication/take must
    establish it, and lookup None alone never constructs a receipt.

    These predicates are modular call obligations, not declarations that
    all Save/Restore implementations or all kernel clients satisfy them. *)
Definition flag_pend_save_call environment critical saved_local sg call mask state
  (local : UCOS2_Verify_State -> Assertion) returned saved acquired
  (before after : model) : Prop :=
  ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg call mask saved state returned acquired /\
  forall frame : Assertion,
    (flag_pend_fields_world environment saved_local sg call mask state ** local state ** frame) before ->
    (kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_fields_inv (task_create_continuation_local saved_local) critical
      sg (task_stack_call_active_key returned) returned saved acquired acquired **
      local acquired ** frame) after.

Definition flag_pend_restore_call environment critical saved_local sg call saved acquired state
  (local : UCOS2_Verify_State -> Assertion) returned current
  (before after : model) : Prop :=
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg call state returned current /\
  forall frame : Assertion,
    (kernel_continuation_call_masked environment.(task_stack_call_continuations)
      kernel_program_fields_inv (task_create_continuation_local saved_local) critical
      sg (task_stack_call_active_key call) call saved acquired state ** local state ** frame) before ->
    (flag_pend_fields_world environment saved_local sg returned (armv7a_irq_fiq_mask saved) current **
      local current ** frame) after.

Lemma flag_pend_save_call_same_invocation : forall environment critical saved_local sg call mask state
  local returned saved acquired before after,
  flag_pend_save_call environment critical saved_local sg call mask state
    local returned saved acquired before after ->
  task_tcb_init_stack_same_call returned call.
Proof.
  intros * [Hsource Hresources]; eapply ContinuationPhaseEffects.os_sched_continuation_phase_save_effect_same_call; exact Hsource.
Qed.

Lemma flag_pend_restore_call_same_invocation : forall environment critical saved_local sg call saved acquired state
  local returned current before after,
  flag_pend_restore_call environment critical saved_local sg call saved acquired state
    local returned current before after ->
  task_tcb_init_stack_same_call returned call.
Proof.
  intros * [Hsource Hresources]; eapply ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect_same_call; exact Hsource.
Qed.

(** Current mathematical entry. No complete public C contract is claimed
    until the fields Scheduler/paired-call cuts and local address bridge
    have been consumed by the actual generated Pend witnesses. *)
Definition flag_pend_entry environment critical sg call mask i pgrp requested wait_type timeout before X : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  (pgrp = 0 \/ (0 <= i < sg.(osKernelConfig).(cfgMaxFlags) /\ pgrp = flag_pool_addr sg i)) /\
  0 <= requested < 65536 /\ 0 <= wait_type < 256 /\ 0 <= timeout < 4294967296 /\
  flag_pend_source_entry call pgrp before /\
  flag_pend_safe environment critical sg call mask i pgrp requested wait_type timeout before X.

(** Lift the observed real call cuts to the public program. These lemmas
    use the same state at each adjacent boundary and the same arbitrary X;
    the normal-return hypotheses describe an observed return, not liveness. *)
Lemma flag_pend_program_protected : forall environment critical sg call mask i pgrp requested wait_type timeout
  before image ready error current,
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
  before.(FlagState).(flagImages) i = Some image -> image.(flagImageType) = 5 ->
  flag_pend_protected_program environment critical sg call mask i requested wait_type timeout
    before (ready, error) current ->
  flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout
    before (ready, error) current.
Proof.
  intros; unfold flag_pend_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.ltb_ge _ _) H0), (proj2 (Z.ltb_ge _ _) H1).
  exists image; split; [exact H2|]. rewrite H3; exact H4.
Qed.

Lemma flag_pend_safe_immediate_return : forall environment critical sg call mask i pgrp requested wait_type timeout
  before image entered saved acquired ready error released returned current X,
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
  before.(FlagState).(flagImages) i = Some image -> image.(flagImageType) = 5 ->
  ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg call mask saved before entered acquired ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn ready error) released ->
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg entered released returned current ->
  flag_pend_safe environment critical sg call mask i pgrp requested wait_type timeout before X ->
  flag_pend_return_safe ready error current X.
Proof.
  intros environment critical sg call mask i pgrp requested wait_type timeout before image
    entered saved acquired ready error released returned current X Hptr Hnest Hlock Himage Htype Hsave Hfirst Hrestore Hsafe.
  eapply flag_pend_safe_return; [|exact Hsafe].
  eapply flag_pend_program_protected; [exact Hptr|exact Hnest|exact Hlock|exact Himage|exact Htype|].
  unfold flag_pend_protected_program, ContinuationPhaseEffects.os_sched_continuation_phase_save_program, StateRelMonad.bind.
  exists (entered, saved), acquired; split; [exact Hsave|].
  exists (FlagPendReturn ready error), released; split; [exact Hfirst|].
  unfold flag_pend_restored_return, ContinuationPhaseEffects.os_sched_continuation_phase_restore_program, StateRelMonad.bind.
  exists returned, current; split; [exact Hrestore|].
  split; reflexivity.
Qed.

Lemma flag_pend_safe_waiting_return : forall environment critical sg call mask i pgrp requested wait_type timeout
  before image entered saved acquired node blocked restored released resumed scheduled
  reentered resaved reacquired ready error cleaned returned current X,
  pgrp <> 0 -> before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
  before.(FlagState).(flagImages) i = Some image -> image.(flagImageType) = 5 ->
  ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg call mask saved before entered acquired ->
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendWaiting node) blocked ->
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg entered blocked restored released ->
  SchedulerPhaseCandidate.os_sched_task_call_history environment critical sg restored mask released resumed scheduled ->
  ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg resumed mask resaved scheduled reentered reacquired ->
  flag_pend_resume_critical sg i node wait_type reacquired (ready, error) cleaned ->
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg reentered cleaned returned current ->
  flag_pend_safe environment critical sg call mask i pgrp requested wait_type timeout before X ->
  flag_pend_return_safe ready error current X.
Proof.
  intros environment critical sg call mask i pgrp requested wait_type timeout before image
    entered saved acquired node blocked restored released resumed scheduled
    reentered resaved reacquired ready error cleaned returned current X
    Hptr Hnest Hlock Himage Htype Hsave Hblock Hrestore Hsched Hsave2 Hresume Hrestore2 Hsafe.
  eapply flag_pend_safe_return; [|exact Hsafe].
  eapply flag_pend_program_protected; [exact Hptr|exact Hnest|exact Hlock|exact Himage|exact Htype|].
  unfold flag_pend_protected_program, ContinuationPhaseEffects.os_sched_continuation_phase_save_program, StateRelMonad.bind.
  exists (entered, saved), acquired; split; [exact Hsave|].
  exists (FlagPendWaiting node), blocked; split; [exact Hblock|].
  exists restored, released; split; [exact Hrestore|].
  unfold flag_pend_after_schedule, StateRelMonad.bind.
  exists resumed, scheduled; split; [apply SchedulerPhaseCandidate.os_sched_task_program_iff; exact Hsched|].
  exists (reentered, resaved), reacquired; split; [exact Hsave2|].
  exists (ready, error), cleaned; split; [exact Hresume|].
  unfold flag_pend_restored_return, ContinuationPhaseEffects.os_sched_continuation_phase_restore_program, StateRelMonad.bind.
  exists returned, current; split; [exact Hrestore2|]. split; reflexivity.
Qed.

Lemma flag_pend_selected_initial_entry_resources : forall environment
  (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  saved_local sg selected node state args acquired image next prev,
  state.(SchedState).(isRunning) = true ->
  armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0
    selected.(armv7a_continuation_fragments) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key selected.(armv7a_continuation_stack)) = None ->
  sched_current_ready_at state.(TskState) state.(SchedState)
    selected.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  node = task_set_links (task_tcb_init_commit_node args acquired
    selected.(armv7a_continuation_stack).(stackLeaseSlot) image) next prev ->
  armv7a_task_restored_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) selected **
  kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
    (task_create_continuation_local saved_local) sg
    (Some (task_stack_key selected.(armv7a_continuation_stack))) state |--
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  coq_prop (flag_pend_task_entry call (armv7a_initial_call_registered selected state)) &&
    flag_pend_fields_world environment saved_local sg call
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr))
      (armv7a_initial_call_registered selected state).
Proof.
  intros environment entry saved_local sg selected node state args acquired image next prev
    Hrunning Hbinding Hfragments Habsent Hready Hgen Hinit.
  cbv zeta.
  set (call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments)).
  assert (Hstage : flag_pend_task_stage call state).
  { unfold flag_pend_task_stage, call, armv7a_initial_call; cbn.
    split; [reflexivity|]. split; [exact Hrunning|]. split; [exact Habsent|].
    exists node; split; [exact Hready|]. split; [exact Hgen|].
    rewrite Hinit; repeat split; reflexivity. }
  pose proof (armv7a_initial_frame_no_call selected Hbinding) as Hnone.
  unfold armv7a_task_restored_execution; rewrite Hnone.
  sep_apply_l_atomic (armv7a_initial_call_resources _ _ _
    environment.(task_stack_call_continuations) entry selected
    state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) Hbinding Hfragments).
  assert (Hclose :
    interrupt_platform_running environment.(task_stack_call_platform)
      state.(TskState).(taskLifecycle).(taskNextInvocation)
      (RunningInvocation selected.(armv7a_continuation_stack).(stackLeaseSlot)
        selected.(armv7a_continuation_stack).(stackLeaseGeneration))
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
    environment.(task_stack_call_external).(os_sched_arch_running) call **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) **
    kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
      (task_create_continuation_local saved_local) sg
      (Some (task_stack_key selected.(armv7a_continuation_stack))) state |--
    flag_pend_fields_world environment saved_local sg call
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) state).
  { unfold flag_pend_fields_world, kernel_continuation_call_closed,
      kernel_call_execution_owned, os_sched_context_resources,
      task_stack_call_active_key, call, armv7a_initial_call; entailer!. }
  intros heap Hheap.
  apply (flag_pend_fields_world_register_entry environment saved_local sg call
    (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) state Hstage eq_refl heap).
  apply (Hclose heap); revert heap Hheap; fold call.
  match goal with |- forall heap, ?P heap -> ?Q heap => change (P |-- Q) end.
  entailer!.
Qed.

Definition flag_pend_prepublication_local (call : OsSchedCallContext) (node : addr)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (flag_pend_task_stage call state) && flag_pend_node_fields node.

Definition flag_pend_waiting_local (sg : StableGlobVars) (call : OsSchedCallContext)
  (node : addr) (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (flag_pend_sched_waiter_binding call node state) &&
    flag_pend_sched_node_fields_rep sg node state.

(** A real Block protocol has a modeled endpoint. This rules out treating
    None in the high-level function as an extra error/termination branch. *)
Lemma flag_pend_block_protocol_has_result : forall sg state waiter old group image timeout,
  flag_block_call_protocol sg state waiter old group image timeout ->
  exists post, flag_block sg state waiter timeout = Some post.
Proof.
  intros sg state waiter old group image timeout Hprotocol.
  unfold flag_block_call_protocol in Hprotocol.
  eapply (flag_block_current_lookup_exists sg state waiter timeout waiter.(flagTask) old group image); tauto.
Qed.

Definition flag_pend_call_world environment
  (local : Armv7aContinuation -> Assertion) sg call mask state : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state.

Definition flag_pend_masked_world environment
  (local : Armv7aContinuation -> Assertion) critical sg call saved acquired state : Assertion :=
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    kernel_program_fields_inv local critical sg (task_stack_call_active_key call)
    call saved acquired state.

Definition flag_pend_call_control environment local sg call mask state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call mask **
    os_sched_fields_capsules environment local state ** unmap_table_rep sg).

Definition flag_pend_masked_control environment local critical sg call saved acquired state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    os_sched_fields_capsules environment local state ** unmap_table_rep sg).

Lemma flag_pend_call_world_split : forall environment local sg call mask state,
  flag_pend_call_world environment local sg call mask state --||--
  flag_pend_call_control environment local sg call mask state ** UCOS2_fields_inv sg state.
Proof.
  intros; unfold flag_pend_call_world, flag_pend_call_control,
    kernel_continuation_call_closed, kernel_continuation_inv, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap; split; entailer!.
Qed.

Lemma flag_pend_masked_world_split : forall environment local critical sg call saved acquired state,
  flag_pend_masked_world environment local critical sg call saved acquired state --||--
  flag_pend_masked_control environment local critical sg call saved acquired state ** UCOS2_fields_inv sg state.
Proof.
  intros; unfold flag_pend_masked_world, flag_pend_masked_control,
    kernel_continuation_call_masked, kernel_continuation_inv, os_sched_fields_capsules.
  rewrite kernel_program_fields_inv_split_unmap; split; entailer!.
Qed.

(** Shared declaration: PrimitiveComponent.flag_pend_non_idle_at. *)

Definition flag_pend_valid_mode (mode : Z) : Prop :=
  0 <= Z.land mode 127 <= 3.

Definition flag_pend_source_domain sg call i pgrp mode state : Prop :=
  pgrp <> 0 -> state.(IntrState).(intNesting) <= 0 ->
  state.(IntrState).(lockNesting) <= 0 ->
  forall image, state.(FlagState).(flagImages) i = Some image ->
    image.(flagImageType) = 5 -> flag_pend_valid_mode mode ->
      flag_pend_task_entry call state /\ task_idle_ready sg state.(TskState) /\ flag_pend_non_idle_at sg call state.

(** The caller kind is fixed by its producer. The interrupt alternative
    retains its actual execution view and parked-map active key. The checked
    nesting guard only eliminates that already-related interrupt alternative. *)
(** Shared declaration: PrimitiveComponent.FlagPendCaller. *)

Definition flag_pend_interrupt_source view state : Prop :=
  exists handler interrupted,
    view.(os_execution_context) = KernelInterrupt handler interrupted /\
    kernel_interrupt_nesting_agrees state.(SchedState).(isRunning) view.(os_execution_context) state.(IntrState).

Definition flag_pend_caller_source sg caller call i pgrp mode state : Prop :=
  match caller with
  | FlagPendTaskCaller task_call =>
      task_call = call /\ flag_pend_source_domain sg call i pgrp mode state
  | FlagPendInterruptCaller view active =>
      flag_pend_interrupt_source view state /\
      (pgrp <> 0 -> state.(IntrState).(intNesting) <= 0 ->
       state.(IntrState).(lockNesting) <= 0 ->
       forall image, state.(FlagState).(flagImages) i = Some image ->
       image.(flagImageType) = 5 -> flag_pend_valid_mode mode -> False)
  end.

Definition flag_pend_caller_world environment local sg caller mask state : Assertion :=
  match caller with
  | FlagPendTaskCaller call => flag_pend_call_world environment local sg call mask state
  | FlagPendInterruptCaller view active =>
      kernel_execution_view_owned environment.(task_stack_call_external)
        environment.(task_stack_call_platform) view mask **
      kernel_continuation_inv environment.(task_stack_call_continuations)
        kernel_program_fields_inv local sg active state
  end.

Definition flag_pend_caller_control environment local sg caller mask state : Assertion :=
  match caller with
  | FlagPendTaskCaller call => flag_pend_call_control environment local sg call mask state
  | FlagPendInterruptCaller view active =>
      coq_prop (task_stack_live_coverage state.(TskState) active) &&
      (kernel_execution_view_owned environment.(task_stack_call_external)
        environment.(task_stack_call_platform) view mask **
       os_sched_fields_capsules environment local state ** unmap_table_rep sg)
  end.

Lemma flag_pend_caller_world_split : forall environment local sg caller mask state,
  flag_pend_caller_world environment local sg caller mask state --||--
  flag_pend_caller_control environment local sg caller mask state ** UCOS2_fields_inv sg state.
Proof.
  intros; destruct caller; cbn [flag_pend_caller_world flag_pend_caller_control].
  - apply flag_pend_call_world_split.
  - unfold kernel_continuation_inv, os_sched_fields_capsules.
    rewrite kernel_program_fields_inv_split_unmap; split; entailer!.
Qed.

Lemma flag_pend_caller_source_task : forall sg caller call i pgrp mode state,
  flag_pend_caller_source sg caller call i pgrp mode state ->
  state.(SchedState).(isRunning) = true ->
  state.(IntrState).(intNesting) <= 0 -> caller = FlagPendTaskCaller call.
Proof.
  intros sg caller call i pgrp mode state Hsource Hrunning Hzero.
  destruct caller as [task_call|view active].
  - destruct Hsource as [-> Hdomain]; reflexivity.
  - destruct Hsource as [[handler [interrupted [Hcontext Hnest]]] Hdomain].
    unfold kernel_interrupt_nesting_agrees in Hnest.
    specialize (Hnest Hrunning); rewrite Hcontext in Hnest.
    change (state.(IntrState).(intNesting) = Z.of_nat (S (kernel_interrupt_depth interrupted))) in Hnest.
    rewrite Nat2Z.inj_succ in Hnest; lia.
Qed.

(** The Boot interrupt path reaches the same ordered C errors. Its paired
    calls keep the real exception view; the normal task program remains the
    existing source program. This does not turn an exception stack into a task. *)
Definition flag_pend_view_program critical sg view (i pgrp requested wait_type timeout : Z) :
  program UCOS2_Verify_State (Z * Z) :=
  fun before result current =>
    if Z.eqb pgrp 0 then result = (0, 110) /\ current = before else
    if Z.ltb 0 before.(IntrState).(intNesting) then result = (0, 2) /\ current = before else
    if Z.ltb 0 before.(IntrState).(lockNesting) then result = (0, 13) /\ current = before else
    exists observed, before.(FlagState).(flagImages) i = Some observed /\
      if negb (Z.eqb observed.(flagImageType) 5)
      then result = (0, 1) /\ current = before
      else exists entered acquired ready error released,
        sched_fields_same_view entered view /\
        critical_region_interval critical sg view.(os_execution_invocation) before acquired /\
        flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn ready error) released /\
        critical_region_interval critical sg entered.(os_execution_invocation) released current /\
        result = (ready, error).

Definition flag_pend_caller_program environment critical sg caller call mask i pgrp requested wait_type timeout :=
  match caller with
  | FlagPendTaskCaller _ => flag_pend_program environment critical sg call mask i pgrp requested wait_type timeout
  | FlagPendInterruptCaller view _ => flag_pend_view_program critical sg view i pgrp requested wait_type timeout
  end.

Definition flag_pend_caller_safe environment critical sg caller call mask i pgrp requested wait_type timeout before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (flag_pend_caller_program environment critical sg caller call mask i pgrp requested wait_type timeout)
    (fun result state => X (fst result) (snd result) state).

Definition flag_pend_same_caller (returned original : FlagPendCaller) : Prop :=
  match returned, original with
  | FlagPendTaskCaller next, FlagPendTaskCaller previous => task_tcb_init_stack_same_call next previous
  | FlagPendInterruptCaller next active, FlagPendInterruptCaller previous old_active =>
      active = old_active /\ sched_fields_same_view next previous
  | _, _ => False
  end.

Lemma flag_pend_caller_safe_task : forall environment critical sg call mask i pgrp requested mode delay before X,
  flag_pend_caller_safe environment critical sg (FlagPendTaskCaller call) call mask i pgrp requested mode delay before X <->
  flag_pend_safe environment critical sg call mask i pgrp requested mode delay before X.
Proof. reflexivity. Qed.

Lemma flag_pend_caller_safe_return : forall environment critical sg caller call mask i pgrp requested mode delay
  before ready error current X,
  flag_pend_caller_program environment critical sg caller call mask i pgrp requested mode delay
    before (ready, error) current ->
  flag_pend_caller_safe environment critical sg caller call mask i pgrp requested mode delay before X ->
  flag_pend_return_safe ready error current X.
Proof.
  intros environment critical sg caller call mask i pgrp requested mode delay before ready error current X
    Hstep Hsafe.
  unfold flag_pend_caller_safe in Hsafe; unfold flag_pend_return_safe.
  eapply (highstependret_derive
    (flag_pend_caller_program environment critical sg caller call mask i pgrp requested mode delay)
    (fun state => state = before) (ready, error) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Definition flag_pend_public_entry environment critical sg caller call mask i pgrp requested wait_type timeout before X : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  (pgrp = 0 \/ (0 <= i < sg.(osKernelConfig).(cfgMaxFlags) /\ pgrp = flag_pool_addr sg i)) /\
  0 <= requested < 65536 /\ 0 <= wait_type < 256 /\ 0 <= timeout < 4294967296 /\
  flag_pend_caller_source sg caller call i pgrp wait_type before /\
  flag_pend_caller_safe environment critical sg caller call mask i pgrp requested wait_type timeout before X.

Definition flag_pend_public_post environment (local : Armv7aContinuation -> Assertion) sg caller original (mask : Z) perr
  (before : UCOS2_Verify_State) (ready : Z)
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current error next_local,
    coq_prop (flag_pend_return_safe ready error current X /\
      flag_pend_same_caller returned caller /\
      match returned, caller with
      | FlagPendTaskCaller next, FlagPendTaskCaller _ =>
          task_tcb_init_stack_same_call next original /\
          (flag_pend_task_entry original before -> flag_pend_task_stage next current)
      | FlagPendInterruptCaller _ _, FlagPendInterruptCaller _ _ => True
      | _, _ => False
      end) &&
    (flag_pend_caller_world environment next_local sg returned mask current ** perr # UChar |-> error).

Lemma flag_pend_task_caller_entry_resources : forall environment local sg call mask state,
  flag_pend_call_world environment local sg call mask state =
  flag_pend_caller_world environment local sg (FlagPendTaskCaller call) mask state.
Proof. reflexivity. Qed.

Lemma flag_pend_interrupt_caller_entry_resources :
  forall environment local sg context active mask state,
  kernel_execution_view_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (os_int_exit_execution_view context) mask **
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg active state =
  flag_pend_caller_world environment local sg
    (FlagPendInterruptCaller (os_int_exit_execution_view context) active) mask state.
Proof. reflexivity. Qed.

Definition flag_pend_group_lookup (state : UCOS2_Verify_State) (i : Z) (image : FlagGroupImage) : Prop :=
  state.(FlagState).(flagImages) i = Some image.
Definition flag_pend_group_type (image : FlagGroupImage) : Z := image.(flagImageType).
Definition flag_pend_group_bits (image : FlagGroupImage) : Z := image.(flagImageBits).

Definition flag_pend_group_without_type_bits (c : KernelConfiguration) (p : addr)
  (image : FlagGroupImage) : Assertion :=
  store_optional_bytes (p + 1) (firstn 3 image.(flagImagePadding)) **
  (p + 4) # Ptr |-> image.(flagImageHead) **
  store_optional_bytes (p + 8 + flag_word_bytes c) (skipn 3 image.(flagImagePadding)) **
  (if c.(cfgFlagNames) then (p + flag_group_name_offset c) # Ptr |-> image.(flagImageName) else emp).

Definition flag_pend_group_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (i : Z) (image : FlagGroupImage) : Assertion :=
  flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image **
  flag_fields_raw_rep_without_group sg state.(FlagState) i **
  UCOS2_raw_rep_missing_flag sg state.

Lemma flag_pend_group_split : forall sg state i image,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_pend_group_lookup state i image ->
  UCOS2_fields_inv sg state |--
  coq_prop (UCOS2_state_inv sg state) &&
  ((flag_pool_addr sg i) # UChar |-> image.(flagImageType) **
   (flag_pool_addr sg i + 8) # UShort |-> image.(flagImageBits) **
   flag_pend_group_frame sg state i image).
Proof.
  intros sg state i image Hconfig Himage.
  unfold UCOS2_fields_inv, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagEnabled].
  Intros.
  sep_apply_l_atomic (proj1 (flag_fields_raw_rep_split_group sg state.(FlagState) i image Himage)).
  unfold flag_group_rep, flag_pend_group_frame, flag_pend_group_without_type_bits, flag_word_rep.
  rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagBits]; entailer!.
Qed.

Lemma flag_pend_group_merge_original : forall sg state i image,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  UCOS2_state_inv sg state -> flag_pend_group_lookup state i image ->
  (flag_pool_addr sg i) # UChar |-> image.(flagImageType) **
  (flag_pool_addr sg i + 8) # UShort |-> image.(flagImageBits) **
  flag_pend_group_frame sg state i image |-- UCOS2_fields_inv sg state.
Proof.
  intros sg state i image Hconfig Hvalid Himage.
  assert (Hgroup :
    (flag_pool_addr sg i) # UChar |-> image.(flagImageType) **
    (flag_pool_addr sg i + 8) # UShort |-> image.(flagImageBits) **
    flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image |--
    flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) image).
  { unfold flag_group_rep, flag_pend_group_without_type_bits, flag_word_rep;
    rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagBits]; entailer!. }
  unfold flag_pend_group_frame; sep_apply_l_atomic Hgroup.
  sep_apply_l_atomic (proj2 (flag_fields_raw_rep_split_group sg state.(FlagState) i image Himage)).
  unfold UCOS2_fields_inv, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagEnabled]; entailer!.
Qed.

Definition flag_pend_counter_frame (sg : StableGlobVars) (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    UCOS2_fields_raw_rep_missing_module sg state InterruptModule.

Lemma flag_pend_counters_split : forall sg state,
  UCOS2_fields_inv sg state --||--
  sg.(g_OSIntNesting) # UChar |-> os_sched_ints state **
  sg.(g_OSLockNesting) # UChar |-> os_sched_locks state **
  flag_pend_counter_frame sg state.
Proof.
  intros; unfold flag_pend_counter_frame.
  rewrite (UCOS2_fields_inv_split_module sg state InterruptModule) by discriminate.
  cbn [UCOS2_module_rep]; unfold os_sched_ints, os_sched_locks.
  split.
  - unfold interrupt_inv, store_int_state; entailer!.
  - pose proof (interrupt_inv_merge_counters sg state.(IntrState)) as Hmerge.
    unfold store_int_state in Hmerge.
    sep_apply_l_atomic Hmerge; entailer!.
Qed.

Definition flag_pend_global_addresses sg intp lockp highp currentp high_tcbp tablep countp unmap readygp readytp current_tcbp : Prop :=
  os_sched_global_addresses sg intp lockp highp currentp high_tcbp tablep countp unmap readygp readytp /\
  current_tcbp = sg.(g_OSTCBCur).

(** Static interpretation of the fixed selected C/ABI: OSTCBStkPtr is
    the first member of struct os_tcb, before every optional field. As with
    the other field bindings below, its address equality is an interpretation
    of the opaque field-address vocabulary, not a theorem about an arbitrary
    evaluator or a new run-time admission condition. *)
Definition flag_pend_source_layout : Prop :=
  flag_block_call_layout /\ flag_unlink_layout /\
  (forall p, &(p # "os_flag_grp" ->ₛ "OSFlagType") = p) /\
  (forall p, &(p # "os_flag_grp" ->ₛ "OSFlagFlags") = p + 8) /\
  (forall p, &(p # "os_tcb" ->ₛ "OSTCBFlagsRdy") = tcb_field_address p TCBFlagsRdy) /\
  (forall p, &(p # "os_tcb" ->ₛ "OSTCBStat") = tcb_field_address p TCBStat) /\
  (forall p, &(p # "os_tcb" ->ₛ "OSTCBStatPend") = tcb_field_address p TCBStatPend) /\
  (forall p, tcb_field_address p TCBStkPtr = p).

Lemma flag_pend_source_layout_implies_stack_field_layout : forall sg,
  flag_pend_source_layout -> kernel_tcb_stack_field_layout sg.
Proof.
  intros sg [_ [_ [_ [_ [_ [_ [_ Hstack]]]]]]] slot Hslot.
  apply Hstack.
Qed.

Lemma flag_pend_source_layout_stack_field_address : forall sg call state,
  flag_pend_source_layout -> UCOS2_state_inv sg state ->
  kernel_call_task_source call state ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot).
Proof.
  intros sg call state Hlayout Hvalid Hsource.
  eapply kernel_call_task_source_stack_field_address; [|exact Hvalid|exact Hsource].
  apply flag_pend_source_layout_implies_stack_field_layout; exact Hlayout.
Qed.

Definition flag_pend_node_address_layout (p next prev tcb group bits mode : Z) : Prop :=
  next = p /\ prev = p + 4 /\ tcb = p + 8 /\ group = p + 12 /\ bits = p + 16 /\ mode = p + 18.

Lemma flag_pend_six_local_cells : forall p next prev tcb group bits mode,
  flag_pend_node_address_layout p next prev tcb group bits mode ->
  next # Ptr |->_ ** prev # Ptr |->_ ** tcb # Ptr |->_ ** group # Ptr |->_ **
  bits # UShort |->_ ** mode # UChar |->_ --||-- flag_pend_node_fields p.
Proof.
  intros p next prev tcb group bits mode [-> [-> [-> [-> [-> ->]]]]].
  unfold flag_pend_node_fields, flag_node_fields_uninit_rep,
    flag_node_mode_offset, flag_word_bytes, selected_kernel_configuration; cbn.
  split; entailer!.
Qed.

Definition flag_pend_current_binding (state : UCOS2_Verify_State) tid old : Prop :=
  state.(SchedState).(curTaskID) = Some tid /\
  state.(TskState).(inUsedTaskStates) tid = Some old.

Definition flag_pend_sched_without_current (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (sched : SchedAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp sched.(readyList) tasks **
  sched_rows_rep sg tasks sched.(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte sched.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte sched.(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg sched.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> sched.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if sched.(isRunning) then 1 else 0).

Definition flag_pend_group_current_frame sg state tid old i image : Assertion :=
  flag_pend_group_without_type_bits sg.(osKernelConfig) (flag_pool_addr sg i) image **
  flag_fields_raw_rep_without_group sg state.(FlagState) i **
  task_public_storage_without_field sg state.(TskState) tid old (TCBCommonField TCBFlagsRdy) **
  flag_pend_sched_without_current sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state.

Lemma flag_pend_flag_frame_split_task_sched : forall sg state,
  UCOS2_raw_rep_missing_flag sg state --||--
  task_public_storage sg state.(TskState) **
  sched_raw_rep sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state.
Proof.
  intros; unfold UCOS2_raw_rep_missing_flag, UCOS2_raw_rep_missing_module,
    UCOS2_selected_rep, UCOS2_raw_rep_missing_task_storage_sched_flag.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  unfold task_shared_rep; split; entailer!.
Qed.

Lemma flag_pend_group_frame_split_current : forall sg state tid old i image,
  flag_pend_current_binding state tid old ->
  flag_pend_group_frame sg state i image |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> old.(tcbFlagsRdy) **
  flag_pend_group_current_frame sg state tid old i image.
Proof.
  intros sg state tid old i image [Hcurrent Hold].
  unfold flag_pend_group_frame, flag_pend_group_current_frame.
  sep_apply_l_atomic (proj1 (flag_pend_flag_frame_split_task_sched sg state)).
  sep_apply_l_atomic (task_public_storage_split_field sg state.(TskState) tid old
    (TCBCommonField TCBFlagsRdy) Hold
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)).
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell].
  unfold sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Lemma flag_pend_group_frame_merge_current : forall sg state tid old i image,
  flag_pend_current_binding state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBFlagsRdy # UShort |-> old.(tcbFlagsRdy) **
  flag_pend_group_current_frame sg state tid old i image |--
  flag_pend_group_frame sg state i image.
Proof.
  intros sg state tid old i image [Hcurrent Hold].
  pose proof (task_public_storage_merge_field sg state.(TskState) tid old
    (TCBCommonField TCBFlagsRdy) Hold
    (tcb_configured_common_field_in _ _ TCBFlagsRdy)) as Htask.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Htask.
  unfold flag_pend_group_current_frame, flag_pend_group_frame.
  sepcon_assoc_change.
  sep_apply_l_atomic Htask.
  sep_apply_r_atomic (proj2 (flag_pend_flag_frame_split_task_sched sg state)).
  unfold sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Definition flag_pend_saved_prefix environment critical sg call mask before i pgrp
  entered saved acquired : Prop :=
  pgrp <> 0 /\ before.(IntrState).(intNesting) <= 0 /\
  before.(IntrState).(lockNesting) <= 0 /\
  (exists image, before.(FlagState).(flagImages) i = Some image /\ image.(flagImageType) = 5) /\
  ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg call mask saved before entered acquired /\
  interrupt_saved_value mask saved /\ task_tcb_init_stack_same_call entered call /\
  before.(IntrState) = acquired.(IntrState).

Definition flag_pend_first_return sg i requested wait_type timeout acquired ready error released : Prop :=
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendReturn ready error) released.

(** This phase observation is indexed by the original stack task even while
    another task runs. It never asserts that the waiting caller is ready.
    A normal returned/current endpoint supplies readiness separately. *)
Definition flag_pend_wait_registration (call : OsSchedCallContext) (node : addr)
  (state : UCOS2_Verify_State) : Prop :=
  exists task,
    state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some task /\
    task.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
    task_invocation_active state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
    task.(eventPtr) = None /\ task.(eventMultiWaitEvents) = [] /\ task.(tcbEventMultiPtr) = 0 /\
    match state.(FlagState).(flagWaitNodes) node with
    | Some waiter =>
        waiter.(flagNodeAddr) = node /\
        task_stack_key call.(os_sched_call_stack) = (waiter.(flagTask), waiter.(flagTaskGeneration)) /\
        task.(tcbFlagNode) = node
    | None => task.(tcbFlagNode) = 0
    end.

Definition flag_pend_wait_phase sg call node state : Assertion :=
  coq_prop (flag_pend_wait_registration call node state) &&
  flag_pend_sched_node_fields_rep sg node state.


(** The paired-call boundary consumes the actual captured heap. Its dynamic
    local family is returned by that same source event. This is a conditional
    linked-C/ABI contract; source proofs must realize it for the concrete active
    phase. In particular ordinary Save has no Scheduler selection cut and the
    active predicate supplies neither current-ready nor a future wake. *)
(** Shared declaration: PrimitiveComponent.flag_pend_active_save_input. *)

(** Shared declaration: PrimitiveComponent.flag_pend_active_restore_input. *)

Definition flag_pend_active_save_event environment critical local active
  sg original mask saved before returned acquired next_local
  (before_heap after_heap : model) : Prop :=
  ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired /\
  task_tcb_init_stack_same_call returned original /\
  task_tcb_init_stack_source_preserved original before acquired /\
  interrupt_saved_value mask saved /\
  flag_pend_active_save_input environment critical local active sg original mask before before_heap /\
  flag_pend_active_restore_input environment critical next_local active
    sg returned saved acquired acquired after_heap.

Definition flag_pend_active_save_output environment critical local active
  sg original mask before before_heap saved : Assertion :=
  fun after_heap => exists returned acquired next_local,
    flag_pend_active_save_event environment critical local active sg original mask saved
      before returned acquired next_local before_heap after_heap.

Definition flag_pend_active_restore_event environment critical local active
  sg original saved acquired released returned current next_local
  (before_heap after_heap : model) : Prop :=
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg original released returned current /\
  task_tcb_init_stack_same_call returned original /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
  (UCOS2_state_inv sg released ->
    task_tcb_init_stack_source_preserved original released current) /\
  flag_pend_active_restore_input environment critical local active
    sg original saved acquired released before_heap /\
  flag_pend_active_save_input environment critical next_local active
    sg returned (armv7a_irq_fiq_mask saved) current after_heap.

Definition flag_pend_active_restore_output environment critical local active
  sg original saved acquired released before_heap : Assertion :=
  fun after_heap => exists returned current next_local,
    flag_pend_active_restore_event environment critical local active
      sg original saved acquired released returned current next_local before_heap after_heap.

Lemma flag_pend_active_save_output_open : forall environment critical local active
  sg original mask before before_heap saved,
  flag_pend_active_save_output environment critical local active
    sg original mask before before_heap saved |--
  EX returned acquired next_local,
    coq_prop (ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg original mask saved
      before returned acquired /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_source_preserved original before acquired /\
      interrupt_saved_value mask saved) &&
    flag_pend_active_restore_input environment critical next_local active
      sg returned saved acquired acquired.
Proof.
  intros environment critical local active sg original mask before before_heap saved heap
    [returned [acquired [next_local [Heffect [Hsame [Hsource [Hsaved [Hbefore Hafter]]]]]]]].
  exists returned, acquired, next_local; split.
  - exact (conj Heffect (conj Hsame (conj Hsource Hsaved))).
  - exact Hafter.
Qed.

Lemma flag_pend_active_restore_output_open : forall environment critical local active
  sg original saved acquired released before_heap,
  flag_pend_active_restore_output environment critical local active
    sg original saved acquired released before_heap |--
  EX returned current next_local,
    coq_prop (ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg original released returned current /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released ->
        task_tcb_init_stack_source_preserved original released current)) &&
    flag_pend_active_save_input environment critical next_local active
      sg returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local active sg original saved acquired released before_heap heap
    [returned [current [next_local [Heffect [Hsame [Hcall [Hsource [Hbefore Hafter]]]]]]]].
  exists returned, current, next_local; split.
  - exact (conj Heffect (conj Hsame (conj Hcall Hsource))).
  - exact Hafter.
Qed.

(** Outcome observations are about the original waiter, even while a different
    task runs. A linked waiter has either the initial FLAG/PendOK phase or the
    actual Tick-expired phase. Detached is supplied only by Post/PendOK or
    Del/PendAbort; arbitrary TaskRdy PendStatus is deliberately insufficient. *)
Definition flag_pend_wait_outcome (original : OsSchedCallContext) (node : addr)
  (state : UCOS2_Verify_State) : Prop :=
  exists task,
    state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some task /\
    match state.(FlagState).(flagWaitNodes) node with
    | Some _ =>
        (task_non_suspension_bits task.(stat) = task_pend_mask PendFlag /\ task.(statPend) = PendOK) \/
        (task_non_suspension_bits task.(stat) = 0 /\ task.(statPend) = PendTimeout /\ task.(dly) = 0)
    | None => (task.(statPend) = PendOK \/ task.(statPend) = PendAbort) /\ task.(dly) = 0
    end.

Definition flag_pend_wait_active sg original node call state : Assertion :=
  coq_prop (flag_pend_wait_outcome original node state /\
    task_idle_ready sg state.(TskState) /\ flag_pend_non_idle_at sg original state) &&
    flag_active_waiting sg original node call state.

Lemma flag_pend_wait_active_prefix : forall sg original node,
  os_sched_active_local_stable (flag_pend_wait_active sg original node).
Proof.
  intros sg original node call state.
  unfold flag_pend_wait_active, flag_pend_wait_outcome, flag_pend_non_idle_at.
  rewrite flag_active_waiting_sched_prefix.
  split; reflexivity.
Qed.

Lemma flag_pend_block_wait_outcome : forall sg state original waiter old group image timeout flags,
  original.(os_sched_call_stack).(stackLeaseSlot) = waiter.(flagTask) ->
  UCOS2_state_inv sg state ->
  valid_flag_state sg state.(FlagState) ->
  flag_block_call_protocol sg state waiter old group image timeout ->
  flag_block_node sg state.(FlagState) waiter (flag_block_call_tcb sg waiter) = Some flags ->
  flag_pend_wait_outcome original waiter.(flagNodeAddr)
    (flag_execution.flag_block_state state waiter flags old timeout).
Proof.
  intros sg state original waiter old group image timeout flags Hslot Hstate Hvalid Hprotocol Hblock.
  destruct Hprotocol as [Hcur [Hprio [Hold [Hready [Hnull [Hptr [Hmulti
    [Hwgen [Hnode [Hfresh [Hgroup [Hgroupgen [Himage Hrest]]]]]]]]]]]]].
  pose proof (flag_block_installs_node sg state.(FlagState) waiter
    (flag_block_call_tcb sg waiter) flags group image Hvalid Hgroup Himage Hfresh Hblock) as Hlinked.
  unfold flag_pend_wait_outcome.
  exists (task_prepare_flag_wait old waiter.(flagNodeAddr) timeout).
  split.
  - cbn [flag_execution.flag_block_state replace_TskS replace_FlagS replace_SchedS
      TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Hslot, Z.eqb_refl; reflexivity.
  - cbn [flag_execution.flag_block_state replace_TskS replace_FlagS replace_SchedS FlagState].
    rewrite Hlinked; left; split; [|reflexivity].
    apply task_prepare_event_wait_pending_bits.
    destruct ((proj1 (proj1 (proj1 (proj2 (proj2 Hstate)))))
      waiter.(flagTask) Hready) as [ready_task [Hlookup [Hrange Heffective]]].
    assert (ready_task = old) by congruence; subst ready_task.
    apply task_effectively_ready_has_no_pending; exact Heffective.
Qed.

Lemma flag_pend_task_rdy_wait_outcome : forall sg state original call node bits result schedule post,
  flag_active_waiting_registration original node call state ->
  (result = PendOK \/ result = PendAbort) ->
  flag_task_rdy sg state node bits result = Some (schedule, post) ->
  flag_pend_wait_outcome original node post.
Proof.
  intros sg state original call node bits result schedule post
    [task [Htask Hbinding]] Hresult Hstep.
  unfold flag_task_rdy in Hstep.
  destruct (flag_unlink_node state.(FlagState) node) as [[waiter flags]|] eqn:Hunlink;
    [|discriminate].
  destruct (state.(TskState).(inUsedTaskStates) waiter.(flagTask)) as [old|] eqn:Hold;
    [|discriminate].
  inversion Hstep; subst post schedule.
  destruct (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink) as [Hlinked Hnone].
  rewrite Hlinked in Hbinding; destruct Hbinding as [Haddr [Hkey Hflag]].
  assert (Hslot : original.(os_sched_call_stack).(stackLeaseSlot) = waiter.(flagTask))
    by exact (f_equal fst Hkey).
  unfold flag_pend_wait_outcome; exists (task_flag_wake old bits result).
  split.
  - cbn [flag_wake_state replace_TskS replace_FlagS replace_SchedS TskState
      glob_task_set_usedtask inUsedTaskStates]; rewrite Hslot, Z.eqb_refl; reflexivity.
  - cbn [flag_wake_state replace_TskS replace_FlagS replace_SchedS FlagState].
    rewrite Hnone; exact (conj Hresult eq_refl).
Qed.

Lemma flag_pend_wait_ready_classification : forall original node state task,
  flag_pend_wait_outcome original node state ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some task ->
  is_effectively_ready task.(stat) task.(dly) = true ->
  (state.(FlagState).(flagWaitNodes) node = None <->
    task.(statPend) = PendOK \/ task.(statPend) = PendAbort) /\
  ((exists waiter, state.(FlagState).(flagWaitNodes) node = Some waiter) <->
    task.(statPend) = PendTimeout).
Proof.
  intros original node state task [observed [Hlookup Houtcome]] Htask Hready.
  assert (observed = task) by congruence; subst observed.
  pose proof (task_effectively_ready_has_no_pending task Hready) as Hclear.
  destruct (state.(FlagState).(flagWaitNodes) node) as [waiter|] eqn:Hnode.
  - destruct Houtcome as [[Hpending Hok]|[Hpending [Htimeout Hdly]]].
    + change (task_pend_mask PendFlag) with 32 in Hpending; lia.
    + rewrite Htimeout; split.
      * split; [discriminate|intros [H|H]; discriminate].
      * split; [intros _; reflexivity|intros _; exists waiter; reflexivity].
  - destruct Houtcome as [Hstatus Hdly]; split.
    + split; auto.
    + split.
      * intros [waiter H]; discriminate.
      * intros H; destruct Hstatus; congruence.
Qed.


Lemma flag_pend_tick_wait_outcome : forall sg original node state old,
  flag_pend_wait_outcome original node state ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some old ->
  flag_pend_wait_outcome original node
    (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state).
Proof.
  intros sg original node state old [observed [Hlookup Houtcome]] Hold.
  assert (observed = old) by congruence; subst observed.
  unfold flag_pend_wait_outcome; exists (tick_task_update old).
  split.
  - rewrite tick_task_step_task_state_eq by exact Hold.
    cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - assert (Hflags : (tick_task_step sg original.(os_sched_call_stack).(stackLeaseSlot) old state).(FlagState) =
      state.(FlagState)).
    { unfold tick_task_step; destruct (Z.eqb old.(dly) 0); [reflexivity|].
      destruct (Z.eqb (tick_task_update old).(dly) 0); reflexivity. }
    rewrite Hflags.
    destruct (state.(FlagState).(flagWaitNodes) node) as [waiter|].
    + destruct Houtcome as [[Hpending Hok]|[Hclear [Htimeout Hz]]].
      * destruct (Z.eq_dec old.(dly) 1) as [Hlast|Hlast].
        -- destruct (tick_task_one_tick_timeout old PendFlag Hlast Hpending ltac:(discriminate))
             as [Hdelay [Hstatus [Hresult Hrest]]]; right; auto.
        -- left; unfold tick_task_update.
           destruct (Z.eqb old.(dly) 0); [auto|].
           assert (Hnotlast : Z.eqb (old.(dly) - 1) 0 = false)
             by (apply Z.eqb_neq; lia).
           rewrite Hnotlast; exact (conj Hpending Hok).
      * rewrite tick_task_zero_delay_eq by exact Hz; right; auto.
    + destruct Houtcome as [Hstatus Hz].
      rewrite tick_task_zero_delay_eq by exact Hz; auto.
Qed.

(** Readiness belongs to the actual execution endpoint. These two producers
    refer respectively to the true no-switch cut and the LAST selected
    installation which returns to this invocation. Neither uses a future
    wake, a generic history post, or the first outgoing switch destination. *)
(** Shared declaration: PrimitiveComponent.flag_pend_current_ready. *)

Lemma flag_pend_nonswitch_current_ready : forall sg call entry,
  UCOS2_state_inv sg entry ->
  kernel_call_task_source call entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  os_sched_requests_switch entry = false ->
  entry.(SchedState).(readyList) <> [] ->
  flag_pend_current_ready call (os_sched_prefix_state entry).
Proof. intros; eapply os_sched_nonswitch_current_ready_at; eassumption. Qed.

Lemma flag_pend_last_install_current_ready :
  forall external sg context outgoing hooked incoming resumed returned,
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_destination_binding external context outgoing hooked incoming resumed ->
  returned.(os_sched_call_stack) = incoming ->
  flag_pend_current_ready returned (os_sched_install_context context outgoing incoming hooked).
Proof.
  intros external sg context outgoing hooked incoming resumed returned Hvalid Hhigh Hdestination Hstack.
  destruct (task_create_install_selected_ready external sg context outgoing hooked incoming resumed
    Hvalid Hhigh Hdestination) as [task [Hready Hgeneration]].
  exists task; rewrite Hstack; exact (conj Hready Hgeneration).
Qed.

Definition flag_pend_fresh_observation (original call : OsSchedCallContext)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (flag_active_fresh_registration original call state) && emp.

Definition flag_pend_first_registration mode original before call state : Prop :=
  (flag_pend_valid_mode mode \/ flag_pend_task_entry original before) ->
    flag_active_fresh_registration original call state.

Definition flag_pend_first_observation mode original before call state : Assertion :=
  coq_prop (flag_pend_first_registration mode original before call state) && emp.

Lemma flag_pend_entry_fresh_observation : forall call state,
  flag_pend_task_entry call state ->
  flag_active_fresh_registration call call state.
Proof.
  intros call state [[Horigin [Hrunning [Habsent [task [Hready [Hgen Hclean]]]]]] Hactive].
  destruct Hready as [Htask Hrest].
  destruct Hclean as [Hnode [Hevent [Hmulti Hmultiptr]]].
  exists task; split; [|exact Hnode].
  unfold flag_active_task_fields, flag_active_event_clear.
  split; [unfold task_tcb_init_stack_same_call; repeat split|].
  exact (conj Horigin (conj Htask (conj Hgen (conj Hactive
    (conj Hevent (conj Hmulti Hmultiptr)))))).
Qed.


Definition flag_pend_block_binding sg original call state i node requested normalized timeout
  waiter old group image : Prop :=
  flag_active_fresh_registration original call state /\
  task_stack_key original.(os_sched_call_stack) = (waiter.(flagTask), waiter.(flagTaskGeneration)) /\
  flag_block_call_protocol sg state waiter old group image timeout /\
  waiter.(flagNodeAddr) = node /\ waiter.(flagGroup) = i /\
  waiter.(flagMask) = requested /\ encode_flag_wait_mode waiter.(flagWaitMode) = normalized.

Lemma flag_pend_block_fields_wait_outcome :
  forall sg state original call waiter old group image timeout,
  flag_active_fresh_registration original call state ->
  task_stack_key original.(os_sched_call_stack) = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  task_idle_ready sg state.(TskState) ->
  flag_pend_non_idle_at sg original state ->
  UCOS2_state_inv sg state ->
  valid_flag_state sg state.(FlagState) ->
  flag_block_call_protocol sg state waiter old group image timeout ->
  flag_block_call_fields_post sg state waiter old timeout |--
  EX flags,
    coq_prop (flag_block_node sg state.(FlagState) waiter (flag_block_call_tcb sg waiter) = Some flags /\
      flag_block_spec.flag_block sg state waiter timeout =
        Some (flag_execution.flag_block_state state waiter flags old timeout)) &&
    (UCOS2_fields_inv sg (flag_execution.flag_block_state state waiter flags old timeout) **
     flag_pend_wait_active sg original waiter.(flagNodeAddr) call
       (flag_execution.flag_block_state state waiter flags old timeout)).
Proof.
  intros sg state original call waiter old group image timeout Hfresh Hkey Hidle Hnonidle Hstate Hvalid Hprotocol.
  sep_apply_l_atomic (flag_active_block_fields_post sg state original call waiter old group image
    timeout Hfresh Hkey Hvalid Hprotocol).
  Intros flags.
  assert (Houtcome : flag_pend_wait_outcome original waiter.(flagNodeAddr)
      (flag_execution.flag_block_state state waiter flags old timeout)).
  { apply (flag_pend_block_wait_outcome sg state original waiter old group image timeout flags
      (f_equal fst Hkey) Hstate Hvalid Hprotocol); tauto. }
  assert (Hslot : original.(os_sched_call_stack).(stackLeaseSlot) = waiter.(flagTask))
    by exact (f_equal fst Hkey).
  assert (Hold : state.(TskState).(inUsedTaskStates) waiter.(flagTask) = Some old)
    by exact (proj1 (proj2 (proj2 Hprotocol))).
  destruct Hnonidle as [idle_node [Hlookup [Hgen Hpriority]]].
  rewrite Hslot in Hlookup.
  assert (idle_node = old) by congruence; subst idle_node.
  assert (Hidle_after : task_idle_ready sg
    (flag_execution.flag_block_state state waiter flags old timeout).(TskState)).
  { eapply task_update_non_idle_preserves_idle_ready; eassumption. }
  assert (Hnonidle_after : flag_pend_non_idle_at sg original
    (flag_execution.flag_block_state state waiter flags old timeout)).
  { exists (task_prepare_flag_wait old waiter.(flagNodeAddr) timeout).
    split.
    - cbn [flag_execution.flag_block_state replace_TskS replace_FlagS replace_SchedS
        TskState glob_task_set_usedtask inUsedTaskStates]; rewrite Hslot, Z.eqb_refl; reflexivity.
    - split; assumption. }
  Exists flags; unfold flag_pend_wait_active; entailer!.
Qed.

Definition flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked : Prop :=
  flag_pend_first_critical sg i requested wait_type timeout acquired (FlagPendWaiting node) blocked.

Definition flag_pend_waiting_prefix environment critical sg original mask before i pgrp
  requested wait_type timeout node returned current : Prop :=
  exists entered saved acquired blocked,
    flag_pend_saved_prefix environment critical sg original mask before i pgrp entered saved acquired /\
    flag_pend_first_waiting sg i requested wait_type timeout acquired node blocked /\
    ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg entered blocked returned current.


Definition flag_pend_mode_parameters original normalized consumed : Prop :=
  normalized = Z.land original 127 /\
  consumed = (if Z.eqb (Z.land original 128) 0 then 0 else 1).

Definition flag_pend_scheduled_prefix environment critical sg original mask before i pgrp
  requested wait_type timeout node returned current : Prop :=
  exists restored released,
    flag_pend_waiting_prefix environment critical sg original mask before i pgrp
      requested wait_type timeout node restored released /\
    SchedulerPhaseCandidate.os_sched_task_call_history environment critical sg restored mask released returned current /\
    flag_pend_current_ready returned current.

Definition flag_pend_resumed_prefix environment critical sg original mask before i pgrp
  requested wait_type timeout node returned saved current : Prop :=
  exists scheduled entry,
    flag_pend_scheduled_prefix environment critical sg original mask before i pgrp
      requested wait_type timeout node scheduled entry /\
    ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg scheduled mask saved entry returned current /\
    flag_pend_current_ready returned current.

Definition flag_pend_resume_result sg i node wait_type acquired ready error cleaned : Prop :=
  flag_pend_resume_critical sg i node wait_type acquired (ready, error) cleaned.

(** The resume source first writes StatPend, then calls Unlink on the timeout
    path, and finally writes Stat. The residual deliberately stays raw while
    the linked waiter has PendOK: the global waiter invariant is open there. *)
Definition flag_pend_resume_frame sg state tid old : Assertion :=
  task_public_storage_without_two_fields sg state.(TskState) tid old
    (TCBCommonField TCBStatPend) (TCBCommonField TCBStat) **
  flag_pend_sched_without_current sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
  flag_fields_raw_rep sg state.(FlagState).

Definition flag_pend_unlink_frame sg state tid : Assertion :=
  task_public_storage_without_task sg state.(TskState) tid **
  flag_pend_sched_without_current sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state.

Definition flag_pend_cleanup_stat_frame sg state tid task : Assertion :=
  task_public_storage_without_field sg state.(TskState) tid task (TCBCommonField TCBStat) **
  flag_pend_sched_without_current sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
  flag_fields_raw_rep sg state.(FlagState).

Definition flag_pend_write_pend_ok (old : TaskAbstractState) : TaskAbstractState :=
  task_set_status (task_clear_pend_status false old) old.(stat).

Lemma flag_pend_write_pend_ok_layout : forall sg old,
  task_layout_image sg (flag_pend_write_pend_ok old) =
    tcb_layout_write (task_layout_image sg old) (TCBCommonField TCBStatPend) (Some 0).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |];
    try destruct field; reflexivity.
Qed.

Lemma flag_pend_resume_fields_split : forall sg state tid old,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_pend_current_binding state tid old ->
  UCOS2_fields_inv sg state |--
  coq_prop (UCOS2_state_inv sg state) &&
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
   tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status old.(statPend) **
   tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> encode_task_status old.(stat) **
   flag_pend_resume_frame sg state tid old).
Proof.
  intros sg state tid old Hconfig [Hcurrent Hold].
  unfold UCOS2_fields_inv, UCOS2_fields_raw_rep, flag_fields_configured_rep.
  rewrite Hconfig; cbn [selected_kernel_configuration cfgFlagEnabled]; Intros.
  sep_apply_l_atomic (proj1 (flag_pend_flag_frame_split_task_sched sg state)).
  sep_apply_l_atomic (task_public_storage_split_two_fields sg state.(TskState) tid old
    (TCBCommonField TCBStatPend) (TCBCommonField TCBStat)
    ltac:(discriminate) Hold
    (tcb_configured_common_field_in _ _ TCBStatPend)
    (tcb_configured_common_field_in _ _ TCBStat)).
  unfold flag_pend_resume_frame, sched_raw_rep, sched_physical_rep, flag_pend_sched_without_current.
  rewrite Hcurrent; cbn [encode_task_link tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell].
  entailer!.
Qed.


Definition flag_pend_error_intermediate state node status intermediate : Prop :=
  exists tid old,
    flag_pend_current_binding state tid old /\ encode_pend_status old.(statPend) = status /\
    if Z.eqb status 2
    then intermediate = flag_pend_update_task state tid (flag_pend_write_pend_ok old)
    else exists waiter flags,
      flag_unlink_node state.(FlagState) node = Some (waiter, flags) /\
      waiter.(flagTask) = tid /\
      intermediate = replace_FlagS flags
        (flag_pend_update_task state tid (task_set_flag_node (flag_pend_write_pend_ok old) 0)).

Lemma flag_pend_error_write_stat_endpoint : forall old,
  task_set_status (flag_pend_write_pend_ok old) Byte.zero = task_clear_pend_status false old /\
  task_set_status (task_set_flag_node (flag_pend_write_pend_ok old) 0) Byte.zero =
    task_set_flag_node (task_clear_pend_status false old) 0.
Proof. intros; split; reflexivity. Qed.

Lemma flag_pend_safe_resumed_return :
  forall environment critical sg original mask before i pgrp requested wait_type timeout node
    reentered saved reacquired ready error cleaned returned current X,
  flag_pend_resumed_prefix environment critical sg original mask before i pgrp
    requested wait_type timeout node reentered saved reacquired ->
  flag_pend_resume_result sg i node wait_type reacquired ready error cleaned ->
  ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg reentered cleaned returned current ->
  flag_pend_safe environment critical sg original mask i pgrp requested wait_type timeout before X ->
  flag_pend_return_safe ready error current X.
Proof.
  intros environment critical sg original mask before i pgrp requested wait_type timeout node
    reentered saved reacquired ready error cleaned returned current X
    Hresumed Hresume Hfinal Hsafe.
  destruct Hresumed as [scheduled [entry [Hscheduled [Hsave Hresumed_ready]]]].
  destruct Hscheduled as [restored [released [Hwaiting [Hsched Hscheduled_ready]]]].
  destruct Hwaiting as [entered [first_saved [acquired [blocked [Hprefix [Hblock Hrestore]]]]]].
  destruct Hprefix as [Hptr [Hnest [Hlock [[image [Himage Htype]] [Hfirst [Hsaved [Hsame Hcounters]]]]]]].
  eapply flag_pend_safe_waiting_return; eassumption.
Qed.

Lemma flag_pend_block_preserves_idle_ready :
  forall sg state waiter flags old timeout,
  state.(TskState).(inUsedTaskStates) waiter.(flagTask) = Some old ->
  old.(curPrio) <> sg.(osLowestPrio) ->
  task_idle_ready sg state.(TskState) ->
  task_idle_ready sg (flag_execution.flag_block_state state waiter flags old timeout).(TskState).
Proof.
  intros sg state waiter flags old timeout Hold Hnonidle Hidle.
  eapply task_update_non_idle_preserves_idle_ready; eassumption.
Qed.


(** A single concrete heap trace supplies both the returned state and its
    resources. The actor is threaded through that very trace, including
    actual origin changes. Extra cuts retain their source-owned phase. *)
Lemma flag_pend_fields_trace_execution_resources :
 forall external port Extra resources extra_step extra_effect extra_source clients sg observer event_observer,
 @kernel_client_fields_resource_guarantee Extra resources extra_step extra_effect ->
 clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
 (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
 (forall publication, clients (task_create_stack_publication_client publication)) ->
 kernel_client_heap_extension_execution_source external port clients sg observer event_observer extra_source extra_effect ->
 forall cut before next after (frame : Assertion),
 kernel_client_heap_trace extra_step sg cut before next after ->
 forall state origin,
 kernel_client_heap_observer_cut observer cut ->
 kernel_client_heap_source_cut extra_source cut origin state ->
 (resources sg cut state ** frame) before ->
 exists returned stopped returned_origin,
 kernel_client_heap_state_trace extra_effect sg cut state next returned /\
 kernel_resumption_task_source_trace external port clients sg observer event_observer origin state stopped returned_origin returned /\
 kernel_client_heap_observer_cut observer next /\
 kernel_client_heap_source_cut extra_source next returned_origin returned /\
 (resources sg next returned ** frame) after.
Proof.
 intros external port Extra resources extra_step extra_effect extra_source clients sg observer event_observer
   Hmodules Henter Hexit Hpublication Hextra cut before next after frame Htrace.
 induction Htrace; intros state origin Hobserver Hcurrent Hpre.
 - exists state, false, origin; split; [constructor|]. split; [constructor|].
   split; [exact Hobserver|]. split; assumption.
 - destruct (Hmodules sg cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
   destruct (kernel_client_heap_state_step_execution_source external port Extra clients sg observer event_observer
     extra_source extra_effect Henter Hexit Hpublication Hextra cut state middle_cut middle_state origin
     Hobserver Hcurrent Hstep) as [Hmiddle_observer [stop1 [middle_origin [Hsource Hmiddle_source]]]].
   destruct (IHHtrace middle_state middle_origin Hmiddle_observer Hmiddle_source Hmiddle)
     as [returned [stop2 [returned_origin [Htail [Htail_source [Hfinal_observer [Hfinal_source Hpost]]]]]]].
   exists returned, (orb stop1 stop2), returned_origin.
   split; [econstructor; eassumption|].
   split; [eapply kernel_resumption_task_source_trace_trans; eassumption|].
   split; [exact Hfinal_observer|]. split; assumption.
Qed.

Lemma flag_pend_nonswitch_ready_resources : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  local sg active call saved acquired state before (current_local frame : Assertion),
  UCOS2_state_inv sg state ->
  kernel_call_task_source call state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  os_sched_selection_enabled state = true ->
  os_sched_requests_switch state = false ->
  state.(SchedState).(readyList) <> [] ->
  (flag_source_restore_input abi kernel_program_fields_inv local critical sg active call saved acquired state
    current_local ** frame) before ->
  exists prefix_heap,
    os_sched_modular_prefix_execution sg state before prefix_heap /\
    forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      os_sched_c_return external critical sg state call call (os_sched_prefix_state state) /\
      flag_pend_current_ready call (os_sched_prefix_state state) /\
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (flag_source_save_input abi kernel_program_fields_inv local sg active call (armv7a_irq_fiq_mask saved)
        (os_sched_prefix_state state) current_local ** frame) after.
Proof.
  intros external platform port critical arch abi restore local sg active call saved acquired state before
    current_local frame Hvalid Hsource Hconsistent Henabled Hnoswitch Hnonempty Hpre.
  pose proof (flag_pend_nonswitch_current_ready sg call state Hvalid Hsource Hconsistent
    Henabled Hnoswitch Hnonempty) as Hready.
  destruct (flag_fields_source_sched_nonswitch_return_resources external platform port critical arch
    abi restore local sg active call saved acquired state before current_local frame
    Hnoswitch ltac:(auto) Hpre) as [prefix_heap [Hprefix Hreturn]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmask Hwrite Hsuffix.
  destruct (Hreturn cursor written middle final_cursor after Hr0 Hmask Hwrite Hsuffix)
    as [Hbody [Hrun [Hlr Howned]]].
  exact (conj Hbody (conj Hready (conj Hrun (conj Hlr Howned)))).
Qed.

Lemma flag_pend_selected_ready_receipt_resources :
  forall external platform port critical arch
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    sg context outgoing hooked source_tasks original saved acquired receipt other resumed before
    (frame : Assertion),
  let local := kernel_sched_saved_local_resource_at platform critical sg source_tasks original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some original /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack) /\
      kernel_call_task_source returned current /\
      flag_pend_current_ready returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
        after.(ConAssertion.s_mem) = restored.(ConAssertion.s_mem) /\
        (kernel_continuation_call_closed abi kernel_program_fields_inv other sg
           (Some (task_stack_key original.(os_sched_call_stack))) returned
           (armv7a_irq_fiq_mask saved) current ** receipt ** frame) after)).
Proof.
  intros external platform port critical arch abi task_abi restore sg context outgoing hooked source_tasks original
    saved acquired receipt other resumed before frame local resource current
    Hvalid Hhigh Hactive Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (os_sched_fields_modular_saved_call_receipt_return external platform port critical arch
    abi task_abi restore sg context outgoing hooked source_tasks original saved acquired receipt other
    resumed before frame Hactive Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease Hreturn]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Hrestore returned.
  destruct (Hreturn restored Hrestore) as [Hcall [Hi [Ho [Hs [Hsource Htail]]]]].
  fold returned in Hs, Hsource, Htail.
  assert (Hready : flag_pend_current_ready returned current).
  { unfold current; eapply flag_pend_last_install_current_ready; eassumption. }
  exact (conj Hcall (conj Hs (conj Hsource (conj Hready Htail)))).
Qed.

Definition flag_pend_block_callee_frame environment local critical sg call saved acquired pend_ptr perr (frame : Assertion) :=
  flag_pend_masked_control environment local critical sg call saved acquired acquired **
  pend_ptr # UChar |->_ ** perr # UChar |->_ ** frame.

Definition flag_pend_unlink_callee_frame environment local critical sg call saved acquired tid current_ptr perr
  (frame : Assertion) :=
  coq_prop (current_ptr = sg.(g_OSTCBCur)) &&
  (flag_pend_unlink_frame sg acquired tid **
   current_ptr # Ptr |-> task_slot_addr sg tid **
   flag_pend_masked_control environment local critical sg call saved acquired acquired **
   perr # UChar |->_ ** frame).

(** These observations contain all registration fields needed by Pend.
    Their source is the actual publication; an SP write may change the TCB
    while preserving these four fields. *)
Definition flag_pend_registration_clean_at (tasks : Glob_TaskAbstractState)
  (slot : TaskID) (generation : nat) : Prop :=
  exists node, tasks.(inUsedTaskStates) slot = Some node /\
    node.(taskGeneration) = generation /\ flag_pend_registration_clean node.

Lemma flag_pend_publication_registration_clean : forall sg publication before after,
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  flag_pend_registration_clean_at after.(TskState) publication.(stack_publication_slot)
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration).
Proof.
  intros sg publication before after [Hinput ->].
  exists (task_set_links
    (task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image)) before.(TskState).(tcbListHead) None).
  split.
  - cbn [task_create_stack_publication_state task_create_stack_published_state
      task_tcb_init_published_state task_tcb_init_commit_state task_sched_commit_state
      replace_SchedS replace_TskS TskState glob_task_set_parked_stacks inUsedTaskStates
      task_commit].
    replace (taskID (task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image))) with publication.(stack_publication_slot) by reflexivity.
    destruct (Z.eq_dec publication.(stack_publication_slot)
      publication.(stack_publication_slot)); [reflexivity|contradiction].
  - split; [reflexivity|]. repeat split; reflexivity.
Qed.

Lemma flag_pend_save_sp_preserves_registration_clean : forall state slot generation outgoing sp,
  flag_pend_registration_clean_at state.(TskState) slot generation ->
  flag_pend_registration_clean_at (os_sched_save_current_sp state outgoing sp).(TskState) slot generation.
Proof.
  intros state slot generation outgoing sp [node [Hnode [Hgen Hclean]]].
  unfold os_sched_save_current_sp.
  destruct (state.(TskState).(inUsedTaskStates) outgoing) as [old|] eqn:Hold.
  - destruct (Z.eqb slot outgoing) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst slot.
      rewrite Hnode in Hold; inversion Hold; subst old.
      exists (task_set_saved_sp node sp).
      split; [cbn; rewrite Z.eqb_refl; reflexivity|]. split; assumption.
    + exists node; split; [cbn; rewrite Heq; exact Hnode|]. split; assumption.
  - exists node; split; [exact Hnode|]. split; assumption.
Qed.

Lemma flag_pend_prefix_preserves_registration_clean : forall state slot generation,
  flag_pend_registration_clean_at state.(TskState) slot generation ->
  flag_pend_registration_clean_at (os_sched_prefix_state state).(TskState) slot generation.
Proof. intros; exact H. Qed.

Lemma flag_pend_install_preserves_registration_clean : forall state slot generation call fragments incoming,
  flag_pend_registration_clean_at state.(TskState) slot generation ->
  flag_pend_registration_clean_at (os_sched_install_context call fragments incoming state).(TskState)
    slot generation.
Proof. intros; exact H. Qed.

(** The source publication supplies the zero FlagNode; the precise scheduler
    prefix/SP/install transformations preserve that field, including aliases.
    No intervening arbitrary client or full-lifetime cleanliness is assumed. *)
Lemma flag_pend_published_sched_entry_registration_clean : forall sg publication before published
  call sp fragments incoming,
  kernel_client_step (task_create_stack_publication_client publication) sg before published ->
  let hooked := os_sched_save_current_sp (os_sched_prefix_state published)
    call.(os_sched_call_stack).(stackLeaseSlot) sp in
  flag_pend_registration_clean_at (os_sched_install_context call fragments incoming hooked).(TskState)
    publication.(stack_publication_slot)
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration).
Proof.
  intros sg publication before published call sp fragments incoming Hpublication hooked.
  apply flag_pend_install_preserves_registration_clean; apply flag_pend_save_sp_preserves_registration_clean.
  apply flag_pend_prefix_preserves_registration_clean; eapply flag_pend_publication_registration_clean; exact Hpublication.
Qed.


Lemma flag_pend_task_entry_of_source_ready_clean : forall call state,
 state.(SchedState).(isRunning) = true -> kernel_call_task_source call state ->
 state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
 flag_pend_current_ready call state ->
 flag_pend_registration_clean_at state.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
   call.(os_sched_call_stack).(stackLeaseGeneration) ->
 flag_pend_task_entry call state.
Proof.
 intros call state Hrunning [Horigin [Hactive Hcurrent]] Hnone
   [node [Hready Hgen]] [clean [Hlookup [Hcleangen Hclean]]].
 assert (clean = node) by (pose proof (proj1 Hready); congruence); subst clean.
 split; [|exact Hactive]. unfold flag_pend_task_stage.
 split; [exact Horigin|]. split; [exact Hrunning|]. split; [exact Hnone|].
 exists node; exact (conj Hready (conj Hgen Hclean)).
Qed.

Lemma flag_pend_publication_preserves_idle_ready : forall sg publication before after,
 UCOS2_state_inv sg before ->
 kernel_client_step (task_create_stack_publication_client publication) sg before after ->
 ((task_create_stack_publication_args publication).(initPrio) = sg.(osLowestPrio) \/
  task_idle_ready sg before.(TskState)) ->
 task_idle_ready sg after.(TskState).
Proof.
 intros sg publication before after Hvalid [Hinput ->] Hidle.
 destruct Hinput as [_ [_ [Hcommit Hrest]]].
 change (task_idle_ready sg (task_tcb_init_published_state sg
   (task_create_stack_publication_args publication) publication.(stack_publication_invocation)
   publication.(stack_publication_acquired) before publication.(stack_publication_slot)
   publication.(stack_publication_image)).(TskState)).
 destruct Hidle as [Hpriority|Hidle].
 - apply task_tcb_init_published_idle_ready; exact Hpriority.
 - eapply task_tcb_init_publication_preserves_idle_ready; eassumption.
Qed.

Lemma flag_pend_wrapper_take_current_ready_iff : forall call state lease,
 flag_pend_current_ready call (os_int_exit_wrapper_restored_state state lease) <->
 flag_pend_current_ready call state.
Proof. intros; reflexivity. Qed.

Lemma flag_pend_save_current_sp_preserves_current_ready : forall call state sp,
 flag_pend_current_ready call state ->
 flag_pend_current_ready call
   (os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot) sp).
Proof.
 intros call state sp [node [Hready Hgen]].
 destruct Hready as [Hnode Hrest].
 unfold os_sched_save_current_sp; rewrite Hnode.
 exists (task_set_saved_sp node sp); split.
 - unfold sched_current_ready_at; cbn [replace_TskS TskState SchedState glob_task_set_usedtask inUsedTaskStates].
   rewrite Z.eqb_refl; split; [reflexivity|exact Hrest].
 - exact Hgen.
Qed.

Lemma flag_pend_saved_map_add_local_resource_absent : forall external platform port
 (abi : Armv7aContinuationABI external platform port) critical sg source_tasks tasks call
 saved acquired receipt other stacks,
 stacks (task_stack_key call.(os_sched_call_stack)) = None ->
 store_parked_continuations (kernel_saved_continuation_entry abi tasks other) stacks |--
 store_parked_continuations
   (kernel_saved_continuation_entry abi tasks
     (kernel_sched_saved_local_resource_at platform critical sg source_tasks call saved acquired receipt other)) stacks.
Proof.
 intros external platform port abi critical sg source_tasks tasks call saved acquired receipt other stacks Hnone.
 unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
 intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
 assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = key) by tauto.
 assert (Hdifferent : task_stack_key descriptor.(armv7a_continuation_stack) <>
   task_stack_key call.(os_sched_call_stack)).
 { intro Heq; rewrite Hkey in Heq; rewrite Heq, Hnone in Hlookup; discriminate. }
 Exists descriptor; unfold kernel_sched_saved_local_resource_at.
 destruct task_stack_key_eq_dec; [contradiction|entailer!].
Qed.

(** The actual first Scheduler capture deposits the active receipt into
    its saved local entry. It is not left in the caller frame during the
    intervening heap trace. The other entries keep their own local family. *)
Local Open Scope list_scope.

Lemma flag_pend_sched_active_capture :
  forall external platform port critical
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    sg state node call saved acquired receipt other old_sp cpsr registers lr prefix suffix first old_words
    before (frame : Assertion),
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  let local := kernel_sched_saved_local_resource_at platform critical sg checkpoint.(TskState)
    call saved acquired receipt other in
  os_sched_requests_switch state = true ->
  state.(SchedState).(readyList) <> [] ->
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_continuation_call_masked abi kernel_program_fields_inv other critical sg
    (Some (task_stack_key call.(os_sched_call_stack))) call saved acquired state ** (receipt ** frame)) before ->
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg before prefix_heap /\
    sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState) /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call descriptor stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
      (UCOS2_fields_inv sg updated **
       task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       kernel_saved_continuation_entry abi updated.(TskState) local
         (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
         updated.(TskState).(parkedTaskStacks) **
       armv7a_task_switch_control task_abi call ** (unmap_table_rep sg ** frame)) captured).
Proof.
  intros external platform port critical abi task_abi sg state node call saved acquired receipt other old_sp cpsr
    registers lr prefix suffix first old_words before frame checkpoint fragments descriptor updated local
    Hswitch Hnonempty Hsource Hnode Hid Hgeneration Habsent Hfragments Hlength Hcpsr Hlr Hranges Hmask
    Hsprange Hsp Haddress Hpre.
  destruct (os_sched_fields_modular_prefix_continuation_resources external platform port abi other critical sg
    (Some (task_stack_key call.(os_sched_call_stack))) call saved acquired state before (receipt ** frame)
    (fun _ => Hnonempty) Hpre) as [prefix_heap [Hprefix [Hhigh Hmasked]]].
  unfold os_sched_modular_prefix_execution in Hprefix; rewrite Hswitch in Hprefix.
  specialize (Hhigh Hswitch); fold checkpoint in Hhigh, Hmasked.
  assert (Hsource_checkpoint : kernel_call_task_source call checkpoint).
  { apply os_sched_prefix_preserves_task_source; exact Hsource. }
  pose proof (proj1 (kernel_call_task_source_current_at call checkpoint Hsource_checkpoint)) as Hcurrent.
  assert (Hcoverage : task_stack_live_coverage checkpoint.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hmasked with ?P prefix_heap => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage checkpoint.(TskState)
        (Some (task_stack_key call.(os_sched_call_stack)))) && TT) end.
    { unfold kernel_continuation_call_masked, kernel_continuation_inv;
        entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve prefix_heap Hmasked)). }
  assert (Hlocal : interrupt_platform_saved platform
      (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) acquired ** receipt |-- local descriptor).
  { unfold local; rewrite kernel_sched_saved_local_resource_at_selected by reflexivity.
    sep_apply_l_atomic (kernel_sched_saved_image_local_resources platform critical sg checkpoint call saved acquired
      old_sp cpsr registers lr fragments Hsource_checkpoint Hmask); entailer!. }
  assert (Hmap : store_parked_continuations
      (kernel_saved_continuation_entry abi checkpoint.(TskState) other)
      checkpoint.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState) local)
      checkpoint.(TskState).(parkedTaskStacks)).
  { unfold local; apply flag_pend_saved_map_add_local_resource_absent; exact Habsent. }
  match type of Hmasked with ?P prefix_heap => assert (Hsave_input : P |--
    kernel_call_execution_owned external platform call 192 ** UCOS2_fields_inv sg checkpoint **
    store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState) local)
      checkpoint.(TskState).(parkedTaskStacks) ** local descriptor ** (unmap_table_rep sg ** frame)) end.
  { unfold kernel_continuation_call_masked, kernel_continuation_inv, critical_region_masked,
      kernel_call_execution_owned; rewrite kernel_program_fields_inv_split_unmap.
    Intros.
    sep_apply_l_atomic Hmap; sep_apply_l_atomic Hlocal; entailer!. }
  destruct (kernel_task_save_continuation_fields_resources external platform port abi task_abi sg checkpoint node call
    old_sp cpsr registers lr prefix suffix first old_words local (unmap_table_rep sg ** frame) prefix_heap
    Hcurrent Hnode Hid Hgeneration Habsent Hcoverage Hfragments Hlength Hcpsr Hlr Hranges Hmask
    Hsprange Hsp Haddress (Hsave_input prefix_heap Hmasked))
    as [written [stored [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]].
  exists prefix_heap, written, stored.
  exact (conj Hprefix (conj Hhigh (conj Hwrites (conj Hload (conj Hstore (conj Hcovered Hcapture)))))).
Qed.


Lemma flag_pend_irq_install_selected_ready : forall external sg transfer,
 UCOS2_state_inv sg transfer.(os_int_exit_hooked_state) ->
 sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
   transfer.(os_int_exit_hooked_state).(SchedState) ->
 os_int_exit_destination_binding external transfer ->
 exists node,
   sched_current_ready_at (os_int_exit_installed_state transfer).(TskState)
     (os_int_exit_installed_state transfer).(SchedState)
     transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) node /\
   node.(taskGeneration) = transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration).
Proof.
 intros external sg transfer Hvalid Hhigh Hdestination.
 destruct Hdestination as [Hselected [[node [Hnode [Hgeneration [Hpriority Hsp]]]] Hrest]].
 pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hready.
 unfold sched_high_ready_consistency in Hhigh.
 destruct transfer.(os_int_exit_hooked_state).(SchedState).(readyList) as [|slot tail] eqn:Hlist.
 - destruct Hhigh as [Hnone Hnone_priority]; congruence.
 - destruct Hhigh as [Hhead Hhead_node].
   assert (Hslot : slot = transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) by congruence.
   destruct (Hready transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) (or_introl Hslot))
     as [ready_node [Hready_node [Hrange Heffective]]].
   assert (ready_node = node) by congruence; subst ready_node.
   assert (Hin : In transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
     transfer.(os_int_exit_hooked_state).(SchedState).(readyList)).
   { rewrite Hlist; left; exact Hslot. }
   exists node; split; [|exact Hgeneration].
   unfold sched_current_ready_at.
   change (transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates)
       transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) = Some node /\
     transfer.(os_int_exit_hooked_state).(SchedState).(highRdyTid) =
       Some transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) /\
     transfer.(os_int_exit_hooked_state).(SchedState).(highRdyPrio) = Some node.(curPrio) /\
     In transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
       transfer.(os_int_exit_hooked_state).(SchedState).(readyList) /\
     is_effectively_ready node.(stat) node.(dly) = true).
   exact (conj Hnode (conj Hselected (conj Hpriority (conj Hin Heffective)))).
Qed.

(** Concrete and abstract steps share each intermediate heap, state and
    resource cut. This certificate is built by the actual module theorem
    on each edge; two flat existential histories are not joined afterwards. *)
Inductive flag_pend_heap_state_resources_trace {Extra}
 (resources : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State -> Assertion)
 (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model -> KernelClientHeapCut Extra -> model -> Prop)
 (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
   KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
 sg (frame : Assertion) :
 KernelClientHeapCut Extra -> UCOS2_Verify_State -> model ->
 KernelClientHeapCut Extra -> UCOS2_Verify_State -> model -> Prop :=
| FlagPendHeapTraceRefl : forall cut state heap,
 (resources sg cut state ** frame) heap ->
 flag_pend_heap_state_resources_trace resources extra_step extra_effect sg frame cut state heap cut state heap
| FlagPendHeapTraceStep : forall cut state before middle_cut middle_state middle next returned after,
 kernel_client_heap_step extra_step sg cut before middle_cut middle ->
 kernel_client_heap_state_step extra_effect sg cut state middle_cut middle_state ->
 (resources sg middle_cut middle_state ** frame) middle ->
 flag_pend_heap_state_resources_trace resources extra_step extra_effect sg frame
   middle_cut middle_state middle next returned after ->
 flag_pend_heap_state_resources_trace resources extra_step extra_effect sg frame
   cut state before next returned after.

Lemma flag_pend_realize_fields_heap_trace : forall Extra resources extra_step extra_effect,
 @kernel_client_fields_resource_guarantee Extra resources extra_step extra_effect ->
 forall sg cut before next after (frame : Assertion),
 kernel_client_heap_trace extra_step sg cut before next after ->
 forall state, (resources sg cut state ** frame) before ->
 exists returned, flag_pend_heap_state_resources_trace resources extra_step extra_effect sg frame
   cut state before next returned after.
Proof.
 intros Extra resources extra_step extra_effect Hmodules sg cut before next after frame Htrace.
 induction Htrace; intros state Hpre.
 - exists state; constructor; exact Hpre.
 - destruct (Hmodules sg cut before middle_cut middle state frame H Hpre)
     as [middle_state [Hstep Hmiddle]].
   destruct (IHHtrace middle_state Hmiddle) as [returned Htail].
   exists returned; econstructor; eassumption.
Qed.

Lemma flag_pend_heap_state_resources_trace_output : forall Extra resources extra_step extra_effect
 sg frame cut state before next returned after,
 @flag_pend_heap_state_resources_trace Extra resources extra_step extra_effect sg frame
   cut state before next returned after ->
 (resources sg next returned ** frame) after.
Proof. intros; induction H; assumption. Qed.

(** A completed source prefix consumes this invocation's captured input and
    reaches the last producer on the SAME concrete heap trace. The module
    premises describe the actual registered Extra steps, including save,
    active deposit and selected installation. They are conditional linked
    module obligations, not a claim of coverage for arbitrary clients. *)
Definition flag_pend_completed_heap_prefix environment critical sg original before
  (input : Assertion) first_heap last_state last_heap (last_input : Assertion) : Prop :=
  exists (Extra : Type)
    (resources : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State -> Assertion)
    (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
      KernelClientHeapCut Extra -> model -> Prop)
    (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
      KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
    (extra_source : Extra -> TaskInvocationOrigin -> UCOS2_Verify_State -> Prop)
    first_cut last_cut (frame : Assertion),
    kernel_client_fields_resource_guarantee resources extra_step extra_effect /\
    critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) /\
    (forall running, critical.(critical_region_clients)
      (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) /\
    (forall publication, critical.(critical_region_clients)
      (task_create_stack_publication_client publication)) /\
    kernel_client_heap_extension_execution_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None extra_source extra_effect /\
    (input |-- resources sg first_cut before ** frame) /\
    input first_heap /\
    kernel_client_heap_observer_cut original.(os_sched_call_invocation) first_cut /\
    kernel_client_heap_source_cut extra_source first_cut original.(os_sched_call_origin) before /\
    flag_pend_heap_state_resources_trace resources extra_step extra_effect sg frame
      first_cut before first_heap last_cut last_state last_heap /\
    (resources sg last_cut last_state ** frame |-- last_input).

Lemma flag_pend_completed_heap_prefix_resources : forall environment critical sg original before
 input first_heap last_state last_heap last_input,
 flag_pend_completed_heap_prefix environment critical sg original before input first_heap
   last_state last_heap last_input ->
 last_input last_heap.
Proof.
 intros environment critical sg original before input first_heap last_state last_heap last_input
   [Extra [resources [extra_step [extra_effect [extra_source [first_cut [last_cut [frame H]]]]]]]].
 destruct H as [Hmodules [Henter [Hexit [Hpublication [Hsource [Hinput [Hpre
   [Hobserver [Horigin [Htrace Hlast]]]]]]]]]].
 apply Hlast; eapply flag_pend_heap_state_resources_trace_output; exact Htrace.
Qed.

Definition flag_pend_selected_return_input external platform port critical
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg context outgoing hooked source_tasks original saved acquired receipt other (frame : Assertion) : Assertion :=
  let local := kernel_sched_saved_local_resource_at platform critical sg source_tasks original saved acquired receipt other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
  resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
  store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
  (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame).

(** Readiness comes from the actual no-switch guards or final destination.
    The endpoint indices are the exact returned call, state and heap.
    Awaiting Restore is deliberately outside this Ready relation. *)

Definition flag_pend_ready_return_owned environment local sg call mask state (receipt : Assertion) : Assertion :=
 kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_fields_inv
   local sg (task_stack_call_active_key call) call mask state ** receipt.

Inductive flag_pend_ready_completed_source environment critical sg original before
  (input : Assertion) first_heap :
  (Armv7aContinuation -> Assertion) -> Assertion -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> model -> Prop :=
| FlagPendReadyNonswitch :
  forall arch (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
    local call saved acquired entry receipt last_heap prefix_heap
    cursor written middle final_cursor after,
  flag_pend_completed_heap_prefix environment critical sg original before input first_heap entry last_heap
    (flag_source_restore_input environment.(task_stack_call_continuations) kernel_program_fields_inv
      local critical sg (task_stack_call_active_key call) call saved acquired entry receipt ** emp) ->
  UCOS2_state_inv sg entry ->
  kernel_call_task_source call entry ->
  sched_current_consistency entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  os_sched_requests_switch entry = false ->
  entry.(SchedState).(readyList) <> [] ->
  os_sched_modular_prefix_execution sg entry last_heap prefix_heap ->
  (forall c w mid fc h,
    c.(kernel_restore_r0) = saved ->
    armv7a_irq_fiq_mask c.(kernel_restore_current_cpsr) = 192 ->
    armv7a_restore_prefix_transition restore c prefix_heap w mid ->
    armv7a_restore_suffix_transition restore w mid fc h ->
    (flag_pend_ready_return_owned environment local sg call (armv7a_irq_fiq_mask saved)
      (os_sched_prefix_state entry) receipt ** emp) h) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  flag_pend_ready_completed_source environment critical sg original before input first_heap
    local receipt call (armv7a_irq_fiq_mask saved) (os_sched_prefix_state entry) after
| FlagPendReadySelected :
  forall arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    context outgoing hooked source_tasks resumed_call saved acquired receipt other resumed last_heap
    installed selected restored cursor written middle final_cursor after,
  flag_pend_completed_heap_prefix environment critical sg original before input first_heap hooked last_heap
    (flag_pend_selected_return_input environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port) critical
      environment.(task_stack_call_continuations) task_abi sg context outgoing hooked source_tasks
      resumed_call saved acquired receipt other emp) ->
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  task_invocation_active hooked.(TskState) resumed_call.(os_sched_call_invocation)
    resumed_call.(os_sched_call_origin) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
    resumed_call.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg resumed_call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg resumed_call.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  sched_install_heap_fragment sg last_heap installed
    (task_slot_addr sg resumed_call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) ->
  armv7a_continuation_restore_reads selected installed ->
  selected.(armv7a_continuation_call) = Some resumed_call ->
  selected.(armv7a_continuation_stack) = resumed_call.(os_sched_call_stack) ->
  (forall restored_heap,
    armv7a_task_restore_transition task_abi context selected installed restored_heap ->
    forall c w mid fc h,
    c.(kernel_restore_r0) = saved ->
    armv7a_irq_fiq_mask c.(kernel_restore_current_cpsr) = 192 ->
    armv7a_restore_prefix_transition restore c restored_heap w mid ->
    armv7a_restore_suffix_transition restore w mid fc h ->
    (flag_pend_ready_return_owned environment other sg
      (kernel_selected_call selected (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked))
      (armv7a_irq_fiq_mask saved)
      (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked) receipt ** emp) h) ->
  armv7a_task_restore_transition task_abi context selected installed restored ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor restored written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  flag_pend_ready_completed_source environment critical sg original before input first_heap
    other receipt
    (kernel_selected_call selected (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked))
    (armv7a_irq_fiq_mask saved)
    (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked) after.

Lemma flag_pend_ready_completed_source_current_ready :
  forall environment critical sg original before input first_heap local receipt returned mask current after,
  flag_pend_ready_completed_source environment critical sg original before input first_heap
    local receipt returned mask current after ->
  flag_pend_current_ready returned current.
Proof.
  intros environment critical sg original before input first_heap local receipt returned mask current after Hsource.
  destruct Hsource.
  - eapply flag_pend_nonswitch_current_ready; eassumption.
  - eapply flag_pend_last_install_current_ready; try eassumption.
    rewrite kernel_selected_call_stack; assumption.
Qed.

Lemma flag_pend_ready_completed_source_resources :
 forall environment critical sg original before input first_heap local receipt returned mask current after,
 flag_pend_ready_completed_source environment critical sg original before input first_heap
   local receipt returned mask current after ->
 flag_pend_ready_return_owned environment local sg returned mask current receipt after.
Proof.
 intros environment critical sg original before input first_heap local receipt returned mask current after Hsource.
 destruct Hsource.
 - assert ((flag_pend_ready_return_owned environment local sg call (armv7a_irq_fiq_mask saved)
     (os_sched_prefix_state entry) receipt ** emp) after) by eauto.
   match goal with Howned : (?P ** emp) ?h |- ?P ?h =>
     assert (Hdrop : P ** emp |-- P) by entailer!; exact (Hdrop h Howned) end.
 - assert ((flag_pend_ready_return_owned environment other sg
     (kernel_selected_call selected (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked))
     (armv7a_irq_fiq_mask saved)
     (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked) receipt ** emp) after) by eauto.
   match goal with Howned : (?P ** emp) ?h |- ?P ?h =>
     assert (Hdrop : P ** emp |-- P) by entailer!; exact (Hdrop h Howned) end.
Qed.

Lemma flag_pend_nonswitch_completed_source_producer :
 forall environment critical sg original before input first_heap arch
 (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
   environment.(task_stack_call_platform) critical arch)
 local call saved acquired entry receipt last_heap,
 flag_pend_completed_heap_prefix environment critical sg original before input first_heap entry last_heap
   (flag_source_restore_input environment.(task_stack_call_continuations) kernel_program_fields_inv
     local critical sg (task_stack_call_active_key call) call saved acquired entry receipt ** emp) ->
 UCOS2_state_inv sg entry ->
 kernel_call_task_source call entry ->
 sched_current_consistency entry.(TskState) entry.(SchedState) ->
 os_sched_selection_enabled entry = true ->
 os_sched_requests_switch entry = false ->
 entry.(SchedState).(readyList) <> [] ->
 exists prefix_heap,
 os_sched_modular_prefix_execution sg entry last_heap prefix_heap /\
 forall cursor written middle final_cursor after,
 cursor.(kernel_restore_r0) = saved ->
 armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
 armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
 armv7a_restore_suffix_transition restore written middle final_cursor after ->
 flag_pend_ready_completed_source environment critical sg original before input first_heap
   local receipt call (armv7a_irq_fiq_mask saved) (os_sched_prefix_state entry) after.
Proof.
 intros environment critical sg original before input first_heap arch restore local call saved acquired entry
   receipt last_heap Hprefix Hvalid Hsource Hconsistent Henabled Hswitch Hnonempty.
 pose proof (flag_pend_completed_heap_prefix_resources _ _ _ _ _ _ _ _ _ _ Hprefix) as Hpre.
 destruct (flag_fields_source_sched_nonswitch_return_resources
   environment.(task_stack_call_external) environment.(task_stack_call_platform) environment.(task_stack_call_port)
   critical arch environment.(task_stack_call_continuations) restore local sg (task_stack_call_active_key call)
   call saved acquired entry last_heap receipt emp Hswitch ltac:(auto) Hpre)
   as [prefix_heap [Hrun Hreturn]].
 exists prefix_heap; split; [exact Hrun|].
 intros cursor written middle final_cursor after Hr0 Hmask Hwrite Hsuffix.
 eapply FlagPendReadyNonswitch; try eassumption.
 intros c w mid fc h H0 H192 Hw Hs.
 destruct (Hreturn c w mid fc h H0 H192 Hw Hs) as [Hbody [Hexec [Hlr Howned]]].
 exact Howned.
Qed.

Lemma flag_pend_selected_completed_source_producer :
 forall environment critical sg original before input first_heap arch
 (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
   environment.(task_stack_call_platform) environment.(task_stack_call_port)
   environment.(task_stack_call_continuations))
 (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
   environment.(task_stack_call_platform) critical arch)
 context outgoing hooked source_tasks resumed_call saved acquired receipt other resumed last_heap,
 flag_pend_completed_heap_prefix environment critical sg original before input first_heap hooked last_heap
   (flag_pend_selected_return_input environment.(task_stack_call_external)
     environment.(task_stack_call_platform) environment.(task_stack_call_port) critical
     environment.(task_stack_call_continuations) task_abi sg context outgoing hooked source_tasks
     resumed_call saved acquired receipt other emp) ->
 UCOS2_state_inv sg hooked ->
 sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
 task_invocation_active hooked.(TskState) resumed_call.(os_sched_call_invocation)
   resumed_call.(os_sched_call_origin) ->
 os_sched_saved_stack_binding context outgoing hooked ->
 os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
   resumed_call.(os_sched_call_stack) resumed ->
 tcb_field_address (task_slot_addr sg resumed_call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
   task_slot_addr sg resumed_call.(os_sched_call_stack).(stackLeaseSlot) ->
 task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
 exists installed selected,
 sched_install_heap_fragment sg last_heap installed
   (task_slot_addr sg resumed_call.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
 forall restored,
 armv7a_task_restore_transition task_abi context selected installed restored ->
 forall cursor written middle final_cursor after,
 cursor.(kernel_restore_r0) = saved ->
 armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
 armv7a_restore_prefix_transition restore cursor restored written middle ->
 armv7a_restore_suffix_transition restore written middle final_cursor after ->
 flag_pend_ready_completed_source environment critical sg original before input first_heap
   other receipt
   (kernel_selected_call selected (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked))
   (armv7a_irq_fiq_mask saved)
   (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked) after.
Proof.
 intros environment critical sg original before input first_heap arch task_abi restore context outgoing hooked
   source_tasks resumed_call saved acquired receipt other resumed last_heap Hprefix Hvalid Hhigh Hactive
   Hsaved Hdestination Haddress Hcoverage.
 pose proof (flag_pend_completed_heap_prefix_resources _ _ _ _ _ _ _ _ _ _ Hprefix) as Hpre.
 destruct (os_sched_fields_modular_saved_call_receipt_return
   environment.(task_stack_call_external) environment.(task_stack_call_platform) environment.(task_stack_call_port)
   critical arch environment.(task_stack_call_continuations) task_abi restore sg context outgoing hooked source_tasks
   resumed_call saved acquired receipt other resumed last_heap emp
   Hactive Hsaved Hdestination Haddress Hcoverage Hpre)
   as [installed [selected [Hinstall [Hreads [Hlease Hreturn]]]]].
 exists installed, selected; split; [exact Hinstall|].
 intros restored Hrestore cursor written middle final_cursor after Hr0 Hmask Hwrite Hsuffix.
 destruct (Hreturn restored Hrestore) as [Hcall [Hi [Ho [Hs [Hsource Htail]]]]].
 eapply FlagPendReadySelected; try eassumption.
 intros restored_heap Hrestore_heap c w mid fc h H0 H192 Hw Hsuf.
 destruct (Hreturn restored_heap Hrestore_heap)
   as [Hcall' [Hi' [Ho' [Hs' [Hsource' Htail']]]]].
 destruct (Htail' c w mid fc h H0 H192 Hw Hsuf) as [Hexec [Hlr [Hmemory Howned]]].
 unfold flag_pend_ready_return_owned.
 assert (Hkey : task_stack_call_active_key
    (kernel_selected_call selected (os_sched_install_context context outgoing resumed_call.(os_sched_call_stack) hooked)) =
    Some (task_stack_key resumed_call.(os_sched_call_stack))).
 { unfold task_stack_call_active_key; rewrite (proj1 Hsource').
   unfold task_stack_key; rewrite Hs'; reflexivity. }
 rewrite Hkey; exact Howned.
Qed.

Lemma flag_pend_task_entry_api_observation : forall call state,
  flag_pend_task_entry call state -> flag_api_task_entry_observation call state.
Proof.
  intros call state [[Horigin [Hrunning [Hnone [node [Hready [Hgen Hclean]]]]]] Hactive].
  destruct Hready as [Hlookup [Hcurrent [Hprio [Hin Heffective]]]].
  split.
  - unfold kernel_call_task_source; split; [exact Horigin|].
    split; [exact Hactive|]. unfold task_execution_current; rewrite Horigin; exact Hcurrent.
  - split.
    + exists node; split; [exact Hlookup|]. split; [exact Hgen|exact (proj1 Hclean)].
    + split; [exact Hnone|]. intro Hempty; rewrite Hempty in Hin; contradiction.
Qed.

Lemma flag_pend_sequential_call_world_resources : forall environment
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform)) local sg previous state mask before after (frame : Assertion),
  flag_pend_task_entry previous state ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before after ->
  (flag_pend_call_world environment local sg previous mask state ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := flag_sequential_registered_state previous state in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (coq_prop (flag_pend_task_entry call registered) &&
    (flag_pend_call_world environment local sg call mask registered ** frame)) after.
Proof.
  intros environment boundary local sg previous state mask before after frame Hstage Hsource Hpre
    call registered.
  pose proof (flag_pend_task_entry_api_observation _ _ Hstage) as Hentry.
  assert (Hopen : flag_pend_call_world environment local sg previous mask state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key previous)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) previous mask **
     kernel_program_fields_inv sg state ** os_sched_fields_capsules environment local state ** frame)).
  { unfold flag_pend_call_world, kernel_continuation_call_closed,
      kernel_continuation_inv, os_sched_fields_capsules; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (flag_sequential_entry_resources environment boundary local sg previous state mask
    before after frame Hentry Hsource Howned) as [Hmemory Hnext].
  split; [exact Hmemory|].
  assert (Hnew : flag_pend_task_entry call registered).
  { apply flag_pend_sequential_entry; exact (proj1 Hstage). }
  match type of Hnext with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold flag_pend_call_world, kernel_continuation_call_closed,
      kernel_continuation_inv, os_sched_fields_capsules.
    change (task_stack_call_active_key call) with (task_stack_call_active_key previous).
    assert (Hcoverage_new : task_stack_live_coverage registered.(TskState)
      (task_stack_call_active_key previous)) by exact Hcoverage.
    entailer!. }
  exact (Hclose after Hnext).
Qed.

Lemma flag_pend_initial_published_call_world_resources : forall environment
  (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations)) sg publication before published
  call sp outgoing selected local node (frame : Assertion),
  kernel_client_step (task_create_stack_publication_client publication) sg before published ->
  selected.(armv7a_continuation_stack).(stackLeaseSlot) = publication.(stack_publication_slot) ->
  selected.(armv7a_continuation_stack).(stackLeaseGeneration) =
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration) ->
  selected.(armv7a_continuation_call) = None ->
  armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 selected.(armv7a_continuation_fragments) ->
  let current := os_sched_install_context call outgoing selected.(armv7a_continuation_stack)
    (os_sched_save_current_sp (os_sched_prefix_state published)
      call.(os_sched_call_stack).(stackLeaseSlot) sp) in
  current.(SchedState).(isRunning) = true ->
  task_current_at current selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  sched_current_ready_at current.(TskState) current.(SchedState)
    selected.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  task_stack_live_coverage current.(TskState) (Some (task_stack_key selected.(armv7a_continuation_stack))) ->
  let first := armv7a_initial_call selected current.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  let registered := armv7a_initial_call_registered selected current in
  armv7a_task_restored_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) selected ** local selected **
    kernel_program_fields_inv sg current ** os_sched_fields_capsules environment local current ** frame |--
  coq_prop (flag_pend_task_entry first registered) &&
    (flag_pend_call_world environment local sg first
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) registered ** (local selected ** frame)).
Proof.
  intros environment entry sg publication before published call sp outgoing selected local node frame
    Hpublication Hslot Hgen Hnone Hbinding Hfragments current Hrunning Hcurrent Hready Hgeneration
    Hcoverage first registered.
  pose proof (flag_initial_published_entry_observation sg publication before published
    call sp outgoing selected Hpublication Hslot Hgen Hcurrent) as Hentry.
  assert (Hclean : flag_pend_registration_clean_at registered.(TskState)
    first.(os_sched_call_stack).(stackLeaseSlot) first.(os_sched_call_stack).(stackLeaseGeneration)).
  { change (flag_pend_registration_clean_at current.(TskState)
      selected.(armv7a_continuation_stack).(stackLeaseSlot)
      selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
    rewrite Hslot, Hgen; eapply flag_pend_published_sched_entry_registration_clean; exact Hpublication. }
  assert (Hstage : flag_pend_task_entry first registered).
  { apply flag_pend_task_entry_of_source_ready_clean.
    - exact Hrunning.
    - exact (proj1 Hentry).
    - exact (proj1 (proj2 (proj2 Hentry))).
    - exists node; split; assumption.
    - exact Hclean. }
  pose proof (flag_initial_published_entry_resources environment entry sg publication before published
    call sp outgoing selected local frame Hpublication Hslot Hgen Hnone Hbinding Hfragments Hcurrent) as Hresources.
  cbv zeta in Hresources.
  fold current in Hresources.
  fold first registered in Hresources.
  sep_apply_l_atomic Hresources.
  unfold flag_pend_call_world, kernel_continuation_call_closed,
    kernel_continuation_inv, os_sched_fields_capsules.
  assert (Hcovered : task_stack_live_coverage registered.(TskState) (task_stack_call_active_key first)).
  { exact Hcoverage. }
  entailer!.
Qed.

Lemma flag_pend_save_sp_preserves_idle_ready : forall sg state outgoing sp,
  task_idle_ready sg state.(TskState) ->
  task_idle_ready sg (os_sched_save_current_sp state outgoing sp).(TskState).
Proof.
  intros sg state outgoing sp [idle [node [Hnode [Hprio Hready]]]].
  unfold os_sched_save_current_sp.
  destruct (state.(TskState).(inUsedTaskStates) outgoing) as [old|] eqn:Hold.
  - destruct (Z.eqb idle outgoing) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst idle.
      rewrite Hnode in Hold; inversion Hold; subst old.
      exists outgoing, (task_set_saved_sp node sp); split.
      * cbn; rewrite Z.eqb_refl; reflexivity.
      * split; assumption.
    + exists idle, node; split; [cbn; rewrite Heq; exact Hnode|]. split; assumption.
  - exists idle, node; split; [exact Hnode|]. split; assumption.
Qed.

Lemma flag_pend_published_initial_idle_ready : forall sg publication before published
  call sp outgoing selected,
  UCOS2_state_inv sg before ->
  kernel_client_step (task_create_stack_publication_client publication) sg before published ->
  task_idle_ready sg before.(TskState) ->
  let current := os_sched_install_context call outgoing selected.(armv7a_continuation_stack)
    (os_sched_save_current_sp (os_sched_prefix_state published)
      call.(os_sched_call_stack).(stackLeaseSlot) sp) in
  task_idle_ready sg (armv7a_initial_call_registered selected current).(TskState).
Proof.
  intros sg publication before published call sp outgoing selected Hvalid Hpublication Hidle current.
  change (task_idle_ready sg (os_sched_save_current_sp (os_sched_prefix_state published)
    call.(os_sched_call_stack).(stackLeaseSlot) sp).(TskState)).
  apply flag_pend_save_sp_preserves_idle_ready.
  change (task_idle_ready sg published.(TskState)).
  eapply flag_pend_publication_preserves_idle_ready; [exact Hvalid|exact Hpublication|auto].
Qed.

(** These are the observations of the last executed selector or the actual
    non-switch branch. They can be transported only through the listed state
    operations. No constructor takes current-ready as a premise. *)
Inductive flag_pend_ready_source_cut (environment : TaskStackCallEnvironment) sg :
  OsSchedCallContext -> UCOS2_Verify_State -> Prop :=
| FlagPendReadyCutNonswitch : forall call state,
    UCOS2_state_inv sg state ->
    kernel_call_task_source call state ->
    sched_current_consistency state.(TskState) state.(SchedState) ->
    os_sched_selection_enabled state = true ->
    os_sched_requests_switch state = false ->
    state.(SchedState).(readyList) <> [] ->
    flag_pend_ready_source_cut environment sg call state
| FlagPendReadyCutSelected : forall context outgoing hooked incoming resumed returned,
    UCOS2_state_inv sg hooked ->
    sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
    os_sched_destination_binding environment.(task_stack_call_external)
      context outgoing hooked incoming resumed ->
    returned.(os_sched_call_stack) = incoming ->
    flag_pend_ready_source_cut environment sg returned
      (os_sched_install_context context outgoing incoming hooked)
| FlagPendReadyCutInterruptSelected : forall transfer returned,
    UCOS2_state_inv sg transfer.(os_int_exit_hooked_state) ->
    sched_high_ready_consistency transfer.(os_int_exit_hooked_state).(TskState)
      transfer.(os_int_exit_hooked_state).(SchedState) ->
    os_int_exit_destination_binding environment.(task_stack_call_external) transfer ->
    returned.(os_sched_call_stack) = transfer.(os_int_exit_incoming_stack) ->
    flag_pend_ready_source_cut environment sg returned (os_int_exit_installed_state transfer)
| FlagPendReadyCutTake : forall call state lease,
    flag_pend_ready_source_cut environment sg call state ->
    flag_pend_ready_source_cut environment sg call (os_int_exit_wrapper_restored_state state lease)
| FlagPendReadyCutSaveSP : forall call state sp,
    flag_pend_ready_source_cut environment sg call state ->
    flag_pend_ready_source_cut environment sg call
      (os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot) sp)
| FlagPendReadyCutPrefix : forall call state,
    flag_pend_ready_source_cut environment sg call state ->
    flag_pend_ready_source_cut environment sg call (os_sched_prefix_state state).

Lemma flag_pend_prefix_current_ready_iff : forall call state,
  flag_pend_current_ready call (os_sched_prefix_state state) <-> flag_pend_current_ready call state.
Proof.
  intros call state; unfold flag_pend_current_ready, sched_current_ready_at,
    os_sched_prefix_state; cbn [replace_SchedS TskState SchedState].
  destruct (os_sched_ready_checkpoint_frame state) as [Hr [Hc [Hp Hi]]].
  rewrite Hr, Hc, Hp; reflexivity.
Qed.

Lemma flag_pend_ready_source_cut_current_ready : forall environment sg call state,
  flag_pend_ready_source_cut environment sg call state -> flag_pend_current_ready call state.
Proof.
  intros environment sg call state Hsource; induction Hsource.
  - pose proof (flag_pend_nonswitch_current_ready sg call state
      H H0 H1 H2 H3 H4) as Hready.
    exact (proj1 (flag_pend_prefix_current_ready_iff call state) Hready).
  - eapply flag_pend_last_install_current_ready; eassumption.
  - destruct (flag_pend_irq_install_selected_ready environment.(task_stack_call_external) sg transfer
      H H0 H1) as [node [Hready Hgen]].
    exists node; rewrite H2; auto.
  - exact IHHsource.
  - apply flag_pend_save_current_sp_preserves_current_ready; exact IHHsource.
  - exact (proj2 (flag_pend_prefix_current_ready_iff call state) IHHsource).
Qed.

Lemma flag_pend_irq_fields_local_ready_return : forall environment sg state local suspended call node handler
  (interrupted_local frame : Assertion) before after,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  flag_pend_ready_source_cut environment sg (armv7a_continuation_resumed_call suspended call) state ->
  (UCOS2_fields_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry environment.(task_stack_call_continuations) state.(TskState)
       (kernel_irq_fields_local local suspended interrupted_local))
     state.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running environment.(task_stack_call_platform)
      handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame)) before ->
  armv7a_restore_transition environment.(task_stack_call_continuations) handler suspended before after ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  flag_pend_ready_source_cut environment sg (armv7a_continuation_resumed_call suspended call) restored /\
  flag_pend_current_ready (armv7a_continuation_resumed_call suspended call) restored /\
  (flag_source_save_input environment.(task_stack_call_continuations)
     (fun sg state => UCOS2_fields_inv sg state) local sg
     (Some (task_stack_key suspended.(armv7a_continuation_stack)))
     (armv7a_continuation_resumed_call suspended call)
     (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) restored interrupted_local **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros environment sg state local suspended call node handler interrupted_local frame before after
    Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hsource Hpre Hrestore restored.
  destruct (kernel_irq_restore_fields_local_resources environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg state local suspended call node handler interrupted_local
    frame before after Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre Hrestore)
    as [Hmemory [Hnone Howned]].
  assert (Hcut : flag_pend_ready_source_cut environment sg
    (armv7a_continuation_resumed_call suspended call) restored) by (constructor; exact Hsource).
  exact (conj Hmemory (conj Hcut (conj (flag_pend_ready_source_cut_current_ready _ _ _ _ Hcut) Howned))).
Qed.

Definition flag_pend_completed_view_heap_prefix environment critical sg (view : OsExecutionView) before
  (input : Assertion) first_heap last_state last_heap (last_input : Assertion) : Prop :=
  exists (Extra : Type)
    (resources : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State -> Assertion)
    (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
      KernelClientHeapCut Extra -> model -> Prop)
    (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
      KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
    (extra_source : Extra -> TaskInvocationOrigin -> UCOS2_Verify_State -> Prop)
    first_cut last_cut (frame : Assertion),
    kernel_client_fields_resource_guarantee resources extra_step extra_effect /\
    critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) /\
    (forall running, critical.(critical_region_clients)
      (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) /\
    (forall publication, critical.(critical_region_clients)
      (task_create_stack_publication_client publication)) /\
    kernel_client_heap_extension_execution_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      view.(os_execution_invocation) None extra_source extra_effect /\
    (input |-- resources sg first_cut before ** frame) /\
    input first_heap /\
    kernel_client_heap_observer_cut view.(os_execution_invocation) first_cut /\
    kernel_client_heap_source_cut extra_source first_cut view.(os_execution_origin) before /\
    flag_pend_heap_state_resources_trace resources extra_step extra_effect sg frame
      first_cut before first_heap last_cut last_state last_heap /\
    (resources sg last_cut last_state ** frame |-- last_input).


(** Shared declaration: PrimitiveComponent.FlagPendSourceOperation. *)

(** Shared declaration: PrimitiveComponent.FlagPendLinkedEvent. *)

(** The environment, critical resources and globals index this C source.
    Its module theorem returns the same event's input and output resources.
    Public C declarations select the constructed source instance. *)
Definition flag_pend_linked_prefix environment critical sg
  (linked : FlagPendProgramSources environment critical sg) operation caller original before
  returned_caller returned current (input : Assertion) first_heap (output : Assertion) last_heap : Prop :=
  flag_pend_program_event_source environment critical sg linked
    {| flag_pend_event_operation := operation;
       flag_pend_event_caller := caller;
       flag_pend_event_original := original;
       flag_pend_event_returned_caller := returned_caller;
       flag_pend_event_returned := returned;
       flag_pend_event_before := before;
       flag_pend_event_current := current;
       flag_pend_event_first_heap := first_heap;
       flag_pend_event_last_heap := last_heap;
       flag_pend_event_input := input;
       flag_pend_event_output := output |}.

Lemma flag_pend_linked_prefix_resources : forall environment critical sg linked operation caller original before
  returned_caller returned current input first_heap output last_heap,
  flag_pend_linked_prefix environment critical sg linked operation caller original before
    returned_caller returned current input first_heap output last_heap ->
  input first_heap /\ output last_heap.
Proof.
  intros environment critical sg linked operation caller original before
    returned_caller returned current input first_heap output last_heap Hsource.
  exact (flag_pend_program_event_resources environment critical sg linked _ Hsource).
Qed.

(** This endpoint packet reuses the existing completed-call ABI observation.
    Its running component is the selected C control rely, never an inference
    from a ready task or an arbitrary kernel-client prefix. *)
Definition flag_pend_call_return_control original before returned current : Prop :=
  kernel_call_normal_return original before returned current /\
  (before.(SchedState).(isRunning) = true -> current.(SchedState).(isRunning) = true) /\
  before.(IntrState) = current.(IntrState).

Definition flag_pend_caller_return_control original before returned current : Prop :=
  kernel_call_normal_return original before returned current /\
  (original.(os_sched_call_origin) <> BootInvocation ->
    flag_pend_call_return_control original before returned current).

Lemma flag_pend_caller_return_control_from_task_control : forall original before returned current,
  flag_pend_call_return_control original before returned current ->
  flag_pend_caller_return_control original before returned current.
Proof. intros original before returned current Hcontrol; split; [exact (proj1 Hcontrol)|auto]. Qed.

Lemma flag_pend_caller_return_control_running_origin : forall original before returned current,
  original.(os_sched_call_origin) <> BootInvocation ->
  flag_pend_caller_return_control original before returned current ->
  flag_pend_call_return_control original before returned current.
Proof. intros original before returned current Horigin [_ Hcontrol]; exact (Hcontrol Horigin). Qed.

Lemma flag_pend_caller_return_control_task_source : forall original before returned current,
  kernel_call_task_source original before ->
  flag_pend_caller_return_control original before returned current ->
  flag_pend_call_return_control original before returned current.
Proof.
  intros original before returned current [Horigin _] Hcontrol.
  apply flag_pend_caller_return_control_running_origin; [rewrite Horigin; discriminate|exact Hcontrol].
Qed.

Lemma flag_pend_caller_return_control_boot : forall original before returned current,
  original.(os_sched_call_origin) = BootInvocation ->
  kernel_call_normal_return original before returned current ->
  flag_pend_caller_return_control original before returned current.
Proof. intros original before returned current Hboot Hnormal; split; [exact Hnormal|tauto]. Qed.

Definition flag_pend_running_available call state : Prop :=
  state.(SchedState).(isRunning) = true /\ kernel_call_stack_available call state.

Lemma flag_pend_normal_return_control : forall sg original before returned current,
  kernel_call_normal_return original before returned current ->
  kernel_call_control_rely sg before current ->
  flag_pend_call_return_control original before returned current.
Proof.
  intros sg original before returned current Hnormal [Hrunning Hcounters].
  split; [exact Hnormal|]. split; [rewrite Hrunning; auto|exact (eq_sym Hcounters)].
Qed.

Lemma flag_pend_return_control_running_available : forall original before returned current,
  flag_pend_call_return_control original before returned current ->
  flag_pend_running_available original before -> flag_pend_running_available returned current.
Proof. unfold flag_pend_call_return_control, flag_pend_running_available,
  kernel_call_normal_return; firstorder. Qed.

Lemma flag_pend_wrapper_take_running_available : forall call state,
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(SchedState).(isRunning) = true ->
  flag_pend_running_available call (os_int_exit_wrapper_restored_state state call.(os_sched_call_stack)).
Proof.
  intros call state Horigin Hrunning; split; [exact Hrunning|].
  apply kernel_call_stack_available_after_take; exact Horigin.
Qed.

Lemma flag_pend_install_running_available : forall context saved call hooked,
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  hooked.(SchedState).(isRunning) = true ->
  flag_pend_running_available call (os_sched_install_context context saved call.(os_sched_call_stack) hooked).
Proof.
  intros context saved call hooked Horigin Hrunning; split; [exact Hrunning|].
  unfold kernel_call_stack_available; rewrite Horigin.
  change (task_stack_take
    (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) saved)
    call.(os_sched_call_stack) (task_stack_key call.(os_sched_call_stack)) = None).
  apply task_stack_take_lookup.
Qed.

Lemma flag_pend_task_stage_running_available : forall call state,
  flag_pend_task_stage call state -> flag_pend_running_available call state.
Proof.
  intros call state [Horigin [Hrunning [Havailable Hready]]].
  split; [exact Hrunning|]; unfold kernel_call_stack_available; rewrite Horigin; exact Havailable.
Qed.

Definition flag_pend_call_source_observations (environment : TaskStackCallEnvironment)
  sg caller original before returned current : Prop :=
  match caller with
  | FlagPendTaskCaller _ =>
      ((kernel_call_task_source original before /\ flag_pend_current_ready original before) ->
        flag_pend_current_ready returned current) /\
      ((kernel_call_task_source original before /\ task_idle_ready sg before.(TskState)) ->
        task_idle_ready sg current.(TskState)) /\
      ((kernel_call_task_source original before /\ flag_pend_non_idle_at sg original before) ->
        flag_pend_non_idle_at sg returned current) /\
      flag_pend_caller_return_control original before returned current
  | FlagPendInterruptCaller _ _ => True
  end.

Definition flag_pend_caller_completed_source operation environment critical sg linked caller original before
  (input : Assertion) first_heap returned_caller returned current after_heap (output : Assertion) : Prop :=
  flag_pend_linked_prefix environment critical sg linked operation caller original before returned_caller returned current
    input first_heap (coq_prop (flag_pend_call_endpoint_observations environment sg caller original before returned current) &&
      output) after_heap.

Lemma flag_pend_caller_completed_source_observations : forall operation environment critical sg linked caller original before
  input first_heap returned_caller returned current after_heap output,
  flag_pend_caller_completed_source operation environment critical sg linked caller original before input first_heap
    returned_caller returned current after_heap output ->
  flag_pend_call_source_observations environment sg caller original before returned current.
Proof.
  intros operation environment critical sg linked caller original before input first_heap returned_caller returned current after_heap output Hsource.
  destruct caller; [|exact I].
  pose proof (proj2 (flag_pend_linked_prefix_resources
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsource)) as Howned.
  destruct (proj1 Howned) as [Hready [Hidle [Hnonidle [Hnormal Hrely]]]].
  split; [exact Hready|]. split; [exact Hidle|]. split; [exact Hnonidle|].
  split; [exact Hnormal|].
  intros Hnonboot.
  exact (flag_pend_normal_return_control sg original before returned current Hnormal (Hrely Hnonboot)).
Qed.



Lemma flag_pend_uninterrupted_save_source_observations : forall environment sg caller call arch registers
  before before_heap final_registers current after_heap,
  kernel_call_save_uninterrupted_execution arch registers before before_heap final_registers current after_heap ->
  flag_pend_call_source_observations environment sg caller call before call current.
Proof.
  intros environment sg caller call arch registers before before_heap final_registers current after_heap Hsource.
  pose proof (kernel_call_save_instructions_preserve_kernel _ _ _ _ _ _ _ _ Hsource) as [Hstate Hheap].
  subst current; destruct caller; cbn [flag_pend_call_source_observations].
  - split; [intros [_ Hready]; exact Hready|].
    split; [tauto|]. split; [tauto|].
    split; [apply kernel_call_normal_return_refl|].
    intros _. split; [apply kernel_call_normal_return_refl|auto].
  - exact I.
Qed.



(** The first paired call also accepts a real exception view at Boot. The
    task_call index is used only in the task branch. The view branch owns its
    actual exception stack and never constructs a task allocation lease. *)
(** Shared declaration: PrimitiveComponent.flag_pend_caller_save_input. *)

(** Shared declaration: PrimitiveComponent.flag_pend_caller_restore_input. *)

Definition flag_pend_caller_save_observation environment critical sg caller original returned_caller returned
  mask saved before acquired : Prop :=
  match caller, returned_caller with
  | FlagPendTaskCaller actual, FlagPendTaskCaller next =>
      actual = original /\ next = returned /\
      ContinuationPhaseEffects.os_sched_continuation_phase_save_effect environment critical sg original mask saved before returned acquired /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_source_preserved original before acquired
  | FlagPendInterruptCaller view key, FlagPendInterruptCaller next next_key =>
      returned = original /\ next_key = key /\ sched_fields_same_view next view /\
      critical_region_interval critical sg view.(os_execution_invocation) before acquired
  | _, _ => False
  end.

Definition flag_pend_caller_restore_observation environment critical sg caller original returned_caller returned
  released current : Prop :=
  match caller, returned_caller with
  | FlagPendTaskCaller actual, FlagPendTaskCaller next =>
      actual = original /\ next = returned /\
      ContinuationPhaseEffects.os_sched_continuation_phase_restore_effect environment critical sg original released returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original released ->
        task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current) /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current)
  | FlagPendInterruptCaller view key, FlagPendInterruptCaller next next_key =>
      returned = original /\ next_key = key /\ sched_fields_same_view next view /\
      critical_region_interval critical sg view.(os_execution_invocation) released current
  | _, _ => False
  end.

Definition flag_pend_caller_save_event environment critical local active sg linked caller original mask saved before
  returned_caller returned acquired next_local (before_heap after_heap : model) : Prop :=
  flag_pend_caller_save_observation environment critical sg caller original returned_caller returned
    mask saved before acquired /\
  interrupt_saved_value mask saved /\
  flag_pend_caller_save_input environment critical local active sg caller original mask before before_heap /\
  flag_pend_caller_restore_input environment critical next_local active sg returned_caller returned
    saved acquired acquired after_heap /\
  flag_pend_caller_completed_source FlagPendSaveSource environment critical sg linked caller original before
    (flag_pend_caller_save_input environment critical local active sg caller original mask before)
    before_heap returned_caller returned acquired after_heap
    (flag_pend_caller_restore_input environment critical next_local active sg returned_caller returned
      saved acquired acquired).

Definition flag_pend_caller_save_output environment critical local active sg linked caller original mask before before_heap saved : Assertion :=
  fun after_heap => exists returned_caller returned acquired next_local,
    flag_pend_caller_save_event environment critical local active sg linked caller original mask saved before
      returned_caller returned acquired next_local before_heap after_heap.

Definition flag_pend_caller_restore_event environment critical local active sg linked caller original saved acquired released
  returned_caller returned current next_local (before_heap after_heap : model) : Prop :=
  flag_pend_caller_restore_observation environment critical sg caller original returned_caller returned released current /\
  flag_pend_caller_restore_input environment critical local active sg caller original saved acquired released before_heap /\
  flag_pend_caller_save_input environment critical next_local active sg returned_caller returned
    (armv7a_irq_fiq_mask saved) current after_heap /\
  flag_pend_caller_completed_source FlagPendRestoreSource environment critical sg linked caller original released
    (flag_pend_caller_restore_input environment critical local active sg caller original saved acquired released)
    before_heap returned_caller returned current after_heap
    (flag_pend_caller_save_input environment critical next_local active sg returned_caller returned
      (armv7a_irq_fiq_mask saved) current).

Definition flag_pend_caller_restore_output environment critical local active sg linked caller original saved acquired released
  before_heap : Assertion :=
  fun after_heap => exists returned_caller returned current next_local,
    flag_pend_caller_restore_event environment critical local active sg linked caller original saved acquired released
      returned_caller returned current next_local before_heap after_heap.

Lemma flag_pend_caller_save_output_open : forall environment critical local active sg linked caller original mask before before_heap saved,
  flag_pend_caller_save_output environment critical local active sg linked caller original mask before before_heap saved |--
  EX returned_caller returned acquired next_local,
    coq_prop (flag_pend_caller_save_observation environment critical sg caller original returned_caller returned
      mask saved before acquired /\ interrupt_saved_value mask saved /\
      flag_pend_call_source_observations environment sg caller original before returned acquired) &&
    flag_pend_caller_restore_input environment critical next_local active sg returned_caller returned saved acquired acquired.
Proof.
  intros environment critical local active sg linked caller original mask before before_heap saved heap
    [returned_caller [returned [acquired [next_local [Hsource [Hsaved [Hbefore [Hafter Hcompleted]]]]]]]].
  exists returned_caller, returned, acquired, next_local; split.
  - split; [exact Hsource|]. split; [exact Hsaved|].
    eapply flag_pend_caller_completed_source_observations; exact Hcompleted.
  - exact Hafter.
Qed.

Lemma flag_pend_caller_restore_output_open : forall environment critical local active sg linked caller original saved acquired released before_heap,
  flag_pend_caller_restore_output environment critical local active sg linked caller original saved acquired released before_heap |--
  EX returned_caller returned current next_local,
    coq_prop (flag_pend_caller_restore_observation environment critical sg caller original returned_caller returned released current /\
      flag_pend_call_source_observations environment sg caller original released returned current) &&
    flag_pend_caller_save_input environment critical next_local active sg returned_caller returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local active sg linked caller original saved acquired released before_heap heap
    [returned_caller [returned [current [next_local [Hsource [Hbefore [Hafter Hcompleted]]]]]]].
  exists returned_caller, returned, current, next_local; split.
  - split; [exact Hsource|]. eapply flag_pend_caller_completed_source_observations; exact Hcompleted.
  - exact Hafter.
Qed.

Definition flag_pend_caller_masked_control environment local critical sg caller task_call saved acquired state : Assertion :=
  match caller with
  | FlagPendTaskCaller actual =>
      coq_prop (actual = task_call) &&
      flag_pend_masked_control environment local critical sg task_call saved acquired state
  | FlagPendInterruptCaller view key =>
      coq_prop (task_stack_live_coverage state.(TskState) key) &&
      (critical_region_masked environment.(task_stack_call_platform) critical sg
         view.(os_execution_invocation) view.(os_execution_origin) saved acquired **
       os_execution_view_resources environment.(task_stack_call_external) view **
       os_sched_fields_capsules environment local state ** unmap_table_rep sg)
  end.

Definition flag_pend_caller_fields_restore_input environment critical local sg caller call saved acquired state : Assertion :=
  flag_pend_caller_restore_input environment critical local (fun _ _ => emp) sg caller call saved acquired state.

Lemma flag_pend_caller_masked_fields_split : forall environment critical local sg caller call saved acquired state,
  flag_pend_caller_fields_restore_input environment critical local sg caller call saved acquired state --||--
  flag_pend_caller_masked_control environment local critical sg caller call saved acquired state **
    UCOS2_fields_inv sg state.
Proof.
  intros; destruct caller; unfold flag_pend_caller_fields_restore_input,
    flag_pend_caller_restore_input, flag_pend_caller_masked_control,
    flag_pend_active_restore_input, os_sched_fields_restore_input,
    flag_pend_masked_control; split; entailer!.
Qed.

Definition flag_pend_caller_saved_prefix environment critical sg caller original mask before i pgrp
  returned_caller returned saved acquired : Prop :=
  pgrp <> 0 /\ before.(IntrState).(intNesting) <= 0 /\ before.(IntrState).(lockNesting) <= 0 /\
  (exists image, before.(FlagState).(flagImages) i = Some image /\ image.(flagImageType) = 5) /\
  flag_pend_caller_save_observation environment critical sg caller original returned_caller returned
    mask saved before acquired /\ interrupt_saved_value mask saved.

Definition flag_pend_priority_at (tasks : Glob_TaskAbstractState) (slot : TaskID) (generation : nat) (priority : Z) : Prop :=
  exists node, tasks.(inUsedTaskStates) slot = Some node /\ node.(taskGeneration) = generation /\ node.(curPrio) = priority.

Lemma flag_pend_publication_priority : forall sg publication before after,
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  flag_pend_priority_at after.(TskState) publication.(stack_publication_slot)
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration)
    (task_create_stack_publication_args publication).(initPrio).
Proof.
  intros sg publication before after [Hinput ->].
  exists (task_set_links
    (task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image)) before.(TskState).(tcbListHead) None).
  split.
  - cbn [task_create_stack_publication_state task_create_stack_published_state
      task_tcb_init_published_state task_tcb_init_commit_state task_sched_commit_state
      replace_SchedS replace_TskS TskState glob_task_set_parked_stacks inUsedTaskStates
      task_commit].
    replace (taskID (task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image))) with publication.(stack_publication_slot) by reflexivity.
    destruct (Z.eq_dec publication.(stack_publication_slot)
      publication.(stack_publication_slot)); [reflexivity|contradiction].
  - split; [reflexivity|]. repeat split; reflexivity.
Qed.

Lemma flag_pend_save_sp_preserves_priority : forall state slot generation priority outgoing sp,
  flag_pend_priority_at state.(TskState) slot generation priority ->
  flag_pend_priority_at (os_sched_save_current_sp state outgoing sp).(TskState) slot generation priority.
Proof.
  intros state slot generation priority outgoing sp [node [Hnode [Hgen Hclean]]].
  unfold os_sched_save_current_sp.
  destruct (state.(TskState).(inUsedTaskStates) outgoing) as [old|] eqn:Hold.
  - destruct (Z.eqb slot outgoing) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst slot.
      rewrite Hnode in Hold; inversion Hold; subst old.
      exists (task_set_saved_sp node sp).
      split; [cbn; rewrite Z.eqb_refl; reflexivity|]. split; assumption.
    + exists node; split; [cbn; rewrite Heq; exact Hnode|]. split; assumption.
  - exists node; split; [exact Hnode|]. split; assumption.
Qed.


Lemma flag_pend_published_initial_non_idle : forall sg publication before published
  call sp outgoing selected,
  kernel_client_step (task_create_stack_publication_client publication) sg before published ->
  selected.(armv7a_continuation_stack).(stackLeaseSlot) = publication.(stack_publication_slot) ->
  selected.(armv7a_continuation_stack).(stackLeaseGeneration) =
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration) ->
  (task_create_stack_publication_args publication).(initPrio) <> sg.(osLowestPrio) ->
  let current := os_sched_install_context call outgoing selected.(armv7a_continuation_stack)
    (os_sched_save_current_sp (os_sched_prefix_state published)
      call.(os_sched_call_stack).(stackLeaseSlot) sp) in
  let first := armv7a_initial_call selected current.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  flag_pend_non_idle_at sg first (armv7a_initial_call_registered selected current).
Proof.
  intros sg publication before published call sp outgoing selected Hpublication Hslot Hgen Hnonidle current first.
  pose proof (flag_pend_publication_priority sg publication before published Hpublication) as Hpriority.
  assert (Hsaved : flag_pend_priority_at current.(TskState)
    publication.(stack_publication_slot)
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration)
    (task_create_stack_publication_args publication).(initPrio)).
  { apply flag_pend_save_sp_preserves_priority; exact Hpriority. }
  destruct Hsaved as [node [Hnode [Hg Hp]]].
  unfold flag_pend_non_idle_at.
  change (exists node, current.(TskState).(inUsedTaskStates)
    selected.(armv7a_continuation_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) /\
    node.(curPrio) <> sg.(osLowestPrio)).
  rewrite Hslot, Hgen; exists node; split; [exact Hnode|].
  split; [exact Hg|]. rewrite Hp; exact Hnonidle.
Qed.


(** The general finite return path includes interrupt resumes. Its last
    selected/no-switch observation and owned resources are in the SAME final
    cut. The registered module interpretation must realize this cut from the
    captured caller footprint; the observation is not taken from the old
    existential Scheduler postcondition. *)
Definition flag_pend_sched_completed_source environment critical local active sg linked
  original mask before first_heap returned current next_local after : Prop :=
  flag_pend_linked_prefix environment critical sg linked FlagPendSchedulerSource (FlagPendTaskCaller original)
    original before (FlagPendTaskCaller returned) returned current
    (os_sched_active_call_pre environment local active sg original mask before) first_heap
    (coq_prop (flag_pend_ready_source_cut environment sg returned current /\
      kernel_call_normal_return original before returned current /\
      kernel_call_control_rely sg before current) &&
      flag_pend_ready_return_owned environment next_local sg returned mask current
        (active returned current)) after.

Definition flag_pend_sched_output environment critical local active sg linked
  original mask before first_heap : Assertion :=
  fun after => exists returned current next_local,
    os_sched_continuation_call_history environment critical sg original mask before returned current /\
    task_tcb_init_stack_same_call returned original /\
    (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
    flag_pend_sched_completed_source environment critical local active sg linked
      original mask before first_heap returned current next_local after.

Definition flag_pend_sched_return_observation environment critical sg original mask before returned current : Prop :=
  SchedulerPhaseCandidate.os_sched_task_call_history environment critical sg original mask before returned current /\
  task_tcb_init_stack_same_call returned original /\
  (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
  flag_pend_current_ready returned current /\
  flag_pend_call_return_control original before returned current.

Lemma flag_pend_sched_output_open : forall environment critical local active sg linked
  original mask before first_heap,
  flag_pend_sched_output environment critical local active sg linked original mask before first_heap |--
  EX returned current next_local,
    coq_prop (os_sched_continuation_call_history environment critical sg original mask before returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current) /\
      flag_pend_current_ready returned current /\
      flag_pend_call_return_control original before returned current) &&
    (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local sg (task_stack_call_active_key returned) returned mask current ** active returned current).
Proof.
  intros environment critical local active sg linked original mask before first_heap after
    [returned [current [next_local [Hhistory [Hsame [Hsource Hcompleted]]]]]].
  destruct (proj2 (flag_pend_linked_prefix_resources
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcompleted))
    as [[Hcut [Hnormal Hrely]] Howned].
  exists returned, current, next_local; split; [|exact Howned].
  exact (conj Hhistory (conj Hsame (conj Hsource
    (conj (flag_pend_ready_source_cut_current_ready _ _ _ _ Hcut)
      (flag_pend_normal_return_control sg original before returned current Hnormal Hrely))))).
Qed.

Lemma flag_pend_sched_output_erases : forall environment critical local active sg linked
  original mask before first_heap,
  flag_pend_sched_output environment critical local active sg linked original mask before first_heap |--
  os_sched_active_history_return_post environment critical active sg original mask before.
Proof.
  intros; sep_apply_l_atomic (flag_pend_sched_output_open environment critical local active sg linked
    original mask before first_heap).
  unfold os_sched_active_history_return_post; Intros returned current next_local.
  Exists returned current next_local; entailer!; tauto.
Qed.

(** Sequential entry does not require a ready task on the early-error Boot
    branch. It still consumes the actual completed-return/next-entry ABI event
    and the same owned world; registration alone produces no physical bytes. *)
Lemma flag_pend_sequential_owned_world : forall environment
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform)) local sg previous state mask before after (frame : Assertion),
  task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin) ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before after ->
  (flag_pend_call_world environment local sg previous mask state ** frame) before ->
  let call := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let registered := flag_sequential_registered_state previous state in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (flag_pend_call_world environment local sg call mask registered ** frame) after.
Proof.
  intros environment boundary local sg previous state mask before after frame Hlive Hsource Hpre
    call registered.
  assert (Hopen : flag_pend_call_world environment local sg previous mask state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key previous)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) previous mask **
     (kernel_program_fields_inv sg state ** os_sched_fields_capsules environment local state ** frame))).
  { unfold flag_pend_call_world, kernel_continuation_call_closed,
      kernel_continuation_inv, os_sched_fields_capsules; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) mask before after _ Hsource Howned)
    as [Hmemory Hafter].
  split; [exact Hmemory|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { rewrite kernel_program_fields_inv_split_unmap.
    sep_apply_l_atomic (flag_fields_begin_invocation sg state previous.(os_sched_call_origin) Hlive).
    unfold flag_pend_call_world, kernel_continuation_call_closed,
      kernel_continuation_inv, os_sched_fields_capsules.
    rewrite kernel_program_fields_inv_split_unmap.
    change (task_stack_call_active_key call) with (task_stack_call_active_key previous).
    assert (Hcoverage_new : task_stack_live_coverage registered.(TskState)
      (task_stack_call_active_key previous)) by exact Hcoverage.
    unfold registered, flag_sequential_registered_state; entailer!. }
  exact (Hclose after Hafter).
Qed.


Definition flag_pend_early_domain (i pgrp mode : Z) (state : UCOS2_Verify_State) : Prop :=
  pgrp = 0 \/ 0 < state.(IntrState).(intNesting) \/
  0 < state.(IntrState).(lockNesting) \/
  (forall image, state.(FlagState).(flagImages) i = Some image ->
    image.(flagImageType) <> 5) \/ ~ flag_pend_valid_mode mode.

Lemma flag_pend_early_domain_source : forall sg call i pgrp mode state,
  flag_pend_early_domain i pgrp mode state ->
  flag_pend_source_domain sg call i pgrp mode state.
Proof.
  intros sg call i pgrp mode state Hearly Hp Hn Hl image Hi Hty Hmode.
  destruct Hearly as [He|[He|[He|[He|He]]]]; exfalso.
  - exact (Hp He).
  - lia.
  - lia.
  - exact (He image Hi Hty).
  - exact (He Hmode).
Qed.

Lemma flag_pend_early_interrupt_source : forall sg view active call i pgrp mode state,
  flag_pend_interrupt_source view state ->
  flag_pend_early_domain i pgrp mode state ->
  flag_pend_caller_source sg (FlagPendInterruptCaller view active) call i pgrp mode state.
Proof.
  intros sg view active call i pgrp mode state Hsource Hearly; split; [exact Hsource|].
  intros Hp Hn Hl image Hi Hty Hmode.
  destruct Hearly as [He|[He|[He|[He|He]]]].
  - exact (Hp He).
  - lia.
  - lia.
  - exact (He image Hi Hty).
  - exact (He Hmode).
Qed.

(** Source labels are supplied by the fixed linked startup/exception module.
    They do not produce a ready task, kernel fields, or a task stack lease.
    The ordinary nested and Boot exception stack event exchanges only the
    actual execution owner and its saved outer frame, before the separately
    checked counter writes. Its frame law preserves every kernel byte.
    First-level task parking uses the registered continuation producer below. *)
Record FlagPendEntryBoundary : Type := {
  flag_pend_startup_source : TaskStackCallEnvironment -> OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop;
  flag_pend_exception_frame : OsExecutionView -> OsExecutionView -> Assertion;
  flag_pend_exception_stack_source : OsExecutionView -> OsExecutionView -> model -> model -> Prop;
  flag_pend_exception_stack_resources : forall environment outer inner mask before saved (frame : Assertion),
    flag_pend_exception_stack_source outer inner before saved ->
    (kernel_execution_view_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) outer mask ** frame) before ->
    (kernel_execution_view_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) inner 192 **
      flag_pend_exception_frame outer inner ** frame) saved
}.




(** This root consumes the real restored initial frame. The publication,
    last selected destination, concrete install and TaskRestore all name
    the same selected lease, state and output heap. *)
Inductive flag_pend_initial_entry_source environment sg :
  (Armv7aContinuation -> Assertion) -> OsSchedCallContext -> Z ->
  UCOS2_Verify_State -> Assertion -> model -> Prop :=
| FlagPendInitialEntry :
  forall (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    publication base published outgoing_call sp outgoing selected resumed local
    before_install installed after (frame : Assertion),
  let hooked := os_sched_save_current_sp (os_sched_prefix_state published)
    outgoing_call.(os_sched_call_stack).(stackLeaseSlot) sp in
  let current := os_sched_install_context outgoing_call outgoing selected.(armv7a_continuation_stack) hooked in
  let first := armv7a_initial_call selected current.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  let registered := armv7a_initial_call_registered selected current in
  UCOS2_state_inv sg base ->
  kernel_client_step (task_create_stack_publication_client publication) sg base published ->
  task_idle_ready sg base.(TskState) ->
  (task_create_stack_publication_args publication).(initPrio) <> sg.(osLowestPrio) ->
  selected.(armv7a_continuation_stack).(stackLeaseSlot) = publication.(stack_publication_slot) ->
  selected.(armv7a_continuation_stack).(stackLeaseGeneration) =
    publication.(stack_publication_acquired).(TskState).(taskLifecycle).(taskNextGeneration) ->
  selected.(armv7a_continuation_call) = None ->
  armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 selected.(armv7a_continuation_fragments) ->
  UCOS2_state_inv sg hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  os_sched_destination_binding environment.(task_stack_call_external) outgoing_call outgoing hooked
    selected.(armv7a_continuation_stack) resumed ->
  current.(SchedState).(isRunning) = true ->
  task_stack_live_coverage current.(TskState) (Some (task_stack_key selected.(armv7a_continuation_stack))) ->
  sched_install_heap_fragment sg before_install installed
    (task_slot_addr sg selected.(armv7a_continuation_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) ->
  armv7a_continuation_restore_reads selected installed ->
  (armv7a_task_switch_control task_abi outgoing_call **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) **
    armv7a_task_continuation_resource environment.(task_stack_call_continuations) selected **
    (local selected ** kernel_program_fields_inv sg current **
     os_sched_fields_capsules environment local current ** frame)) installed ->
  armv7a_task_restore_transition task_abi outgoing_call selected installed after ->
  flag_pend_initial_entry_source environment sg local first
    (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) registered (local selected ** frame) after.

Lemma flag_pend_initial_entry_source_resources : forall environment sg local call mask state frame heap,
  flag_pend_initial_entry_source environment sg local call mask state frame heap ->
  (coq_prop (flag_pend_task_entry call state /\ task_idle_ready sg state.(TskState) /\
     flag_pend_non_idle_at sg call state) &&
    (flag_pend_call_world environment local sg call mask state ** frame)) heap.
Proof.
  intros environment sg local call mask state frame heap Hroot.
  destruct Hroot as [entry task_abi publication base published outgoing_call sp outgoing selected resumed
    local before_install installed after frame hooked current first registered Hbase Hpub Hidle Hnonidle
    Hslot Hgen Hnone Hinitial Hrange Hvalid Hhigh Hdestination Hrunning Hcoverage Hinstall Hreads Hpre Hrestore].
  destruct (task_create_install_selected_ready environment.(task_stack_call_external) sg
    outgoing_call outgoing hooked selected.(armv7a_continuation_stack) resumed
    Hvalid Hhigh Hdestination) as [node [Hready Hgeneration]].
  assert (Hcurrent : task_current_at current selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { split; [exact (proj1 (proj2 Hready))|]. exists node; split; [exact (proj1 Hready)|exact Hgeneration]. }
  destruct (armv7a_task_restore_resources _ _ _ environment.(task_stack_call_continuations)
    task_abi outgoing_call selected _ installed after Hreads Hpre Hrestore) as [Hmemory [Hsource Hafter]].
  pose proof (flag_pend_initial_published_call_world_resources environment entry sg publication base published
    outgoing_call sp outgoing selected local node frame Hpub Hslot Hgen Hnone Hinitial Hrange
    Hrunning Hcurrent Hready Hgeneration Hcoverage) as Hresources.
  cbv zeta in Hresources; fold hooked current first registered in Hresources.
  match type of Hafter with ?P after => assert (Horder : P |--
    armv7a_task_restored_execution environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) selected ** local selected **
    kernel_program_fields_inv sg current ** os_sched_fields_capsules environment local current ** frame)
    by entailer! end.
  destruct (Hresources after (Horder after Hafter)) as [Hentry Hworld].
  split; [|exact Hworld]. split; [exact Hentry|]. split.
  - exact (flag_pend_published_initial_idle_ready sg publication base published
      outgoing_call sp outgoing selected Hbase Hpub Hidle).
  - exact (flag_pend_published_initial_non_idle sg publication base published
      outgoing_call sp outgoing selected Hpub Hslot Hgen Hnonidle).
Qed.

Lemma flag_pend_sequential_source_domain : forall sg previous state i pgrp mode,
  flag_pend_source_domain sg previous i pgrp mode state ->
  flag_pend_source_domain sg
    (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation))
    i pgrp mode (flag_sequential_registered_state previous state).
Proof.
  intros sg previous state i pgrp mode Hdomain Hp Hn Hl image Hi Hty Hmode.
  destruct (Hdomain Hp Hn Hl image Hi Hty Hmode) as [Hentry [Hidle Hnonidle]].
  split; [apply flag_pend_sequential_entry; exact (proj1 Hentry)|].
  split; assumption.
Qed.


Definition flag_pend_caller_view (caller : FlagPendCaller) : OsExecutionView :=
  match caller with FlagPendTaskCaller call => os_sched_execution_view call
  | FlagPendInterruptCaller view _ => view end.

Definition flag_pend_caller_active_key (caller : FlagPendCaller) : option (Z * nat) :=
  match caller with FlagPendTaskCaller call => task_stack_call_active_key call
  | FlagPendInterruptCaller _ key => key end.

Lemma flag_pend_caller_world_view : forall environment local sg caller mask state,
  flag_pend_caller_world environment local sg caller mask state =
  kernel_execution_view_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (flag_pend_caller_view caller) mask **
  kernel_continuation_inv environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (flag_pend_caller_active_key caller) state.
Proof. intros; destruct caller; reflexivity. Qed.

Lemma flag_pend_irq_counter_fields_frames : forall sg state (frame : Assertion) before,
  (state.(SchedState).(isRunning) = true -> 0 <= state.(IntrState).(intNesting) < 255) ->
  (UCOS2_fields_inv sg state ** frame) before ->
  exists after,
    kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg state) before after /\
    (UCOS2_fields_inv sg (armv7a_irq_entry_counter_state state) ** frame) after.
Proof.
  intros sg state frame before Hbound [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  destruct (armv7a_irq_entry_counter_fields_raw_post sg state owned Hraw) as [written [Hrun Hpost]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [after [Hwhole Hfinal]].
  exists after; split; [exact Hwhole|].
  exists written, rest; split; [exact Hfinal|]. split; [|exact Hframe].
  split; [|exact Hpost]. rewrite (armv7a_irq_entry_counter_eq_c_entry state Hbound).
  apply os_int_enter_preserves_validity; exact Hvalid.
Qed.

Lemma flag_pend_exception_entry_resources : forall environment boundary local sg caller inner handler
  mask state before saved after (frame : Assertion),
  inner.(os_execution_context) = KernelInterrupt handler (flag_pend_caller_view caller).(os_execution_context) ->
  kernel_interrupt_nesting_agrees state.(SchedState).(isRunning)
    (flag_pend_caller_view caller).(os_execution_context) state.(IntrState) ->
  (state.(SchedState).(isRunning) = true ->
    (kernel_interrupt_depth (flag_pend_caller_view caller).(os_execution_context) < 255)%nat) ->
  flag_pend_exception_stack_source boundary (flag_pend_caller_view caller) inner before saved ->
  kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg state) saved after ->
  (flag_pend_caller_world environment local sg caller mask state ** frame) before ->
  (coq_prop (flag_pend_interrupt_source inner (armv7a_irq_entry_counter_state state)) &&
    (flag_pend_caller_world environment local sg
      (FlagPendInterruptCaller inner (flag_pend_caller_active_key caller)) 192
      (armv7a_irq_entry_counter_state state) **
      (flag_pend_exception_frame boundary (flag_pend_caller_view caller) inner ** frame))) after.
Proof.
  intros environment boundary local sg caller inner handler mask state before saved after frame
    Hcontext Hagrees Hdepth Hstack Hcounter Hpre.
  assert (Hbound : state.(SchedState).(isRunning) = true -> 0 <= state.(IntrState).(intNesting) < 255).
  { intro Hrunning; specialize (Hagrees Hrunning); specialize (Hdepth Hrunning); lia. }
  assert (Hopen : flag_pend_caller_world environment local sg caller mask state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) (flag_pend_caller_active_key caller)) &&
    (kernel_execution_view_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (flag_pend_caller_view caller) mask **
     (UCOS2_fields_inv sg state ** os_sched_fields_capsules environment local state ** unmap_table_rep sg ** frame))).
  { rewrite flag_pend_caller_world_view; unfold kernel_continuation_inv, os_sched_fields_capsules.
    rewrite kernel_program_fields_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  pose proof (flag_pend_exception_stack_resources boundary environment _ _ _ _ _ _ Hstack Howned) as Hsaved.
  match type of Hsaved with ?P saved =>
    assert (Horder : P |-- UCOS2_fields_inv sg state **
      (kernel_execution_view_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
         inner 192 ** flag_pend_exception_frame boundary (flag_pend_caller_view caller) inner **
       os_sched_fields_capsules environment local state ** unmap_table_rep sg ** frame)) by entailer! end.
  destruct (flag_pend_irq_counter_fields_frames sg state _ saved Hbound (Horder saved Hsaved))
    as [produced [Hrun Hresult]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hinterrupt : flag_pend_interrupt_source inner (armv7a_irq_entry_counter_state state)).
  { exists handler, (flag_pend_caller_view caller).(os_execution_context); split; [exact Hcontext|].
    rewrite Hcontext, (armv7a_irq_entry_counter_eq_c_entry state Hbound).
    apply kernel_interrupt_entry_preserves_nesting_agreement; assumption. }
  match type of Hresult with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold flag_pend_caller_world, kernel_continuation_inv, os_sched_fields_capsules.
    rewrite kernel_program_fields_inv_split_unmap.
    assert (Htasks : (armv7a_irq_entry_counter_state state).(TskState) = state.(TskState)).
    { unfold armv7a_irq_entry_counter_state; destruct state.(SchedState).(isRunning); reflexivity. }
    rewrite Htasks; entailer!. }
  exact (Hclose after Hresult).
Qed.

Inductive flag_pend_first_irq_source environment sg :
  (Armv7aContinuation -> Assertion) -> OsExecutionView -> UCOS2_Verify_State -> Assertion -> model -> Prop :=
| FlagPendFirstIrqSource : forall local entry node handler descriptor publication
    before saved after (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call descriptor.(armv7a_continuation_sp)
    descriptor.(armv7a_continuation_fragments) in
  os_int_exit_context_resources environment.(task_stack_call_port) handler =
    os_execution_view_resources environment.(task_stack_call_external) (os_int_exit_execution_view handler) ->
  armv7a_task_frame_slice descriptor ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    descriptor.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) descriptor.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform) handler **
    (UCOS2_fields_inv sg entry **
     store_parked_continuations (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
       entry.(TskState) local) entry.(TskState).(parkedTaskStacks) ** local descriptor **
     (unmap_table_rep sg ** frame))) before ->
  armv7a_save_transition environment.(task_stack_call_continuations) handler descriptor before saved ->
  kernel_heap_execution (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp)) saved after ->
  flag_pend_first_irq_source environment sg local (os_int_exit_execution_view handler) parked frame after.

Lemma flag_pend_first_irq_source_resources : forall environment sg local view state frame heap,
  flag_pend_first_irq_source environment sg local view state frame heap ->
  (coq_prop (flag_pend_interrupt_source view state /\ 0 < state.(IntrState).(intNesting)) &&
    (flag_pend_caller_world environment local sg (FlagPendInterruptCaller view None) 192 state ** frame)) heap.
Proof.
  intros environment sg local view state frame heap Hsource.
  destruct Hsource as [local entry node handler descriptor publication before saved after frame call parked
    Hport Hslice Hrunning Hnest Hcur Hnode Hid Hgen Hnone Haddress Hregion Hrange Hpub Hsp Hcoverage
    Hpre Hsave Hactual].
  destruct (flag_irq_entry_fields_source environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg entry node handler descriptor publication
    local (unmap_table_rep sg ** frame) before saved
    Hslice Hrunning Hnest Hcur Hnode Hid Hgen Hnone Haddress Hregion Hrange Hpub Hsp Hcoverage Hpre Hsave)
    as [produced [Hbinding [Hlease [Hparked [Hcall [Hpc [Hmask [Hwrites [Hrun [Hcovered Hworld]]]]]]]]]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hdepth : parked.(IntrState).(intNesting) = 1).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    rewrite Hrunning; cbn; rewrite Hnest; reflexivity. }
  assert (Hinterrupt : flag_pend_interrupt_source (os_int_exit_execution_view handler) parked).
  { exists handler.(os_int_exit_invocation),
      (KernelCaller call.(os_sched_call_invocation) call.(os_sched_call_origin)); split; [reflexivity|].
    intro Hr; exact Hdepth. }
  split; [split; [exact Hinterrupt|lia]|].
  match type of Hworld with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold flag_pend_caller_world, kernel_execution_view_owned, kernel_continuation_inv,
      os_sched_fields_capsules.
    rewrite kernel_program_fields_inv_split_unmap, Hport.
    unfold parked, call; cbn [os_int_exit_execution_view os_execution_invocation os_execution_origin].
    entailer!. }
  exact (Hclose after Hworld).
Qed.

(** Entry consumes the original C source's completed event and its exact
    input/output resources. The next-call ABI uses that completed return
    heap. Task, Boot, first IRQ, exception and sequential domains remain. *)
Inductive flag_pend_entry_source environment critical
  (boundary : FlagPendEntryBoundary) sg (linked : FlagPendProgramSources environment critical sg) :
  (Armv7aContinuation -> Assertion) -> FlagPendCaller -> OsSchedCallContext -> Z ->
  Z -> Z -> Z -> UCOS2_Verify_State -> Assertion -> model -> Prop :=
| FlagPendEntryInitial : forall local call mask i pgrp mode state frame heap,
  flag_pend_initial_entry_source environment sg local call mask state frame heap ->
  flag_pend_entry_source environment critical boundary sg linked local (FlagPendTaskCaller call) call mask
    i pgrp mode state frame heap
| FlagPendEntryStartup : forall local call mask i pgrp mode state frame heap,
  flag_pend_startup_source boundary environment call state heap ->
  call.(os_sched_call_origin) = BootInvocation ->
  state.(SchedState).(isRunning) = false ->
  flag_pend_early_domain i pgrp mode state ->
  (flag_pend_call_world environment local sg call mask state ** frame) heap ->
  flag_pend_entry_source environment critical boundary sg linked local (FlagPendTaskCaller call) call mask
    i pgrp mode state frame heap
| FlagPendEntryFirstInterrupt : forall local view state frame heap call i pgrp mode,
  flag_pend_first_irq_source environment sg local view state frame heap ->
  flag_pend_entry_source environment critical boundary sg linked local
    (FlagPendInterruptCaller view None) call 192 i pgrp mode state frame heap
| FlagPendEntryException : forall local caller call mask root_i root_pgrp root_mode state frame before
    inner handler saved after i pgrp mode,
  flag_pend_entry_source environment critical boundary sg linked local caller call mask
    root_i root_pgrp root_mode state frame before ->
  (state.(SchedState).(isRunning) = false \/
    exists outer_handler interrupted, (flag_pend_caller_view caller).(os_execution_context) =
      KernelInterrupt outer_handler interrupted) ->
  inner.(os_execution_context) = KernelInterrupt handler (flag_pend_caller_view caller).(os_execution_context) ->
  kernel_interrupt_nesting_agrees state.(SchedState).(isRunning)
    (flag_pend_caller_view caller).(os_execution_context) state.(IntrState) ->
  (state.(SchedState).(isRunning) = true ->
    (kernel_interrupt_depth (flag_pend_caller_view caller).(os_execution_context) < 255)%nat) ->
  flag_pend_exception_stack_source boundary (flag_pend_caller_view caller) inner before saved ->
  kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg state) saved after ->
  flag_pend_early_domain i pgrp mode (armv7a_irq_entry_counter_state state) ->
  flag_pend_entry_source environment critical boundary sg linked local
    (FlagPendInterruptCaller inner (flag_pend_caller_active_key caller)) call 192 i pgrp mode
    (armv7a_irq_entry_counter_state state)
    (flag_pend_exception_frame boundary (flag_pend_caller_view caller) inner ** frame) after
| FlagPendEntrySequential : forall
  (sequential : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  root_local root_call root_mask root_i root_pgrp root_mode root_state root_frame root_heap
  local previous mask i pgrp mode state frame before after,
  flag_pend_entry_source environment critical boundary sg linked root_local (FlagPendTaskCaller root_call)
    root_call root_mask root_i root_pgrp root_mode root_state root_frame root_heap ->
  flag_pend_linked_prefix environment critical sg linked FlagPendLinkedCodeSource
    (FlagPendTaskCaller root_call) root_call root_state (FlagPendTaskCaller previous) previous state
    (flag_pend_call_world environment root_local sg root_call root_mask root_state ** root_frame)
    root_heap
    (coq_prop (task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin) /\
      flag_pend_source_domain sg previous i pgrp mode state) &&
      (flag_pend_call_world environment local sg previous mask state ** frame)) before ->
  kernel_sequential_call_source sequential previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before after ->
  flag_pend_entry_source environment critical boundary sg linked local
    (FlagPendTaskCaller (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation)))
    (kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation)) mask i pgrp mode
    (flag_sequential_registered_state previous state) frame after
| FlagPendEntryInterrupt : forall local view active call mask i pgrp mode state frame heap
    origin input first_heap,
  flag_pend_linked_prefix environment critical sg linked FlagPendLinkedCodeSource
    (FlagPendInterruptCaller origin active) call input (FlagPendInterruptCaller view active) call state
    (kernel_execution_view_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) origin mask **
     kernel_continuation_inv environment.(task_stack_call_continuations)
       kernel_program_fields_inv local sg active input ** frame)
    first_heap
    (coq_prop (flag_pend_interrupt_source view state /\ flag_pend_early_domain i pgrp mode state) &&
      (flag_pend_caller_world environment local sg (FlagPendInterruptCaller view active) mask state ** frame)) heap ->
  flag_pend_entry_source environment critical boundary sg linked local
    (FlagPendInterruptCaller origin active) call mask i pgrp mode input frame first_heap ->
  flag_pend_entry_source environment critical boundary sg linked local
    (FlagPendInterruptCaller view active) call mask i pgrp mode state frame heap.

Lemma flag_pend_entry_source_resources : forall environment critical boundary sg linked
  local caller call mask i pgrp mode state frame heap,
  flag_pend_entry_source environment critical boundary sg linked local caller call mask i pgrp mode state frame heap ->
  (coq_prop (flag_pend_caller_source sg caller call i pgrp mode state) &&
    (flag_pend_caller_world environment local sg caller mask state ** frame)) heap.
Proof.
  intros environment critical boundary sg linked local caller call mask i pgrp mode state frame heap Hsource.
  induction Hsource.
  - destruct (flag_pend_initial_entry_source_resources _ _ _ _ _ _ _ _ H) as [[Hentry [Hidle Hnonidle]] Hworld].
    split; [|exact Hworld]. split; [reflexivity|].
    intros Hp Hn Hl image Hi Hty Hmode; exact (conj Hentry (conj Hidle Hnonidle)).
  - split; [|exact H3]. split; [reflexivity|].
    apply flag_pend_early_domain_source; exact H2.
  - destruct (flag_pend_first_irq_source_resources _ _ _ _ _ _ _ H) as [[Hinterrupt Hnest] Hworld].
    split; [|exact Hworld]. apply flag_pend_early_interrupt_source; [exact Hinterrupt|].
    right; left; exact Hnest.
  - destruct IHHsource as [Hcaller Hworld].
    destruct (flag_pend_exception_entry_resources environment boundary local sg caller inner handler mask state
      before saved after frame H0 H1 H2 H3 H4 Hworld) as [Hinterrupt Hafter].
    split; [apply flag_pend_early_interrupt_source; assumption|exact Hafter].
  - destruct (proj2 (flag_pend_linked_prefix_resources
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)) as [[Hlive Hdomain] Hworld].
    destruct (flag_pend_sequential_owned_world environment sequential local sg previous state mask
      before after frame Hlive H0 Hworld) as [Hmemory Hafter].
    split; [|exact Hafter]. split; [reflexivity|].
    apply flag_pend_sequential_source_domain; exact Hdomain.
  - destruct (proj2 (flag_pend_linked_prefix_resources
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)) as [[Hinterrupt Hearly] Hworld].
    split; [apply flag_pend_early_interrupt_source; assumption|exact Hworld].
Qed.

Definition flag_pend_owned_input environment critical boundary local sg linked caller call mask
  i pgrp requested mode delay perr before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) (frame : Assertion) : Assertion :=
  fun heap =>
    flag_pend_entry_source environment critical boundary sg linked local caller call mask i pgrp mode before
      ((perr # UChar |->_) ** frame) heap /\
    sg.(osKernelConfig) = selected_kernel_configuration /\
    (pgrp = 0 \/ (0 <= i < sg.(osKernelConfig).(cfgMaxFlags) /\ pgrp = flag_pool_addr sg i)) /\
    0 <= requested < 65536 /\ 0 <= mode < 256 /\ 0 <= delay < 4294967296 /\
    flag_pend_caller_safe environment critical sg caller call mask i pgrp requested mode delay before X.

Lemma flag_pend_owned_input_open : forall environment critical boundary local sg linked caller call mask
  i pgrp requested mode delay perr before X frame,
  flag_pend_owned_input environment critical boundary local sg linked caller call mask
    i pgrp requested mode delay perr before X frame |--
  coq_prop (flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode delay before X) &&
    (flag_pend_caller_world environment local sg caller mask before ** (perr # UChar |->_) ** frame).
Proof.
  intros environment critical boundary local sg linked caller call mask i pgrp requested mode delay perr before X frame
    heap [Hsource Hargs].
  destruct (flag_pend_entry_source_resources _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsource) as [Hentry Hworld].
  assert (Hpublic : flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode delay before X).
  { unfold flag_pend_public_entry; tauto. }
  assert (Horder : flag_pend_caller_world environment local sg caller mask before **
    ((perr # UChar |->_) ** frame) |--
    coq_prop (flag_pend_public_entry environment critical sg caller call mask i pgrp requested mode delay before X) &&
    (flag_pend_caller_world environment local sg caller mask before **
      (perr # UChar |->_) ** frame)) by entailer!.
  exact (Horder heap Hworld).
Qed.


(** Facts established at the actual C branch before Block. The satisfaction
    observation uses the original normalized mode and the acquired image;
    it is not a new public guard. *)
Definition flag_pend_first_unsatisfied sg image requested wait_type : Prop :=
  exists mode,
    decode_flag_wait_mode sg.(osKernelConfig) (Z.land wait_type 127) = Some mode /\
    flag_wait_satisfied mode
      (flag_ready_bits sg.(osKernelConfig) image.(flagImageBits) requested mode)
      requested = false.

Definition flag_pend_block_source_facts sg original call state : Prop :=
  UCOS2_state_inv sg state /\ flag_pend_current_ready call state /\
  task_idle_ready sg state.(TskState) /\ flag_pend_non_idle_at sg original state /\
  flag_pend_running_available call state.

(** The old status and registration remain pure observations of reacquired
    while C temporarily stores PendOK in the still-linked timeout node. *)
Definition flag_pend_error_source_facts sg original call node state tid task : Prop :=
  UCOS2_state_inv sg state /\
  flag_pend_current_binding state tid task /\
  flag_pend_current_ready call state /\
  flag_pend_running_available call state /\
  flag_pend_wait_outcome original node state /\
  flag_active_waiting_registration original node call state /\
  encode_pend_status task.(statPend) <> 0.

Definition flag_pend_timeout_waiter_binding original node tid waiter : Prop :=
  waiter.(flagNodeAddr) = node /\ waiter.(flagTask) = tid /\
  task_stack_key original.(os_sched_call_stack) =
    (waiter.(flagTask), waiter.(flagTaskGeneration)).


Lemma flag_pend_fresh_ready_task_stage : forall original call state,
  flag_active_fresh_registration original call state ->
  flag_pend_current_ready call state -> flag_pend_running_available call state ->
  flag_pend_task_stage call state.
Proof.
  intros original call state [node [Hfields Hnode]]
    [current [Hready Hcurrentgen]] [Hrunning Havailable].
  destruct Hfields as [Hsame [Horigin [Hlookup [Hgen [Hactive Hclear]]]]].
  destruct Hsame as [Hinvocation [Hcallorigin Hstack]].
  assert (Horigin_call : call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration)).
  { rewrite Hcallorigin, Hstack; exact Horigin. }
  assert (Hnode_eq : current = node).
  { destruct Hready as [Hcurrent _]; rewrite Hstack in Hcurrent; congruence. }
  subst current.
  unfold flag_pend_task_stage; split; [exact Horigin_call|].
  split; [exact Hrunning|]. split.
  - unfold kernel_call_stack_available in Havailable; rewrite Horigin_call in Havailable; exact Havailable.
  - exists node; split; [exact Hready|]. split; [exact Hcurrentgen|].
    exact (conj Hnode Hclear).
Qed.


(** Keep the full endpoint observation of the same existing completed call.
    This does not add a guarantee to the primitive or select a new heap. *)
Lemma flag_pend_caller_completed_source_endpoints : forall operation environment critical sg linked caller original before
  input first_heap returned_caller returned current after_heap output,
  flag_pend_caller_completed_source operation environment critical sg linked caller original before input first_heap
    returned_caller returned current after_heap output ->
  flag_pend_call_endpoint_observations environment sg caller original before returned current.
Proof.
  intros operation environment critical sg linked caller original before input first_heap
    returned_caller returned current after_heap output Hsource.
  exact (proj1 (proj2 (flag_pend_linked_prefix_resources
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsource))).
Qed.

Lemma flag_pend_caller_save_output_endpoints : forall environment critical local active sg linked caller original mask before before_heap saved,
  flag_pend_caller_save_output environment critical local active sg linked caller original mask before before_heap saved |--
  EX returned_caller returned acquired next_local,
    coq_prop (flag_pend_caller_save_observation environment critical sg caller original returned_caller returned
      mask saved before acquired /\ interrupt_saved_value mask saved /\
      flag_pend_call_source_observations environment sg caller original before returned acquired /\
      flag_pend_call_endpoint_observations environment sg caller original before returned acquired) &&
    flag_pend_caller_restore_input environment critical next_local active sg returned_caller returned saved acquired acquired.
Proof.
  intros environment critical local active sg linked caller original mask before before_heap saved heap
    [returned_caller [returned [acquired [next_local [Hsource [Hsaved [Hbefore [Hafter Hcompleted]]]]]]]].
  exists returned_caller, returned, acquired, next_local; split; [|exact Hafter].
  split; [exact Hsource|]. split; [exact Hsaved|]. split.
  - eapply flag_pend_caller_completed_source_observations; exact Hcompleted.
  - eapply flag_pend_caller_completed_source_endpoints; exact Hcompleted.
Qed.

Lemma flag_pend_caller_restore_output_endpoints : forall environment critical local active sg linked caller original saved acquired released before_heap,
  flag_pend_caller_restore_output environment critical local active sg linked caller original saved acquired released before_heap |--
  EX returned_caller returned current next_local,
    coq_prop (flag_pend_caller_restore_observation environment critical sg caller original returned_caller returned released current /\
      flag_pend_call_source_observations environment sg caller original released returned current /\
      flag_pend_call_endpoint_observations environment sg caller original released returned current) &&
    flag_pend_caller_save_input environment critical next_local active sg returned_caller returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical local active sg linked caller original saved acquired released before_heap heap
    [returned_caller [returned [current [next_local [Hsource [Hbefore [Hafter Hcompleted]]]]]]].
  exists returned_caller, returned, current, next_local; split; [|exact Hafter].
  split; [exact Hsource|]. split.
  - eapply flag_pend_caller_completed_source_observations; exact Hcompleted.
  - eapply flag_pend_caller_completed_source_endpoints; exact Hcompleted.
Qed.

(** The public caller consumes the actual task-return history and the SAME
    returned/current/local resource tuple.  No arbitrary linked event is built. *)
Lemma flag_pend_task_sched_output_open : forall environment critical active sg original mask before,
  SchedulerPhaseCandidate.os_sched_task_history_return_post environment critical active sg original mask before |--
  EX returned current next_local,
    coq_prop (flag_pend_sched_return_observation environment critical sg original mask before returned current) &&
    (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_fields_inv
      next_local sg (task_stack_call_active_key returned) returned mask current ** active returned current).
Proof.
  intros environment critical active sg original mask before heap Hpost.
  destruct Hpost as [returned [current [next_local [Hfacts Howned]]]].
  destruct Hfacts as [Hhistory [Hsame [Hsource [Hready [Hnormal Hcontrol]]]]].
  exists returned, current, next_local; split; [|exact Howned].
  unfold flag_pend_sched_return_observation.
  split; [exact Hhistory|]. split; [exact Hsame|]. split; [exact Hsource|]. split.
  - exact Hready.
  - exact (flag_pend_normal_return_control sg original before returned current Hnormal Hcontrol).
Qed.

End PendPhaseCandidate.
