Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_frame_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A source-event list for the EXISTING finite handler registry. Every
    label below is consumed by an actual body execution and by the concrete
    state update. It is not an extra BSP contract or an output invariant. *)
Definition mutex_del_restore_client_state (kind : RestoreHandlerClientKind)
  (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  match kind with
  | RestoreHandlerIntEnter => os_int_enter_state state
  | RestoreHandlerIntExitNoSchedule => os_int_exit_counter_state state.(SchedState).(isRunning) state
  end.

Fixpoint mutex_del_restore_clients_state (clients : list RestoreHandlerClientKind)
  (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  match clients with
  | [] => state
  | kind :: rest => mutex_del_restore_clients_state rest (mutex_del_restore_client_state kind state)
  end.

Inductive mutex_del_restore_handler_trace {Local}
  (local_step : RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop)
  (sg : StableGlobVars)
  : list RestoreHandlerClientKind -> RestoreHandlerCursor Local -> model ->
    RestoreHandlerCursor Local -> model -> Prop :=
| MutexDelRestoreHandlerReturn : forall cursor heap,
    mutex_del_restore_handler_trace local_step sg [] cursor heap cursor heap
| MutexDelRestoreHandlerLocal : forall clients cursor before middle_cursor middle returned_cursor after,
    local_step cursor before middle_cursor middle ->
    mutex_del_restore_handler_trace local_step sg clients middle_cursor middle returned_cursor after ->
    mutex_del_restore_handler_trace local_step sg clients cursor before returned_cursor after
| MutexDelRestoreHandlerKernel : forall clients cursor before call middle returned_cursor after,
    cursor.(restore_handler_pc) = call.(restore_handler_kernel_call_pc) ->
    restore_handler_client_execution sg call.(restore_handler_kernel_kind) before middle ->
    mutex_del_restore_handler_trace local_step sg clients
      (restore_handler_return_cursor cursor call.(restore_handler_kernel_return_pc)) middle returned_cursor after ->
    mutex_del_restore_handler_trace local_step sg (call.(restore_handler_kernel_kind) :: clients)
      cursor before returned_cursor after.

Lemma mutex_del_restore_handler_execution_trace : forall Local local_step sg cursor before returned_cursor after,
  @restore_handler_execution Local local_step sg cursor before returned_cursor after ->
  exists clients, mutex_del_restore_handler_trace local_step sg clients cursor before returned_cursor after.
Proof.
  intros Local local_step sg cursor before returned_cursor after Hrun; induction Hrun.
  - exists []; constructor.
  - destruct IHHrun as [clients Htrace]; exists clients; econstructor; eassumption.
  - destruct IHHrun as [clients Htrace]; exists (call.(restore_handler_kernel_kind) :: clients).
    econstructor; eassumption.
Qed.

Lemma mutex_del_restore_clients_task_sched_eq : forall clients state,
  (mutex_del_restore_clients_state clients state).(TskState) = state.(TskState) /\
  (mutex_del_restore_clients_state clients state).(SchedState) = state.(SchedState).
Proof.
  induction clients as [|kind rest IH]; intros state; [split; reflexivity|].
  cbn [mutex_del_restore_clients_state].
  specialize (IH (mutex_del_restore_client_state kind state)); destruct kind; exact IH.
Qed.

(** The pure event list's effect is justified on the exact physical trace.
    Private steps use the existing frame law; kernel steps use their real
    source/heap certificate. The BSP never supplies the abstract state. *)
Lemma mutex_del_restore_handler_trace_preserves_world : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus Local
  (private : RestoreHandlerCall -> Local -> Assertion) local_step normal_return
  (bsp : RestoreHandlerContract private local_step normal_return)
  sg clients cursor before returned_cursor after (frame : Assertion),
  mutex_del_restore_handler_trace local_step sg clients cursor before returned_cursor after ->
  forall state,
  (armv7a_continuation_world abi focus (kernel_program_inv sg) state **
    (private cursor.(restore_handler_current_call) cursor.(restore_handler_local) ** frame)) before ->
  (armv7a_continuation_world abi focus (kernel_program_inv sg)
     (mutex_del_restore_clients_state clients state) **
    (private returned_cursor.(restore_handler_current_call) returned_cursor.(restore_handler_local) ** frame)) after.
Proof.
  intros external platform port abi focus Local private local_step normal_return bsp sg clients cursor before
    returned_cursor after frame Htrace; induction Htrace; intros state Hpre.
  - exact Hpre.
  - apply IHHtrace.
    assert (Horder : armv7a_continuation_world abi focus (kernel_program_inv sg) state **
        (private cursor.(restore_handler_current_call) cursor.(restore_handler_local) ** frame) |--
      private cursor.(restore_handler_current_call) cursor.(restore_handler_local) **
        (armv7a_continuation_world abi focus (kernel_program_inv sg) state ** frame)) by entailer!.
    pose proof (restore_handler_local_resources _ _ _ bsp _ _ _ _ _ H (Horder before Hpre)) as Hmiddle.
    assert (Hback : private middle_cursor.(restore_handler_current_call) middle_cursor.(restore_handler_local) **
        (armv7a_continuation_world abi focus (kernel_program_inv sg) state ** frame) |--
      armv7a_continuation_world abi focus (kernel_program_inv sg) state **
        (private middle_cursor.(restore_handler_current_call) middle_cursor.(restore_handler_local) ** frame))
      by entailer!.
    exact (Hback middle Hmiddle).
  - destruct (restore_handler_client_execution_source external platform port abi focus sg
      _ state before middle _ H0 Hpre) as [middle_state Hsource].
    pose proof (restore_handler_client_preserves_world external platform port abi focus sg
      _ state before middle_state middle _ Hsource Hpre) as Hmiddle.
    assert (Heffect : middle_state = mutex_del_restore_client_state call.(restore_handler_kernel_kind) state)
      by (destruct Hsource; reflexivity).
    cbn [mutex_del_restore_clients_state]; rewrite <- Heffect; apply IHHtrace; exact Hmiddle.
Qed.

(** These are source-side first-level safety obligations already required
    by the checked IRQ entry producer. They are NOT an ABI field, and no
    old public Require is strengthened to supply them. *)
Definition mutex_del_restore_irq_input (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (handler : OsIntExitCallContext) (saved : Armv7aContinuation)
  (node : TaskAbstractState) (publication : nat) (kind : MutexDelRestoreExitKind) : Prop :=
  let call := handler.(os_int_exit_interrupted_call) in
  state.(SchedState).(isRunning) = true /\ state.(IntrState).(intNesting) = 0 /\
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) /\
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) /\
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) /\
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) /\
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) /\
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) saved.(armv7a_continuation_sp) /\
  (kind = MutexDelRestoreSamePriority -> state.(SchedState).(readyList) <> []).

Definition mutex_del_restore_irq_parked (state : UCOS2_Verify_State)
  (handler : OsIntExitCallContext) (saved : Armv7aContinuation) : UCOS2_Verify_State :=
  armv7a_irq_live_parked_state state handler.(os_int_exit_interrupted_call)
    saved.(armv7a_continuation_sp) saved.(armv7a_continuation_fragments).

Definition mutex_del_restore_irq_state (state : UCOS2_Verify_State)
  (handler : OsIntExitCallContext) (saved : Armv7aContinuation)
  (clients : list RestoreHandlerClientKind) (kind : MutexDelRestoreExitKind) : UCOS2_Verify_State :=
  os_int_exit_wrapper_restored_state
    (mutex_del_restore_exit_state kind
      (mutex_del_restore_clients_state clients (mutex_del_restore_irq_parked state handler saved)))
    handler.(os_int_exit_interrupted_call).(os_sched_call_stack).

Lemma mutex_del_restore_handler_normal_return_trace : forall Local private local_step normal_return
  (bsp : @RestoreHandlerContract Local private local_step normal_return)
  sg cursor before returned_cursor after,
  normal_return sg cursor before returned_cursor after ->
  exists clients,
    returned_cursor.(restore_handler_current_call) = cursor.(restore_handler_current_call) /\
    returned_cursor.(restore_handler_pc) = cursor.(restore_handler_current_call).(restore_handler_return_word) /\
    mutex_del_restore_handler_trace local_step sg clients cursor before returned_cursor after.
Proof.
  intros Local private local_step normal_return bsp sg cursor before returned_cursor after Hreturn.
  destruct (restore_handler_return_refinement _ _ _ bsp _ _ _ _ _ Hreturn) as [Hcall [Hpc Hrun]].
  destruct (mutex_del_restore_handler_execution_trace _ _ _ _ _ _ _ Hrun) as [clients Htrace].
  exists clients; split; [exact Hcall|]. split; assumption.
Qed.

(** Real IRQ return to the BX cut, without executing BX yet. Its output
    is again the original ABI's ordinary owned execution, one program
    world, and the same inactive handler stack. The temporary equality
    index is consumed by take; the now-empty focus is discharged to emp.
    This is the resource boundary actually used by the finite call below. *)
Lemma mutex_del_restore_irq_returns_owned : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state handler saved node publication clients kind
  Local local_step normal_return
  (bsp : RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    local_step normal_return)
  before saved_heap handler_heap handler_cursor returned_cursor returned_heap exit_cursor exit_heap exited_heap after
  (frame : Assertion),
  mutex_del_restore_irq_input sg state handler saved node publication kind ->
  (kernel_call_execution_owned external platform handler.(os_int_exit_interrupted_call)
     handler.(os_int_exit_interrupted_mask) **
   (kernel_program_inv sg state **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  kernel_heap_execution
    (armv7a_irq_live_entry_writes sg state handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_sp)) saved_heap handler_heap ->
  mutex_del_restore_handler_trace local_step sg clients handler_cursor handler_heap returned_cursor returned_heap ->
  local_step returned_cursor returned_heap exit_cursor exit_heap ->
  mutex_del_restore_exit_execution sg kind exit_heap exited_heap ->
  armv7a_continuation_restore_reads saved exited_heap ->
  armv7a_restore_transition abi handler saved exited_heap after ->
  saved.(armv7a_continuation_call) = Some handler.(os_int_exit_interrupted_call) /\
  saved.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
  saved.(armv7a_continuation_stack) = handler.(os_int_exit_interrupted_call).(os_sched_call_stack) /\
  armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = handler.(os_int_exit_interrupted_mask) /\
  armv7a_irq_restore_pointer_reads sg exited_heap
    (task_slot_addr sg handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot))
    saved.(armv7a_continuation_sp) /\
  (kernel_call_execution_owned external platform
     (armv7a_continuation_resumed_call saved handler.(os_int_exit_interrupted_call))
     handler.(os_int_exit_interrupted_mask) **
   (kernel_program_inv sg (mutex_del_restore_irq_state state handler saved clients kind) **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) after.
Proof.
  intros external platform port abi sg state handler saved node publication clients kind Local local_step normal_return
    bsp before saved_heap handler_heap handler_cursor returned_cursor returned_heap exit_cursor exit_heap exited_heap after
    frame Hsafe Hpre Hsave Hentry Htrace Hwrapper Hexit Hreads Hrestore.
  destruct Hsafe as [Hrunning [Hnesting [Hcurrent [Hnode [Hid [Hgen [Hnone [Haddress [Hregion [Hgeometry
    [Hpublication [Hsp Hready]]]]]]]]]]]].
  set (call := handler.(os_int_exit_interrupted_call)) in *.
  set (focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc) saved.(armv7a_continuation_lr)).
  set (retained := mutex_del_retained_continuation_abi external platform port abi saved).
  set (parked := mutex_del_restore_irq_parked state handler saved).
  set (body_state := mutex_del_restore_clients_state clients parked).
  set (exited := mutex_del_restore_exit_state kind body_state).
  assert (Hopen : kernel_call_execution_owned external platform call handler.(os_int_exit_interrupted_mask) **
      (kernel_program_inv sg state **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) |--
    os_int_exit_frame_save_pre external platform handler **
      (armv7a_continuation_world abi focus (kernel_program_inv sg) state ** frame)).
  { rewrite kernel_program_inv_split_unmap, kernel_program_continuation_world_split_unmap.
    sep_apply_l_atomic (armv7a_continuation_world_open_absent external platform port abi focus sg state Hnone).
    unfold os_int_exit_frame_save_pre, call; entailer!. }
  destruct (mutex_del_irq_source_deposits_retained_descriptor external platform port abi sg state node handler saved
    publication frame before saved_heap Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp (Hopen before Hpre) Hsave)
    as [produced [Hcall [Hpc [Hsaved_mask [Hwrites [Hentry_run Hhandler]]]]]].
  assert (produced = handler_heap) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced.
  assert (Hhandler_pre : (armv7a_continuation_world retained focus (kernel_program_inv sg) parked **
    (mutex_del_restore_handler_owner platform port handler ** frame)) handler_heap).
  { assert (Horder : armv7a_continuation_world retained focus (kernel_program_inv sg) parked **
        (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
         os_int_exit_context_resources port handler ** frame) |--
      armv7a_continuation_world retained focus (kernel_program_inv sg) parked **
        (mutex_del_restore_handler_owner platform port handler ** frame)).
    { unfold mutex_del_restore_handler_owner; entailer!. }
    exact (Horder handler_heap Hhandler). }
  pose proof (mutex_del_restore_handler_trace_preserves_world external platform port retained focus Local
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    local_step normal_return bsp sg clients handler_cursor handler_heap returned_cursor returned_heap frame Htrace
    parked Hhandler_pre) as Hbody.
  assert (Hprivate_first : armv7a_continuation_world retained focus (kernel_program_inv sg) body_state **
      (mutex_del_restore_handler_owner platform port handler ** frame) |--
    mutex_del_restore_handler_owner platform port handler **
      (armv7a_continuation_world retained focus (kernel_program_inv sg) body_state ** frame)) by entailer!.
  pose proof (restore_handler_local_resources _ _ _ bsp returned_cursor returned_heap exit_cursor exit_heap _
    Hwrapper (Hprivate_first returned_heap Hbody)) as Hmasked.
  assert (Hworld_first : mutex_del_restore_handler_owner platform port handler **
      (armv7a_continuation_world retained focus (kernel_program_inv sg) body_state ** frame) |--
    armv7a_continuation_world retained focus (kernel_program_inv sg) body_state **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)).
  { unfold mutex_del_restore_handler_owner; entailer!. }
  destruct (mutex_del_restore_clients_task_sched_eq clients parked) as [Ht Hs].
  assert (Hbody_ready : kind = MutexDelRestoreSamePriority -> body_state.(SchedState).(readyList) <> []).
  { intros Hkind; unfold body_state; rewrite Hs; unfold parked, mutex_del_restore_irq_parked,
      armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, os_sched_save_current_sp,
      armv7a_irq_entry_counter_state; rewrite Hrunning; exact (Hready Hkind). }
  pose proof (mutex_del_restore_exit_preserves_world external platform port retained focus sg kind body_state _
    exit_heap exited_heap Hbody_ready (Hworld_first exit_heap Hmasked) Hexit) as Hexit_world.
  destruct (mutex_del_restore_parked_wrapper_binding state call saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) node Hrunning Hcurrent Hnode) as [Hpark_current [Hpark_node Hparked]].
  assert (Hexit_current : exited.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold exited, mutex_del_restore_exit_state; destruct kind;
      cbn [os_int_exit_selection_state os_int_exit_counter_state replace_IntrS replace_SchedS SchedState
        sched_refresh_high curTaskID]; unfold body_state; rewrite Hs; exact Hpark_current. }
  assert (Hexit_node : exited.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node saved.(armv7a_continuation_sp))).
  { unfold exited, mutex_del_restore_exit_state; destruct kind;
      cbn [os_int_exit_selection_state os_int_exit_counter_state replace_IntrS replace_SchedS TskState];
      unfold body_state; rewrite Ht; exact Hpark_node. }
  assert (Hexit_parked : exited.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { unfold exited, mutex_del_restore_exit_state; destruct kind;
      cbn [os_int_exit_selection_state os_int_exit_counter_state replace_IntrS replace_SchedS TskState];
      unfold body_state; rewrite Ht; exact Hparked. }
  destruct (mutex_del_wrapper_takes_retained_descriptor external platform port abi saved focus sg exited
    call.(os_sched_call_stack) saved.(armv7a_continuation_fragments)
    (task_set_saved_sp node saved.(armv7a_continuation_sp)) _ exited_heap
    Hexit_current Hexit_node Hexit_parked eq_refl Haddress Hexit_world)
    as [Hpointers [Hbinding [Hfocused [Hstack [Hfragments Howned]]]]].
  assert (Horder : armv7a_continuation_world retained focus (kernel_program_inv sg)
      (os_int_exit_wrapper_restored_state exited call.(os_sched_call_stack)) **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion) saved.(armv7a_continuation_fragments) **
    armv7a_dormant_continuation abi saved **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion) saved.(armv7a_continuation_fragments) **
    armv7a_dormant_continuation abi saved **
    (armv7a_continuation_world retained focus (kernel_program_inv sg)
      (os_int_exit_wrapper_restored_state exited call.(os_sched_call_stack)) ** frame)) by entailer!.
  destruct (armv7a_restore_call_resources external platform port abi handler saved call _ exited_heap after
    Hcall Hreads (Horder exited_heap Howned) Hrestore) as [Hmemory Hresumed].
  assert (Habsent : (os_int_exit_wrapper_restored_state exited call.(os_sched_call_stack)).(TskState).(parkedTaskStacks)
    (armv7a_call_focus_key focus) = None).
  { unfold os_int_exit_wrapper_restored_state, focus, armv7a_call_focus_key, armv7a_call_focus.
    cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks]; apply task_stack_take_lookup. }
  assert (Hclose : kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved call)
      (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (armv7a_continuation_world retained focus (kernel_program_inv sg)
      (os_int_exit_wrapper_restored_state exited call.(os_sched_call_stack)) ** frame) |--
    kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved call)
      handler.(os_int_exit_interrupted_mask) **
    (kernel_program_inv sg (mutex_del_restore_irq_state state handler saved clients kind) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)).
  { unfold armv7a_continuation_world, armv7a_parked_continuations.
    sep_apply_l_atomic (armv7a_parked_focus_absent_emp external platform port retained focus _ Habsent).
    rewrite Hsaved_mask; unfold mutex_del_restore_irq_state, exited, body_state, parked, call; entailer!. }
  split; [exact Hcall|]. split; [exact Hpc|]. split; [exact Hstack|]. split; [exact Hsaved_mask|].
  split; [exact Hpointers|exact (Hclose after Hresumed)].
Qed.

Section RestoreCallComposition.
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (abi : Armv7aContinuationABI external platform port)
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

(** An explicit first-level source-and-safety cut, not an assumption that
    every public Restore has this shape. Its OS state is computed by the
    registered source effects; no resource postcondition is stored here.
    The actual BSP return and its concrete trace share all heap endpoints.
    The trace witness is supplied by the existing normal-return refinement
    lemma, not a stronger external contract. *)
Inductive mutex_del_restore_irq_execution (mask bx_pc return_word : Z)
  : OsSchedCallContext -> UCOS2_Verify_State -> model ->
    OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| MutexDelRestoreIRQExecution : forall state handler saved node publication clients kind
    before saved_heap handler_heap handler_cursor returned_cursor returned_heap exit_cursor exit_heap exited_heap after,
    mutex_del_restore_irq_input sg state handler saved node publication kind ->
    handler.(os_int_exit_interrupted_pc) = bx_pc ->
    handler.(os_int_exit_interrupted_mask) = mask ->
    saved.(armv7a_continuation_lr) = return_word ->
    handler.(os_int_exit_handler_stack) = handler_stack ->
    handler.(os_int_exit_handler_fragments) = handler_fragments ->
    armv7a_save_transition abi handler saved before saved_heap ->
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
    mutex_del_restore_irq_execution mask bx_pc return_word
      handler.(os_int_exit_interrupted_call) state before
      (armv7a_continuation_resumed_call saved handler.(os_int_exit_interrupted_call))
      (mutex_del_restore_irq_state state handler saved clients kind) after.

(** Repeated interrupts are finite because this is a supplied normally
    returning execution, not because an interrupt bound is postulated.
    Each step saves/takes/restores its own actual descriptor; only the
    original public BX location and raw LR are shared across iterations. *)
Inductive mutex_del_restore_irqs_execution (mask bx_pc return_word : Z)
  : OsSchedCallContext -> UCOS2_Verify_State -> model ->
    OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| MutexDelRestoreIRQsDone : forall call state heap,
    mutex_del_restore_irqs_execution mask bx_pc return_word call state heap call state heap
| MutexDelRestoreIRQsNext : forall call state before middle_call middle_state middle returned final after,
    mutex_del_restore_irq_execution mask bx_pc return_word call state before middle_call middle_state middle ->
    mutex_del_restore_irqs_execution mask bx_pc return_word middle_call middle_state middle returned final after ->
    mutex_del_restore_irqs_execution mask bx_pc return_word call state before returned final after.

Lemma mutex_del_restore_irq_execution_resources : forall mask bx_pc return_word call state before returned final after
  (frame : Assertion),
  mutex_del_restore_irq_execution mask bx_pc return_word call state before returned final after ->
  (kernel_call_execution_owned external platform call mask **
   (kernel_program_inv sg state ** task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  (kernel_call_execution_owned external platform returned mask **
   (kernel_program_inv sg final ** task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros mask bx_pc return_word call state before returned final after frame Hrun Hpre.
  destruct Hrun as [state handler saved node publication clients kind before saved_heap handler_heap handler_cursor
    returned_cursor returned_heap exit_cursor exit_heap exited_heap after Hsafe Hpc Hmask Hlr Hstack Hfragments
    Hsave Hentry Hreturn Hsame Hreturn_pc Htrace Hwrapper Hexit Hreads Hrestore].
  assert (Hinput : (kernel_call_execution_owned external platform handler.(os_int_exit_interrupted_call)
      handler.(os_int_exit_interrupted_mask) **
    (kernel_program_inv sg state ** task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) before).
  { rewrite Hmask, Hstack, Hfragments; exact Hpre. }
  destruct (mutex_del_restore_irq_returns_owned external platform port abi sg state handler saved node publication
    clients kind Local (local_step handler) (normal_return handler) (handler_contract handler)
    before saved_heap handler_heap handler_cursor returned_cursor returned_heap exit_cursor exit_heap exited_heap after
    frame Hsafe Hinput Hsave Hentry Htrace Hwrapper Hexit Hreads Hrestore)
    as [Hcall [Hsaved_pc [Hsaved_stack [Hsaved_mask [Hpointers Hpost]]]]].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsaved_stack|].
  rewrite Hmask, Hstack, Hfragments in Hpost; exact Hpost.
Qed.

Lemma mutex_del_restore_irqs_execution_resources : forall mask bx_pc return_word call state before returned final after
  (frame : Assertion),
  mutex_del_restore_irqs_execution mask bx_pc return_word call state before returned final after ->
  (kernel_call_execution_owned external platform call mask **
   (kernel_program_inv sg state ** task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  (kernel_call_execution_owned external platform returned mask **
   (kernel_program_inv sg final ** task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros mask bx_pc return_word call state before returned final after frame Hrun; induction Hrun; intros Hpre.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|exact Hpre].
  - destruct (mutex_del_restore_irq_execution_resources _ _ _ _ _ _ _ _ _ _ H Hpre)
      as [Hi [Ho [Hs Hmiddle]]].
    destruct (IHHrun Hmiddle) as [Hi' [Ho' [Hs' Hpost]]].
    split; [congruence|]. split; [congruence|]. split; [congruence|exact Hpost].
Qed.

(** Producer for one real completed IRQ in the finite call relation.
    No labelled trace is assumed: the already approved BSP contract
    produces that witness from this SAME actual normal return. The
    constructed execution is immediately consumed for its resource post. *)
Lemma mutex_del_restore_irq_normal_return_resources : forall mask bx_pc return_word state handler saved node publication kind
  before saved_heap handler_heap handler_cursor returned_cursor returned_heap exit_cursor exit_heap exited_heap after
  (frame : Assertion),
  mutex_del_restore_irq_input sg state handler saved node publication kind ->
  handler.(os_int_exit_interrupted_pc) = bx_pc ->
  handler.(os_int_exit_interrupted_mask) = mask ->
  saved.(armv7a_continuation_lr) = return_word ->
  handler.(os_int_exit_handler_stack) = handler_stack ->
  handler.(os_int_exit_handler_fragments) = handler_fragments ->
  (kernel_call_execution_owned external platform handler.(os_int_exit_interrupted_call) mask **
   (kernel_program_inv sg state ** task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  kernel_heap_execution
    (armv7a_irq_live_entry_writes sg state handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot)
      saved.(armv7a_continuation_sp)) saved_heap handler_heap ->
  normal_return handler sg handler_cursor handler_heap returned_cursor returned_heap ->
  local_step handler returned_cursor returned_heap exit_cursor exit_heap ->
  mutex_del_restore_exit_execution sg kind exit_heap exited_heap ->
  armv7a_continuation_restore_reads saved exited_heap ->
  armv7a_restore_transition abi handler saved exited_heap after ->
  exists clients,
    mutex_del_restore_irqs_execution mask bx_pc return_word handler.(os_int_exit_interrupted_call) state before
      (armv7a_continuation_resumed_call saved handler.(os_int_exit_interrupted_call))
      (mutex_del_restore_irq_state state handler saved clients kind) after /\
    (kernel_call_execution_owned external platform
       (armv7a_continuation_resumed_call saved handler.(os_int_exit_interrupted_call)) mask **
     (kernel_program_inv sg (mutex_del_restore_irq_state state handler saved clients kind) **
      task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros mask bx_pc return_word state handler saved node publication kind before saved_heap handler_heap handler_cursor
    returned_cursor returned_heap exit_cursor exit_heap exited_heap after frame Hsafe Hpc Hmask Hlr Hstack Hfragments
    Hpre Hsave Hentry Hreturn Hwrapper Hexit Hreads Hrestore.
  destruct (mutex_del_restore_handler_normal_return_trace Local
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    (local_step handler) (normal_return handler) (handler_contract handler) sg handler_cursor handler_heap
    returned_cursor returned_heap Hreturn) as [clients [Hsame [Hreturn_pc Htrace]]].
  assert (Hstep : mutex_del_restore_irq_execution mask bx_pc return_word
    handler.(os_int_exit_interrupted_call) state before
    (armv7a_continuation_resumed_call saved handler.(os_int_exit_interrupted_call))
    (mutex_del_restore_irq_state state handler saved clients kind) after).
  { econstructor; eassumption. }
  destruct (mutex_del_restore_irq_execution_resources _ _ _ _ _ _ _ _ _ _ Hstep Hpre)
    as [Hi [Ho [Hs Hpost]]].
  exists clients; split; [econstructor; [exact Hstep|constructor]|exact Hpost].
Qed.

(** One MSR prefix, zero or more actual ordinary IRQ returns at that SAME
    source BX continuation, then one supplied BX. This composes the real
    resource consumers; it does not classify arbitrary switching returns
    or insert OS facts into an external ABI. The suffix cursor is the
    existing MSR-cut observation record, not a claim that live CPSR equals
    its pre-MSR field throughout handler execution. *)
Lemma mutex_del_restore_call_normal_return : forall critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  call saved entry checkpoint restore_entry cursor before written_cursor released
  returned final resumed final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry ** os_sched_context_resources external call **
   (kernel_program_inv sg checkpoint ** task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor released ->
  mutex_del_restore_irqs_execution (armv7a_irq_fiq_mask saved) (restore_entry + 8)
    cursor.(kernel_restore_lr) call checkpoint released returned final resumed ->
  armv7a_restore_suffix_transition restore written_cursor resumed final_cursor after ->
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (kernel_program_closed platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) final **
   os_sched_context_resources external returned **
   task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros critical arch restore call saved entry checkpoint restore_entry cursor before written_cursor released returned
    final resumed final_cursor after frame Hr0 Hmask Hpre Hprefix Hirqs Hsuffix.
  destruct (armv7a_restore_prefix_releases_critical_region external platform critical arch restore sg call saved entry
    cursor before written_cursor released
    (kernel_program_inv sg checkpoint ** task_stack_fragments_rep handler_stack handler_fragments ** frame)
    Hr0 Hmask Hpre Hprefix) as [Hwritten [Hmemory Howned]].
  destruct (mutex_del_restore_irqs_execution_resources _ _ _ _ _ _ _ _ _ _ Hirqs Howned)
    as [Hi [Ho [Hs Hresumed]]].
  set (written := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Hword : written_cursor.(kernel_restore_msr_word) = Some written) by (rewrite Hwritten; reflexivity).
  assert (Hwritten_mask : armv7a_irq_fiq_mask written = armv7a_irq_fiq_mask saved).
  { unfold written; rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity. }
  rewrite <- Hwritten_mask in Hresumed.
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch restore returned written
    written_cursor resumed final_cursor after
    (kernel_program_inv sg final ** task_stack_fragments_rep handler_stack handler_fragments ** frame)
    Hword Hresumed Hsuffix) as [Hfinal [Hsuffix_memory Hpost]].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|]. split.
  - rewrite Hfinal, Hwritten; reflexivity.
  - assert (Hclose : kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask written) **
      (kernel_program_inv sg final ** task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
      kernel_program_closed platform critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin)
        (armv7a_irq_fiq_mask saved) final ** os_sched_context_resources external returned **
      task_stack_fragments_rep handler_stack handler_fragments ** frame).
    { rewrite kernel_program_closed_equiv, Hwritten_mask; unfold kernel_call_execution_owned; rewrite Hi, Ho; entailer!. }
    exact (Hclose after Hpost).
Qed.

(** The ordinary call owner comes from the existing actual first-entry
    interpretation, not from a numerical invocation or a strengthened Del
    Require. The borrowed stack partition and initial execution are both
    consumed once. The table is carried as the existing program frame. *)
Lemma mutex_del_initial_call_program_resources : forall
  (entry_abi : Armv7aInitialCallABI external platform port abi) state initial fragments,
  armv7a_initial_frame_binding initial ->
  task_stack_fragments_in_range initial.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_current_at state initial.(armv7a_continuation_stack).(stackLeaseSlot)
    initial.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  let call := armv7a_initial_call initial state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  kernel_program_inv sg state ** armv7a_initial_execution abi initial **
    task_stack_fragments_rep initial.(armv7a_continuation_stack).(stackLeaseRegion) fragments |--
  coq_prop (kernel_call_task_source call (armv7a_initial_call_registered initial state)) &&
  (kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask initial.(armv7a_continuation_cpsr)) **
   kernel_program_inv sg (armv7a_initial_call_registered initial state)).
Proof.
  intros entry_abi state initial fragments Hbinding Hgeometry Hcurrent call.
  rewrite !kernel_program_inv_split_unmap.
  pose proof (armv7a_initial_call_register_resources external platform port abi entry_abi sg state initial fragments
    Hbinding Hgeometry Hcurrent) as Hregister.
  cbv zeta in Hregister; sep_apply_l_atomic Hregister; unfold call; entailer!.
Qed.

(** Actual owner-to-caller composition. This is the concrete ordinary
    first-entry / uninterrupted Save / Restore source chain. The caller's
    initial PC, real stack partition and current/live binding are supplied
    by the existing first-entry owner. No intervening arbitrary C body is
    asserted to preserve the heap. In particular this is NOT a proof of
    the complete Del prefix/body or an arbitrary interrupted Save.

    Restore itself admits a finite supplied sequence of ordinary IRQs,
    whose concrete body effects may change the final OS state. The inactive
    handler stack is an input from its actual initialization/execution
    owner and is returned; neither first-entry ABI manufactures it. *)
Lemma mutex_del_initial_save_restore_normal_return : forall critical arch
  (entry_abi : Armv7aInitialCallABI external platform port abi)
  (save_abi : Armv7aSaveSuffixABI external platform critical arch)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  state initial fragments registers before saved_registers saved_heap
  restore_entry cursor written_cursor released returned final resumed final_cursor after (frame : Assertion),
  let call := armv7a_initial_call initial state.(TskState).(taskLifecycle).(taskNextInvocation) fragments in
  let registered := armv7a_initial_call_registered initial state in
  armv7a_initial_frame_binding initial ->
  task_stack_fragments_in_range initial.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_current_at state initial.(armv7a_continuation_stack).(stackLeaseSlot)
    initial.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask initial.(armv7a_continuation_cpsr) ->
  cursor.(kernel_restore_r0) = saved_registers.(kernel_save_r0) ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  ((kernel_program_inv sg state ** armv7a_initial_execution abi initial **
    task_stack_fragments_rep initial.(armv7a_continuation_stack).(stackLeaseRegion) fragments) **
   (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  armv7a_save_suffix_transition save_abi (kernel_save_read_cpsr registers) registered before
    saved_registers registered saved_heap ->
  armv7a_restore_prefix_transition restore cursor saved_heap written_cursor released ->
  mutex_del_restore_irqs_execution (armv7a_irq_fiq_mask saved_registers.(kernel_save_r0)) (restore_entry + 8)
    cursor.(kernel_restore_lr) call registered released returned final resumed ->
  armv7a_restore_suffix_transition restore written_cursor resumed final_cursor after ->
  kernel_call_task_source call registered /\
  kernel_call_save_uninterrupted_execution arch registers registered before saved_registers registered saved_heap /\
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (kernel_program_closed platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) (armv7a_irq_fiq_mask initial.(armv7a_continuation_cpsr)) final **
   os_sched_context_resources external returned **
   task_stack_fragments_rep handler_stack handler_fragments ** frame) after.
Proof.
  intros critical arch entry_abi save_abi restore state initial fragments registers before saved_registers saved_heap
    restore_entry cursor written_cursor released returned final resumed final_cursor after frame call registered
    Hbinding Hgeometry Hcurrent Hreturn Hcpsr Hinitial_mask Hr0 Hmasked Hpre Hsave Hprefix Hirqs Hsuffix.
  assert (Hregister : (kernel_program_inv sg state ** armv7a_initial_execution abi initial **
      task_stack_fragments_rep initial.(armv7a_continuation_stack).(stackLeaseRegion) fragments) **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    coq_prop (kernel_call_task_source call registered) &&
    (kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask initial.(armv7a_continuation_cpsr)) **
      (kernel_program_inv sg registered ** task_stack_fragments_rep handler_stack handler_fragments ** frame))).
  { pose proof (mutex_del_initial_call_program_resources entry_abi state initial fragments
      Hbinding Hgeometry Hcurrent) as Hentry; cbv zeta in Hentry.
    sep_apply_l_atomic Hentry; unfold call, registered; entailer!. }
  destruct (Hregister before Hpre) as [Htask Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hcpsr|reflexivity]. }
  rewrite <- Hinitial_mask in Howned.
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch save_abi sg call
    (kernel_save_read_cpsr registers) registered before saved_registers registered saved_heap
    (kernel_program_inv sg registered ** task_stack_fragments_rep handler_stack handler_fragments ** frame)
    Hsaved Howned Hsave) as [Hstate [Hmemory [Hsave_lr [Hsaved_r0 Hmasked_owned]]]].
  assert (Hsave_source : kernel_call_save_uninterrupted_execution arch registers registered before
    saved_registers registered saved_heap).
  { unfold kernel_call_save_uninterrupted_execution; econstructor.
    - constructor; [exact Hreturn|reflexivity].
    - exact (armv7a_save_suffix_source _ _ _ _ save_abi _ _ _ _ _ _ Hsave). }
  destruct (mutex_del_restore_call_normal_return critical arch restore call saved_registers.(kernel_save_r0)
    registered registered restore_entry cursor saved_heap written_cursor released returned final resumed final_cursor after
    frame Hr0 Hmasked Hmasked_owned Hprefix Hirqs Hsuffix) as [Hi [Ho [Hs [Hfinal Hpost]]]].
  assert (Hreturn_mask : armv7a_irq_fiq_mask saved_registers.(kernel_save_r0) =
    armv7a_irq_fiq_mask initial.(armv7a_continuation_cpsr)).
  { rewrite Hsaved_r0; exact Hinitial_mask. }
  split; [exact Htask|]. split; [exact Hsave_source|]. split; [exact Hi|].
  split; [exact Ho|]. split; [exact Hs|]. split; [exact Hfinal|].
  rewrite Hreturn_mask in Hpost; exact Hpost.
Qed.
End RestoreCallComposition.
