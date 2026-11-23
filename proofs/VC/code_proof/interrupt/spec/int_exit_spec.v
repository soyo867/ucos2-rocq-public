Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_timer_region.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSIntExit, Source/os_core.c:693--739, V2.93.01.  [running_observed]
    indexes the OUTER test before Save; it is not a new OS field or a read
    repeated inside the critical section.  On the true branch [entry] is
    the post-Save state; on the false branch it is the no-Save observation
    point.  No equality across that interval is asserted by this model.

    The selected profile has profiling/TLS/trace disabled.  A true-branch
    endpoint is before the first remaining trace/TLS/platform call or
    Restore, not a complete ISR return.  OSIntCtxSw has its own contract.
    The scheduler preparation sequence is source-identical to the one in
    sched_spec; proof reuse does NOT assert a C call to OS_Sched. *)
Definition os_int_exit_after_nesting (entry : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_IntrS (interrupt_exit_state true entry.(IntrState)) entry.

Definition os_int_exit_requests_switch (running_observed : bool)
  (entry : UCOS2_Verify_State) : bool :=
  if running_observed then os_sched_requests_switch (os_int_exit_after_nesting entry)
  else false.

Definition os_int_exit_ready_checkpoint (running_observed : bool)
  (entry : UCOS2_Verify_State) : UCOS2_Verify_State :=
  if running_observed then
    let counted := os_int_exit_after_nesting entry in
    replace_SchedS (os_sched_ready_checkpoint counted) counted
  else entry.

(** Resource endpoint of the source preparation.  Updated nesting cells
    reside in the EXISTING global residual; the same ready/cache resources
    used for scheduler preparation are reused, not re-owned elsewhere. *)
Definition os_int_exit_prefix_rep (sg : StableGlobVars) (running_observed : bool)
  (entry : UCOS2_Verify_State) : Assertion :=
  if running_observed then
    task_public_storage sg entry.(TskState) **
    os_sched_prefix_rep sg (os_int_exit_after_nesting entry) **
    UCOS2_raw_rep_missing_task_storage_sched sg (os_int_exit_after_nesting entry)
  else UCOS2_raw_rep sg entry.

Lemma os_int_exit_after_nesting_selection_eq : forall entry,
  os_sched_selection_enabled (os_int_exit_after_nesting entry) =
  interrupt_exit_requests_schedule true entry.(IntrState).
Proof.
  intro entry; unfold os_sched_selection_enabled, os_int_exit_after_nesting,
    interrupt_exit_requests_schedule; simpl.
  unfold interrupt_exit_state; destruct (0 <? entry.(IntrState).(intNesting)); reflexivity.
Qed.

Lemma os_int_exit_selection_before_counts_iff : forall entry,
  interrupt_in_range entry.(IntrState) ->
  (os_sched_selection_enabled (os_int_exit_after_nesting entry) = true <->
    0 <= entry.(IntrState).(intNesting) <= 1 /\ entry.(IntrState).(lockNesting) = 0).
Proof.
  intros entry [Hnonnegative Hlock].
  rewrite os_int_exit_after_nesting_selection_eq, interrupt_exit_requests_schedule_iff.
  unfold interrupt_exit_state; simpl.
  destruct (0 <? entry.(IntrState).(intNesting)) eqn:Hpositive; simpl.
  - apply Z.ltb_lt in Hpositive; lia.
  - apply Z.ltb_ge in Hpositive; lia.
Qed.

Lemma os_int_exit_requests_switch_iff : forall observed entry,
  os_int_exit_requests_switch observed entry = true <->
  observed = true /\ interrupt_exit_requests_schedule true entry.(IntrState) = true /\
  sched_selected_priority entry.(TskState) entry.(SchedState) <>
    sched_priority_byte entry.(SchedState).(curSchedPrio).
Proof.
  intros [] entry; unfold os_int_exit_requests_switch.
  - rewrite os_sched_requests_switch_iff, os_int_exit_after_nesting_selection_eq.
    cbn [os_int_exit_after_nesting replace_IntrS TskState SchedState]; tauto.
  - split; [discriminate|intros [H _]; discriminate].
Qed.

Lemma os_int_exit_not_running_no_effect : forall entry,
  os_int_exit_ready_checkpoint false entry = entry /\
  os_int_exit_requests_switch false entry = false.
Proof. intro entry; split; reflexivity. Qed.

Lemma os_int_exit_checkpoint_frame : forall observed entry,
  let post := os_int_exit_ready_checkpoint observed entry in
  post.(TskState) = entry.(TskState) /\
  post = replace_SchedS post.(SchedState) (replace_IntrS post.(IntrState) entry).
Proof. intros [] entry; [split; reflexivity|destruct entry; split; reflexivity]. Qed.

Lemma os_int_exit_checkpoint_nesting_eq : forall observed entry,
  (os_int_exit_ready_checkpoint observed entry).(IntrState) =
    interrupt_exit_state observed entry.(IntrState).
Proof. intros [] entry; reflexivity. Qed.

Lemma os_int_exit_checkpoint_current_frame : forall observed entry,
  let sched' := (os_int_exit_ready_checkpoint observed entry).(SchedState) in
  sched'.(curTaskID) = entry.(SchedState).(curTaskID) /\
  sched'.(curSchedPrio) = entry.(SchedState).(curSchedPrio) /\
  sched'.(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intros [] entry; [|split; [reflexivity|split; reflexivity]].
  exact (proj2 (os_sched_ready_checkpoint_frame (os_int_exit_after_nesting entry))).
Qed.

Lemma os_int_exit_checkpoint_counter_eq : forall observed entry,
  (os_int_exit_ready_checkpoint observed entry).(SchedState).(ctxSwCtr) =
    if os_int_exit_requests_switch observed entry
    then (entry.(SchedState).(ctxSwCtr) + 1) mod 4294967296 else entry.(SchedState).(ctxSwCtr).
Proof.
  intros [] entry; [|reflexivity].
  cbn [os_int_exit_ready_checkpoint replace_SchedS SchedState].
  rewrite os_sched_ready_checkpoint_counter_eq.
  unfold os_sched_counter_stage, os_int_exit_requests_switch.
  destruct (os_sched_requests_switch (os_int_exit_after_nesting entry)); reflexivity.
Qed.

Lemma os_int_exit_after_nesting_preserves_validity : forall sg entry,
  UCOS2_state_inv sg entry ->
  UCOS2_state_inv sg (os_int_exit_after_nesting entry).
Proof. intros; exact H. Qed.

(** First close the actual decrement before using the shared scheduler
    preparation slice.  The two counter cells are not owned twice. *)
Lemma os_int_exit_nesting_merge_inv : forall sg entry,
  UCOS2_state_inv sg entry ->
  store_int_state sg (interrupt_exit_state true entry.(IntrState)) **
  UCOS2_raw_rep_missing_interrupt sg entry |--
    UCOS2_inv sg (os_int_exit_after_nesting entry).
Proof.
  intros sg entry Hvalid.
  sep_apply_l_atomic (interrupt_inv_merge_counters sg (interrupt_exit_state true entry.(IntrState))).
  apply UCOS2_inv_merge_updated_interrupt; exact Hvalid.
Qed.

Lemma os_int_exit_ready_checkpoint_preserves_validity : forall sg observed entry,
  UCOS2_state_inv sg entry ->
  UCOS2_state_inv sg (os_int_exit_ready_checkpoint observed entry).
Proof.
  intros sg [] entry Hvalid; [|exact Hvalid].
  apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid.
Qed.

Lemma os_int_exit_prefix_merge_inv : forall sg observed entry,
  UCOS2_state_inv sg entry ->
  (interrupt_exit_requests_schedule observed entry.(IntrState) = true ->
    entry.(SchedState).(readyList) <> []) ->
  os_int_exit_prefix_rep sg observed entry |--
    UCOS2_inv sg (os_int_exit_ready_checkpoint observed entry).
Proof.
  intros sg [] entry Hvalid Hnonempty.
  - apply (os_sched_prefix_merge_inv sg (os_int_exit_after_nesting entry)); [exact Hvalid|].
    rewrite os_int_exit_after_nesting_selection_eq; exact Hnonempty.
  - unfold os_int_exit_prefix_rep, os_int_exit_ready_checkpoint, UCOS2_inv; entailer!.
Qed.

(** Any observer's Task lifetime/private-creation state is unchanged by this
    preparation.  A later platform switch/ISR return is not certified here. *)
Lemma os_int_exit_checkpoint_invocation_frame : forall observed entry observer origin,
  task_invocation_active entry.(TskState) observer origin ->
  task_invocation_active (os_int_exit_ready_checkpoint observed entry).(TskState) observer origin.
Proof. intros; rewrite (proj1 (os_int_exit_checkpoint_frame observed entry)); exact H. Qed.

(** A scheduler lock does not mask interrupts.  In this source branch it
    does, however, suppress the ready-cache reads, counter increment and
    context-switch call.  The counter update below therefore has a contract
    on the actual complement of a borrowed Timer pool, not on a second
    copy of the full kernel invariant.  Zero ISR nesting is kept: the C
    decrement is conditional and the lock test still suppresses selection.
    These are preparation/resource theorems; Save/Restore and the ISR
    wrapper must still transfer this same view at their boundaries. *)
Lemma os_int_exit_locked_selection_disabled : forall entry,
  entry.(IntrState).(lockNesting) <> 0 ->
  os_sched_selection_enabled (os_int_exit_after_nesting entry) = false.
Proof.
  intros entry Hlocked; rewrite os_int_exit_after_nesting_selection_eq.
  unfold interrupt_exit_requests_schedule.
  apply Z.eqb_neq in Hlocked; rewrite Hlocked, Bool.andb_false_r; reflexivity.
Qed.

Lemma os_int_exit_locked_no_switch : forall observed entry,
  entry.(IntrState).(lockNesting) <> 0 ->
  os_int_exit_requests_switch observed entry = false.
Proof.
  intros [] entry Hlocked; [|reflexivity].
  unfold os_int_exit_requests_switch, os_sched_requests_switch.
  rewrite (os_int_exit_locked_selection_disabled entry Hlocked); reflexivity.
Qed.

(** No ready-list selection also covers boot and nested ISR exits.  Use
    the actual source decision rather than requiring a positive lock in
    paths where OSIntExit never even executes that lock test. *)
Lemma os_int_exit_no_schedule_checkpoint_eq : forall observed entry,
  interrupt_exit_requests_schedule observed entry.(IntrState) = false ->
  os_int_exit_ready_checkpoint observed entry =
    replace_IntrS (interrupt_exit_state observed entry.(IntrState)) entry.
Proof.
  intros [] entry Hdisabled.
  - unfold os_int_exit_ready_checkpoint, os_sched_ready_checkpoint.
    rewrite os_int_exit_after_nesting_selection_eq, Hdisabled.
    unfold os_int_exit_after_nesting; destruct entry; reflexivity.
  - unfold os_int_exit_ready_checkpoint, interrupt_exit_state; destruct entry; reflexivity.
Qed.

Lemma os_int_exit_no_schedule_no_switch : forall observed entry,
  interrupt_exit_requests_schedule observed entry.(IntrState) = false ->
  os_int_exit_requests_switch observed entry = false.
Proof.
  intros [] entry Hdisabled; [|reflexivity].
  unfold os_int_exit_requests_switch, os_sched_requests_switch.
  rewrite os_int_exit_after_nesting_selection_eq, Hdisabled; reflexivity.
Qed.

Lemma os_int_exit_no_schedule_merge_timer_region : forall sg observed entry,
  UCOS2_state_inv sg entry ->
  interrupt_exit_requests_schedule observed entry.(IntrState) = false ->
  store_int_state sg (interrupt_exit_state observed entry.(IntrState)) **
    UCOS2_raw_rep_missing_timer_pool_body_interrupt sg entry |--
  UCOS2_inv_missing_timer_pool_body sg (os_int_exit_ready_checkpoint observed entry).
Proof.
  intros sg observed entry Hvalid Hdisabled.
  rewrite (os_int_exit_no_schedule_checkpoint_eq observed entry Hdisabled).
  sep_apply_l_atomic
    (interrupt_inv_merge_counters sg (interrupt_exit_state observed entry.(IntrState))).
  apply UCOS2_inv_missing_timer_pool_body_merge_updated_interrupt; exact Hvalid.
Qed.

Lemma os_int_exit_locked_checkpoint_eq : forall observed entry,
  entry.(IntrState).(lockNesting) <> 0 ->
  os_int_exit_ready_checkpoint observed entry =
    replace_IntrS (interrupt_exit_state observed entry.(IntrState)) entry.
Proof.
  intros observed entry Hlocked; apply os_int_exit_no_schedule_checkpoint_eq.
  unfold interrupt_exit_requests_schedule; apply Z.eqb_neq in Hlocked.
  rewrite Hlocked; apply Bool.andb_false_r.
Qed.

Lemma os_int_exit_locked_merge_timer_region : forall sg observed entry,
  UCOS2_state_inv sg entry -> entry.(IntrState).(lockNesting) <> 0 ->
  store_int_state sg (interrupt_exit_state observed entry.(IntrState)) **
    UCOS2_raw_rep_missing_timer_pool_body_interrupt sg entry |--
  UCOS2_inv_missing_timer_pool_body sg (os_int_exit_ready_checkpoint observed entry).
Proof.
  intros sg observed entry Hvalid Hlocked.
  apply os_int_exit_no_schedule_merge_timer_region; [exact Hvalid|].
  unfold interrupt_exit_requests_schedule; apply Z.eqb_neq in Hlocked.
  rewrite Hlocked; apply Bool.andb_false_r.
Qed.

(** Full OSIntExit boundary.  A handler's execution stack is distinct from
    the interrupted task's ALREADY saved, parked fragments.  The allocation
    origin is not an ISA execution mode.  In particular none of these fields
    is a new field of the kernel state. *)
Record OsIntExitCallContext : Type := {
  os_int_exit_invocation : nat;
  os_int_exit_origin : TaskInvocationOrigin;
  os_int_exit_handler_stack : TaskStackRegion;
  os_int_exit_handler_fragments : TaskStackFragments;
  os_int_exit_interrupted_stack : TaskStackLease;
  os_int_exit_interrupted_sp : Z;
  os_int_exit_interrupted_fragments : TaskStackFragments;
  (** The first-level wrapper saves this actual C continuation, including
      its PC and pre-exception mask.  These are ghost observations of the
      saved frame, not fields added to a TCB.  Allocation generation alone
      is not an identity for a suspended invocation. *)
  os_int_exit_interrupted_call : OsSchedCallContext;
  os_int_exit_interrupted_pc : Z;
  os_int_exit_interrupted_mask : Z;
}.

(** The first-level wrapper runs on the exception stack, while the task
    lease below remains the provenance of its suspended continuation. A C
    API called by this handler uses this same execution view, not a fresh
    task lease or a KernelCaller label. *)
Definition os_int_exit_execution_view (context : OsIntExitCallContext) : OsExecutionView :=
  {| os_execution_invocation := context.(os_int_exit_invocation);
     os_execution_origin := context.(os_int_exit_origin);
     os_execution_context := KernelInterrupt context.(os_int_exit_invocation)
       (KernelCaller context.(os_int_exit_interrupted_call).(os_sched_call_invocation)
         context.(os_int_exit_interrupted_call).(os_sched_call_origin));
     os_execution_stack := context.(os_int_exit_handler_stack);
     os_execution_fragments := context.(os_int_exit_handler_fragments) |}.

(** The selected external port binds these assertions/relations to the
    exception wrapper and exception return.  [entry_source] means that the
    wrapper saved the interrupted context/TCB SP BEFORE entering this handler
    stack, and that the current call is in its supported masked SVC context.
    [return_source] restores the specified destination frame, not the BL
    continuation of OSIntCtxSw.  This is not a new invariant certificate or
    an implementation proof of a particular floating-point assembly variant.
    The already approved scheduler external object supplies the SAME hook
    source action/certificate and incoming-frame restore relation. *)
Record OsIntExitPlatformResources : Type := {
  os_int_exit_handler_running : OsIntExitCallContext -> Assertion;
  os_int_exit_entry_source : OsIntExitCallContext -> Prop;
  os_int_exit_return_source : OsIntExitCallContext -> TaskStackLease -> Z ->
    TaskStackFragments -> Prop;
  (** PC observation of the exact interrupted frame restored by the
      wrapper.  This relation supplies no OS-state or ownership fact. *)
  os_int_exit_frame_return_source : OsIntExitCallContext -> Z -> Prop;
  os_int_exit_transferred : OsIntExitCallContext -> InterruptSaveToken ->
    TaskStackLease -> Z -> TaskStackFragments -> Assertion;
}.

(** A linked representation instance, not a law relating arbitrary ports.
    Only the running-resource interpretation is selected from [external].
    The existing entry/return/transfer source parameters are unchanged; an
    architecture ABI used with this instance must still be supplied for
    this very instance. Constructing it creates no execution permission. *)
Definition os_int_exit_shared_execution_port (external : OsSchedExternalResources)
  (source : OsIntExitPlatformResources) : OsIntExitPlatformResources :=
  {| os_int_exit_handler_running := fun context =>
       external.(os_sched_arch_running) (os_int_exit_execution_view context);
     os_int_exit_entry_source := source.(os_int_exit_entry_source);
     os_int_exit_return_source := source.(os_int_exit_return_source);
     os_int_exit_frame_return_source := source.(os_int_exit_frame_return_source);
     os_int_exit_transferred := source.(os_int_exit_transferred) |}.

Definition os_int_exit_context_resources (port : OsIntExitPlatformResources)
  (context : OsIntExitCallContext) : Assertion :=
  task_stack_fragments_rep context.(os_int_exit_handler_stack)
    context.(os_int_exit_handler_fragments) ** port.(os_int_exit_handler_running) context.

Lemma os_int_exit_shared_context_resources_eq : forall external source context,
  os_int_exit_context_resources (os_int_exit_shared_execution_port external source) context =
  os_execution_view_resources external (os_int_exit_execution_view context).
Proof. reflexivity. Qed.

(** The first-level wrapper already made this frame available; OSIntCtxSw
    does not park or save its own C call frame.  A formerly running lifetime
    may have been retired, so there is NO live-current-task condition here.
    If its generation is still live, its actual TCB SP names the saved frame.
    The parked map owns the bytes, exactly once, through UCOS2_inv. *)
Definition os_int_exit_saved_exception_binding (context : OsIntExitCallContext)
  (entry : UCOS2_Verify_State) : Prop :=
  let interrupted := context.(os_int_exit_interrupted_stack) in
  entry.(TskState).(parkedTaskStacks) (task_stack_key interrupted) =
    Some (interrupted.(stackLeaseRegion), context.(os_int_exit_interrupted_fragments)) /\
  (forall node, entry.(TskState).(inUsedTaskStates) interrupted.(stackLeaseSlot) = Some node ->
    node.(taskGeneration) = interrupted.(stackLeaseGeneration) ->
    node.(tcbStkPtr) = context.(os_int_exit_interrupted_sp)).

Record OsIntExitTransfer : Type := {
  os_int_exit_hooked_state : UCOS2_Verify_State;
  os_int_exit_incoming_stack : TaskStackLease;
  os_int_exit_incoming_sp : Z;
  os_int_exit_incoming_fragments : TaskStackFragments;
}.

Definition os_int_exit_destination_binding (external : OsSchedExternalResources)
  (transfer : OsIntExitTransfer) : Prop :=
  let hooked := transfer.(os_int_exit_hooked_state) in
  let incoming := transfer.(os_int_exit_incoming_stack) in
  hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
  (exists node, hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
    node.(tcbStkPtr) = transfer.(os_int_exit_incoming_sp)) /\
  task_stack_live_binding hooked.(TskState) incoming /\
  hooked.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), transfer.(os_int_exit_incoming_fragments)) /\
  external.(os_sched_arch_restore_source) incoming transfer.(os_int_exit_incoming_sp)
    transfer.(os_int_exit_incoming_fragments).

Definition os_int_exit_installed_state (transfer : OsIntExitTransfer) : UCOS2_Verify_State :=
  let hooked := transfer.(os_int_exit_hooked_state) in
  let cached := replace_SchedS (sched_install_selected hooked.(SchedState)) hooked in
  replace_TskS
    (glob_task_set_parked_stacks cached.(TskState)
      (task_stack_take cached.(TskState).(parkedTaskStacks) transfer.(os_int_exit_incoming_stack))) cached.

(** Actual source order: C preparation; hook; reread high pointer/byte;
    install current caches; take/restore the selected parked stack.
    No endpoint-validity test, task-level save or later ISR resumption is
    hidden in this relation.  Hook divergence has no completed transfer,
    just as it has no ordinary return; no termination claim is made. *)
Definition os_int_exit_transfer_source (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (entry : UCOS2_Verify_State)
  (transfer : OsIntExitTransfer) : Prop :=
  os_int_exit_requests_switch true entry = true /\
  port.(os_int_exit_entry_source) context /\
  os_int_exit_saved_exception_binding context entry /\
  kernel_client_step external.(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true entry) transfer.(os_int_exit_hooked_state) /\
  os_int_exit_destination_binding external transfer /\
  port.(os_int_exit_return_source) context transfer.(os_int_exit_incoming_stack)
    transfer.(os_int_exit_incoming_sp) transfer.(os_int_exit_incoming_fragments).

Definition os_int_exit_switch_input (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (entry : UCOS2_Verify_State) : Prop :=
  port.(os_int_exit_entry_source) context /\
  os_int_exit_saved_exception_binding context entry /\
  (forall hooked, kernel_client_step external.(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true entry) hooked ->
    exists incoming sp fragments,
      let transfer := {| os_int_exit_hooked_state := hooked;
        os_int_exit_incoming_stack := incoming; os_int_exit_incoming_sp := sp;
        os_int_exit_incoming_fragments := fragments |} in
      os_int_exit_destination_binding external transfer /\
      port.(os_int_exit_return_source) context incoming sp fragments).

Definition os_int_exit_entry_safety (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (entry : UCOS2_Verify_State) : Prop :=
  (interrupt_exit_requests_schedule true entry.(IntrState) = true ->
    entry.(SchedState).(readyList) <> []) /\
  (os_int_exit_requests_switch true entry = true ->
    os_int_exit_switch_input external port sg context entry).

Definition os_int_exit_acquire_safety (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext)
  (before : UCOS2_Verify_State) : Prop :=
  before.(SchedState).(isRunning) = true ->
  forall entry, critical_region_interval critical sg context.(os_int_exit_invocation) before entry ->
    os_int_exit_entry_safety external port sg context entry.

Definition os_int_exit_running (state : UCOS2_Verify_State) : Z :=
  if state.(SchedState).(isRunning) then 1 else 0.

Definition os_int_exit_global_addresses (sg : StableGlobVars)
  (running ints locks high current high_tcb table counter unmap group rows : Z) : Prop :=
  running = sg.(g_OSRunning) /\
  os_sched_global_addresses sg ints locks high current high_tcb table counter unmap group rows.

(** The outside protocol lends the actual OSRunning cell for the source
    observation.  Save consumes that loan, then reopens the full invariant
    at its possibly different protected state; Restore returns the loan.
    This is an explicit observation/acquisition platform specialization,
    not an assertion that the pre-Save OSRunning byte remains unchanged. *)
Definition os_int_exit_outside_frame (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform context.(os_int_exit_invocation)
    context.(os_int_exit_origin) mask **
  critical_region_outside_without_running critical sg context.(os_int_exit_invocation) state **
  os_int_exit_context_resources port context ** unmap_table_rep sg.

Definition os_int_exit_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (mask : Z) (before : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\
    os_int_exit_acquire_safety external port critical sg context before) &&
  (sg.(g_OSRunning) # UChar |-> os_int_exit_running before **
    os_int_exit_outside_frame platform port critical sg context mask before).

Definition os_int_exit_inside_frame (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext) (saved : Z)
  (entry : UCOS2_Verify_State) : Assertion :=
  critical_region_masked platform critical sg context.(os_int_exit_invocation)
    context.(os_int_exit_origin) saved entry **
  os_int_exit_context_resources port context.

Lemma os_int_exit_pre_closed_equiv : forall external platform port critical sg context mask before,
  os_int_exit_pre external platform port critical sg context mask before --||--
    coq_prop (UCOS2_state_inv sg before /\
      os_int_exit_acquire_safety external port critical sg context before) &&
    (interrupt_platform_running platform context.(os_int_exit_invocation)
       context.(os_int_exit_origin) mask **
     critical_region_outside critical sg context.(os_int_exit_invocation) before **
     os_int_exit_context_resources port context ** unmap_table_rep sg).
Proof.
  intros; unfold os_int_exit_pre, os_int_exit_outside_frame,
    os_int_exit_running, critical_region_outside.
  split; entailer!.
Qed.

Definition os_int_exit_return_relation (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext)
  (before entry : UCOS2_Verify_State) : Prop :=
  (if before.(SchedState).(isRunning)
   then critical_region_interval critical sg context.(os_int_exit_invocation) before entry
   else entry = before) /\
  os_int_exit_requests_switch before.(SchedState).(isRunning) entry = false.

Definition os_int_exit_post (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext) (mask : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  EX entry,
    let final := os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry in
    coq_prop (os_int_exit_return_relation critical sg context before entry /\
      UCOS2_state_inv sg final) &&
    (sg.(g_OSRunning) # UChar |-> os_int_exit_running final **
      os_int_exit_outside_frame platform port critical sg context mask final).

(** Resource-explicit terminal contract, separate from its empty ordinary
    C-return projection.  All kernel/parked resources are handed to the
    external transfer, and its completed endpoint owns the selected running
    fragments and full updated invariant.  The abandoned handler fragments
    and disjoint caller frame remain resources; they are not deleted or
    claimed to be executing in the destination.  The saved ISR token and
    critical handle are consumed by the nonlocal transfer protocol. *)
Definition os_int_exit_transfer_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (saved : Z) (entry : UCOS2_Verify_State) : Assertion :=
  coq_prop (os_int_exit_requests_switch true entry = true /\
    os_int_exit_switch_input external port sg context entry) &&
  (UCOS2_inv sg (os_int_exit_ready_checkpoint true entry) ** unmap_table_rep sg **
    os_int_exit_inside_frame platform port critical sg context saved entry).

Definition os_int_exit_transfer_post (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (saved : Z) (entry : UCOS2_Verify_State)
  (transfer : OsIntExitTransfer) : Assertion :=
  coq_prop (os_int_exit_transfer_source external port sg context entry transfer) &&
  (UCOS2_inv sg (os_int_exit_installed_state transfer) **
    task_stack_fragments_rep transfer.(os_int_exit_incoming_stack).(stackLeaseRegion)
      transfer.(os_int_exit_incoming_fragments) **
    task_stack_fragments_rep context.(os_int_exit_handler_stack)
      context.(os_int_exit_handler_fragments) ** unmap_table_rep sg **
    port.(os_int_exit_transferred) context
      (save_token saved context.(os_int_exit_invocation) context.(os_int_exit_origin))
      transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_sp)
      transfer.(os_int_exit_incoming_fragments)).

Lemma os_int_exit_transfer_source_after_hook : forall external port sg context entry hooked,
  os_int_exit_requests_switch true entry = true ->
  os_int_exit_switch_input external port sg context entry ->
  kernel_client_step external.(os_sched_hook_action) sg
    (os_int_exit_ready_checkpoint true entry) hooked ->
  exists transfer, transfer.(os_int_exit_hooked_state) = hooked /\
    os_int_exit_transfer_source external port sg context entry transfer.
Proof.
  intros external port sg context entry hooked Hrequest [Hentry [Hsaved Hhook]] Hstep.
  destruct (Hhook hooked Hstep) as [incoming [sp [fragments [Hdest Hreturn]]]].
  exists {| os_int_exit_hooked_state := hooked; os_int_exit_incoming_stack := incoming;
    os_int_exit_incoming_sp := sp; os_int_exit_incoming_fragments := fragments |}.
  split; [reflexivity|]. unfold os_int_exit_transfer_source; simpl; tauto.
Qed.

Lemma os_int_exit_install_cache_preserves_validity : forall sg hooked,
  UCOS2_state_inv sg hooked ->
  (forall p, hooked.(SchedState).(highRdyPrio) = Some p -> task_priority_in_range sg p) ->
  UCOS2_state_inv sg (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked).
Proof.
  intros sg hooked Hvalid Hindex; apply UCOS2_replace_sched_preserves_validity;
    [exact Hvalid| |reflexivity].
  apply sched_install_selected_preserves_in_range;
    [exact (proj1 (proj2 (proj2 Hvalid)))|exact Hindex].
Qed.

Lemma os_int_exit_installed_state_preserves_validity : forall sg transfer,
  UCOS2_state_inv sg transfer.(os_int_exit_hooked_state) ->
  (forall p, transfer.(os_int_exit_hooked_state).(SchedState).(highRdyPrio) = Some p ->
    task_priority_in_range sg p) ->
  UCOS2_state_inv sg (os_int_exit_installed_state transfer).
Proof.
  intros sg transfer Hvalid Hindex; unfold os_int_exit_installed_state.
  apply UCOS2_replace_parked_stacks_preserves_validity.
  - apply os_int_exit_install_cache_preserves_validity; assumption.
  - apply task_stack_take_preserves_consistency.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
Qed.

Lemma os_int_exit_transfer_preserves_validity : forall external port sg context entry transfer,
  UCOS2_state_inv sg entry ->
  os_int_exit_transfer_source external port sg context entry transfer ->
  UCOS2_state_inv sg (os_int_exit_installed_state transfer).
Proof.
  intros external port sg context entry transfer Hvalid [_ [_ [_ [Hhook [Hdest _]]]]].
  assert (Hhooked : UCOS2_state_inv sg transfer.(os_int_exit_hooked_state)).
  { eapply os_sched_hook_preserves_validity; [|exact Hhook].
    apply os_int_exit_ready_checkpoint_preserves_validity; exact Hvalid. }
  apply os_int_exit_installed_state_preserves_validity.
  - exact Hhooked.
  - destruct Hdest as [_ [[node [Hnode [_ [Hpriority _]]]] _]].
    intros p Hp; assert (p = node.(curPrio)) by congruence; subst p.
    pose proof (proj1 (proj2 Hhooked)) as Htasks.
    assert (Hpriorities : forall tid t,
      transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates) tid = Some t ->
      task_priority_in_range sg t.(curPrio))
      by (unfold task_in_range in Htasks; tauto).
    eapply Hpriorities; exact Hnode.
Qed.

Lemma os_int_exit_install_cache_merge : forall sg hooked,
  UCOS2_state_inv sg hooked ->
  (forall p, hooked.(SchedState).(highRdyPrio) = Some p -> task_priority_in_range sg p) ->
  task_public_storage sg hooked.(TskState) **
  sched_raw_rep sg hooked.(TskState) (sched_install_selected hooked.(SchedState)) **
  UCOS2_raw_rep_missing_task_storage_sched sg hooked |--
  UCOS2_inv sg (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked).
Proof.
  intros sg hooked Hvalid Hindex.
  exact (UCOS2_inv_merge_updated_task_storage_sched sg hooked
    (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked)
    (os_int_exit_install_cache_preserves_validity sg hooked Hvalid Hindex) eq_refl).
Qed.

Lemma os_int_exit_take_destination_resources : forall sg transfer,
  transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks)
    (task_stack_key transfer.(os_int_exit_incoming_stack)) =
    Some (transfer.(os_int_exit_incoming_stack).(stackLeaseRegion),
      transfer.(os_int_exit_incoming_fragments)) ->
  UCOS2_inv sg (replace_SchedS
    (sched_install_selected transfer.(os_int_exit_hooked_state).(SchedState))
    transfer.(os_int_exit_hooked_state)) |--
  UCOS2_inv sg (os_int_exit_installed_state transfer) **
    task_stack_fragments_rep transfer.(os_int_exit_incoming_stack).(stackLeaseRegion)
      transfer.(os_int_exit_incoming_fragments).
Proof.
  intros sg transfer Hentry.
  rewrite UCOS2_inv_split_parked_stacks; Intros.
  sep_apply_l_atomic (store_parked_stacks_take_fragments _ _ _ Hentry).
  assert (Hconsistent : parked_stacks_consistent
    transfer.(os_int_exit_hooked_state).(TskState)
    (task_stack_take transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks)
      transfer.(os_int_exit_incoming_stack))).
  { apply task_stack_take_preserves_consistency.
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in H; tauto. }
  unfold os_int_exit_installed_state.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg
    (replace_SchedS (sched_install_selected transfer.(os_int_exit_hooked_state).(SchedState))
      transfer.(os_int_exit_hooked_state)) _ H Hconsistent).
  entailer!.
Qed.

Lemma os_int_exit_installed_current_eq : forall transfer,
  (os_int_exit_installed_state transfer).(SchedState).(curTaskID) =
    transfer.(os_int_exit_hooked_state).(SchedState).(highRdyTid) /\
  (os_int_exit_installed_state transfer).(SchedState).(curSchedPrio) =
    transfer.(os_int_exit_hooked_state).(SchedState).(highRdyPrio) /\
  (os_int_exit_installed_state transfer).(TskState).(inUsedTaskStates) =
    transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates) /\
  (os_int_exit_installed_state transfer).(IntrState) =
    transfer.(os_int_exit_hooked_state).(IntrState).
Proof. intros; repeat split; reflexivity. Qed.

(** Reassemble the actual cache writes and remove the selected parked
    owner exactly once.  The hook's existing certificate supplies the
    logical invariant; the external transfer receipt supplies the changed
    control owner.  Neither conclusion is assumed by transfer_source. *)
Lemma os_int_exit_transfer_resources_merge : forall external port sg context saved entry transfer,
  UCOS2_state_inv sg entry ->
  os_int_exit_transfer_source external port sg context entry transfer ->
  task_public_storage sg transfer.(os_int_exit_hooked_state).(TskState) **
  sched_raw_rep sg transfer.(os_int_exit_hooked_state).(TskState)
    (sched_install_selected transfer.(os_int_exit_hooked_state).(SchedState)) **
  UCOS2_raw_rep_missing_task_storage_sched sg transfer.(os_int_exit_hooked_state) **
  task_stack_fragments_rep context.(os_int_exit_handler_stack)
    context.(os_int_exit_handler_fragments) ** unmap_table_rep sg **
  port.(os_int_exit_transferred) context
    (save_token saved context.(os_int_exit_invocation) context.(os_int_exit_origin))
    transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_sp)
    transfer.(os_int_exit_incoming_fragments) |--
  os_int_exit_transfer_post external port sg context saved entry transfer.
Proof.
  intros external port sg context saved entry transfer Hvalid Hsource.
  pose proof Hsource as [_ [_ [_ [Hhook [Hdest Hreturn]]]]].
  destruct Hdest as [Hhigh [Hnode [Hlive [Hparked Harch]]]].
  assert (Hhooked : UCOS2_state_inv sg transfer.(os_int_exit_hooked_state)).
  { eapply os_sched_hook_preserves_validity; [|exact Hhook].
    apply os_int_exit_ready_checkpoint_preserves_validity; exact Hvalid. }
  assert (Hindex : forall p,
    transfer.(os_int_exit_hooked_state).(SchedState).(highRdyPrio) = Some p ->
    task_priority_in_range sg p).
  { destruct Hnode as [node [Hnode [_ [Hpriority _]]]].
    intros p Hp; assert (p = node.(curPrio)) by congruence; subst p.
    pose proof (proj1 (proj2 Hhooked)) as Htasks.
    assert (Hpriorities : forall tid t,
      transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates) tid = Some t ->
      task_priority_in_range sg t.(curPrio))
      by (unfold task_in_range in Htasks; tauto).
    eapply Hpriorities; exact Hnode. }
  sep_apply_l_atomic (os_int_exit_install_cache_merge sg
    transfer.(os_int_exit_hooked_state) Hhooked Hindex).
  sep_apply_l_atomic (os_int_exit_take_destination_resources sg transfer Hparked).
  unfold os_int_exit_transfer_post; entailer!.
Qed.

Definition os_int_exit_body_facts (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Prop :=
  before.(SchedState).(isRunning) = true /\
  critical_region_interval critical sg context.(os_int_exit_invocation) before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  os_int_exit_entry_safety external port sg context entry.

Lemma os_int_exit_acquire_facts : forall external port critical sg context mask saved before entry,
  UCOS2_state_inv sg before ->
  os_int_exit_acquire_safety external port critical sg context before ->
  os_int_exit_running before = 1 ->
  critical_region_interval critical sg context.(os_int_exit_invocation) before entry ->
  interrupt_saved_value mask saved ->
  os_int_exit_body_facts external port critical sg context mask saved before entry.
Proof.
  intros external port critical sg context mask saved before entry Hvalid Hsafe Hrun Hinterval Hsaved.
  unfold os_int_exit_running in Hrun.
  destruct before.(SchedState).(isRunning) eqn:Hrunning; [|discriminate].
  unfold os_int_exit_body_facts.
  pose proof (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)
    as [Hentry Hframe].
  split; [exact Hrunning|]. split; [exact Hinterval|]. split; [exact Hentry|].
  split; [exact Hsaved|].
  exact (Hsafe Hrunning entry Hinterval).
Qed.

(** Pure/source and spatial consequences of the common Save endpoint.
    The external Save protocol itself still has to exchange the outside
    observation loan for the protected current raw representation. *)
Lemma os_int_exit_save_consequence : forall external port critical sg context mask saved before entry,
  UCOS2_state_inv sg before ->
  os_int_exit_acquire_safety external port critical sg context before ->
  os_int_exit_running before = 1 ->
  critical_region_interval critical sg context.(os_int_exit_invocation) before entry ->
  interrupt_saved_value mask saved ->
  UCOS2_raw_rep sg entry ** unmap_table_rep sg |--
    coq_prop (os_int_exit_body_facts external port critical sg context mask saved before entry) &&
    os_sched_work_cells sg entry (os_sched_old_high entry)
      (os_sched_old_pointer sg entry) (os_sched_counter entry).
Proof.
  intros external port critical sg context mask saved before entry Hvalid Hsafe Hrun Hinterval Hsaved.
  pose proof (os_int_exit_acquire_facts external port critical sg context mask saved before entry
    Hvalid Hsafe Hrun Hinterval Hsaved) as Hfacts.
  rewrite os_sched_work_cells_entry_equiv; entailer!.
Qed.

Inductive OsIntExitOutcome : Type :=
| OsIntExitReturned (entry : UCOS2_Verify_State)
| OsIntExitExceptionTransferred (entry : UCOS2_Verify_State) (transfer : OsIntExitTransfer).

(** This full-call semantics retains BOTH kinds of exit.  QCP's ordinary
    Ensure is only its Returned projection.  A completed external transfer
    has the separate resource post above and never resumes the source's
    remaining OS_CPU_SR_Restore call. *)
Definition os_int_exit_full_call (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext)
  (before : UCOS2_Verify_State) (outcome : OsIntExitOutcome) : Prop :=
  match outcome with
  | OsIntExitReturned entry => os_int_exit_return_relation critical sg context before entry
  | OsIntExitExceptionTransferred entry transfer =>
      before.(SchedState).(isRunning) = true /\
      critical_region_interval critical sg context.(os_int_exit_invocation) before entry /\
      os_int_exit_transfer_source external port sg context entry transfer
  end.

Definition os_int_exit_outcome_state (before : UCOS2_Verify_State)
  (outcome : OsIntExitOutcome) : UCOS2_Verify_State :=
  match outcome with
  | OsIntExitReturned entry => os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry
  | OsIntExitExceptionTransferred _ transfer => os_int_exit_installed_state transfer
  end.

Lemma os_int_exit_full_call_preserves_validity : forall external port critical sg context before outcome,
  UCOS2_state_inv sg before ->
  os_int_exit_full_call external port critical sg context before outcome ->
  UCOS2_state_inv sg (os_int_exit_outcome_state before outcome).
Proof.
  intros external port critical sg context before [entry|entry transfer] Hvalid Hcall.
  - destruct Hcall as [Hinterval Hnoswitch].
    unfold os_int_exit_outcome_state.
    destruct before.(SchedState).(isRunning) eqn:Hrunning.
    + apply os_int_exit_ready_checkpoint_preserves_validity.
      exact (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)).
    + subst entry; exact Hvalid.
  - destruct Hcall as [Hrunning [Hinterval Htransfer]].
    eapply os_int_exit_transfer_preserves_validity; [|exact Htransfer].
    exact (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)).
Qed.

Lemma os_int_exit_transfer_not_ordinary_return : forall entry transfer returned,
  OsIntExitExceptionTransferred entry transfer <> OsIntExitReturned returned.
Proof. discriminate. Qed.

(** The first-level exception wrapper continues AFTER an ordinary
    OSIntExit return.  The ARM source reads OSTCBCur, reads that TCB's SP,
    and restores that frame.  Unlike OSIntCtxSw it does not write either
    current cache here.  These are the read/restore source atoms, not a
    promise that the interrupted task was necessarily selected.

    [os_int_exit_return_source] and [os_sched_arch_restore_source] are the
    already approved port relations.  No new platform-resource field is
    introduced.  Returning to a particular suspended C continuation still
    requires its existing saved-frame/return binding. *)
Definition os_int_exit_wrapper_destination
  (external : OsSchedExternalResources) (port : OsIntExitPlatformResources)
  (context : OsIntExitCallContext) (state : UCOS2_Verify_State)
  (incoming : TaskStackLease) (sp : Z) (fragments : TaskStackFragments) : Prop :=
  state.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) /\
  (exists node, state.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration) /\ node.(tcbStkPtr) = sp) /\
  task_stack_live_binding state.(TskState) incoming /\
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) /\
  external.(os_sched_arch_restore_source) incoming sp fragments /\
  port.(os_int_exit_return_source) context incoming sp fragments.

Definition os_int_exit_wrapper_restored_state (state : UCOS2_Verify_State)
  (incoming : TaskStackLease) : UCOS2_Verify_State :=
  replace_TskS (glob_task_set_parked_stacks state.(TskState)
    (task_stack_take state.(TskState).(parkedTaskStacks) incoming)) state.

Definition os_int_exit_wrapper_return_source
  (external : OsSchedExternalResources) (port : OsIntExitPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (before : UCOS2_Verify_State)
  (incoming : TaskStackLease) (sp : Z) (fragments : TaskStackFragments)
  (after : UCOS2_Verify_State) : Prop :=
  exists entry,
    os_int_exit_full_call external port critical sg context before (OsIntExitReturned entry) /\
    let returned := os_int_exit_outcome_state before (OsIntExitReturned entry) in
    os_int_exit_wrapper_destination external port context returned incoming sp fragments /\
    after = os_int_exit_wrapper_restored_state returned incoming.

Lemma os_int_exit_wrapper_return_current :
  forall external port critical sg context before incoming sp fragments after,
  os_int_exit_wrapper_return_source external port critical sg context before
    incoming sp fragments after ->
  after.(SchedState).(curTaskID) = Some incoming.(stackLeaseSlot) /\
  exists node, after.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration).
Proof.
  intros external port critical sg context before incoming sp fragments after
    [entry [Hcall [Hdestination ->]]].
  destruct Hdestination as [Hcurrent [[node [Hnode [Hgeneration Hsp]]] Hrest]].
  split; [exact Hcurrent|]. exists node; split; assumption.
Qed.

Lemma os_int_exit_wrapper_return_preserves_validity :
  forall external port critical sg context before incoming sp fragments after,
  UCOS2_state_inv sg before ->
  os_int_exit_wrapper_return_source external port critical sg context before
    incoming sp fragments after -> UCOS2_state_inv sg after.
Proof.
  intros external port critical sg context before incoming sp fragments after Hvalid
    [entry [Hcall [Hdestination ->]]].
  pose proof (os_int_exit_full_call_preserves_validity external port critical sg
    context before (OsIntExitReturned entry) Hvalid Hcall) as Hreturned.
  unfold os_int_exit_wrapper_restored_state.
  apply UCOS2_replace_parked_stacks_preserves_validity; [exact Hreturned|].
  apply task_stack_take_preserves_consistency.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hreturned; tauto.
Qed.

Lemma os_int_exit_restore_consequence : forall external platform port critical sg context mask saved before entry,
  os_int_exit_body_facts external port critical sg context mask saved before entry ->
  os_int_exit_requests_switch true entry = false ->
  sg.(g_OSRunning) # UChar |-> os_int_exit_running (os_int_exit_ready_checkpoint true entry) **
  os_int_exit_outside_frame platform port critical sg context mask
    (os_int_exit_ready_checkpoint true entry) |--
  os_int_exit_post platform port critical sg context mask before.
Proof.
  intros external platform port critical sg context mask saved before entry
    [Hrunning [Hinterval [Hvalid [Hsaved Hsafe]]]] Hnoswitch.
  unfold os_int_exit_post; Exists entry; rewrite Hrunning.
  assert (Hfinal : UCOS2_state_inv sg (os_int_exit_ready_checkpoint true entry)).
  { apply os_int_exit_ready_checkpoint_preserves_validity; exact Hvalid. }
  unfold os_int_exit_return_relation; rewrite Hrunning; entailer!.
Qed.

Lemma os_int_exit_not_running_return : forall platform port critical sg context mask before,
  UCOS2_state_inv sg before -> os_int_exit_running before <> 1 ->
  sg.(g_OSRunning) # UChar |-> os_int_exit_running before **
  os_int_exit_outside_frame platform port critical sg context mask before |--
  os_int_exit_post platform port critical sg context mask before.
Proof.
  intros platform port critical sg context mask before Hvalid Hnotrunning.
  unfold os_int_exit_running in Hnotrunning.
  destruct before.(SchedState).(isRunning) eqn:Hrunning; [contradiction|].
  unfold os_int_exit_post; Exists before; rewrite Hrunning.
  unfold os_int_exit_return_relation; rewrite Hrunning; simpl.
  entailer!.
Qed.

Definition os_int_exit_counted_ints (entry : UCOS2_Verify_State) : Z :=
  (os_int_exit_after_nesting entry).(IntrState).(intNesting).

Definition os_int_exit_ready_tables (sg : StableGlobVars) (group : Z)
  (rows : list Z) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows **
  unmap_table_rep sg.

Lemma os_int_exit_sched_new_split_high : forall sg group rows high,
  sched_new_rep sg group rows high --||--
    sg.(g_OSPrioHighRdy) # UChar |-> high ** os_int_exit_ready_tables sg group rows.
Proof. intros; unfold sched_new_rep, os_int_exit_ready_tables; split; entailer!. Qed.

Definition os_int_exit_prefix_cells (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) : Assertion :=
  let counted := os_int_exit_after_nesting entry in
  os_sched_work_cells sg counted
    (if os_sched_selection_enabled counted then os_sched_selected counted else os_sched_old_high counted)
    (if os_sched_selection_enabled counted then os_sched_selected_tcb sg counted else os_sched_old_pointer sg counted)
    (if os_sched_requests_switch counted
     then (os_sched_counter counted + 1) mod 4294967296 else os_sched_counter counted).

Lemma os_int_exit_prefix_cells_merge : forall sg entry,
  UCOS2_state_inv sg entry ->
  (interrupt_exit_requests_schedule true entry.(IntrState) = true -> entry.(SchedState).(readyList) <> []) ->
  os_int_exit_prefix_cells sg entry |--
    UCOS2_inv sg (os_int_exit_ready_checkpoint true entry) ** unmap_table_rep sg.
Proof.
  intros sg entry Hvalid Hnonempty.
  pose proof (os_int_exit_prefix_merge_inv sg true entry Hvalid Hnonempty) as Hmerge.
  unfold os_int_exit_prefix_cells, os_sched_work_cells, os_sched_work_frame,
    os_int_exit_prefix_rep, os_sched_prefix_rep, os_sched_prefix_physical_rep,
    sched_new_rep, os_sched_ints, os_sched_locks, os_sched_group, os_sched_rows,
    os_sched_old_high, os_sched_old_pointer, os_sched_selected, os_sched_selected_tcb,
    os_sched_current, os_sched_counter, os_sched_table,
    task_public_storage, task_public_storage_without_prio_tbl, store_prio_tbl,
    UCOS2_raw_rep_missing_task_storage_sched, sched_physical_without_high,
    sched_cache_cells, os_sched_counter_stage in *.
  rewrite sched_rows_array_equiv in Hmerge.
  unfold UCOS2_selected_rep in *; cbn [UCOS2_module_rep] in *.
  pose proof (interrupt_inv_merge_counters sg
    (os_int_exit_after_nesting entry).(IntrState)) as Hintr.
  unfold store_int_state in Hintr.
  sep_apply_l_atomic Hintr.
  destruct (os_sched_selection_enabled (os_int_exit_after_nesting entry)) eqn:Hen;
    destruct (os_sched_requests_switch (os_int_exit_after_nesting entry)) eqn:Hswitch.
  - cbn [os_int_exit_after_nesting replace_IntrS TskState SchedState IntrState
      EventState TickState FlagState MemoryState TimerState StatsState ControlState NameState
      sched_increment_switch_counter curTaskID curSchedPrio isRunning ctxSwCtr] in Hmerge |- *.
    sep_apply_r_atomic Hmerge.
    entailer!.
  - cbn [os_int_exit_after_nesting replace_IntrS TskState SchedState IntrState
      EventState TickState FlagState MemoryState TimerState StatsState ControlState NameState]
      in Hmerge |- *.
    sep_apply_r_atomic Hmerge.
    entailer!.
  - unfold os_sched_requests_switch in Hswitch; rewrite Hen in Hswitch; discriminate.
  - unfold sched_physical_rep in Hmerge.
    cbn [os_int_exit_after_nesting replace_IntrS TskState SchedState IntrState
      EventState TickState FlagState MemoryState TimerState StatsState ControlState NameState]
      in Hmerge |- *.
    sep_apply_r_atomic Hmerge.
    entailer!.
Qed.
