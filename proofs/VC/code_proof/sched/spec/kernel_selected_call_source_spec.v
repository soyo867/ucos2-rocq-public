Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The source-selected descriptor decides whether this is an initial C
    entry or the continuation of an existing call. Only initial entry
    registers a fresh invocation; a saved call keeps its actual identity. *)
Definition kernel_selected_call (selected : Armv7aContinuation)
  (state : UCOS2_Verify_State) : OsSchedCallContext :=
  match selected.(armv7a_continuation_call) with
  | Some previous => armv7a_continuation_resumed_call selected previous
  | None => armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
      selected.(armv7a_continuation_fragments)
  end.

Definition kernel_selected_call_state (selected : Armv7aContinuation)
  (state : UCOS2_Verify_State) : UCOS2_Verify_State :=
  match selected.(armv7a_continuation_call) with
  | Some _ => state
  | None => armv7a_initial_call_registered selected state
  end.

(** A running task and an earlier pending call share this ONE world.
    [active] records the actual stack-coverage exception. It does not
    assert that the running invocation is registered: a saved descriptor
    alone has no such lifecycle fact. The pending identity remains in the
    focused continuation entry, backed by its physical parked bytes. *)
Definition kernel_pending_call_world {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg focus payload active state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) active /\
    state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) &&
  (kernel_program_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
    state.(TskState).(parkedTaskStacks)).

Lemma kernel_selected_call_stack : forall selected state,
  (kernel_selected_call selected state).(os_sched_call_stack) = selected.(armv7a_continuation_stack).
Proof.
  intros; unfold kernel_selected_call; destruct selected.(armv7a_continuation_call); reflexivity.
Qed.

(** Preserve the old observer, never infer its registration from a CPU
    token. In the None branch the existing begin-invocation proof supplies
    freshness, using validity of the actual pre-registration world. *)
Lemma kernel_selected_call_preserves_pending_fields : forall sg selected state original lease sp,
  UCOS2_state_inv sg state ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  task_saved_pointer_at state lease sp ->
  task_invocation_active (kernel_selected_call_state selected state).(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
  task_saved_pointer_at (kernel_selected_call_state selected state) lease sp.
Proof.
  intros sg selected state original lease sp Hvalid Hactive Hpointer.
  unfold kernel_selected_call_state; destruct selected.(armv7a_continuation_call); [auto|].
  split; [|exact Hpointer].
  apply task_begin_invocation_preserves_invocation_active; [|exact Hactive].
  pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto.
Qed.

(** Both selector producers already own these resources. None consumes
    the approved initial-entry contract and establishes a new invocation;
    Some consumes the restored continuation directly. This theorem does
    not assume any future foreign body, return, or IRQ. *)
Lemma kernel_selected_call_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (entry : Armv7aInitialCallABI external platform port abi)
  sg focus payload incoming selected node state,
  (selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected) ->
  (selected.(armv7a_continuation_call) = None ->
    task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
      0 selected.(armv7a_continuation_fragments)) ->
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  os_sched_source_selected_post external platform port abi sg focus incoming selected node state **
    unmap_table_rep sg |--
  let call := kernel_selected_call selected state in
  let current := kernel_selected_call_state selected state in
  coq_prop (call.(os_sched_call_stack) = incoming /\
    sched_current_ready_at current.(TskState) current.(SchedState) incoming.(stackLeaseSlot) node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    (selected.(armv7a_continuation_call) = None -> kernel_call_task_source call current)) &&
  (kernel_call_execution_owned external platform call
     (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
   kernel_pending_call_world abi sg focus payload (Some (task_stack_key incoming)) current).
Proof.
  intros external platform port abi entry sg focus payload incoming selected node state
    Hinitial Hgeometry Hpending; cbv zeta.
  unfold os_sched_source_selected_post; Intros.
  assert (Hlease : selected.(armv7a_continuation_stack) = incoming) by tauto.
  assert (Hready : sched_current_ready_at state.(TskState) state.(SchedState) incoming.(stackLeaseSlot) node)
    by tauto.
  assert (Hgeneration : node.(taskGeneration) = incoming.(stackLeaseGeneration)) by tauto.
  assert (Hcoverage : task_stack_live_coverage state.(TskState) (Some (task_stack_key incoming))) by tauto.
  unfold kernel_selected_call, kernel_selected_call_state, armv7a_task_restored_execution.
  destruct selected.(armv7a_continuation_call) as [previous|] eqn:Hselected.
  - unfold kernel_pending_call_world; rewrite kernel_program_inv_split_unmap.
    cbn [armv7a_continuation_resumed_call os_sched_call_stack]; entailer!; discriminate.
  - assert (Hcurrent : task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
      selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
    { rewrite Hlease; split; [exact (proj1 (proj2 Hready))|].
      exists node; exact (conj (proj1 Hready) Hgeneration). }
    pose proof (armv7a_initial_call_register_resources external platform port abi entry sg state selected
      selected.(armv7a_continuation_fragments) (Hinitial eq_refl) (Hgeometry eq_refl) Hcurrent) as Hregister.
    cbv zeta in Hregister; sep_apply_l_atomic Hregister; Intros.
    unfold kernel_pending_call_world; rewrite kernel_program_inv_split_unmap.
    change (armv7a_task_call_stacks abi (armv7a_initial_call_registered selected state).(TskState) focus
      (armv7a_initial_call_registered selected state).(TskState).(parkedTaskStacks)) with
      (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks)).
    cbn [armv7a_initial_call os_sched_call_stack]; entailer!.
Qed.

