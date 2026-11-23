Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.

Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The caller uses semantic error constructors while OS_TCBInit's existing
    result observation records its INT8U value.  Use the shared encoding,
    not a second error catalog or an unconstrained return observer.  This
    adapter does not add a stack/platform implementation or replace the
    caller's required entry and physical-resource evidence. *)
Definition task_create_tcb_init_call (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (args : TaskTCBInitArgs) : program UCOS2_Verify_State OSErrCode :=
  fun initial result released =>
    task_tcb_init_result critical sg args invocation origin initial
      (encode_os_err_code result) released.

Lemma task_create_tcb_init_call_return_cases :
  forall critical sg invocation origin args initial result released,
  task_create_tcb_init_call critical sg invocation origin args initial result released ->
  result = OS_ERR_NONE \/ result = OS_ERR_TASK_NO_MORE_TCB.
Proof.
  intros critical sg invocation origin args initial result released Hcall.
  destruct (task_tcb_init_result_return_codes critical sg args invocation origin
    initial (encode_os_err_code result) released Hcall) as [Hsuccess|Hno_free].
  - left; apply encode_os_err_code_injective; exact Hsuccess.
  - right; apply encode_os_err_code_injective; exact Hno_free.
Qed.

Lemma task_create_tcb_init_call_no_free_iff :
  forall critical sg invocation origin args initial released,
  task_create_tcb_init_call critical sg invocation origin args
    initial OS_ERR_TASK_NO_MORE_TCB released <->
  task_tcb_init_result critical sg args invocation origin initial 66 released.
Proof. reflexivity. Qed.

Lemma task_create_initialization_return_cases :
  forall critical sg invocation origin clear_stack initialize_stack enabled args initial_name
    before result released,
  task_create_initialization clear_stack initialize_stack
    (task_create_tcb_init_call critical sg invocation origin)
    enabled args initial_name before result released ->
  result = OS_ERR_NONE \/ result = OS_ERR_TASK_NO_MORE_TCB.
Proof.
  intros critical sg invocation origin clear_stack initialize_stack enabled args initial_name
    before result released
    [before_init [stack_pointer [after_init [Hclear [Hstack Htcb]]]]].
  eapply task_create_tcb_init_call_return_cases; exact Htcb.
Qed.

(** Only the protected OSTCBPrioTbl[prio] = NULL body is described here.
    This has no extra C test: the lifecycle guard is proved separately from
    the caller's failed initialization and protected pending fragment.
    Save, its exact token, Restore and any subsequent interference must wrap
    this body before it can instantiate task_create_tail's [rollback] call.
    In particular this transformer does not restore an old global snapshot. *)
Definition task_create_rollback_store (priority : Priority)
  : program UCOS2_Verify_State unit :=
  fun before result after => result = tt /\
    after = replace_TskS (task_rollback_reservation before.(TskState) priority) before.

Lemma task_create_no_free_rollback_store_client :
  forall critical sg args invocation origin initial released acquired result after,
  task_tcb_init_result critical sg args invocation origin initial 66 released ->
  critical_region_interval critical sg invocation released acquired ->
  task_create_rollback_store args.(initPrio) acquired result after ->
  kernel_client_step (task_create_rollback_client args.(initPrio) invocation) sg acquired after.
Proof.
  intros critical sg args invocation origin initial released acquired result after
    Hresult Hinterval [_ Hafter].
  destruct (task_create_no_free_after_environment critical sg args invocation origin
    initial released acquired Hresult Hinterval) as [Hguard Hvalid].
  split; [exact Hguard|exact Hafter].
Qed.

(** Spatial consumer for the real failed-creation store.  The antecedent
    contains the ACTUAL cell after it has been written to zero, and the
    missing table/residual of the current acquired state.  Neither pure
    validity nor a lifecycle-frame equality manufactures that ownership.
    Slot identity and continuation evidence are transported from the same
    original invocation, not chosen after the environment has run. *)
Lemma task_create_no_free_rollback_merge_inv :
  forall critical sg args invocation origin initial released acquired,
  task_tcb_init_entry sg args invocation origin initial ->
  task_tcb_init_result critical sg args invocation origin initial 66 released ->
  critical_region_interval critical sg invocation released acquired ->
  (sg.(g_OSTCBPrioTbl) + args.(initPrio) * sizeof(PTR)) # Ptr |-> 0 **
    store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) args.(initPrio) **
    UCOS2_raw_rep_missing_priority_table sg acquired |--
  coq_prop (task_invocation_active
    (task_rollback_reservation acquired.(TskState) args.(initPrio)) invocation origin) &&
  UCOS2_inv sg
    (replace_TskS (task_rollback_reservation acquired.(TskState) args.(initPrio)) acquired).
Proof.
  intros critical sg args invocation origin initial released acquired Hentry Hresult Hinterval.
  assert (Hreleased : task_tcb_init_entry sg args invocation origin released).
  { inversion Hresult; subst; eapply task_tcb_init_acquire_entry; eassumption. }
  pose proof (task_tcb_init_acquire_entry critical sg args invocation origin
    released acquired Hreleased Hinterval) as Hacquired.
  destruct (task_create_no_free_after_environment critical sg args invocation origin
    initial released acquired Hresult Hinterval) as [Hguard Hpost].
  pose proof (task_create_no_free_preserves_continuation critical sg args invocation origin
    initial released acquired Hentry Hresult Hinterval) as Hactive.
  eapply derivable1_trans.
  - apply UCOS2_inv_merge_rollback_priority with (invocation := invocation);
      [exact (proj1 Hacquired)|exact Hguard].
  - entailer!.
Qed.

Lemma task_create_tcb_no_free_rollback_merge_inv :
  forall critical sg args invocation origin initial released acquired result after,
  task_tcb_init_entry sg args invocation origin initial ->
  task_create_tcb_init_call critical sg invocation origin args
    initial OS_ERR_TASK_NO_MORE_TCB released ->
  critical_region_interval critical sg invocation released acquired ->
  task_create_rollback_store args.(initPrio) acquired result after ->
  (sg.(g_OSTCBPrioTbl) + args.(initPrio) * sizeof(PTR)) # Ptr |-> 0 **
    store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) args.(initPrio) **
    UCOS2_raw_rep_missing_priority_table sg acquired |--
  coq_prop (result = tt /\ task_invocation_active after.(TskState) invocation origin) &&
  UCOS2_inv sg after.
Proof.
  intros critical sg args invocation origin initial released acquired result after
    Hentry Hcall Hinterval [Hunit Hafter].
  subst result; subst after.
  sep_apply_l_atomic (task_create_no_free_rollback_merge_inv critical sg args invocation origin
    initial released acquired Hentry Hcall Hinterval).
  entailer!.
Qed.
