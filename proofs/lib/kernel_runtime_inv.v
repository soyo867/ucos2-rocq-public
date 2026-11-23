Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.task_idle_ready.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** The initialized C kernel's running protocol.  The earlier structural
    invariant records an Idle tail but does not imply that Idle is ready.
    Publication/start establish the additional observation; registered C
    operations must preserve it.  It is neither an ARM postcondition nor
    a fact about an arbitrary structurally valid kernel state.

    Active-call stack availability is deliberately separate: the active
    key can be parked during an interrupt and removed again on return. *)
Definition kernel_running_idle_ready (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Prop :=
  state.(SchedState).(isRunning) = true -> task_idle_ready sg state.(TskState).

Definition kernel_runtime_inv (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (kernel_running_idle_ready sg state) && kernel_program_inv sg state.
