Require Import Coq.ZArith.ZArith Coq.Strings.String.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_source_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Static symbol interpretation and the explicit module R/G composition
    condition for the real Scheduler callee. No ready-client theorem is
    inferred from the old source-classification configuration. The public
    Del admission below only consumes this in OS_DEL_ALWAYS after the ordered
    early checks. OS_DEL_NO_PEND has no Scheduler dependency. *)
Definition mutex_del_scheduler_link sg configuration : Prop :=
  os_sched_global_addresses sg &("OSIntNesting") &("OSLockNesting")
    &("OSPrioHighRdy") &("OSPrioCur") &("OSTCBHighRdy") &("OSTCBPrioTbl")
    &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl") /\
  kernel_sched_ready_clients (mutex_program_region configuration).

Definition mutex_del_scheduler_admission sg configuration pe before eid opt : Prop :=
  mutex_del_parent_prefix_ok pe before eid -> opt = 1 ->
  mutex_del_scheduler_link sg configuration.

Lemma mutex_del_scheduler_admission_continue : forall sg configuration pe before eid opt,
  mutex_del_scheduler_admission sg configuration pe before eid opt ->
  mutex_del_parent_prefix_ok pe before eid -> opt = 1 ->
  mutex_del_scheduler_link sg configuration.
Proof. intros; apply H; assumption. Qed.

Lemma mutex_del_scheduler_admission_early : forall sg configuration pe before eid opt error,
  mutex_del_before_save_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) = Some error ->
  mutex_del_scheduler_admission sg configuration pe before eid opt.
Proof.
  intros; unfold mutex_del_scheduler_admission, mutex_del_parent_prefix_ok; congruence.
Qed.

Lemma mutex_del_scheduler_admission_no_schedule : forall sg configuration pe before eid opt,
  opt <> 1 -> mutex_del_scheduler_admission sg configuration pe before eid opt.
Proof. intros; unfold mutex_del_scheduler_admission; intros; contradiction. Qed.
