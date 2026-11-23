Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_active_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Import UCOS2_C_Rules PendPhaseCandidate.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendActiveProtocol.

(** These are the three local assertion families at the actual Pend call
    sites. This selection contains no assertion about a future execution.
    Preservation and recovery are separately proved for the actual C source. *)
Inductive flag_pend_active_protocol (sg : StableGlobVars) :
  (OsSchedCallContext -> UCOS2_Verify_State -> Assertion) -> Prop :=
| FlagPendActiveFirst : forall mode original initial,
    flag_pend_active_protocol sg (flag_pend_first_observation mode original initial)
| FlagPendActiveWaiting : forall original node,
    flag_pend_active_protocol sg (flag_pend_wait_active sg original node)
| FlagPendActiveFresh : forall original,
    flag_pend_active_protocol sg (flag_pend_fresh_observation original).

Lemma flag_pend_active_protocol_first : forall sg mode original initial,
  flag_pend_active_protocol sg (flag_pend_first_observation mode original initial).
Proof. intros; constructor. Qed.

Lemma flag_pend_active_protocol_waiting : forall sg original node,
  flag_pend_active_protocol sg (flag_pend_wait_active sg original node).
Proof. intros; constructor. Qed.

Lemma flag_pend_active_protocol_fresh : forall sg original,
  flag_pend_active_protocol sg (flag_pend_fresh_observation original).
Proof. intros; constructor. Qed.

Lemma flag_pend_first_observation_prefix_stable : forall mode original initial,
  os_sched_active_local_stable (flag_pend_first_observation mode original initial).
Proof.
  intros mode original initial call state.
  unfold flag_pend_first_observation, flag_pend_first_registration,
    flag_active_fresh_registration, flag_active_task_fields.
  split; reflexivity.
Qed.

Lemma flag_pend_fresh_observation_prefix_stable : forall original,
  os_sched_active_local_stable (flag_pend_fresh_observation original).
Proof.
  intros original call state.
  unfold flag_pend_fresh_observation, flag_active_fresh_registration, flag_active_task_fields.
  split; reflexivity.
Qed.

Lemma flag_pend_active_protocol_prefix_stable : forall sg active,
  flag_pend_active_protocol sg active -> os_sched_active_local_stable active.
Proof.
  intros sg active Hprotocol; destruct Hprotocol.
  - apply flag_pend_first_observation_prefix_stable.
  - apply flag_pend_wait_active_prefix.
  - apply flag_pend_fresh_observation_prefix_stable.
Qed.

End FlagPendActiveProtocol.
