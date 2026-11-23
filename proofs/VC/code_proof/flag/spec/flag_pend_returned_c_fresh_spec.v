Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_fresh_recovery_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_fresh_fields_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_returned_c_segment_spec.

Module OSIntExitReturnedFresh.
Import OSIntExitReturnedC FlagPendFreshRecovery FlagPendFreshSource.

Lemma os_int_exit_returned_c_step_preserves_fresh_fields :
  forall environment critical sg entry before input stopped current after output origin,
  os_int_exit_returned_c_step environment critical sg entry before input stopped current after output ->
  flag_pend_fresh_fields_at_origin origin entry ->
  flag_pend_fresh_fields_at_origin origin current.
Proof.
  intros until origin; intros Hstep Hfields.
  eapply flag_pend_fresh_fields_used_eq.
  - exact (proj1 (os_int_exit_returned_c_step_task_fields _ _ _ _ _ _ _ _ _ _ Hstep)).
  - exact Hfields.
Qed.

End OSIntExitReturnedFresh.
