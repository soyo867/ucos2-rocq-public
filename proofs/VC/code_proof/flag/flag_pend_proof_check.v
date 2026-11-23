(** Complete current VC interface instance; prepared, not yet checked. *)
Require Import Ucos2Verify.VC.code.flag.flag_pend_goal.
Require Import Ucos2Verify.VC.code.flag.flag_pend_proof_auto.
Require Import Ucos2Verify.VC.code.flag.flag_pend_proof_manual.

Module VC_Correctness <: Ucos2Verify.VC.code.flag.flag_pend_goal.VC_Correct.
  Include Ucos2Verify.VC.code.flag.flag_pend_proof_auto.PendPhaseAutoProofs.
  Include Ucos2Verify.VC.code.flag.flag_pend_proof_manual.PendManualProofs.
End VC_Correctness.
