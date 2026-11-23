From Ucos2Verify.VC.code.interrupt Require Import
  int_exit_goal int_exit_proof_auto_checked int_exit_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_exit_proof_auto_checked.
  Include int_exit_proof_manual.
End VC_Correctness.
