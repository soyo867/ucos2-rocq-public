From Ucos2Verify.VC.code.time Require Import time_get_goal time_get_proof_auto time_get_proof_manual.

Module VC_Correctness : VC_Correct.
  Include time_get_proof_auto.
  Include time_get_proof_manual.
End VC_Correctness.
