From Ucos2Verify.VC.code.time Require Import time_set_goal time_set_proof_auto time_set_proof_manual.

Module VC_Correctness : VC_Correct.
  Include time_set_proof_auto.
  Include time_set_proof_manual.
End VC_Correctness.
