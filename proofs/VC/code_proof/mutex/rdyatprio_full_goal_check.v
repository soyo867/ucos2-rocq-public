From Ucos2Verify.VC.code.mutex Require Import rdyatprio_full_goal rdyatprio_full_proof_auto rdyatprio_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include rdyatprio_full_proof_auto.
  Include rdyatprio_full_proof_manual.
End VC_Correctness.
