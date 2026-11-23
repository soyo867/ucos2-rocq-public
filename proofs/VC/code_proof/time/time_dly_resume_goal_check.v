From Ucos2Verify.VC.code.time Require Import time_dly_resume_goal time_dly_resume_proof_auto time_dly_resume_proof_manual.

Module VC_Correctness : VC_Correct.
  Include time_dly_resume_proof_auto.
  Include time_dly_resume_proof_manual.
End VC_Correctness.
