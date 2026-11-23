From Ucos2Verify.VC.code.task Require Import task_resume_goal task_resume_proof_auto task_resume_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_resume_proof_auto.
  Include task_resume_proof_manual.
End VC_Correctness.
