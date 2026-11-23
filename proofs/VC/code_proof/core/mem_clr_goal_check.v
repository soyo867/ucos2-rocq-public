From Ucos2Verify.VC.code.core Require Import mem_clr_goal mem_clr_proof_auto mem_clr_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mem_clr_proof_auto.
  Include mem_clr_proof_manual.
End VC_Correctness.
