From Ucos2Verify.VC.code.memory Require Import mem_get_goal mem_get_proof_auto mem_get_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mem_get_proof_auto.
  Include mem_get_proof_manual.
End VC_Correctness.
