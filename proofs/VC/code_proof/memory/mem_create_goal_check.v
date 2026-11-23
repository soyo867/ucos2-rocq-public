From Ucos2Verify.VC.code.memory Require Import mem_create_goal mem_create_proof_auto mem_create_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mem_create_proof_auto.
  Include mem_create_proof_manual.
End VC_Correctness.
