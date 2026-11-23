From Ucos2Verify.VC.code.memory Require Import mem_init_goal mem_init_proof_auto mem_init_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mem_init_proof_auto.
  Include mem_init_proof_manual.
End VC_Correctness.
