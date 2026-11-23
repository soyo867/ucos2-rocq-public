From Ucos2Verify.VC.code.memory Require Import mem_name_set_goal mem_name_set_proof_auto mem_name_set_proof_manual.

Module VC_Correctness : VC_Correct.
  Include mem_name_set_proof_auto.
  Include mem_name_set_proof_manual.
End VC_Correctness.
