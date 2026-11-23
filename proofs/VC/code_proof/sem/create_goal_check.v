From Ucos2Verify.VC.code.sem Require Import create_goal create_proof_auto create_proof_manual.

Module VC_Correctness : VC_Correct.
  Include create_proof_auto.
  Include create_proof_manual.
End VC_Correctness.
