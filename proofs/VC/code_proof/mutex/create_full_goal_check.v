From Ucos2Verify.VC.code.mutex Require Import create_full_goal create_full_proof_auto create_full_proof_manual.

Module VC_Correctness : VC_Correct.
  Include create_full_proof_auto.
  Include create_full_proof_manual.
End VC_Correctness.
