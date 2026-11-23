From Ucos2Verify.VC.code.mutex Require Import create_native_goal create_native_proof_auto_checked create_native_proof_manual.

Module VC_Correctness : VC_Correct.
  Include create_native_proof_auto_checked.
  Include create_native_proof_manual.
End VC_Correctness.
