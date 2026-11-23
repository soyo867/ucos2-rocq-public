From Ucos2Verify.VC.code.mutex Require Import pend_native_goal pend_native_proof_auto_checked pend_native_proof_manual.

Module VC_Correctness : VC_Correct.
  Include pend_native_proof_auto_checked.
  Include pend_native_proof_manual.
End VC_Correctness.
