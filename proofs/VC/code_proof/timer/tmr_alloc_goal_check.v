From Ucos2Verify.VC.code.timer Require Import tmr_alloc_goal tmr_alloc_proof_auto tmr_alloc_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmr_alloc_proof_auto.
  Include tmr_alloc_proof_manual.
End VC_Correctness.
