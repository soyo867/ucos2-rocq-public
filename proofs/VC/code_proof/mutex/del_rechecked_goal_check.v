From Ucos2Verify.VC.code.mutex Require Import del_rechecked_goal del_rechecked_proof_auto del_rechecked_proof_manual.

Module VC_Correctness : VC_Correct.
  Include del_rechecked_proof_auto.
  Include del_rechecked_proof_manual.
End VC_Correctness.
