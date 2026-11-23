From Ucos2Verify.VC.code.flag Require Import flag_accept_goal flag_accept_proof_auto flag_accept_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_accept_proof_auto.
  Include flag_accept_proof_manual.
End VC_Correctness.
