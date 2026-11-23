From Ucos2Verify.VC.code.flag Require Import flag_del_goal flag_del_proof_auto flag_del_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_del_proof_auto.
  Include flag_del_proof_manual.
End VC_Correctness.
