From Ucos2Verify.VC.code.flag Require Import flag_name_get_goal flag_name_get_proof_auto flag_name_get_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_name_get_proof_auto.
  Include flag_name_get_proof_manual.
End VC_Correctness.
