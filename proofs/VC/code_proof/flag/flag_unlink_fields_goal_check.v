From Ucos2Verify.VC.code.flag Require Import flag_unlink_fields_goal flag_unlink_fields_proof_auto flag_unlink_fields_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_unlink_fields_proof_auto.
  Include flag_unlink_fields_proof_manual.
End VC_Correctness.
