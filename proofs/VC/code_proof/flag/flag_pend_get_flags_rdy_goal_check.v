From Ucos2Verify.VC.code.flag Require Import flag_pend_get_flags_rdy_goal flag_pend_get_flags_rdy_proof_auto flag_pend_get_flags_rdy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_pend_get_flags_rdy_proof_auto.
  Include flag_pend_get_flags_rdy_proof_manual.
End VC_Correctness.
