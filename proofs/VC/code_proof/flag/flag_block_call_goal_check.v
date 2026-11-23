From Ucos2Verify.VC.code.flag Require Import flag_block_call_goal flag_block_call_proof_auto flag_block_call_proof_manual.

Module VC_Correctness : VC_Correct.
  Include flag_block_call_proof_auto.
  Include flag_block_call_proof_manual.
End VC_Correctness.
