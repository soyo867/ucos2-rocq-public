From Ucos2Verify.VC.code.tick Require Import time_tick_complement_goal time_tick_complement_proof_auto time_tick_complement_proof_manual.

Module VC_Correctness : VC_Correct.
  Include time_tick_complement_proof_auto.
  Include time_tick_complement_proof_manual.
End VC_Correctness.
