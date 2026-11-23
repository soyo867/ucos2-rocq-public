From Ucos2Verify.VC.code.tick Require Import app_time_tick_hook_goal app_time_tick_hook_proof_auto app_time_tick_hook_proof_manual.

Module VC_Correctness : VC_Correct.
  Include app_time_tick_hook_proof_auto.
  Include app_time_tick_hook_proof_manual.
End VC_Correctness.
