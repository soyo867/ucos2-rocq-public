From Ucos2Verify.VC.code.tick Require Import
  time_tick_hook_isr_goal time_tick_hook_isr_proof_auto_checked time_tick_hook_isr_proof_manual.
Module VC_Correctness : VC_Correct.
  Include time_tick_hook_isr_proof_auto_checked.
  Include time_tick_hook_isr_proof_manual.
End VC_Correctness.
