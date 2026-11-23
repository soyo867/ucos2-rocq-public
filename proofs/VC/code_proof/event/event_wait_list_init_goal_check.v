From Ucos2Verify.VC.code.event Require Import event_wait_list_init_goal event_wait_list_init_proof_auto_checked event_wait_list_init_proof_manual.

Module VC_Correctness : VC_Correct.
  Include event_wait_list_init_proof_auto_checked.
  Include event_wait_list_init_proof_manual.
End VC_Correctness.
