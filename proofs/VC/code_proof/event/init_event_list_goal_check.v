From Ucos2Verify.VC.code.event Require Import init_event_list_goal init_event_list_proof_auto init_event_list_proof_manual.

Module VC_Correctness : VC_Correct.
  Include init_event_list_proof_auto.
  Include init_event_list_proof_manual.
End VC_Correctness.
