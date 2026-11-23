From Ucos2Verify.VC.code.sched Require Import init_rdy_list_goal init_rdy_list_proof_auto init_rdy_list_proof_manual.

Module VC_Correctness : VC_Correct.
  Include init_rdy_list_proof_auto.
  Include init_rdy_list_proof_manual.
End VC_Correctness.
