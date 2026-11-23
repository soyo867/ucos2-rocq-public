From Ucos2Verify.VC.code.task Require Import task_del_req_goal task_del_req_proof_auto task_del_req_proof_manual.

Module VC_Correctness : VC_Correct.
  Include task_del_req_proof_auto.
  Include task_del_req_proof_manual.
End VC_Correctness.
