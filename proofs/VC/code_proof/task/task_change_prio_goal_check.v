From Ucos2Verify.VC.code.task Require Import task_change_prio_goal task_change_prio_proof_auto task_change_prio_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include task_change_prio_proof_auto.
  Include task_change_prio_proof_manual.
End VC_Correctness.
