From Ucos2Verify.VC.code.sched Require Import sched_del_history_goal sched_del_history_proof_auto_checked sched_del_history_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sched_del_history_proof_auto_checked.
  Include sched_del_history_proof_manual.
End VC_Correctness.
