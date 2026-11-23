From Ucos2Verify.VC.code.sched Require Import sched_del_continuation_goal sched_del_continuation_proof_auto sched_del_continuation_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sched_del_continuation_proof_auto.
  Include sched_del_continuation_proof_manual.
End VC_Correctness.
