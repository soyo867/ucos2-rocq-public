From Ucos2Verify.VC.code.sched Require Import
  sched_lock_call_goal sched_lock_call_proof_auto_checked sched_lock_call_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sched_lock_call_proof_auto_checked.
  Include sched_lock_call_proof_manual.
End VC_Correctness.
