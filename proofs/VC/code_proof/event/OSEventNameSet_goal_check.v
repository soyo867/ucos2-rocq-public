From Ucos2Verify.VC.code.event Require Import OSEventNameSet_goal OSEventNameSet_proof_auto OSEventNameSet_proof_manual.

Module VC_Correctness : VC_Correct.
  Include OSEventNameSet_proof_auto.
  Include OSEventNameSet_proof_manual.
End VC_Correctness.
