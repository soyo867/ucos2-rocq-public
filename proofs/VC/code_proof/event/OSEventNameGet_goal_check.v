From Ucos2Verify.VC.code.event Require Import OSEventNameGet_goal OSEventNameGet_proof_auto OSEventNameGet_proof_manual.

Module VC_Correctness : VC_Correct.
  Include OSEventNameGet_proof_auto.
  Include OSEventNameGet_proof_manual.
End VC_Correctness.
