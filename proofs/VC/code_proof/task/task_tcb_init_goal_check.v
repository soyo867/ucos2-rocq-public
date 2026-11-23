From Ucos2Verify.VC.code.task Require Import task_tcb_init_goal task_tcb_init_proof_auto task_tcb_init_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include task_tcb_init_proof_auto.
  Include task_tcb_init_proof_manual.
End VC_Correctness.
