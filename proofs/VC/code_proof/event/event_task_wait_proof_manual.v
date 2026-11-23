Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.event Require Import event_task_wait_goal.
From Ucos2Verify.VC.code.event Require Import event_task_wait_proof_auto_checked.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_EventTaskWait_return_wit_1 : OS_EventTaskWait_return_wit_1.
Proof.
  unfold OS_EventTaskWait_return_wit_1; left; intros.
  prop_apply_p (store_uchar_range
    (&(tcb # "os_tcb" ->ₛ "OSTCBBitX")) bit_x).
  prop_apply_p (store_uchar_range
    (&(tcb # "os_tcb" ->ₛ "OSTCBBitY")) bit_y).
  Intros.
  change compcert.lib.Integers.Byte.max_unsigned with 255 in *.
  rewrite (unsigned_last_nbits_eq bit_x 8) by (change (0 <= bit_x < 256); lia).
  rewrite (unsigned_last_nbits_eq bit_y 8) by (change (0 <= bit_y < 256); lia).
  unfold event_task_wait_post, event_task_wait_ready_group, event_task_wait_ready_row.
  rewrite PreH1; cbn [Z.eqb].
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskWait_return_wit_2 : OS_EventTaskWait_return_wit_2.
Proof.
  unfold OS_EventTaskWait_return_wit_2; left; intros.
  prop_apply_p (store_uchar_range
    (&(tcb # "os_tcb" ->ₛ "OSTCBBitX")) bit_x).
  prop_apply_p (store_uchar_range
    (&(tcb # "os_tcb" ->ₛ "OSTCBBitY")) bit_y).
  Intros.
  change compcert.lib.Integers.Byte.max_unsigned with 255 in *.
  rewrite (unsigned_last_nbits_eq bit_x 8) by (change (0 <= bit_x < 256); lia).
  rewrite (unsigned_last_nbits_eq bit_y 8) by (change (0 <= bit_y < 256); lia).
  unfold event_task_wait_post, event_task_wait_ready_group, event_task_wait_ready_row.
  apply Z.eqb_neq in PreH1; rewrite PreH1.
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskWait_which_implies_wit_1 : OS_EventTaskWait_which_implies_wit_1.
Proof.
  unfold OS_EventTaskWait_which_implies_wit_1; left; intros.
  prop_apply_p (store_uchar_range
    (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR)) event_row).
  prop_apply_p (store_uchar_range
    (&(pevent # "os_event" ->ₛ "OSEventGrp")) event_group).
  Intros.
  change compcert.lib.Integers.Byte.max_unsigned with 255 in *.
  entailer!.
Qed.
