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
From Ucos2Verify.VC.code.event Require Import event_task_remove_goal.
From Ucos2Verify.VC.code.event Require Import event_task_remove_proof_auto_checked.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OS_EventTaskRemove_return_wit_1 : OS_EventTaskRemove_return_wit_1.
Proof.
  unfold OS_EventTaskRemove_return_wit_1; left.
  intros pevent ptcb group_value row_value bit_y bit_x row Hzero Hlo Hhi.
  unfold event_task_remove_post, event_task_remove_group,
    event_task_remove_cleared.
  cbn [Ucos2Verify.lib.task_storage.tcb_field_address].
  rewrite Hzero, Z.eqb_refl.
  rewrite sizeof_uchar, Z.mul_1_r.
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRemove_return_wit_2 : OS_EventTaskRemove_return_wit_2.
Proof.
  unfold OS_EventTaskRemove_return_wit_2; left.
  intros pevent ptcb group_value row_value bit_y bit_x row Hnonzero Hlo Hhi.
  unfold event_task_remove_post, event_task_remove_group,
    event_task_remove_cleared.
  cbn [Ucos2Verify.lib.task_storage.tcb_field_address].
  assert (Hguard : Z.eqb
    (Z.land row_value (unsigned_last_nbits (Z.lnot bit_x) 8)) 0 = false)
    by (apply Z.eqb_neq; exact Hnonzero).
  rewrite Hguard, sizeof_uchar, Z.mul_1_r.
  entailer!.
Qed.

Lemma proof_of_OS_EventTaskRemove_which_implies_wit_1 : OS_EventTaskRemove_which_implies_wit_1.
Proof.
  unfold OS_EventTaskRemove_which_implies_wit_1; left.
  intros group_value row_value bit_y bit_x row pevent ptcb.
  unfold event_task_remove_pre.
  cbn [Ucos2Verify.lib.task_storage.tcb_field_address].
  rewrite sizeof_uchar, Z.mul_1_r.
  entailer!.
Qed.
