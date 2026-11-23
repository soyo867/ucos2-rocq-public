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
From Ucos2Verify.VC.code.interrupt Require Import int_enter_api_goal.
From Ucos2Verify.VC.code.interrupt Require Import int_enter_api_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_api_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSIntEnter_return_wit_1 : OSIntEnter_return_wit_1.
Proof.
  unfold OSIntEnter_return_wit_1; left.
  intros X before sg mask origin invocation platform Hlt Hguard Haddr Hvalid
    Hnonnegative Hbounded Haddr' Hmasked Hsafe.
  assert (Hrunning : isRunning (SchedState before) = true).
  { unfold os_int_enter_running in Hguard.
    destruct (isRunning (SchedState before)); [reflexivity |].
    vm_compute in Hguard; discriminate. }
  assert (Htest : (intNesting (IntrState before) <? 255) = true).
  { apply Z.ltb_lt; exact Hlt. }
  assert (Hnesting : os_int_enter_nesting (os_int_enter_state before) =
    os_int_enter_nesting before + 1).
  { change (intNesting (interrupt_enter_state
      (isRunning (SchedState before)) (IntrState before)) =
      intNesting (IntrState before) + 1).
    unfold interrupt_enter_state; rewrite Hrunning, Htest; reflexivity. }
  pose proof (os_int_enter_inv_merge sg before Hvalid) as Hmerge.
  destruct Haddr as [Hrunning_address Hnesting_address].
  rewrite <- Hrunning_address, <- Hnesting_address, Hnesting in Hmerge.
  pose proof (os_int_enter_safe_return before X Hsafe) as Hreturn.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed. 

Lemma proof_of_OSIntEnter_return_wit_2 : OSIntEnter_return_wit_2.
Proof.
  unfold OSIntEnter_return_wit_2; left.
  intros X before sg mask origin invocation platform Hge Hguard Haddr Hvalid
    Hnonnegative Hbounded Haddr' Hmasked Hsafe.
  assert (Hrunning : isRunning (SchedState before) = true).
  { unfold os_int_enter_running in Hguard.
    destruct (isRunning (SchedState before)); [reflexivity |].
    vm_compute in Hguard; discriminate. }
  assert (Htest : (intNesting (IntrState before) <? 255) = false).
  { apply Z.ltb_ge; unfold os_int_enter_nesting in Hge; lia. }
  assert (Hnesting : os_int_enter_nesting (os_int_enter_state before) =
    os_int_enter_nesting before).
  { change (intNesting (interrupt_enter_state
      (isRunning (SchedState before)) (IntrState before)) =
      intNesting (IntrState before)).
    unfold interrupt_enter_state; rewrite Hrunning, Htest; reflexivity. }
  pose proof (os_int_enter_inv_merge sg before Hvalid) as Hmerge.
  destruct Haddr as [Hrunning_address Hnesting_address].
  rewrite <- Hrunning_address, <- Hnesting_address, Hnesting in Hmerge.
  pose proof (os_int_enter_safe_return before X Hsafe) as Hreturn.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed. 

Lemma proof_of_OSIntEnter_return_wit_3 : OSIntEnter_return_wit_3.
Proof.
  unfold OSIntEnter_return_wit_3; left.
  intros X before sg mask origin invocation platform Hguard Haddr Hvalid
    Hnonnegative Hbounded Haddr' Hmasked Hsafe.
  assert (Hrunning : isRunning (SchedState before) = false).
  { unfold os_int_enter_running in Hguard.
    destruct (isRunning (SchedState before)); [|reflexivity].
    exfalso; apply Hguard; reflexivity. }
  assert (Hnesting : os_int_enter_nesting (os_int_enter_state before) =
    os_int_enter_nesting before).
  { change (intNesting (interrupt_enter_state
      (isRunning (SchedState before)) (IntrState before)) =
      intNesting (IntrState before)).
    unfold interrupt_enter_state; rewrite Hrunning; reflexivity. }
  pose proof (os_int_enter_inv_merge sg before Hvalid) as Hmerge.
  destruct Haddr as [Hrunning_address Hnesting_address].
  rewrite <- Hrunning_address, <- Hnesting_address, Hnesting in Hmerge.
  pose proof (os_int_enter_safe_return before X Hsafe) as Hreturn.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed. 

Lemma proof_of_OSIntEnter_which_implies_wit_1 : OSIntEnter_which_implies_wit_1.
Proof.
  unfold OSIntEnter_which_implies_wit_1; left.
  intros before sg Haddr.
  pose proof (os_int_enter_inv_split sg before) as Hsplit.
  destruct Haddr as [Hrunning_address Hnesting_address].
  rewrite <- Hrunning_address, <- Hnesting_address in Hsplit.
  rewrite Hsplit.
  Intros.
  prop_apply_p (UCOS2_C_Rules.store_uchar_range
    (&("OSIntNesting")) (os_int_enter_nesting before)).
  Intros.
  unfold os_int_enter_global_addresses.
  entailer!.
Qed. 

