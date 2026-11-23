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
From Ucos2Verify.VC.code.interrupt Require Import int_exit_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_api_program_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSIntExit_safety_wit_1 : OSIntExit_safety_wit_1.
Proof.
  unfold OSIntExit_safety_wit_1; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSIntExit_safety_wit_2 : OSIntExit_safety_wit_2.
Proof.
  unfold OSIntExit_safety_wit_2; intros.
  discriminate PreH1.
Qed.

Lemma proof_of_OSIntExit_safety_wit_3 : OSIntExit_safety_wit_3.
Proof.
  unfold OSIntExit_safety_wit_3; intros.
  entailer!; lia.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_1_pure : OSIntExit_partial_solve_wit_1_pure.
Proof.
  unfold OSIntExit_partial_solve_wit_1_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_1 : OSIntExit_partial_solve_wit_1.
Proof.
  unfold OSIntExit_partial_solve_wit_1, OSIntExit_partial_solve_wit_1_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_2 : OSIntExit_partial_solve_wit_2.
Proof.
  unfold OSIntExit_partial_solve_wit_2, OSIntExit_partial_solve_wit_2_aux; intros.
  assert (Hrunning : os_int_exit_running before = 1).
  { unfold os_int_exit_running in PreH1 |- *.
    destruct before.(SchedState).(isRunning); [reflexivity|discriminate PreH1]. }
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_3_pure : OSIntExit_partial_solve_wit_3_pure.
Proof.
  unfold OSIntExit_partial_solve_wit_3_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_3 : OSIntExit_partial_solve_wit_3.
Proof.
  unfold OSIntExit_partial_solve_wit_3, OSIntExit_partial_solve_wit_3_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_4_pure : OSIntExit_partial_solve_wit_4_pure.
Proof.
  unfold OSIntExit_partial_solve_wit_4_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_4 : OSIntExit_partial_solve_wit_4.
Proof.
  unfold OSIntExit_partial_solve_wit_4, OSIntExit_partial_solve_wit_4_aux; intros.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_5 : OSIntExit_partial_solve_wit_5.
Proof.
  unfold OSIntExit_partial_solve_wit_5; intros.
  sep_apply (PtrArray.full_split_to_missing_i (&( "OSTCBPrioTbl" ))
    (os_sched_selected entry) 64 (os_sched_table sg entry) 0 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_6 : OSIntExit_partial_solve_wit_6.
Proof.
  unfold OSIntExit_partial_solve_wit_6; intros.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_7_pure : OSIntExit_partial_solve_wit_7_pure.
Proof.
  unfold OSIntExit_partial_solve_wit_7_pure; intros.
  entailer!.
Qed.

Lemma proof_of_OSIntExit_partial_solve_wit_7 : OSIntExit_partial_solve_wit_7.
Proof.
  unfold OSIntExit_partial_solve_wit_7, OSIntExit_partial_solve_wit_7_aux; intros.
  entailer!.
Qed.
