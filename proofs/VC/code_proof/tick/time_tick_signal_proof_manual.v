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
From Ucos2Verify.VC.code.tick Require Import time_tick_signal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_isr_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSTmrSignal_which_implies_wit_1 : OSTmrSignal_which_implies_wit_1.
Proof.
  unfold OSTmrSignal_which_implies_wit_1; left; intros.
  pose proof (proj1 PreH1) as Henabled.
  unfold time_tick_sched_owned.
  rewrite PreH2.
  sep_apply (time_tick_signal_read_split sg before Henabled).
  entailer!.
Qed.

Lemma proof_of_OSSemPost_derive_tick_signal_read_by_tick_sem_source : OSSemPost_derive_tick_signal_read_by_tick_sem_source.
Proof.
  unfold OSSemPost_derive_tick_signal_read_by_tick_sem_source.
  intros pe before region_entry origin invocation sg critical platform; Intros.
  match goal with Hentry : time_tick_signal_entry sg before |- _ =>
    destruct Hentry as [Henabled [Hprofile [Hread Hnest]]]
  end.
  match goal with Haddr : ?address = g_OSTmrSemSignal sg |- _ =>
    rewrite Haddr
  end.
  sep_apply (time_tick_signal_read_merge sg before Henabled).
  Exists platform critical sg invocation origin region_entry before (time_tick_signal_pointer before).
  unfold time_tick_sched_owned.
  apply derivable1s_emp_sepcon_unfold; [entailer! |].
  apply derivable1s_wand_sepcon_adjoint; entailer!.
Qed.
