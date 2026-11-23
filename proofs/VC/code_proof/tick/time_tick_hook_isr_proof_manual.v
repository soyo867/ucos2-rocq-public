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
From Ucos2Verify.VC.code.tick Require Import time_tick_hook_isr_goal.
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

Require Import Ucos2Verify.lib.kernel_resources.

Lemma proof_of_OSTimeTickHook_entail_wit_1 : OSTimeTickHook_entail_wit_1.
Proof.
  unfold OSTimeTickHook_entail_wit_1; left; intros.
  pose proof (kernel_u16_in_range (counter + 1)) as Hrange.
  change (0 <= time_tick_hook_advanced counter < 65536) in Hrange.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= time_tick_hook_advanced counter < 4294967296); lia).
  change (time_tick_hook_advanced counter >= 10) in PreH1.
  entailer!; lia.
Qed.

Lemma proof_of_OSTimeTickHook_return_wit_2 : OSTimeTickHook_return_wit_2.
Proof.
  unfold OSTimeTickHook_return_wit_2; left; intros.
  pose proof (kernel_u16_in_range (counter + 1)) as Hrange.
  change (0 <= time_tick_hook_advanced counter < 65536) in Hrange.
  rewrite unsigned_last_nbits_eq in PreH1 by (change (0 <= time_tick_hook_advanced counter < 4294967296); lia).
  change (time_tick_hook_advanced counter < 10) in PreH1.
  sep_apply_r_atomic (time_tick_hook_isr_no_signal_return platform critical application sg invocation origin
    region_entry before app_value (&("OSTmrCtr")) counter PreH3 PreH1).
  entailer!.
Qed.

Lemma proof_of_OSTimeTickHook_which_implies_wit_1 : OSTimeTickHook_which_implies_wit_1.
Proof.
  unfold OSTimeTickHook_which_implies_wit_1; left; intros.
  sep_apply (time_tick_hook_isr_open platform critical application sg invocation origin
    region_entry before app_value (&("OSTmrCtr")) counter PreH1).
  entailer!.
Qed.

Lemma proof_of_OSTimeTickHook_which_implies_wit_2 : OSTimeTickHook_which_implies_wit_2.
Proof.
  unfold OSTimeTickHook_which_implies_wit_2; left; intros.
  rewrite time_tick_hook_advanced_unsigned.
  entailer!.
Qed.

Lemma proof_of_OSTimeTickHook_which_implies_wit_3 : OSTimeTickHook_which_implies_wit_3.
Proof.
  unfold OSTimeTickHook_which_implies_wit_3; left; intros.
  apply (time_tick_hook_isr_signal_return platform critical application sg invocation origin
    region_entry before app_value (&("OSTmrCtr")) counter error after); assumption.
Qed.
