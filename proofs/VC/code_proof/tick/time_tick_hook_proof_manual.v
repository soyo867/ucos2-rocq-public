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
From Ucos2Verify.VC.code.tick Require Import time_tick_hook_goal.
From Ucos2Verify.VC.code.tick Require Import time_tick_hook_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_hook_spec.
Require Import Ucos2Verify.VC.code.tick.spec.time_tick_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_resume_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope monad_scope.
Local Open Scope sac.

Lemma proof_of_OSTimeTickHook_return_wit_2 : OSTimeTickHook_return_wit_2.
Proof.
unfold OSTimeTickHook_return_wit_2; left; intros.
rewrite time_tick_hook_advanced_unsigned in *.
assert (Hsignal : time_tick_hook_signals counter = false).
{ apply time_tick_hook_no_signal_guard; change (time_tick_hook_advanced counter < 10) in PreH1; exact PreH1. }
pose proof (time_tick_hook_no_signal_return environment critical saved_local sg caller mask eid
  (&("OSTmrCtr")) counter before X Hsignal PreH6) as Hreturn.
unfold time_tick_hook_frame in Hreturn.
sep_apply_l_atomic Hreturn; entailer!.
Qed. 

Lemma proof_of_OSTimeTickHook_partial_solve_wit_3_pure : OSTimeTickHook_partial_solve_wit_3_pure.
Proof.
unfold OSTimeTickHook_partial_solve_wit_3_pure; left; intros.
rewrite time_tick_hook_advanced_unsigned in PreH1.
change (time_tick_hook_advanced counter >= 10) in PreH1.
entailer!.
Qed. 

Lemma proof_of_OSTimeTickHook_partial_solve_wit_5_pure : OSTimeTickHook_partial_solve_wit_5_pure.
Proof.
unfold OSTimeTickHook_partial_solve_wit_5_pure; left; intros.
rewrite time_tick_hook_advanced_unsigned in PreH7.
change (time_tick_hook_advanced counter >= 10) in PreH7.
entailer!.
Qed. 

Lemma proof_of_OSTimeTickHook_which_implies_wit_1 : OSTimeTickHook_which_implies_wit_1.
Proof.
unfold OSTimeTickHook_which_implies_wit_1; left; intros.
unfold time_tick_hook_frame; entailer!.
Qed. 

Lemma proof_of_OSTimeTickHook_which_implies_wit_2 : OSTimeTickHook_which_implies_wit_2.
Proof.
unfold OSTimeTickHook_which_implies_wit_2; left; intros.
pose proof (time_tick_hook_signal_guard counter PreH1) as Hsignal.
destruct (PreH2 Hsignal) as [Hprofile [Hvalid [Hinput [Hlayout Hschedule]]]].
pose proof (time_tick_hook_signal_safe _ _ _ _ _ _ _ _ _ Hsignal PreH3) as Hsafe.
entailer!.
Qed. 

Lemma proof_of_OSTimeTickHook_which_implies_wit_3 : OSTimeTickHook_which_implies_wit_3.
Proof.
unfold OSTimeTickHook_which_implies_wit_3; left; intros.
apply time_tick_hook_signal_return.
apply time_tick_hook_signal_guard; exact PreH1.
Qed. 

