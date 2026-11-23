Require Import Ucos2Verify.VC.code.queue.q_init_generic_goal.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_source_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.queue_core.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Coq.ZArith.ZArith Coq.Strings.String.
Require Import Coq.micromega.Lia.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Lemma q_init_clear_call_prepare : OS_QInit_which_implies_wit_1.
Proof.
  unfold OS_QInit_which_implies_wit_1; left; intros sg Hprofile Haddr.
  unfold os_q_table_addr in Haddr.
  destruct Hprofile as [Hcount Hsize].
  change (sizeof_alias_type "os_q") with (sizeof("os_q")) in Hsize.
  unfold sizeof_OS_Q in Hsize; rewrite Hsize.
  replace (( &( "OSQTbl" ) ) + 0 * 24) with sg.(g_OSQTbl) by lia.
  change (24 * 4) with 96.
  unfold queue_init_pre.
  sep_apply_l_atomic (q_init_undef_table_to_bytes sg ltac:(split; assumption)).
  Intros; entailer!.
  rewrite Z.rem_mod_nonneg by lia; exact (proj1 H).
Qed.

Lemma q_init_clear_call_restore : OS_QInit_which_implies_wit_2.
Proof.
  unfold OS_QInit_which_implies_wit_2; left;
    intros sg Hprofile Haddr Halign Hp Hend.
  unfold os_q_table_addr in Haddr.
  destruct Hprofile as [Hcount Hsize].
  change (sizeof_alias_type "os_q") with (sizeof("os_q")) in Hsize.
  unfold sizeof_OS_Q in Hsize; rewrite Hsize.
  replace (( &( "OSQTbl" ) ) + 0 * 24) with sg.(g_OSQTbl) by lia.
  change (24 * 4) with 96.
  unfold q_init_after_clear.
  rewrite Z.rem_mod_nonneg in Halign by lia.
  sep_apply_l_atomic (q_init_cleared_table_to_typed sg
    ltac:(split; assumption) Hp Hend Halign).
  entailer!.
Qed.
