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
From Ucos2Verify.VC.code.task Require Import task_reg_set_goal.
From Ucos2Verify.VC.code.task Require Import task_reg_set_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_reg_set_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskRegSet_entail_wit_1 : OSTaskRegSet_entail_wit_1.
Proof.
  unfold OSTaskRegSet_entail_wit_1; left; intros.
  prop_apply_p (store_uchar_range (&("prio")) prio_pre).
  Intros_p Hprio; change (0 <= prio_pre <= 255) in Hprio.
  prop_apply_p (store_uint_range (&("value")) value_pre).
  Intros_p Hvalue; entailer!; lia.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_2 : OSTaskRegSet_entail_wit_2.
Proof.
  unfold OSTaskRegSet_entail_wit_2; left; intros.
  prop_apply_p (store_uchar_range (&("id")) id_pre).
  Intros_p Hid; change (0 <= id_pre <= 255) in Hid.
  entailer!; lia.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_4_1 : OSTaskRegSet_entail_wit_4_1.
Proof.
  unfold OSTaskRegSet_entail_wit_4_1; left; intros.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry_2 PreH1 PreH6)) as Hvalid.
  Exists entry_2.
  unfold UCOS2_inv, task_reg_set_priority_valid; entailer!; lia.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_4_2 : OSTaskRegSet_entail_wit_4_2.
Proof.
  unfold OSTaskRegSet_entail_wit_4_2; left; intros.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry_2 PreH1 PreH5)) as Hvalid.
  Exists entry_2.
  unfold UCOS2_inv, task_reg_set_priority_valid; entailer!; lia.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_5 : OSTaskRegSet_entail_wit_5.
Proof.
  unfold OSTaskRegSet_entail_wit_5; left; intros.
  assert (Hcast : unsigned_last_nbits prio_pre 32 = prio_pre).
  { apply unsigned_last_nbits_eq; unfold task_reg_set_priority_valid in PreH3; lia. }
  rewrite Hcast in PreH1.
  destruct PreH7 as [Hcurrent Htable].
  rewrite Hcurrent.
  sep_apply_l_atomic (task_reg_set_split_current sg entry_2).
  Intros; Exists entry_2; unfold task_reg_set_addresses; entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_6 : OSTaskRegSet_entail_wit_6.
Proof.
  unfold OSTaskRegSet_entail_wit_6; left; intros.
  assert (Hcast : unsigned_last_nbits prio_pre 32 = prio_pre).
  { apply unsigned_last_nbits_eq; unfold task_reg_set_priority_valid in PreH3; lia. }
  rewrite Hcast in PreH1.
  assert (Hpriority : 0 <= prio_pre < 64).
  { unfold task_reg_set_priority_valid in PreH3; lia. }
  destruct PreH7 as [Hcurrent Htable].
  rewrite Htable.
  sep_apply_l_atomic (task_reg_set_split_table sg entry_2 prio_pre Hpriority).
  Intros; Exists entry_2; unfold task_reg_set_addresses.
  unfold task_reg_set_priority_valid in PreH3; entailer!; lia.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_7_1 : OSTaskRegSet_entail_wit_7_1.
Proof.
  unfold OSTaskRegSet_entail_wit_7_1; left; intros.
  destruct PreH5 as [Hcurrent Htable].
  rewrite Hcurrent.
  sep_apply_l_atomic (task_reg_set_merge_current sg entry PreH7).
  Exists entry.
  subst prio_pre.
  unfold task_reg_set_priority_valid, task_reg_set_pointer; cbn; entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_7_2 : OSTaskRegSet_entail_wit_7_2.
Proof.
  unfold OSTaskRegSet_entail_wit_7_2; left; intros.
  assert (Hpriority : 0 <= prio_pre < 64) by lia.
  assert (Hself : Z.eqb prio_pre 255 = false) by (apply Z.eqb_neq; lia).
  destruct PreH6 as [Hcurrent Htable].
  rewrite Htable.
  sep_apply_l_atomic (task_reg_set_merge_table sg entry prio_pre PreH8 Hpriority).
  Exists entry.
  unfold task_reg_set_priority_valid, task_reg_set_pointer, task_reg_set_table_pointer.
  rewrite Hself; entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_8_1 : OSTaskRegSet_entail_wit_8_1.
Proof.
  left; intros.
  assert (Heffect : task_reg_set_effect sg entry_2 caller prio_pre id_pre value_pre ptcb 67 entry_2 caller).
  { unfold task_reg_set_effect; split; [assumption|]; split; [assumption|].
    split; [assumption|]; left; repeat split; auto. }
  Exists entry_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_8_2 : OSTaskRegSet_entail_wit_8_2.
Proof.
  left; intros.
  assert (Heffect : task_reg_set_effect sg entry_2 caller prio_pre id_pre value_pre ptcb 67 entry_2 caller).
  { unfold task_reg_set_effect; split; [assumption|]; split; [assumption|].
    split; [assumption|]; left; repeat split; auto. }
  Exists entry_2; entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_9 : OSTaskRegSet_entail_wit_9.
Proof.
  left; intros.
  assert (Hwrite : task_reg_set_writable sg entry_2 caller ptcb value_pre).
  { rewrite PreH8; eapply task_reg_set_selection_writable; eauto; congruence. }
  sep_apply_l_atomic (task_reg_set_focus_writable sg entry_2 caller ptcb value_pre Hwrite).
  Intros released after_caller residual.
  Exists released after_caller residual entry_2.
  entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_entail_wit_10 : OSTaskRegSet_entail_wit_10.
Proof.
  left; intros; subst id_pre.
  destruct PreH11 as [Hvalid [Hcommit Hmerge]].
  assert (Harray : (&(ptcb # "os_tcb" ->ₛ "OSTCBRegTbl")) # UInt |-> value_pre |--
    UIntArray.full (tcb_field_address ptcb TCBReg0) 1 (value_pre :: nil)).
  { unfold UIntArray.full, store_array; simpl.
    unfold StoreUIntAsElement.storeA, tcb_field_address; simpl.
    rewrite Z.add_0_r; entailer!. }
  replace (0 + 1) with 1 by lia.
  sep_apply_l_atomic (proj1 (UIntArray.undef_seg_empty
    (&(ptcb # "os_tcb" ->ₛ "OSTCBRegTbl")) 1)).
  replace (&(ptcb # "os_tcb" ->ₛ "OSTCBRegTbl") + 0 * sizeof(UINT)) with
    (&(ptcb # "os_tcb" ->ₛ "OSTCBRegTbl")) by lia.
  sep_apply_l_atomic Harray.
  sep_apply_l_atomic Hmerge.
  Exists released_2 after_caller_2 entry_2.
  assert (Heffect : task_reg_set_effect sg entry_2 caller prio_pre 0 value_pre ptcb 0 released_2 after_caller_2).
  { unfold task_reg_set_effect; split; [assumption|]; split; [reflexivity|].
    split; [assumption|]; right; repeat split; assumption. }
  entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_return_wit_1 : OSTaskRegSet_return_wit_1.
Proof.
  left; intros.
  unfold task_reg_set_restore_post; Intros after.
  assert (Hresult : task_reg_set_result critical sg invocation before caller
    prio_pre id_pre value_pre 67 after caller).
  { right; right; exists entry, entry, ptcb; split; [exact PreH1|];
    split; [exact PreH3|assumption]. }
  pose proof (task_reg_set_safe_return critical sg invocation before caller
    prio_pre id_pre value_pre 67 after caller X Hresult PreH4) as Hsafe.
  unfold task_reg_set_post.
  Right.
  Exists entry entry after caller ptcb 67.
  rewrite <- (proj2 PreH2).
  entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_return_wit_2 : OSTaskRegSet_return_wit_2.
Proof.
  left; intros.
  assert (Hresult : task_reg_set_result critical sg invocation before caller
    prio_pre id_pre value_pre 8 before caller).
  { right; left; split; [right; exact PreH2|].
    split; [lia|]; repeat split; reflexivity. }
  pose proof (task_reg_set_safe_return critical sg invocation before caller
    prio_pre id_pre value_pre 8 before caller X Hresult PreH17) as Hsafe.
  unfold task_reg_set_post.
  Left; Right.
  unfold task_reg_set_closed, task_reg_set_priority_valid; entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_return_wit_3 : OSTaskRegSet_return_wit_3.
Proof.
  left; intros.
  assert (Hresult : task_reg_set_result critical sg invocation before caller
    prio_pre id_pre value_pre 8 before caller).
  { right; left; split; [left; exact PreH2|].
    split; [lia|]; repeat split; reflexivity. }
  pose proof (task_reg_set_safe_return critical sg invocation before caller
    prio_pre id_pre value_pre 8 before caller X Hresult PreH16) as Hsafe.
  unfold task_reg_set_post.
  Left; Right.
  unfold task_reg_set_closed, task_reg_set_priority_valid; entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_return_wit_4 : OSTaskRegSet_return_wit_4.
Proof.
  left; intros.
  assert (Hresult : task_reg_set_result critical sg invocation before caller
    prio_pre id_pre value_pre 42 before caller).
  { left; split; [lia|]; split; [exact PreH1|]; repeat split; reflexivity. }
  pose proof (task_reg_set_safe_return critical sg invocation before caller
    prio_pre id_pre value_pre 42 before caller X Hresult PreH16) as Hsafe.
  unfold task_reg_set_post.
  Left; Left.
  unfold task_reg_set_closed; entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_return_wit_5 : OSTaskRegSet_return_wit_5.
Proof.
  left; intros.
  unfold task_reg_set_restore_post; Intros after.
  assert (Hresult : task_reg_set_result critical sg invocation before caller
    prio_pre id_pre value_pre 0 after after_caller).
  { right; right; exists entry, released, ptcb; split; [exact PreH1|];
    split; [exact PreH3|assumption]. }
  pose proof (task_reg_set_safe_return critical sg invocation before caller
    prio_pre id_pre value_pre 0 after after_caller X Hresult PreH4) as Hsafe.
  unfold task_reg_set_post.
  Right.
  Exists entry released after after_caller ptcb 0.
  rewrite <- (proj2 PreH2).
  entailer!.
Qed.

Lemma proof_of_OSTaskRegSet_which_implies_wit_1 : OSTaskRegSet_which_implies_wit_1.
Proof.
  unfold OSTaskRegSet_which_implies_wit_1; left; intros.
  unfold task_reg_set_pre, task_reg_set_closed; entailer!.
Qed.

