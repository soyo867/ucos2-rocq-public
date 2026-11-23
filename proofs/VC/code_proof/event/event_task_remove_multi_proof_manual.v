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
From Ucos2Verify.VC.code.event Require Import event_task_remove_multi_goal.
From Ucos2Verify.VC.code.event Require Import event_task_remove_multi_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_multi_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_EventTaskRemoveMulti_entail_wit_1 : OS_EventTaskRemoveMulti_entail_wit_1.
Proof.
  pre_process; entailer!.
  - unfold tcb_bit_x_of_prio.
    assert (Hx : 0 <= tcb_x_of_prio (curPrio t) < 8)
      by (unfold tcb_x_of_prio; apply Z.mod_pos_bound; lia).
    rewrite Z.shiftl_1_l.
    change (2 ^ tcb_x_of_prio (curPrio t) < 2 ^ 8).
    apply Z.pow_lt_mono_r; lia.
  - unfold tcb_bit_x_of_prio.
    assert (Hx : 0 <= tcb_x_of_prio (curPrio t) < 8)
      by (unfold tcb_x_of_prio; apply Z.mod_pos_bound; lia).
    rewrite Z.shiftl_1_l.
    apply Z.pow_nonneg; lia.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_entail_wit_2 : OS_EventTaskRemoveMulti_entail_wit_2.
Proof.
  pre_process; entailer!.
  - unfold tcb_bit_y_of_prio.
    rewrite Z.shiftl_1_l.
    change (2 ^ tcb_y_of_prio (curPrio t) < 2 ^ 8).
    apply Z.pow_lt_mono_r; lia.
  - unfold tcb_bit_y_of_prio.
    rewrite Z.shiftl_1_l.
    apply Z.pow_nonneg; lia.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_entail_wit_4_1 : OS_EventTaskRemoveMulti_entail_wit_4_1.
Proof.
  unfold OS_EventTaskRemoveMulti_entail_wit_4_1; left; intros.
  subst y bitx bity.
  Exists events_2 eid_2 e_2 index_3.
  unfold event_task_remove_group.
  rewrite (event_task_remove_multi_cleared_eq_land
    (encode_event_wait_tbl_at_or e_2.(waitList) tasks (tcb_y_of_prio t.(curPrio)))
    (tcb_bit_x_of_prio t.(curPrio)) ltac:(lia)).
  rewrite PreH1, Z.eqb_refl.
  rewrite (event_task_remove_multi_cleared_eq_land
    (encode_event_wait_grp e_2.(waitList) tasks) (tcb_bit_y_of_prio t.(curPrio)) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_entail_wit_4_2 : OS_EventTaskRemoveMulti_entail_wit_4_2.
Proof.
  unfold OS_EventTaskRemoveMulti_entail_wit_4_2; left; intros.
  subst y bitx bity.
  Exists events_2 eid_2 e_2 index_3.
  unfold event_task_remove_group.
  rewrite (event_task_remove_multi_cleared_eq_land
    (encode_event_wait_tbl_at_or e_2.(waitList) tasks (tcb_y_of_prio t.(curPrio)))
    (tcb_bit_x_of_prio t.(curPrio)) ltac:(lia)).
  apply Z.eqb_neq in PreH1; rewrite PreH1.
  entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_entail_wit_5 : OS_EventTaskRemoveMulti_entail_wit_5.
Proof.
  unfold OS_EventTaskRemoveMulti_entail_wit_5; right; intros.
  unfold event_task_remove_multi_cursor, event_task_remove_multi_value; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_return_wit_1 : OS_EventTaskRemoveMulti_return_wit_1.
Proof.
  unfold OS_EventTaskRemoveMulti_return_wit_1; left; intros.
  unfold event_task_remove_multi_post, event_task_remove_multi_tcb_reads, tcb_y_of_prio; entailer!.
Qed.

Lemma proof_of_OS_EventTaskRemoveMulti_which_implies_wit_1 : OS_EventTaskRemoveMulti_which_implies_wit_1.
Proof.
  unfold OS_EventTaskRemoveMulti_which_implies_wit_1; left; intros.
  pose proof (event_task_remove_multi_loop_start sg tasks entry tid t pointers instances PreH1) as Hloop.
  assert (Hrow : 0 <= t.(curPrio) / 8 < 8) by (unfold event_task_remove_multi_input in PreH1; tauto).
  unfold event_task_remove_multi_loop_assert, tcb_y_of_prio; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_which_implies_wit_2 : OS_EventTaskRemoveMulti_which_implies_wit_2.
Proof.
  unfold OS_EventTaskRemoveMulti_which_implies_wit_2; left; intros.
  pose proof (event_multi_array_split_index pevents_multi_pre pointers 0 (conj (Z.le_refl 0) (Zlength_nonneg pointers))) as Hsplit.
  replace (pevents_multi_pre + 0 * 4) with pevents_multi_pre in Hsplit by lia.
  sep_apply_l_atomic Hsplit; unfold event_task_remove_multi_pointer, event_task_remove_multi_array_missing; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_which_implies_wit_3 : OS_EventTaskRemoveMulti_which_implies_wit_3.
Proof.
  unfold OS_EventTaskRemoveMulti_which_implies_wit_3; left; intros.
  unfold event_task_remove_multi_pointer, event_task_remove_multi_array_missing.
  pose proof (event_multi_array_merge_index pevents_multi_pre pointers 0 PreH2
    (conj (Z.le_refl 0) (Zlength_nonneg pointers))) as Hmerge.
  replace (pevents_multi_pre + 0 * 4) with pevents_multi_pre in Hmerge by lia.
  sep_apply_l_atomic Hmerge.
  unfold event_task_remove_multi_cursor, event_task_remove_multi_value; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_which_implies_wit_4 : OS_EventTaskRemoveMulti_which_implies_wit_4.
Proof.
  unfold OS_EventTaskRemoveMulti_which_implies_wit_4; left; intros; unfold event_task_remove_multi_loop_assert; Intros.
  unfold event_multi_array_rep at 1; Intros.
  unfold event_task_remove_multi_value, event_task_remove_multi_pointer in PreH2.
  destruct (event_task_remove_multi_current_entry sg tasks entry tid t pevents_multi_pre pointers instances index_2 events_2
    PreH4 ltac:(assumption) ltac:(assumption) ltac:(congruence)) as [eid [e Hselected]].
  destruct Hselected as [Heid [Haddress [Hlookup [Hlayout Hlt]]]].
  unfold event_task_remove_multi_pointer in Haddress.
  assert (Hrow : 0 <= t.(curPrio) / 8 < 8) by (unfold event_task_remove_multi_input in PreH4; tauto).
  assert (Hpevent : pevent = event_addr sg eid) by congruence.
  sep_apply_l_atomic (event_task_remove_multi_split_event sg tasks events_2 eid e (t.(curPrio) / 8) Hlookup Hlayout Hrow).
  prop_apply_p (store_uchar_range
    (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + t.(curPrio) / 8 * sizeof(UCHAR))
    (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))).
  prop_apply_p (store_uchar_range (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp"))
    (encode_event_wait_grp e.(waitList) tasks)).
  Intros; change compcert.lib.Integers.Byte.max_unsigned with 255 in *.
  Exists events_2 eid e index_2.
  unfold event_task_remove_multi_selected, event_task_remove_multi_value, event_task_remove_multi_pointer,
    event_multi_array_rep, tcb_y_of_prio.
  rewrite Hpevent; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_which_implies_wit_5 : OS_EventTaskRemoveMulti_which_implies_wit_5.
Proof.
  unfold OS_EventTaskRemoveMulti_which_implies_wit_5; left; intros; unfold event_task_remove_multi_loop_assert; Intros.
  destruct PreH4 as [Heid [Haddress [Hlookup [Hlayout Hlt]]]].
  unfold event_task_remove_multi_value in PreH2.
  assert (Hpevent : pevent = event_addr sg eid) by congruence.
  pose proof PreH3 as (Hsg & Hunique & Hprio & Ht & Hrow & Hbinding & Hlayouts & Hcanonical_entry).
  assert (Hcanonical : event_waitList_canonical sg tasks e.(waitList)).
  { match goal with H : event_task_remove_multi_loop _ _ _ _ _ _ _ _ |- _ =>
      exact (proj1 (proj2 (proj2 H)) eid e Hlookup) end. }
  rewrite Hpevent; unfold tcb_y_of_prio; sepcon_assoc_change.
  sep_apply_l_atomic (event_task_remove_multi_merge_event sg tasks events eid e tid t
    Hsg Hunique Hcanonical Hprio Ht Hlayout Hrow).
  pose proof (event_task_remove_multi_loop_step sg tasks entry tid pointers instances index events eid e
    ltac:(assumption) Hlt Heid Hlookup) as Hnext.
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&("pevent")) (event_addr sg eid)).
  Exists (update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))) (index + 1).
  unfold event_task_remove_multi_cursor in *; change (sizeof(PTR)) with 4; entailer!; lia.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_which_implies_wit_6 : OS_EventTaskRemoveMulti_which_implies_wit_6.
Proof.
  unfold OS_EventTaskRemoveMulti_which_implies_wit_6; left; intros; unfold event_task_remove_multi_loop_assert; Intros.
  assert (Hindex : 0 <= next_2 <= Zlength pointers).
  { match goal with H : event_task_remove_multi_loop _ _ _ _ _ _ _ _ |- _ => exact (proj1 H) end. }
  unfold event_task_remove_multi_cursor in PreH1; subst pevents.
  sep_apply_l_atomic (event_multi_array_split_index pevents_multi_pre pointers next_2 Hindex).
  Exists after_2 next_2; unfold event_task_remove_multi_array_missing, event_task_remove_multi_pointer,
    event_task_remove_multi_cursor; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_which_implies_wit_7 : OS_EventTaskRemoveMulti_which_implies_wit_7.
Proof.
  unfold OS_EventTaskRemoveMulti_which_implies_wit_7; left; intros; unfold event_task_remove_multi_loop_assert; Intros.
  assert (Hindex : 0 <= next_2 <= Zlength pointers).
  { match goal with H : event_task_remove_multi_loop _ _ _ _ _ _ _ _ |- _ => exact (proj1 H) end. }
  unfold event_task_remove_multi_cursor in PreH1; subst pevents.
  unfold event_task_remove_multi_pointer, event_task_remove_multi_array_missing.
  sep_apply_l_atomic (event_multi_array_merge_index pevents_multi_pre pointers next_2 PreH3 Hindex).
  Exists after_2 next_2; unfold event_task_remove_multi_value, event_task_remove_multi_cursor; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskRemoveMulti_which_implies_wit_8 : OS_EventTaskRemoveMulti_which_implies_wit_8.
Proof.
  unfold OS_EventTaskRemoveMulti_which_implies_wit_8; left; intros; unfold event_task_remove_multi_loop_assert; Intros.
  unfold event_multi_array_rep at 1; Intros.
  assert (Hindex : index = Zlength pointers).
  { match goal with H : event_task_remove_multi_loop _ _ _ _ _ _ _ _ |- _ => pose proof (proj1 H) as Hrange end.
    apply (proj1 (event_multi_array_null_iff_end pevents_multi_pre pointers index ltac:(assumption) Hrange)).
    unfold event_task_remove_multi_value, event_task_remove_multi_pointer in PreH1; lia. }
  assert (Hend : events = event_task_remove_multi_events entry tid instances).
  { eapply event_task_remove_multi_loop_end; eassumption. }
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&("pevent")) pevent).
  rewrite Hend; unfold event_multi_array_rep; entailer!.
Qed. 
