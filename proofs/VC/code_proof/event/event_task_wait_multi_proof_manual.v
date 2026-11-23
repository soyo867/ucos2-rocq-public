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
From Ucos2Verify.VC.code.event Require Import event_task_wait_multi_goal.
From Ucos2Verify.VC.code.event Require Import event_task_wait_multi_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_multi_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OS_EventTaskWaitMulti_entail_wit_1 : OS_EventTaskWaitMulti_entail_wit_1.
Proof.
  unfold OS_EventTaskWaitMulti_entail_wit_1; left; intros.
  prop_apply_p (store_uchar_range (&(tcb # "os_tcb" ->ₛ "OSTCBBitX")) (tcb_bit_x_of_prio t.(curPrio))).
  Intros; change compcert.lib.Integers.Byte.max_unsigned with 255 in *; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_entail_wit_2 : OS_EventTaskWaitMulti_entail_wit_2.
Proof.
  unfold OS_EventTaskWaitMulti_entail_wit_2; left; intros.
  prop_apply_p (store_uchar_range (&(tcb # "os_tcb" ->ₛ "OSTCBBitY")) (tcb_bit_y_of_prio t.(curPrio))).
  Intros; change compcert.lib.Integers.Byte.max_unsigned with 255 in *; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_return_wit_1 : OS_EventTaskWaitMulti_return_wit_1.
Proof.
  unfold OS_EventTaskWaitMulti_return_wit_1; left; intros.
  unfold event_task_wait_multi_post, event_task_wait_ready_group, event_task_wait_ready_row, tcb_y_of_prio.
  rewrite PreH1; cbn [Z.eqb].
  entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_return_wit_2 : OS_EventTaskWaitMulti_return_wit_2.
Proof.
  unfold OS_EventTaskWaitMulti_return_wit_2; left; intros.
  unfold event_task_wait_multi_post, event_task_wait_ready_group, event_task_wait_ready_row, tcb_y_of_prio.
  apply Z.eqb_neq in PreH1; rewrite PreH1.
  entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_which_implies_wit_1 : OS_EventTaskWaitMulti_which_implies_wit_1.
Proof.
  unfold OS_EventTaskWaitMulti_which_implies_wit_1; left; intros; unfold event_task_wait_multi_loop_assert; Intros.
  match goal with H : event_task_wait_multi_input _ _ _ _ _ _ _ |- _ =>
    pose proof H as Hinput; destruct H as [_ [_ [_ [_ [Hrow [Hbinding Hlayout]]]]]] end.
  pose proof (event_task_wait_multi_loop_start sg tasks entry tid pointers instances Hbinding) as Hloop.
  unfold tcb_y_of_prio; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_which_implies_wit_2 : OS_EventTaskWaitMulti_which_implies_wit_2.
Proof.
  unfold OS_EventTaskWaitMulti_which_implies_wit_2; left; intros.
  pose proof (event_multi_array_split_index base pointers 0 (conj (Z.le_refl 0) (Zlength_nonneg pointers))) as Hsplit.
  replace (base + 0 * 4) with base in Hsplit by lia.
  sep_apply_l_atomic Hsplit; unfold event_task_wait_multi_pointer, event_task_wait_multi_array_missing; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_which_implies_wit_3 : OS_EventTaskWaitMulti_which_implies_wit_3.
Proof.
  unfold OS_EventTaskWaitMulti_which_implies_wit_3; left; intros; unfold event_task_wait_multi_loop_assert; Intros.
  unfold event_task_wait_multi_pointer, event_task_wait_multi_array_missing.
  pose proof (event_multi_array_merge_index base pointers 0 ltac:(assumption)
    (conj (Z.le_refl 0) (Zlength_nonneg pointers))) as Hmerge.
  replace (base + 0 * 4) with base in Hmerge by lia.
  sep_apply_l_atomic Hmerge.
  unfold event_task_wait_multi_cursor, event_task_wait_multi_value; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_which_implies_wit_4 : OS_EventTaskWaitMulti_which_implies_wit_4.
Proof.
  unfold OS_EventTaskWaitMulti_which_implies_wit_4; left; intros; unfold event_task_wait_multi_loop_assert; Intros.
  unfold event_multi_array_rep at 1; Intros.
  match goal with H : event_task_wait_multi_value _ _ _ |- _ =>
    unfold event_task_wait_multi_value, event_task_wait_multi_pointer in H end.
  destruct (event_task_wait_multi_current_entry sg tasks entry tid t base pointers instances index_2 events_2
    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(congruence))
    as [eid [e Hselected]].
  destruct Hselected as [Heid [Haddress [Hlookup [Hlayout Hlt]]]].
  assert (Hrow : 0 <= t.(curPrio) / 8 < 8).
  { match goal with H : event_task_wait_multi_input _ _ _ _ _ _ _ |- _ => unfold event_task_wait_multi_input in H; tauto end. }
  assert (Hpevent : pevent = event_addr sg eid) by congruence.
  sep_apply_l_atomic (event_task_wait_multi_split_event sg tasks events_2 eid e (t.(curPrio) / 8) Hlookup Hlayout Hrow).
  prop_apply_p (store_uchar_range
    (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + t.(curPrio) / 8 * sizeof(UCHAR))
    (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))).
  prop_apply_p (store_uchar_range (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp"))
    (encode_event_wait_grp e.(waitList) tasks)).
  Intros; change compcert.lib.Integers.Byte.max_unsigned with 255 in *.
  Exists eid e events_2 index_2.
  unfold event_task_wait_multi_selected, event_task_wait_multi_value, event_task_wait_multi_pointer,
    event_multi_array_rep, tcb_y_of_prio.
  rewrite Hpevent; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_which_implies_wit_5 : OS_EventTaskWaitMulti_which_implies_wit_5.
Proof.
  unfold OS_EventTaskWaitMulti_which_implies_wit_5; left; intros; unfold event_task_wait_multi_loop_assert; Intros.
  match goal with H : event_task_wait_multi_selected _ _ _ _ _ _ _ |- _ =>
    destruct H as [Heid [Haddress [Hlookup [Hlayout Hlt]]]] end.
  match goal with H : event_task_wait_multi_value _ _ _ |- _ =>
    unfold event_task_wait_multi_value in H end.
  assert (Hpevent : pevent = event_addr sg eid) by congruence.
  assert (Ht : tasks.(inUsedTaskStates) tid = Some t /\ 0 <= t.(curPrio) / 8 < 8).
  { match goal with H : event_task_wait_multi_input _ _ _ _ _ _ _ |- _ => unfold event_task_wait_multi_input in H; tauto end. }
  rewrite Hpevent; unfold tcb_y_of_prio.
  sep_apply_l_atomic (event_task_wait_multi_merge_event sg tasks events eid e tid t (proj1 Ht) Hlayout (proj2 Ht)).
  pose proof (event_task_wait_multi_loop_step sg tasks entry tid pointers instances index events eid e
    ltac:(assumption) Hlt Heid Hlookup) as Hnext.
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&("pevent")) (event_addr sg eid)).
  Exists (update_event_field_raw events eid (event_insert_waiter sg tasks e tid)) (index + 1).
  unfold event_task_wait_multi_cursor in *; change (sizeof(PTR)) with 4; entailer!; lia.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_which_implies_wit_6 : OS_EventTaskWaitMulti_which_implies_wit_6.
Proof.
  unfold OS_EventTaskWaitMulti_which_implies_wit_6; left; intros; unfold event_task_wait_multi_loop_assert; Intros.
  assert (Hindex : 0 <= next_2 <= Zlength pointers).
  { match goal with H : event_task_wait_multi_loop _ _ _ _ _ _ _ _ |- _ => exact (proj1 H) end. }
  match goal with H : event_task_wait_multi_cursor _ _ _ |- _ => unfold event_task_wait_multi_cursor in H; subst pevents end.
  sep_apply_l_atomic (event_multi_array_split_index base pointers next_2 Hindex).
  Exists after_2 next_2; unfold event_task_wait_multi_array_missing, event_task_wait_multi_pointer,
    event_task_wait_multi_cursor; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_which_implies_wit_7 : OS_EventTaskWaitMulti_which_implies_wit_7.
Proof.
  unfold OS_EventTaskWaitMulti_which_implies_wit_7; left; intros; unfold event_task_wait_multi_loop_assert; Intros.
  assert (Hindex : 0 <= next_2 <= Zlength pointers).
  { match goal with H : event_task_wait_multi_loop _ _ _ _ _ _ _ _ |- _ => exact (proj1 H) end. }
  match goal with H : event_task_wait_multi_cursor _ _ _ |- _ => unfold event_task_wait_multi_cursor in H; subst pevents end.
  unfold event_task_wait_multi_pointer, event_task_wait_multi_array_missing.
  sep_apply_l_atomic (event_multi_array_merge_index base pointers next_2 ltac:(assumption) Hindex).
  Exists after_2 next_2; unfold event_task_wait_multi_value, event_task_wait_multi_cursor; entailer!.
Qed. 

Lemma proof_of_OS_EventTaskWaitMulti_which_implies_wit_8 : OS_EventTaskWaitMulti_which_implies_wit_8.
Proof.
  unfold OS_EventTaskWaitMulti_which_implies_wit_8; left; intros; unfold event_task_wait_multi_loop_assert; Intros.
  unfold event_multi_array_rep at 1; Intros.
  assert (Hindex : index = Zlength pointers).
  { match goal with H : event_task_wait_multi_loop _ _ _ _ _ _ _ _ |- _ => pose proof (proj1 H) as Hrange end.
    apply (proj1 (event_multi_array_null_iff_end base pointers index ltac:(assumption) Hrange)).
    match goal with H : event_task_wait_multi_value _ _ _ |- _ => unfold event_task_wait_multi_value, event_task_wait_multi_pointer in H; lia end. }
  assert (Hend : events = event_task_wait_multi_events sg tasks entry tid instances).
  { eapply event_task_wait_multi_loop_end; eassumption. }
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&("pevent")) pevent).
  rewrite Hend; unfold event_multi_array_rep; entailer!.
Qed. 

