Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion IntLib.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Import UCOS2_C_Rules KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The ordinary OS_EventTaskRemove source used at SemPend's timeout cut.
    The row store precedes the zero test. The group store and bit-Y load
    occur only on its zero branch; the final pointer store always occurs. *)
Definition sem_pend_timeout_remove_fragment tcb group table row bit_x bit_y row_value group_value
  (before after : model) : Prop :=
  exists row_written group_written,
    uchar_load (tcb_field_address tcb TCBY) row before /\
    uchar_load (tcb_field_address tcb TCBBitX) bit_x before /\
    uchar_load (table + row) row_value before /\
    kernel_heap_execution [(table + row, event_task_remove_cleared row_value bit_x)] before row_written /\
    uchar_load (table + row) (event_task_remove_cleared row_value bit_x) row_written /\
    (if Z.eqb (event_task_remove_cleared row_value bit_x) 0 then
       uchar_load (tcb_field_address tcb TCBBitY) bit_y row_written /\
       uchar_load group group_value row_written /\
       kernel_heap_execution [(group, event_task_remove_cleared group_value bit_y)] row_written group_written
     else group_written = row_written) /\
    kernel_heap_execution (pointer_store_writes (tcb_field_address tcb TCBEventPtr) 0) group_written after.

Lemma sem_pend_timeout_cleared_in_range : forall value mask,
  0 <= event_task_remove_cleared value mask < 256.
Proof.
  intros; unfold event_task_remove_cleared, unsigned_last_nbits.
  rewrite <- (Z.land_ones (Z.lnot mask) 8 ltac:(lia)).
  rewrite Z.land_assoc, Z.land_ones by lia.
  apply Z.mod_pos_bound; reflexivity.
Qed.

(** This physical producer returns the existing, already canonical-checked
    helper post. SemPend consumes that post to recover its global state;
    no chosen after-state or timeout effect is assumed here. *)
Lemma sem_pend_timeout_remove_source : forall tcb group table row bit_x bit_y row_value group_value
  (frame : Assertion) before,
  (event_task_remove_pre tcb group table row bit_x bit_y row_value group_value ** frame) before ->
  exists after,
    sem_pend_timeout_remove_fragment tcb group table row bit_x bit_y row_value group_value before after /\
    (event_task_remove_post tcb group table row bit_x bit_y row_value group_value ** frame) after.
Proof.
  intros tcb group table row bit_x bit_y row_value group_value frame before Hpre.
  assert (Hrow : 0 <= row < 8).
  { assert (Hfacts : event_task_remove_pre tcb group table row bit_x bit_y row_value group_value ** frame |--
      coq_prop (0 <= row < 8) && TT).
    { unfold event_task_remove_pre; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hfacts before Hpre)). }
  assert (Hreads : uchar_load (tcb_field_address tcb TCBY) row before /\
    uchar_load (tcb_field_address tcb TCBBitX) bit_x before /\ uchar_load (table + row) row_value before).
  { split; [|split]; eapply framed_uchar_store_load;
      match goal with |- (?P ** _) before =>
        assert (Hfocus : event_task_remove_pre tcb group table row bit_x bit_y row_value group_value ** frame |--
          P ** TT) by (unfold event_task_remove_pre; entailer!; intros ? ?; exact I);
        exact (Hfocus before Hpre) end. }
  set (rest := tcb_field_address tcb TCBY # UChar |-> row **
    tcb_field_address tcb TCBBitX # UChar |-> bit_x **
    tcb_field_address tcb TCBBitY # UChar |-> bit_y **
    tcb_field_address tcb TCBEventPtr # Ptr |->_ ** frame).
  assert (Hsplit : event_task_remove_pre tcb group table row bit_x bit_y row_value group_value ** frame |--
    (table + row) # UChar |-> row_value ** (group # UChar |-> group_value ** rest)).
  { unfold event_task_remove_pre, rest; entailer!. }
  destruct (kernel_heap_framed_uchar_store (table + row) row_value (event_task_remove_cleared row_value bit_x)
    (group # UChar |-> group_value ** rest) before (sem_pend_timeout_cleared_in_range _ _)
    (Hsplit before Hpre)) as [row_written [Hwrite_row Hrow_post]].
  assert (Hread_row : uchar_load (table + row) (event_task_remove_cleared row_value bit_x) row_written)
    by (eapply framed_uchar_store_load; exact Hrow_post).
  assert (Hgroup : exists group_written,
    (if Z.eqb (event_task_remove_cleared row_value bit_x) 0 then
       uchar_load (tcb_field_address tcb TCBBitY) bit_y row_written /\
       uchar_load group group_value row_written /\
       kernel_heap_execution [(group, event_task_remove_cleared group_value bit_y)] row_written group_written
     else group_written = row_written) /\
    ((table + row) # UChar |-> event_task_remove_cleared row_value bit_x **
      group # UChar |-> event_task_remove_group row_value group_value bit_x bit_y ** rest) group_written).
  { destruct (Z.eqb (event_task_remove_cleared row_value bit_x) 0) eqn:Hzero.
    - assert (Hbit_y : uchar_load (tcb_field_address tcb TCBBitY) bit_y row_written).
      { eapply framed_uchar_store_load.
        match type of Hrow_post with ?P row_written => assert (Hfocus : P |--
          tcb_field_address tcb TCBBitY # UChar |-> bit_y ** TT)
          by (unfold rest; entailer!; intros ? ?; exact I) end.
        exact (Hfocus row_written Hrow_post). }
      assert (Hread_group : uchar_load group group_value row_written).
      { eapply framed_uchar_store_load.
        match type of Hrow_post with ?P row_written => assert (Hfocus : P |-- group # UChar |-> group_value ** TT)
          by (entailer!; intros ? ?; exact I) end.
        exact (Hfocus row_written Hrow_post). }
      match type of Hrow_post with ?P row_written => assert (Horder : P |-- group # UChar |-> group_value **
        ((table + row) # UChar |-> event_task_remove_cleared row_value bit_x ** rest)) by entailer! end.
      destruct (kernel_heap_framed_uchar_store group group_value (event_task_remove_cleared group_value bit_y)
        ((table + row) # UChar |-> event_task_remove_cleared row_value bit_x ** rest) row_written
        (sem_pend_timeout_cleared_in_range _ _) (Horder row_written Hrow_post))
        as [group_written [Hwrite_group Hgroup_post]].
      exists group_written; split; [tauto|].
      match type of Hgroup_post with ?P group_written => match goal with |- ?Q group_written =>
        assert (Hclose : P |-- Q) by (unfold event_task_remove_group; rewrite Hzero; entailer!) end end.
      exact (Hclose group_written Hgroup_post).
    - exists row_written; split; [reflexivity|].
      unfold event_task_remove_group; rewrite Hzero.
      match type of Hrow_post with ?P row_written => match goal with |- ?Q row_written =>
        assert (Hclose : P |-- Q) by entailer! end end.
      exact (Hclose row_written Hrow_post). }
  destruct Hgroup as [group_written [Hgroup_source Hgroup_post]].
  set (pointer_frame := tcb_field_address tcb TCBY # UChar |-> row **
    tcb_field_address tcb TCBBitX # UChar |-> bit_x **
    tcb_field_address tcb TCBBitY # UChar |-> bit_y **
    (table + row) # UChar |-> event_task_remove_cleared row_value bit_x **
    group # UChar |-> event_task_remove_group row_value group_value bit_x bit_y ** frame).
  match type of Hgroup_post with ?P group_written => assert (Hpointer : P |--
    tcb_field_address tcb TCBEventPtr # Ptr |->_ ** pointer_frame) by (unfold rest, pointer_frame; entailer!) end.
  destruct (framed_pointer_store_execution (tcb_field_address tcb TCBEventPtr) 0 pointer_frame group_written
    ltac:(lia) (Hpointer group_written Hgroup_post)) as [after [Hwrite_pointer Hafter]].
  exists after; split.
  - exists row_written, group_written; tauto.
  - match type of Hafter with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) by (unfold event_task_remove_post, pointer_frame; entailer!) end end.
    exact (Hclose after Hafter).
Qed.
