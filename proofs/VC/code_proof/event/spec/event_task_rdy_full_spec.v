Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
Require Export Ucos2Verify.lib.field_storage.
Require Export Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_remove_multi_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(** Caller-protected internal contract. Canonical priority selection does not
    require the single-event-only linked-wait predicate. A nonzero MultiPtr
    borrows the actual array and its live generation binding, with duplicates
    allowed. Arbitrary byte masks/results are not decoded into a stable task. *)
Definition event_task_rdy_full_entry sg tasks events eid e tid t pointers instances : Prop :=
  full_features_kernel_profile sg /\ task_in_range sg tasks /\
  events.(inUsedEventStates) eid = Some e /\ event_object_layout_prop sg eid /\
  event_waitList_canonical sg tasks e.(waitList) /\
  hd_error e.(waitList) = Some tid /\ tasks.(inUsedTaskStates) tid = Some t /\
  (t.(tcbEventMultiPtr) <> 0 ->
    event_task_remove_multi_input sg tasks events tid t pointers instances).

Definition event_task_rdy_full_array (base : Z) (pointers : list Z) : Assertion :=
  if Z.eq_dec base 0 then emp else event_multi_array_rep base pointers.

Definition event_task_rdy_full_before_remove_image sg t message mask result :=
  tcb_layout_write
    (tcb_layout_write
      (tcb_layout_write
        (tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBDly) (Some 0))
        (TCBCommonField TCBMsg) (Some message))
      (TCBCommonField TCBStat) (Some (task_status_clear_wait (encode_task_status t.(stat)) mask)))
    (TCBCommonField TCBStatPend) (Some result).

Definition event_task_rdy_full_after_remove_image sg t message mask result :=
  tcb_layout_write (event_task_rdy_full_before_remove_image sg t message mask result)
    (TCBCommonField TCBEventPtr) (Some 0).

Definition event_task_rdy_full_task_image sg t eid message mask result :=
  let image := event_task_rdy_full_after_remove_image sg t message mask result in
  if Z.eq_dec t.(tcbEventMultiPtr) 0 then image
  else tcb_layout_set_multi image 0 (event_addr sg eid).

Definition event_task_rdy_full_after_remove events eid e tid :=
  update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList))).

Definition event_task_rdy_full_events events eid e tid t instances :=
  let after := event_task_rdy_full_after_remove events eid e tid in
  if Z.eq_dec t.(tcbEventMultiPtr) 0 then after
  else event_task_remove_multi_events after tid instances.

Definition event_task_rdy_full_ready sg t mask group rows : Assertion :=
  sg.(g_OSRdyGrp) # UChar |->
    event_task_rdy_ready_group (task_status_clear_wait (encode_task_status t.(stat)) mask)
      group (tcb_bit_y_of_prio t.(curPrio)) **
  UCharArray.full sg.(g_OSRdyTbl) 8
    (event_task_rdy_ready_rows (task_status_clear_wait (encode_task_status t.(stat)) mask)
      (tcb_y_of_prio t.(curPrio)) (tcb_bit_x_of_prio t.(curPrio)) rows).

Definition event_task_rdy_full_pre sg tasks events eid e tid t pointers instances mask result group rows : Assertion :=
  coq_prop (event_task_rdy_full_entry sg tasks events eid e tid t pointers instances /\
    0 <= mask < 256 /\ 0 <= result < 256 /\ Zlength rows = 8) &&
  (tcb_configured_storage_rep true true (task_slot_addr sg tid) (task_layout_image sg t) **
   event_raw_rep sg tasks events ** event_task_rdy_full_array t.(tcbEventMultiPtr) pointers **
   unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
   sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows).

(** All fields written before RemoveMulti are represented at their real time.
    Event ownership has already been reassembled, including the selected ECB. *)
Definition event_task_rdy_full_after_single sg tasks events eid e tid t pointers instances
  message mask result group rows : Assertion :=
  coq_prop (event_task_rdy_full_entry sg tasks events eid e tid t pointers instances) &&
  (tcb_configured_storage_rep true true (task_slot_addr sg tid)
     (event_task_rdy_full_after_remove_image sg t message mask result) **
   event_raw_rep sg tasks (event_task_rdy_full_after_remove events eid e tid) **
   event_task_rdy_full_array t.(tcbEventMultiPtr) pointers **
   unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
   event_task_rdy_full_ready sg t mask group rows).

Definition event_task_rdy_full_post sg tasks events eid e tid t pointers
  instances message mask result group rows returned : Assertion :=
  coq_prop (returned = event_wait_priority tasks e /\ returned = t.(curPrio)) &&
  (tcb_configured_storage_rep true true (task_slot_addr sg tid)
     (event_task_rdy_full_task_image sg t eid message mask result) **
   event_raw_rep sg tasks (event_task_rdy_full_events events eid e tid t instances) **
   event_task_rdy_full_array t.(tcbEventMultiPtr) pointers **
   unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
   event_task_rdy_full_ready sg t mask group rows).

Lemma event_task_rdy_full_selection : forall sg tasks events eid e tid t pointers instances,
  event_task_rdy_full_entry sg tasks events eid e tid t pointers instances ->
  event_wait_priority tasks e = t.(curPrio) /\
  tasks.(prioTbl) t.(curPrio) = PTTask tid /\
  valid_task_prio sg t.(curPrio) /\ 0 <= t.(curPrio) < 64 /\
  unmap_value (encode_event_wait_grp e.(waitList) tasks) = tcb_y_of_prio t.(curPrio) /\
  unmap_value (encode_event_wait_tbl_at_or e.(waitList) tasks (tcb_y_of_prio t.(curPrio))) =
    tcb_x_of_prio t.(curPrio).
Proof.
  intros sg tasks events eid e tid t pointers instances
    [Hprofile [Htasks [He [Hlayout [Hcanonical [Hhead [Ht Hmulti]]]]]]].
  pose proof (proj1 Hprofile) as Hsg.
  destruct e.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  pose proof (event_wait_priority_head_eq sg tasks e tid tail t Hsg
    ltac:(rewrite Hlist; exact Hcanonical) Hlist Ht) as Hprio.
  pose proof Htasks as [_ [_ [_ [_ [_ [Hregistered _]]]]]].
  pose proof (Hregistered tid t Ht) as Htable.
  destruct Hcanonical as [Hnd [Hsorted Hmembers]].
  destruct (Hmembers tid (or_introl eq_refl)) as [node [Hnode Hp]].
  assert (node = t) by congruence; subst node.
  pose proof Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  pose proof (unmap_in_range (encode_event_wait_grp e.(waitList) tasks)) as Hy.
  pose proof (unmap_in_range (encode_event_wait_tbl_at_or e.(waitList) tasks
    (unmap_value (encode_event_wait_grp e.(waitList) tasks)))) as Hx.
  assert (Hcoord : unmap_value (encode_event_wait_grp e.(waitList) tasks) =
    tcb_y_of_prio t.(curPrio)).
  { unfold event_wait_priority in Hprio; cbn zeta in Hprio.
    unfold tcb_y_of_prio; rewrite <- Hprio, Z.add_comm, Z.div_add by lia.
    rewrite Z.div_small by lia; lia. }
  repeat split; try assumption; try (unfold valid_task_prio in Hp; lia).
  - rewrite <- Hlist; exact Hcoord.
  - rewrite <- Hlist.
    pose proof (f_equal (fun p => p mod 8) Hprio) as Hmod.
    unfold event_wait_priority in Hmod; cbn zeta in Hmod.
    rewrite Z.add_comm, Z.mod_add, Z.mod_small in Hmod by lia.
    unfold tcb_x_of_prio; rewrite <- Hcoord; exact Hmod.
Qed.

Lemma event_task_rdy_full_remove_multi_input : forall sg tasks events eid e tid t pointers instances,
  event_task_rdy_full_entry sg tasks events eid e tid t pointers instances ->
  t.(tcbEventMultiPtr) <> 0 ->
  event_task_remove_multi_input sg tasks
    (event_task_rdy_full_after_remove events eid e tid) tid t pointers instances.
Proof.
  intros sg tasks events eid e tid t pointers instances
    [_ [_ [He [_ [_ [_ [_ Hmulti]]]]]]] Hnonzero.
  destruct (Hmulti Hnonzero) as [Hsg [Hu [Hp [Ht [Hr [Hb [Hl Hc]]]]]]].
  unfold event_task_remove_multi_input, event_task_rdy_full_after_remove.
  rewrite <- (event_multi_remove_waiters_singleton events tid eid e He).
  split; [exact Hsg|]; split; [exact Hu|]; split; [exact Hp|]; split; [exact Ht|].
  split; [exact Hr|]; split.
  - apply event_multi_remove_waiters_preserves_binding; exact Hb.
  - split; [exact Hl|apply event_multi_remove_waiters_preserves_canonical; exact Hc].
Qed.

Definition event_task_rdy_full_tcb_frame base image : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBEventPtr) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true))))))))) image.

Lemma event_task_rdy_full_tcb_split : forall base image,
  tcb_configured_storage_rep true true base image |--
  tcb_layout_cell true base (TCBCommonField TCBDly) (image (TCBCommonField TCBDly)) **
  tcb_layout_cell true base (TCBCommonField TCBMsg) (image (TCBCommonField TCBMsg)) **
  tcb_layout_cell true base (TCBCommonField TCBStat) (image (TCBCommonField TCBStat)) **
  tcb_layout_cell true base (TCBCommonField TCBStatPend) (image (TCBCommonField TCBStatPend)) **
  tcb_layout_cell true base (TCBCommonField TCBY) (image (TCBCommonField TCBY)) **
  tcb_layout_cell true base (TCBCommonField TCBBitX) (image (TCBCommonField TCBBitX)) **
  tcb_layout_cell true base (TCBCommonField TCBBitY) (image (TCBCommonField TCBBitY)) **
  tcb_layout_cell true base (TCBCommonField TCBEventPtr) (image (TCBCommonField TCBEventPtr)) ** event_task_rdy_full_tcb_frame base image.
Proof.
  intros; unfold tcb_configured_storage_rep.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (tcb_configured_fields true true) image (TCBCommonField TCBDly)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)) image (TCBCommonField TCBMsg)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true))) image (TCBCommonField TCBStat)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)))) image (TCBCommonField TCBStatPend)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true))))) image (TCBCommonField TCBY)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)))))) image (TCBCommonField TCBBitX)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true))))))) image (TCBCommonField TCBBitY)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)))))))) image (TCBCommonField TCBEventPtr)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  unfold event_task_rdy_full_tcb_frame; entailer!.
Qed.

Lemma event_task_rdy_full_tcb_merge : forall base image,
  tcb_layout_cell true base (TCBCommonField TCBDly) (image (TCBCommonField TCBDly)) **
  tcb_layout_cell true base (TCBCommonField TCBMsg) (image (TCBCommonField TCBMsg)) **
  tcb_layout_cell true base (TCBCommonField TCBStat) (image (TCBCommonField TCBStat)) **
  tcb_layout_cell true base (TCBCommonField TCBStatPend) (image (TCBCommonField TCBStatPend)) **
  tcb_layout_cell true base (TCBCommonField TCBY) (image (TCBCommonField TCBY)) **
  tcb_layout_cell true base (TCBCommonField TCBBitX) (image (TCBCommonField TCBBitX)) **
  tcb_layout_cell true base (TCBCommonField TCBBitY) (image (TCBCommonField TCBBitY)) **
  tcb_layout_cell true base (TCBCommonField TCBEventPtr) (image (TCBCommonField TCBEventPtr)) ** event_task_rdy_full_tcb_frame base image |--
  tcb_configured_storage_rep true true base image.
Proof.
  intros; unfold event_task_rdy_full_tcb_frame.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)))))))) image (TCBCommonField TCBEventPtr)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true))))))) image (TCBCommonField TCBBitY)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)))))) image (TCBCommonField TCBBitX)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBStatPend) (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true))))) image (TCBCommonField TCBY)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBStat) (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)))) image (TCBCommonField TCBStatPend)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBMsg) (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true))) image (TCBCommonField TCBStat)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBDly) (tcb_configured_fields true true)) image (TCBCommonField TCBMsg)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (tcb_configured_fields true true) image (TCBCommonField TCBDly)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  unfold tcb_configured_storage_rep; entailer!.
Qed.

Definition event_task_rdy_full_multi_frame base image : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBEventMultiRdy) (remove TCBLayoutField_eq_dec (TCBEventMultiPtr) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true)))))) image.

Lemma event_task_rdy_full_multi_split : forall base image,
  tcb_configured_storage_rep true true base image |--
  tcb_layout_cell true base (TCBCommonField TCBY) (image (TCBCommonField TCBY)) **
  tcb_layout_cell true base (TCBCommonField TCBBitX) (image (TCBCommonField TCBBitX)) **
  tcb_layout_cell true base (TCBCommonField TCBBitY) (image (TCBCommonField TCBBitY)) **
  tcb_layout_cell true base (TCBEventMultiPtr) (image (TCBEventMultiPtr)) **
  tcb_layout_cell true base (TCBEventMultiRdy) (image (TCBEventMultiRdy)) ** event_task_rdy_full_multi_frame base image.
Proof.
  intros; unfold tcb_configured_storage_rep.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (tcb_configured_fields true true) image (TCBCommonField TCBY)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true)) image (TCBCommonField TCBBitX)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true))) image (TCBCommonField TCBBitY)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true)))) image (TCBEventMultiPtr)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBEventMultiPtr) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true))))) image (TCBEventMultiRdy)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  unfold event_task_rdy_full_multi_frame; entailer!.
Qed.

Lemma event_task_rdy_full_multi_merge : forall base image,
  tcb_layout_cell true base (TCBCommonField TCBY) (image (TCBCommonField TCBY)) **
  tcb_layout_cell true base (TCBCommonField TCBBitX) (image (TCBCommonField TCBBitX)) **
  tcb_layout_cell true base (TCBCommonField TCBBitY) (image (TCBCommonField TCBBitY)) **
  tcb_layout_cell true base (TCBEventMultiPtr) (image (TCBEventMultiPtr)) **
  tcb_layout_cell true base (TCBEventMultiRdy) (image (TCBEventMultiRdy)) ** event_task_rdy_full_multi_frame base image |--
  tcb_configured_storage_rep true true base image.
Proof.
  intros; unfold event_task_rdy_full_multi_frame.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBEventMultiPtr) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true))))) image (TCBEventMultiRdy)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitY) (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true)))) image (TCBEventMultiPtr)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBBitX) (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true))) image (TCBCommonField TCBBitY)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBY) (tcb_configured_fields true true)) image (TCBCommonField TCBBitX)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (tcb_configured_fields true true) image (TCBCommonField TCBY)
    ltac:(repeat apply tcb_configured_fields_remove_nodup; apply tcb_configured_fields_nodup)
    ltac:(vm_compute; intuition congruence)).
  unfold tcb_configured_storage_rep; entailer!.
Qed.

Lemma event_task_rdy_full_tcb_frame_updated_eq : forall sg t base message mask result,
  event_task_rdy_full_tcb_frame base
    (event_task_rdy_full_after_remove_image sg t message mask result) =
  event_task_rdy_full_tcb_frame base (task_layout_image sg t).
Proof.
  intros; unfold event_task_rdy_full_tcb_frame, event_task_rdy_full_after_remove_image,
    event_task_rdy_full_before_remove_image, tcb_layout_write.
  repeat rewrite TaskFieldStorage.store_fields_update_unlisted by
    (vm_compute; intuition discriminate).
  reflexivity.
Qed.

Lemma event_task_rdy_full_multi_frame_updated_eq : forall base image array ready,
  event_task_rdy_full_multi_frame base (tcb_layout_set_multi image array ready) =
  event_task_rdy_full_multi_frame base image.
Proof.
  intros; unfold event_task_rdy_full_multi_frame, tcb_layout_set_multi, tcb_layout_write.
  repeat rewrite TaskFieldStorage.store_fields_update_unlisted by
    (vm_compute; intuition discriminate).
  reflexivity.
Qed.

Lemma event_task_rdy_full_tcb_merge_updated : forall sg t base message mask result,
  tcb_cell base TCBDly (Some 0) ** tcb_cell base TCBMsg (Some message) **
  tcb_cell base TCBStat (Some (task_status_clear_wait (encode_task_status t.(stat)) mask)) **
  tcb_cell base TCBStatPend (Some result) **
  tcb_cell base TCBY (Some (tcb_y_of_prio t.(curPrio))) **
  tcb_cell base TCBBitX (Some (tcb_bit_x_of_prio t.(curPrio))) **
  tcb_cell base TCBBitY (Some (tcb_bit_y_of_prio t.(curPrio))) **
  tcb_cell base TCBEventPtr (Some 0) **
  event_task_rdy_full_tcb_frame base (task_layout_image sg t) |--
  tcb_configured_storage_rep true true base
    (event_task_rdy_full_after_remove_image sg t message mask result).
Proof.
  intros; rewrite <- (event_task_rdy_full_tcb_frame_updated_eq sg t base message mask result).
  exact (event_task_rdy_full_tcb_merge base
    (event_task_rdy_full_after_remove_image sg t message mask result)).
Qed.

Lemma event_task_rdy_full_multi_merge_updated : forall base image array ready,
  tcb_layout_cell true base (TCBCommonField TCBY) (image (TCBCommonField TCBY)) **
  tcb_layout_cell true base (TCBCommonField TCBBitX) (image (TCBCommonField TCBBitX)) **
  tcb_layout_cell true base (TCBCommonField TCBBitY) (image (TCBCommonField TCBBitY)) **
  task_multi_fields_rep base array ready ** event_task_rdy_full_multi_frame base image |--
  tcb_configured_storage_rep true true base (tcb_layout_set_multi image array ready).
Proof.
  intros; rewrite <- (event_task_rdy_full_multi_frame_updated_eq base image array ready).
  pose proof (event_task_rdy_full_multi_merge base (tcb_layout_set_multi image array ready)) as Hmerge.
  destruct (tcb_layout_set_multi_fields image array ready) as [Harray [Hready Hcommon]].
  rewrite Harray, Hready, !Hcommon in Hmerge.
  cbn [tcb_layout_cell] in Hmerge.
  unfold task_multi_fields_rep; rewrite <- Hmerge; entailer!.
Qed.
