Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sched.

Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** This internal helper assumes caller-provided exclusion and ordinary
    protected-cell ownership.  It neither enters/exits a critical section
    nor schedules.  In particular no pending/ready consistency is assumed:
    Stat, StatPend and Dly may already contain the caller's pending prefix.
    The current-TCB pointer cell stays owned with the same value throughout.
    The parameters [current], [ready_group] and [ready_table] are the actual
    C global addresses, not unbound StableGlobVars names. *)
Definition event_task_wait_ready_row (row bit_x : Z) : Z :=
  Z.land row (unsigned_last_nbits (Z.lnot bit_x) 8).

Definition event_task_wait_ready_group (row group bit_x bit_y : Z) : Z :=
  if Z.eqb (event_task_wait_ready_row row bit_x) 0
  then Z.land group (unsigned_last_nbits (Z.lnot bit_y) 8)
  else group.

Definition event_task_wait_post
  (current tcb pevent ready_group ready_table : addr)
  (row bit_x bit_y event_row event_group ready_row ready_grp : Z) : Assertion :=
  current # Ptr |-> tcb **
  &(tcb # "os_tcb" ->ₛ "OSTCBEventPtr") # Ptr |-> pevent **
  &(tcb # "os_tcb" ->ₛ "OSTCBY") # UChar |-> row **
  &(tcb # "os_tcb" ->ₛ "OSTCBBitX") # UChar |-> bit_x **
  &(tcb # "os_tcb" ->ₛ "OSTCBBitY") # UChar |-> bit_y **
  (&(pevent # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR))
    # UChar |-> Z.lor event_row bit_x **
  &(pevent # "os_event" ->ₛ "OSEventGrp") # UChar |-> Z.lor event_group bit_y **
  (ready_table + row * sizeof(UCHAR)) # UChar |-> event_task_wait_ready_row ready_row bit_x **
  ready_group # UChar |-> event_task_wait_ready_group ready_row ready_grp bit_x bit_y.

(** The field inventory is the existing complete 64-byte TCB inventory,
    including both padding bytes.  These four fields are the exact local
    slice; all other fields stay in the structural residual. *)
Definition event_task_wait_tcb_rest (base : addr) (image : TCBCommonImage) : Assertion :=
  tcb64_fields_rep base
    (remove TCBField_eq_dec TCBBitY
      (remove TCBField_eq_dec TCBBitX
        (remove TCBField_eq_dec TCBY
          (remove TCBField_eq_dec TCBEventPtr tcb_fields)))) image.

Lemma event_task_wait_tcb_split : forall base image,
  tcb64_storage_rep base image |--
  tcb_cell base TCBEventPtr (image TCBEventPtr) **
  tcb_cell base TCBY (image TCBY) **
  tcb_cell base TCBBitX (image TCBBitX) **
  tcb_cell base TCBBitY (image TCBBitY) **
  event_task_wait_tcb_rest base image.
Proof.
  intros base image.
  sep_apply_l_atomic (tcb64_storage_split base image TCBEventPtr).
  unfold tcb64_storage_without.
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBEventPtr tcb_fields) base image TCBY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBEventPtr tcb_fields))
    base image TCBBitX
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBBitX
      (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBEventPtr tcb_fields)))
    base image TCBBitY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  unfold event_task_wait_tcb_rest; entailer!.
Qed.

Lemma event_task_wait_tcb_merge_event_ptr : forall base image pointer,
  tcb_cell base TCBEventPtr (Some pointer) **
  tcb_cell base TCBY (image TCBY) **
  tcb_cell base TCBBitX (image TCBBitX) **
  tcb_cell base TCBBitY (image TCBBitY) **
  event_task_wait_tcb_rest base image |--
  tcb64_storage_rep base (tcb_write image TCBEventPtr (Some pointer)).
Proof.
  intros base image pointer; unfold event_task_wait_tcb_rest.
  sep_apply_l_atomic (tcb64_fields_rep_merge
    (remove TCBField_eq_dec TCBBitX
      (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBEventPtr tcb_fields)))
    base image TCBBitY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_merge
    (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBEventPtr tcb_fields))
    base image TCBBitX
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_merge
    (remove TCBField_eq_dec TCBEventPtr tcb_fields) base image TCBY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(cbn; tauto)).
  fold (tcb64_storage_without base TCBEventPtr image).
  sep_apply_l_atomic (tcb64_storage_merge_updated base image TCBEventPtr (Some pointer)).
  entailer!.
Qed.

Lemma event_task_wait_task_split : forall sg tid t,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  used_task_rep sg tid t |--
  tcb_cell (tcb64_addr sg tid) TCBEventPtr (Some (encode_event_link sg t.(eventPtr))) **
  tcb_cell (tcb64_addr sg tid) TCBY (Some (tcb_y_of_prio t.(curPrio))) **
  tcb_cell (tcb64_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio t.(curPrio))) **
  tcb_cell (tcb64_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio t.(curPrio))) **
  event_task_wait_tcb_rest (tcb64_addr sg tid) (task_tcb64_image sg t).
Proof.
  intros sg tid t Hmulti Hprofile; rewrite used_task_rep_tcb64 by assumption.
  apply event_task_wait_tcb_split.
Qed.

Lemma event_task_wait_task_merge_event_ptr : forall sg tid t eid,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tcb_cell (tcb64_addr sg tid) TCBEventPtr (Some (event_addr sg eid)) **
  tcb_cell (tcb64_addr sg tid) TCBY (Some (tcb_y_of_prio t.(curPrio))) **
  tcb_cell (tcb64_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio t.(curPrio))) **
  tcb_cell (tcb64_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio t.(curPrio))) **
  event_task_wait_tcb_rest (tcb64_addr sg tid) (task_tcb64_image sg t) |--
  used_task_rep sg tid (task_set_event_ptr t (Some eid)).
Proof.
  intros sg tid t eid Hmulti Hprofile; rewrite used_task_rep_tcb64 by assumption.
  rewrite task_set_event_ptr_image_eq.
  exact (event_task_wait_tcb_merge_event_ptr (tcb64_addr sg tid)
    (task_tcb64_image sg t) (event_addr sg eid)).
Qed.

Definition event_task_wait_event_rest (named : bool) (base : addr) (row : Z)
  (image : EventStorage) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec EventGrpField
      (remove EventField_eq_dec (event_table_field row) (event_fields named))) image.

Lemma event_task_wait_event_split : forall named base image row row_value group_value,
  0 <= row < 8 -> image (event_table_field row) = Some row_value ->
  image EventGrpField = Some group_value ->
  event_storage_rep named base image |--
  (base + (11 + row)) # UChar |-> row_value **
  (base + 10) # UChar |-> group_value ** event_task_wait_event_rest named base row image.
Proof.
  intros named base image row row_value group_value Hrow Htable Hgroup.
  sep_apply_l_atomic (event_storage_split_field named base image (event_table_field row)
    (event_table_field_in_fields named row)).
  rewrite Htable, event_table_cell_eq by exact Hrow.
  unfold event_storage_without_field.
  sep_apply_l_atomic (EventFieldStorage.store_fields_split_field
    EventField (option Z) EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec (event_table_field row) (event_fields named)) image EventGrpField
    ltac:(destruct named; destruct (event_table_field row); cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(apply in_in_remove; [intro E; apply (event_table_field_not_group row); symmetry; exact E|cbn; tauto])).
  rewrite Hgroup; unfold event_task_wait_event_rest; cbn [event_cell event_field_offset]; entailer!.
Qed.

Lemma event_task_wait_event_merge_waiter : forall named base image row row_value group_value bit_x bit_y,
  0 <= row < 8 ->
  (base + (11 + row)) # UChar |-> Z.lor row_value bit_x **
  (base + 10) # UChar |-> Z.lor group_value bit_y **
  event_task_wait_event_rest named base row image |--
  event_storage_rep named base (event_mark_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros named base image row row_value group_value bit_x bit_y Hrow.
  assert (Hcomm : event_write
    (event_write image EventGrpField (Some (Z.lor group_value bit_y)))
    (event_table_field row) (Some (Z.lor row_value bit_x)) =
    event_mark_waiter image row row_value group_value bit_x bit_y).
  { apply functional_extensionality; intro f.
    unfold event_mark_waiter, event_mark_wait_row, event_write, field_update.
    destruct (EventField_eq_dec f (event_table_field row));
      destruct (EventField_eq_dec f EventGrpField); try reflexivity.
    exfalso; apply (event_table_field_not_group row); congruence. }
  rewrite <- Hcomm.
  unfold event_task_wait_event_rest.
  change ((base + 10) # UChar |-> Z.lor group_value bit_y) with
    (event_cell base EventGrpField (Some (Z.lor group_value bit_y))).
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_updated_field
    EventField (option Z) EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec (event_table_field row) (event_fields named))
    image EventGrpField (Some (Z.lor group_value bit_y))
    ltac:(destruct named; destruct (event_table_field row); cbn; repeat constructor; simpl; intuition discriminate)
    ltac:(apply in_in_remove; [intro E; apply (event_table_field_not_group row); symmetry; exact E|cbn; tauto])).
  rewrite <- event_table_cell_eq by exact Hrow.
  fold (event_storage_without_field named base
    (event_write image EventGrpField (Some (Z.lor group_value bit_y))) (event_table_field row)).
  sep_apply_l_atomic (event_storage_merge_updated_field named base
    (event_write image EventGrpField (Some (Z.lor group_value bit_y)))
    (event_table_field row) (Some (Z.lor row_value bit_x)) (event_table_field_in_fields named row)).
  entailer!.
Qed.

(** The numeric ECB representation is connected to the source lvalues only
    through the existing explicit layout premise.  Neither stable-global
    validity nor numeric equality of unrelated addresses supplies it. *)
Lemma event_task_wait_event_split_c_fields : forall sg eid image row row_value group_value,
  event_object_layout_prop sg eid ->
  0 <= row < 8 -> image (event_table_field row) = Some row_value ->
  image EventGrpField = Some group_value ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) image |--
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR))
    # UChar |-> row_value **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp") # UChar |-> group_value **
  event_task_wait_event_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) row image.
Proof.
  intros sg eid image row row_value group_value Hlayout Hrow Htable Hgroup.
  destruct (event_object_layout_wait_proj sg eid Hlayout) as [Hgrp Htbl].
  unfold OSEventGrp_off, OSEventTbl_off in Hgrp, Htbl.
  rewrite Hgrp, Htbl; change (sizeof(UCHAR)) with 1.
  replace (event_addr sg eid + 11 + row * 1) with (event_addr sg eid + (11 + row)) by lia.
  apply event_task_wait_event_split; assumption.
Qed.

Lemma event_task_wait_event_merge_c_fields : forall sg eid image row row_value group_value bit_x bit_y,
  event_object_layout_prop sg eid -> 0 <= row < 8 ->
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + row * sizeof(UCHAR))
    # UChar |-> Z.lor row_value bit_x **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp") # UChar |-> Z.lor group_value bit_y **
  event_task_wait_event_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) row image |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_mark_waiter image row row_value group_value bit_x bit_y).
Proof.
  intros sg eid image row row_value group_value bit_x bit_y Hlayout Hrow.
  destruct (event_object_layout_wait_proj sg eid Hlayout) as [Hgrp Htbl].
  unfold OSEventGrp_off, OSEventTbl_off in Hgrp, Htbl.
  rewrite Hgrp, Htbl; change (sizeof(UCHAR)) with 1.
  replace (event_addr sg eid + 11 + row * 1) with (event_addr sg eid + (11 + row)) by lia.
  apply event_task_wait_event_merge_waiter; exact Hrow.
Qed.

Lemma event_task_wait_event_merge_inserted_task : forall sg tasks eid e tid t,
  event_object_layout_prop sg eid -> tasks.(inUsedTaskStates) tid = Some t ->
  0 <= t.(curPrio) / 8 < 8 ->
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + t.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> Z.lor (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (tcb_bit_x_of_prio t.(curPrio)) **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    # UChar |-> Z.lor (encode_event_wait_grp e.(waitList) tasks) (tcb_bit_y_of_prio t.(curPrio)) **
  event_task_wait_event_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (t.(curPrio) / 8) (event_image sg tasks e) |--
  used_event_rep sg tasks eid (event_insert_waiter sg tasks e tid).
Proof.
  intros sg tasks eid e tid t Hlayout Ht Hrow.
  unfold used_event_rep; rewrite (event_insert_waiter_image_eq sg tasks e tid t Ht Hrow).
  apply event_task_wait_event_merge_c_fields; assumption.
Qed.

(** The existing bitmap encoding transport applies to this helper because
    changing only EventPtr preserves every task priority lookup.  It also
    applies to ready rows: the Event and Scheduler OR encodings coincide. *)
Lemma event_task_wait_bitmap_task_index_eq : forall ids tasks tid old eid,
  tasks.(inUsedTaskStates) tid = Some old ->
  let updated := glob_task_set_usedtask tasks tid (task_set_event_ptr old (Some eid)) in
  encode_event_wait_grp ids tasks = encode_event_wait_grp ids updated /\
  forall row, encode_event_wait_tbl_at_or ids tasks row =
    encode_event_wait_tbl_at_or ids updated row.
Proof.
  intros ids tasks tid old eid Hold updated.
  apply event_wait_encoding_priority_ext; intros slot Hin.
  unfold updated; cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E; subst slot; rewrite Hold; reflexivity.
Qed.

Lemma event_task_wait_event_image_task_index_eq : forall sg tasks tid old eid e,
  tasks.(inUsedTaskStates) tid = Some old ->
  event_image sg tasks e =
  event_image sg (glob_task_set_usedtask tasks tid (task_set_event_ptr old (Some eid))) e.
Proof.
  intros sg tasks tid old eid e Hold.
  destruct (event_task_wait_bitmap_task_index_eq e.(waitList) tasks tid old eid Hold)
    as [Hgroup Htable].
  apply functional_extensionality; intros []; cbn [event_image];
    rewrite ?Hgroup, ?Htable; reflexivity.
Qed.

(** This is only bitmap structure.  The caller has already changed pending
    fields, so sched_in_range is intentionally not a premise here. *)
Lemma event_task_wait_ready_rows_eq : forall sg tasks s tid t,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) tid = Some t -> task_priority_in_range sg t.(curPrio) ->
  sched_ready_structure sg tasks s -> 0 <= t.(curPrio) / 8 < 8 ->
  sched_row_values tasks (sched_remove_ready_task s tid).(readyList) =
    replace_Znth (t.(curPrio) / 8)
      (event_task_wait_ready_row (encode_ready_tbl_at_or s.(readyList) tasks (t.(curPrio) / 8))
        (tcb_bit_x_of_prio t.(curPrio))) (sched_row_values tasks s.(readyList)).
Proof.
  intros sg tasks s tid t Hsg Hunique Ht Hprio Hstructure Hy.
  destruct (sched_remove_ready_encoding sg tasks s tid t Hsg Hunique Ht Hprio Hstructure)
    as [Hgroup Htable].
  set (y := t.(curPrio) / 8) in *.
  assert (Hvalues : sched_row_values tasks (sched_remove_ready_task s tid).(readyList) =
    map (fun row => if Z.eqb row y
      then event_task_wait_ready_row (encode_ready_tbl_at_or s.(readyList) tasks y)
        (tcb_bit_x_of_prio t.(curPrio))
      else encode_ready_tbl_at_or s.(readyList) tasks row) [0;1;2;3;4;5;6;7]).
  { unfold sched_row_values; apply map_ext; intro row.
    rewrite Htable; destruct (Z.eqb row y) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst row; reflexivity. }
  rewrite Hvalues.
  assert (Hcases : y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/
    y = 4 \/ y = 5 \/ y = 6 \/ y = 7) by lia.
  repeat destruct Hcases as [Hcases|Hcases]; rewrite Hcases; reflexivity.
Qed.

Lemma event_task_wait_ready_merge_removed_task : forall sg tasks s tid t,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) tid = Some t -> task_priority_in_range sg t.(curPrio) ->
  sched_ready_structure sg tasks s -> 0 <= t.(curPrio) / 8 < 8 ->
  (sg.(g_OSRdyTbl) + t.(curPrio) / 8 * sizeof(UCHAR)) # UChar |->
    event_task_wait_ready_row (encode_ready_tbl_at_or s.(readyList) tasks (t.(curPrio) / 8))
      (tcb_bit_x_of_prio t.(curPrio)) **
  UCharArray.missing_i sg.(g_OSRdyTbl) (t.(curPrio) / 8) 0 8
    (sched_row_values tasks s.(readyList)) **
  sg.(g_OSRdyGrp) # UChar |-> event_task_wait_ready_group
    (encode_ready_tbl_at_or s.(readyList) tasks (t.(curPrio) / 8))
    (encode_ready_grp s.(readyList) tasks)
    (tcb_bit_x_of_prio t.(curPrio)) (tcb_bit_y_of_prio t.(curPrio)) |--
  sched_rows_rep sg tasks (sched_remove_ready_task s tid).(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp (sched_remove_ready_task s tid).(readyList) tasks.
Proof.
  intros sg tasks s tid t Hsg Hunique Ht Hprio Hstructure Hy.
  destruct (sched_remove_ready_encoding sg tasks s tid t Hsg Hunique Ht Hprio Hstructure)
    as [Hgroup Htable].
  rewrite sched_rows_array_equiv.
  rewrite (event_task_wait_ready_rows_eq sg tasks s tid t Hsg Hunique Ht Hprio Hstructure Hy).
  change (encode_ready_grp (sched_remove_ready_task s tid).(readyList) tasks =
    event_task_wait_ready_group (encode_ready_tbl_at_or s.(readyList) tasks (t.(curPrio) / 8))
      (encode_ready_grp s.(readyList) tasks)
      (tcb_bit_x_of_prio t.(curPrio)) (tcb_bit_y_of_prio t.(curPrio))) in Hgroup.
  rewrite Hgroup.
  sep_apply_l_atomic (sched_rows_merge_updated_array sg tasks s.(readyList) (t.(curPrio) / 8)
    (event_task_wait_ready_row (encode_ready_tbl_at_or s.(readyList) tasks (t.(curPrio) / 8))
      (tcb_bit_x_of_prio t.(curPrio))) Hy).
  entailer!.
Qed.

(** The abstract wait-entry consequence reuses the caller's pending prefix.
    It establishes the newly linked entry but does not claim that this
    helper wrote Stat/StatPend/Dly or restored the whole kernel protocol. *)
Lemma event_task_wait_establishes_wait_entry : forall sg tasks eid e tid old kind,
  task_in_range sg tasks -> event_wait_entry_consistency sg tasks eid e ->
  tasks.(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] ->
  task_non_suspension_bits old.(stat) = task_pend_mask kind ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  let updated := glob_task_set_usedtask tasks tid (task_set_event_ptr old (Some eid)) in
  event_wait_entry_consistency sg updated eid (event_insert_waiter sg updated e tid) /\
  (task_set_event_ptr old (Some eid)).(stat) = old.(stat) /\
  (task_set_event_ptr old (Some eid)).(statPend) = old.(statPend) /\
  (task_set_event_ptr old (Some eid)).(dly) = old.(dly) /\
  (task_set_event_ptr old (Some eid)).(msg) = old.(msg).
Proof.
  intros sg tasks eid e tid old kind Htasks Hentry Hold Hprio Hnull Hmulti Hpending Hkind updated.
  split; [eapply event_wait_entry_insert_update_task; eauto|repeat split; reflexivity].
Qed.
