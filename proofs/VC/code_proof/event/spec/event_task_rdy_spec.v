Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.helpers.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.task_status.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.event_wait.
Require Export Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.VC.code.event.spec.event_task_remove_spec.

Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Internal, caller-protected entry.  The nonempty canonical wait list and
    registered task supply the real priority-table owner.  These are initial
    snapshots, not a global invariant required at the inner Remove call. *)
Definition event_task_rdy_entry (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (eid : Z) (e : OSEventAbstractState)
  (tid : Z) (t : TaskAbstractState) : Prop :=
  valid_stable_glob_vars sg /\ event_object_layout_prop sg eid /\
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false /\
  task_in_range sg tasks /\ event_wait_entry_consistency sg tasks eid e /\
  hd_error e.(waitList) = Some tid /\ tasks.(inUsedTaskStates) tid = Some t.

(** The raw byte result is intentionally not decoded as PendStatus.  This
    function-specific prefix extends the existing typed wake image to the
    complete byte argument domain without changing canonical task semantics. *)
Definition event_task_rdy_before_remove_image (sg : StableGlobVars)
  (t : TaskAbstractState) (message mask result : Z) : TCBCommonImage :=
  tcb_write
    (tcb_write
      (tcb_write (tcb_write (task_tcb64_image sg t) TCBDly (Some 0))
        TCBMsg (Some message))
      TCBStat (Some (task_status_clear_wait (encode_task_status t.(stat)) mask)))
    TCBStatPend (Some result).

Definition event_task_rdy_task_image (sg : StableGlobVars)
  (t : TaskAbstractState) (message mask result : Z) : TCBCommonImage :=
  tcb_write (event_task_rdy_before_remove_image sg t message mask result)
    TCBEventPtr (Some 0).

Definition event_task_rdy_ready_group (bits group bit_y : Z) : Z :=
  if task_status_is_suspended bits then group else Z.lor group bit_y.

Definition event_task_rdy_ready_rows (bits row bit_x : Z) (rows : list Z) : list Z :=
  if task_status_is_suspended bits then rows
  else replace_Znth row (Z.lor (Znth row rows 0) bit_x) rows.

Definition event_task_rdy_prio_frame (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (priority : Z) : Assertion :=
  PtrArray.missing_i sg.(g_OSTCBPrioTbl) priority 0 64
    (map (fun q => prio_tbl_entry_to_addr sg (tasks.(prioTbl) q)) (Zrange 0 64)).

Lemma event_task_rdy_prio_split : forall sg tasks tid priority,
  0 <= priority < 64 -> tasks.(prioTbl) priority = PTTask tid ->
  store_prio_tbl sg tasks.(prioTbl) |--
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> task_slot_addr sg tid **
  event_task_rdy_prio_frame sg tasks priority.
Proof.
  intros sg tasks tid priority Hp Howner; unfold store_prio_tbl, event_task_rdy_prio_frame.
  pose proof (prio_table_values_Znth sg tasks.(prioTbl) priority Hp) as Hvalue.
  rewrite Howner in Hvalue; cbn [prio_tbl_entry_to_addr] in Hvalue; rewrite <- Hvalue.
  apply PtrArray.full_split_to_missing_i; exact Hp.
Qed.

Lemma event_task_rdy_prio_merge : forall sg tasks tid priority,
  0 <= priority < 64 -> tasks.(prioTbl) priority = PTTask tid ->
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |-> task_slot_addr sg tid **
  event_task_rdy_prio_frame sg tasks priority |-- store_prio_tbl sg tasks.(prioTbl).
Proof.
  intros sg tasks tid priority Hp Howner; unfold store_prio_tbl, event_task_rdy_prio_frame.
  pose proof (prio_table_values_Znth sg tasks.(prioTbl) priority Hp) as Hvalue.
  rewrite Howner in Hvalue; cbn [prio_tbl_entry_to_addr] in Hvalue.
  pose proof (PtrArray.missing_i_merge_to_full sg.(g_OSTCBPrioTbl) priority 64
    (Znth priority (map (fun q => prio_tbl_entry_to_addr sg (tasks.(prioTbl) q))
      (Zrange 0 64)) 0)
    (map (fun q => prio_tbl_entry_to_addr sg (tasks.(prioTbl) q)) (Zrange 0 64)) Hp) as Hmerge.
  rewrite replace_Znth_Znth in Hmerge.
  rewrite <- Hvalue; exact Hmerge.
Qed.

Definition event_task_rdy_pre (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (eid : Z) (e : OSEventAbstractState)
  (tid : Z) (t : TaskAbstractState) (mask result group : Z) (rows : list Z) : Assertion :=
  “ (event_task_rdy_entry sg tasks eid e tid t /\
     0 <= mask < 256 /\ 0 <= result < 256 /\ Zlength rows = 8) ” &&
  (tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg t) **
   event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (event_image sg tasks e) **
   unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
   sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows).

(** Full object images and both unchanged lookup tables are returned.  The
    ready bitmap input is a raw snapshot; the scheduler lemmas below connect
    canonical inputs to sched_wake_by_status.  Arbitrary disjoint resources
    follow the frame rule.  No global-invariant or architecture-switch claim
    is made for arbitrary byte mask/result arguments. *)
Definition event_task_rdy_post (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (eid : Z) (e : OSEventAbstractState)
  (tid : Z) (t : TaskAbstractState) (message mask result group : Z)
  (rows : list Z) (returned : Z) : Assertion :=
  “ (returned = event_wait_priority tasks e /\ returned = t.(curPrio)) ” &&
  (tcb64_storage_rep (task_slot_addr sg tid)
     (event_task_rdy_task_image sg t message mask result) **
   event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
     (event_image sg tasks (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))) **
   unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
   sg.(g_OSRdyGrp) # UChar |->
     event_task_rdy_ready_group (task_status_clear_wait (encode_task_status t.(stat)) mask)
       group (tcb_bit_y_of_prio t.(curPrio)) **
   UCharArray.full sg.(g_OSRdyTbl) 8
     (event_task_rdy_ready_rows (task_status_clear_wait (encode_task_status t.(stat)) mask)
       (tcb_y_of_prio t.(curPrio)) (tcb_bit_x_of_prio t.(curPrio)) rows)).

Lemma event_task_rdy_selection : forall sg tasks eid e tid t,
  event_task_rdy_entry sg tasks eid e tid t ->
  event_wait_priority tasks e = t.(curPrio) /\
  tasks.(prioTbl) t.(curPrio) = PTTask tid /\
  valid_task_prio sg t.(curPrio) /\
  0 <= t.(curPrio) < 64 /\
  unmap_value (encode_event_wait_grp e.(waitList) tasks) = tcb_y_of_prio t.(curPrio) /\
  unmap_value (encode_event_wait_tbl_at_or e.(waitList) tasks (tcb_y_of_prio t.(curPrio))) =
    tcb_x_of_prio t.(curPrio).
Proof.
  intros sg tasks eid e tid t [Hsg [Hlayout [Hmulti [Htasks [Hentry [Hhead Ht]]]]]].
  destruct e.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wait_priority_table_entry sg tasks eid e tid tail
    Hsg Htasks Hentry Hlist) as [found [Hfound [Hprio Htable]]].
  assert (found = t) by congruence; subst found.
  destruct Hentry as [[Hnd [Hsorted Hmembers]] Hphase].
  destruct (Hmembers tid ltac:(rewrite Hlist; left; reflexivity)) as [node [Hnode Hp]].
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
  - rewrite <- Hprio; exact Htable.
  - rewrite <- Hlist; exact Hcoord.
  - rewrite <- Hlist.
    pose proof (f_equal (fun p => p mod 8) Hprio) as Hmod.
    unfold event_wait_priority in Hmod; cbn zeta in Hmod.
    rewrite Z.add_comm, Z.mod_add, Z.mod_small in Hmod by lia.
    unfold tcb_x_of_prio; rewrite <- Hcoord; exact Hmod.
Qed.

Lemma event_task_rdy_task_image_frame : forall sg t message mask result field,
  field <> TCBDly -> field <> TCBMsg -> field <> TCBStat ->
  field <> TCBStatPend -> field <> TCBEventPtr ->
  event_task_rdy_task_image sg t message mask result field = task_tcb64_image sg t field.
Proof.
  intros; unfold event_task_rdy_task_image, event_task_rdy_before_remove_image;
    repeat rewrite tcb_write_frame by assumption; reflexivity.
Qed.

Lemma event_task_rdy_before_remove_typed_image_eq : forall sg t message kind result,
  event_task_rdy_before_remove_image sg t message (task_pend_mask kind)
    (encode_pend_status result) =
  task_tcb64_image sg (task_event_wake_before_remove t kind message result).
Proof. intros; rewrite task_event_wake_before_remove_image_eq; reflexivity. Qed.

Lemma event_task_rdy_typed_image_eq : forall sg t message mask raw_result kind result,
  mask = task_pend_mask kind -> raw_result = encode_pend_status result ->
  event_task_rdy_task_image sg t message mask raw_result =
  task_tcb64_image sg (task_event_wake_single t kind message result).
Proof.
  intros; subst; unfold event_task_rdy_task_image.
  rewrite event_task_rdy_before_remove_typed_image_eq, task_event_wake_single_image_eq;
    reflexivity.
Qed.

Lemma event_task_rdy_wait_relation : forall sg tasks eid e tid new,
  event_wait_entry_consistency sg tasks eid e ->
  event_wait_entry_consistency sg (glob_task_set_usedtask tasks tid new) eid
    (event_set_wait_list e (remove_Z_eqb tid e.(waitList))).
Proof. intros; apply event_wait_entry_remove_update_task; assumption. Qed.

Lemma event_task_rdy_scheduler_group_eq : forall sg tasks s tid t bits,
  tasks.(inUsedTaskStates) tid = Some t ->
  event_task_rdy_ready_group bits (encode_ready_grp s.(readyList) tasks)
    (tcb_bit_y_of_prio t.(curPrio)) =
  encode_ready_grp (sched_wake_by_status sg tasks s tid bits).(readyList) tasks.
Proof.
  intros; symmetry; exact (proj1 (sched_wake_by_status_encoding sg tasks s tid t bits H)).
Qed.

Lemma event_task_rdy_scheduler_rows_eq : forall sg tasks s tid t bits,
  tasks.(inUsedTaskStates) tid = Some t -> 0 <= t.(curPrio) < 64 ->
  event_task_rdy_ready_rows bits (tcb_y_of_prio t.(curPrio))
    (tcb_bit_x_of_prio t.(curPrio)) (sched_row_values tasks s.(readyList)) =
  sched_row_values tasks (sched_wake_by_status sg tasks s tid bits).(readyList).
Proof.
  intros sg tasks s tid t bits Ht Hp.
  destruct (sched_wake_by_status_encoding sg tasks s tid t bits Ht) as [_ Hrows].
  unfold event_task_rdy_ready_rows, sched_row_values.
  cbn [map].
  rewrite (Hrows 0), (Hrows 1), (Hrows 2), (Hrows 3),
    (Hrows 4), (Hrows 5), (Hrows 6), (Hrows 7).
  destruct (task_status_is_suspended bits); [reflexivity|].
  unfold tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio.
  assert (Hy : 0 <= t.(curPrio) / 8 < 8).
  { split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hcases : t.(curPrio) / 8 = 0 \/ t.(curPrio) / 8 = 1 \/
    t.(curPrio) / 8 = 2 \/ t.(curPrio) / 8 = 3 \/ t.(curPrio) / 8 = 4 \/
    t.(curPrio) / 8 = 5 \/ t.(curPrio) / 8 = 6 \/ t.(curPrio) / 8 = 7) by lia.
  repeat destruct Hcases as [Hcases|Hcases]; rewrite Hcases; reflexivity.
Qed.
(** Structural residual of this function's eight accessed TCB fields.
    It retains all other fields and both padding bytes, with their old values. *)
Definition event_task_rdy_tcb_frame (base : addr) (image : TCBCommonImage) : Assertion :=
  tcb64_fields_rep base (remove TCBField_eq_dec TCBEventPtr (remove TCBField_eq_dec TCBBitY (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields)))))))) image.

Lemma event_task_rdy_tcb_split : forall base image,
  tcb64_storage_rep base image |--
  tcb_cell base TCBDly (image TCBDly) **
  tcb_cell base TCBMsg (image TCBMsg) **
  tcb_cell base TCBStat (image TCBStat) **
  tcb_cell base TCBStatPend (image TCBStatPend) **
  tcb_cell base TCBY (image TCBY) **
  tcb_cell base TCBBitX (image TCBBitX) **
  tcb_cell base TCBBitY (image TCBBitY) **
  tcb_cell base TCBEventPtr (image TCBEventPtr) ** event_task_rdy_tcb_frame base image.
Proof.
  intros; unfold tcb64_storage_rep.
  sep_apply_l_atomic (tcb64_fields_rep_split tcb_fields base image TCBDly
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBDly tcb_fields) base image TCBMsg
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields)) base image TCBStat
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields))) base image TCBStatPend
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields)))) base image TCBY
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields))))) base image TCBBitX
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields)))))) base image TCBBitY
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBBitY (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields))))))) base image TCBEventPtr
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  unfold event_task_rdy_tcb_frame; entailer!.
Qed.

Lemma event_task_rdy_tcb_merge : forall base image,
  tcb_cell base TCBDly (image TCBDly) **
  tcb_cell base TCBMsg (image TCBMsg) **
  tcb_cell base TCBStat (image TCBStat) **
  tcb_cell base TCBStatPend (image TCBStatPend) **
  tcb_cell base TCBY (image TCBY) **
  tcb_cell base TCBBitX (image TCBBitX) **
  tcb_cell base TCBBitY (image TCBBitY) **
  tcb_cell base TCBEventPtr (image TCBEventPtr) ** event_task_rdy_tcb_frame base image |--
  tcb64_storage_rep base image.
Proof.
  intros; unfold event_task_rdy_tcb_frame.
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBBitY (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields))))))) base image TCBEventPtr
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields)))))) base image TCBBitY
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields))))) base image TCBBitX
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields)))) base image TCBY
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields))) base image TCBStatPend
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBMsg (remove TCBField_eq_dec TCBDly tcb_fields)) base image TCBStat
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBDly tcb_fields) base image TCBMsg
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge tcb_fields base image TCBDly
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  unfold tcb64_storage_rep; entailer!.
Qed.

Lemma event_task_rdy_tcb_frame_updated_eq : forall sg t base message mask result,
  event_task_rdy_tcb_frame base (event_task_rdy_task_image sg t message mask result) =
  event_task_rdy_tcb_frame base (task_tcb64_image sg t).
Proof.
  intros; unfold event_task_rdy_tcb_frame, event_task_rdy_task_image,
    event_task_rdy_before_remove_image.
  repeat rewrite tcb64_fields_rep_off_field by
    (vm_compute; intuition discriminate).
  reflexivity.
Qed.

Lemma event_task_rdy_tcb_merge_updated : forall sg t base message mask result,
  tcb_cell base TCBDly (Some 0) **
  tcb_cell base TCBMsg (Some message) **
  tcb_cell base TCBStat (Some (task_status_clear_wait (encode_task_status t.(stat)) mask)) **
  tcb_cell base TCBStatPend (Some result) **
  tcb_cell base TCBY (Some (tcb_y_of_prio t.(curPrio))) **
  tcb_cell base TCBBitX (Some (tcb_bit_x_of_prio t.(curPrio))) **
  tcb_cell base TCBBitY (Some (tcb_bit_y_of_prio t.(curPrio))) **
  tcb_cell base TCBEventPtr (Some 0) **
  event_task_rdy_tcb_frame base (task_tcb64_image sg t) |--
  tcb64_storage_rep base (event_task_rdy_task_image sg t message mask result).
Proof.
  intros; rewrite <- (event_task_rdy_tcb_frame_updated_eq sg t base message mask result).
  exact (event_task_rdy_tcb_merge base (event_task_rdy_task_image sg t message mask result)).
Qed.
