Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.sched.

Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The concrete lookup result is total on byte-valued ready bitmaps.  It
    reuses the source table's decoder, without assuming that the bitmap
    represents any ready task or that the scheduler is running. *)
Definition sched_new_priority (group : Z) (rows : list Z) : Z :=
  unmap_value group * 8 +
  unmap_value (Znth (unmap_value group) rows 0).

Definition sched_new_global_addresses (sg : StableGlobVars)
  (unmap group rows high : Z) : Prop :=
  unmap = sg.(g_OSUnMapTbl) /\ group = sg.(g_OSRdyGrp) /\
  rows = sg.(g_OSRdyTbl) /\ high = sg.(g_OSPrioHighRdy).

(** Exact owned cells of the helper, in the caller's UCOS2 assertion
    instance.  Interrupt protection is supplied by the caller; this helper
    has no critical transition.  An arbitrary disjoint frame carries the
    current cache, the old high-ready TCB pointer and all other resources. *)
Definition sched_new_rep (sg : StableGlobVars)
  (group : Z) (rows : list Z) (high : Z) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> group **
  UCharArray.full sg.(g_OSRdyTbl) 8 rows **
  unmap_table_rep sg **
  sg.(g_OSPrioHighRdy) # UChar |-> high.

Lemma sched_new_priority_in_range : forall group rows,
  0 <= sched_new_priority group rows < 64.
Proof.
  intros; unfold sched_new_priority.
  pose proof (unmap_in_range group).
  pose proof (unmap_in_range (Znth (unmap_value group) rows 0)); lia.
Qed.

Lemma sched_new_priority_empty_eq_zero :
  sched_new_priority 0 [0;0;0;0;0;0;0;0] = 0.
Proof. reflexivity. Qed.

Lemma sched_new_priority_eq_selected : forall tasks s,
  sched_new_priority (encode_ready_grp s.(readyList) tasks)
    (sched_row_values tasks s.(readyList)) = sched_selected_priority tasks s.
Proof.
  intros; unfold sched_new_priority, sched_selected_priority.
  rewrite sched_row_values_Znth by apply unmap_in_range; reflexivity.
Qed.

(** The minimum-ready-task consequence needs canonical bitmap/priority
    correspondence and a nonempty ready list.  It is not an extra Require
    on the source-total byte contract. *)
Lemma sched_new_priority_eq_head : forall sg tasks s head tail t,
  valid_stable_glob_vars sg -> sched_ready_in_range sg tasks s ->
  s.(readyList) = head :: tail -> tasks.(inUsedTaskStates) head = Some t ->
  sched_new_priority (encode_ready_grp s.(readyList) tasks)
    (sched_row_values tasks s.(readyList)) = t.(curPrio).
Proof.
  intros; rewrite sched_new_priority_eq_selected.
  eapply sched_selected_priority_eq_head; eassumption.
Qed.

(** Caller-side framing exposes just the cells OS_SchedNew reads/writes.
    No task ownership, current cache or high pointer is consumed. *)
Lemma sched_raw_rep_sched_new_equiv : forall sg tasks s,
  sched_raw_rep sg tasks s ** unmap_table_rep sg --||--
  sched_new_rep sg (encode_ready_grp s.(readyList) tasks)
    (sched_row_values tasks s.(readyList))
    (sched_priority_byte s.(highRdyPrio)) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sched_physical_without_high sg s.
Proof.
  intros; unfold sched_raw_rep, sched_new_rep.
  rewrite sched_rows_array_equiv.
  unfold sched_physical_rep, sched_physical_without_high.
  split; entailer!.
Qed.

Lemma sched_new_rep_priority_written_equiv : forall sg tasks s,
  sched_new_rep sg (encode_ready_grp s.(readyList) tasks)
    (sched_row_values tasks s.(readyList))
    (sched_new_priority (encode_ready_grp s.(readyList) tasks)
      (sched_row_values tasks s.(readyList))) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sched_physical_without_high sg s --||--
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tasks **
  sched_rows_rep sg tasks s.(readyList) [0;1;2;3;4;5;6;7] **
  sched_priority_written_rep sg tasks s ** unmap_table_rep sg.
Proof.
  intros; unfold sched_new_rep, sched_priority_written_rep, sched_cache_cells.
  rewrite sched_new_priority_eq_selected, sched_rows_array_equiv.
  split; entailer!.
Qed.

Lemma sched_new_rep_after_priority_write_equiv : forall sg tasks s,
  sched_new_rep sg (encode_ready_grp s.(readyList) tasks)
    (sched_row_values tasks s.(readyList))
    (sched_new_priority (encode_ready_grp s.(readyList) tasks)
      (sched_row_values tasks s.(readyList))) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sched_physical_without_high sg s --||--
  sched_raw_rep sg tasks (sched_priority_write_state tasks s) **
  unmap_table_rep sg.
Proof.
  intros; rewrite sched_new_rep_priority_written_equiv.
  rewrite sched_priority_written_physical_eq.
  unfold sched_raw_rep, sched_priority_write_state, sched_write_high_priority.
  simpl; split; entailer!.
Qed.
