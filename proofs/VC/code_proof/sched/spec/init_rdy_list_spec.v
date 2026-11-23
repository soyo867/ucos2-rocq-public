Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.sched.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(** The six parameters are the actual C global-cell addresses.  No TCB
    object, counter, running flag, lookup table, or pre-existing scheduler
    invariant is consumed.  Any disjoint caller resource is a frame. *)
Definition init_rdy_list_pre
  (group table current_prio high_prio high_tcb current_tcb : addr) : Assertion :=
  group # UChar |->_ ** UCharArray.undef_full table 8 **
  current_prio # UChar |->_ ** high_prio # UChar |->_ **
  high_tcb # Ptr |->_ ** current_tcb # Ptr |->_ .

Definition init_rdy_list_post
  (group table current_prio high_prio high_tcb current_tcb : addr) : Assertion :=
  group # UChar |-> 0 ** UCharArray.full table 8 (repeat 0 8) **
  current_prio # UChar |-> 0 ** high_prio # UChar |-> 0 **
  high_tcb # Ptr |-> 0 ** current_tcb # Ptr |-> 0.

(** The processed prefix contains exactly zeros; the suffix has writable
    ownership, without an assumption on the overwritten initial values. *)
Definition init_rdy_list_table_prefix (table count : Z) : Assertion :=
  UCharArray.full table count (repeat 0 (Z.to_nat count)) **
  UCharArray.undef_seg table count 8.

Definition init_rdy_list_row_frame (table count : Z) : Assertion :=
  UCharArray.full table count (repeat 0 (Z.to_nat count)) **
  UCharArray.undef_seg table (count + 1) 8.

Lemma init_rdy_list_pre_split_group :
  forall group table current_prio high_prio high_tcb current_tcb,
  init_rdy_list_pre group table current_prio high_prio high_tcb current_tcb |--
  group # UChar |->_ ** init_rdy_list_table_prefix table 0 **
  current_prio # UChar |->_ ** high_prio # UChar |->_ **
  high_tcb # Ptr |->_ ** current_tcb # Ptr |->_ .
Proof.
  intros; unfold init_rdy_list_pre, init_rdy_list_table_prefix.
  change (Z.to_nat 0) with 0%nat; simpl repeat.
  rewrite UCharArray.full_empty.
  change (UCharArray.undef_full table 8) with (UCharArray.undef_seg table 0 8).
  entailer!.
Qed.

Lemma init_rdy_list_table_prefix_split_row : forall table count,
  0 <= count < 8 ->
  init_rdy_list_table_prefix table count |--
  (table + count) # UChar |->_ ** init_rdy_list_row_frame table count.
Proof.
  intros table count Hcount.
  unfold init_rdy_list_table_prefix, init_rdy_list_row_frame.
  rewrite UCharArray.undef_seg_unfold by lia.
  unfold StoreUCharAsElement.undefstoreA; change (sizeof(UCHAR)) with 1.
  replace (table + count * 1) with (table + count) by lia; entailer!.
Qed.

Lemma init_rdy_list_table_prefix_merge_row : forall table count,
  0 <= count < 8 ->
  (table + count) # UChar |-> 0 ** init_rdy_list_row_frame table count |--
  init_rdy_list_table_prefix table (count + 1).
Proof.
  intros table count Hcount.
  unfold init_rdy_list_row_frame, init_rdy_list_table_prefix.
  assert (Hrepeat : repeat 0 (Z.to_nat (count + 1)) =
    repeat 0 (Z.to_nat count) ++ [0]).
  { replace (Z.to_nat (count + 1)) with (Z.to_nat count + 1)%nat by lia.
    apply repeat_app. }
  rewrite Hrepeat.
  assert (Hcell : (table + count) # UChar |-> 0 |--
    UCharArray.full (table + count) 1 [0]).
  { rewrite UCharArray.full_unfold, UCharArray.seg_empty.
    unfold StoreUCharAsElement.storeA, StoreUCharAsElement.sizeA;
      change (sizeof(UCHAR)) with 1.
    replace (table + count + 0 * 1) with (table + count) by lia.
    entailer!. }
  sep_apply_l_atomic Hcell.
  pose proof (UCharArray.full_merge_to_full table count (count + 1)
    (repeat 0 (Z.to_nat count)) [0] ltac:(lia)) as Hmerge.
  unfold StoreUCharAsElement.sizeA in Hmerge; change (sizeof(UCHAR)) with 1 in Hmerge.
  replace (table + count * 1) with (table + count) in Hmerge by lia.
  replace (count + 1 - count) with 1 in Hmerge by lia.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma init_rdy_list_table_prefix_complete : forall table,
  init_rdy_list_table_prefix table 8 |--
  UCharArray.full table 8 (repeat 0 8).
Proof.
  intros; unfold init_rdy_list_table_prefix.
  rewrite UCharArray.undef_seg_empty; entailer!.
Qed.

(** OS_InitMisc supplies these two already-zero cells before OS_InitRdyList.
    They are composition premises, not effects of this function.  Applying
    this lemma to the C Ensure requires the actual six global addresses to
    be identified with the corresponding StableGlobVars fields.  The raw
    representation needs no assumption about the used-task map. *)
Lemma init_rdy_list_post_implies_sched_boot_rep : forall sg tasks,
  init_rdy_list_post sg.(g_OSRdyGrp) sg.(g_OSRdyTbl)
    sg.(g_OSPrioCur) sg.(g_OSPrioHighRdy) sg.(g_OSTCBHighRdy) sg.(g_OSTCBCur) **
  sg.(g_OSCtxSwCtr) # UInt |-> 0 ** sg.(g_OSRunning) # UChar |-> 0 |--
  sched_raw_rep sg tasks sched_boot.
Proof.
  intros; unfold init_rdy_list_post, sched_raw_rep, sched_physical_rep, sched_boot.
  cbn [sched_rows_rep readyList curSchedPrio highRdyPrio curTaskID highRdyTid
    ctxSwCtr isRunning sched_priority_byte Ucos2Verify.lib.task.encode_task_link
    encode_ready_grp encode_ready_tbl_at_or fold_right].
  cbn [repeat].
  rewrite UCharArray.full_unfold.
  repeat rewrite UCharArray.seg_unfold.
  rewrite UCharArray.seg_empty.
  unfold StoreUCharAsElement.storeA; change (sizeof(UCHAR)) with 1.
  repeat match goal with
  | |- context [g_OSRdyTbl sg + ?row * 1] =>
      replace (g_OSRdyTbl sg + row * 1) with (g_OSRdyTbl sg + row) by lia
  end.
  entailer!.
Qed.

(** Only the later scheduler-invariant consequence uses the empty used map.
    OS_InitTCBList follows OS_InitRdyList in OSInit; this is not an entry
    premise of OS_InitRdyList. *)
Lemma init_rdy_list_post_implies_sched_boot_inv : forall sg tasks,
  (forall tid, tasks.(inUsedTaskStates) tid = None) ->
  init_rdy_list_post sg.(g_OSRdyGrp) sg.(g_OSRdyTbl)
    sg.(g_OSPrioCur) sg.(g_OSPrioHighRdy) sg.(g_OSTCBHighRdy) sg.(g_OSTCBCur) **
  sg.(g_OSCtxSwCtr) # UInt |-> 0 ** sg.(g_OSRunning) # UChar |-> 0 |--
  sched_inv sg tasks sched_boot.
Proof.
  intros sg tasks Hempty.
  sep_apply_l_atomic (init_rdy_list_post_implies_sched_boot_rep sg tasks).
  unfold sched_inv; entailer!; apply sched_boot_in_range; exact Hempty.
Qed.
