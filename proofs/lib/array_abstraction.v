(* ================================================================== *)
(* lib/array_abstraction.v                                            *)
(*                                                                    *)
(* 通用数组 list 抽象基础设施,服务于 mutex 模块变下标访问:           *)
(*   - OSRdyTbl[8]     : OS_PRIO (uint8)                              *)
(*   - OSTCBPrioTbl[64]: OS_TCB *  (指针)                             *)
(*   - OSEventTbl[8]   : OS_PRIO (uint8,per-event 偏移 11)            *)
(*                                                                    *)
(* 参照 los_verify lib/sched.v 的 g_priQueueList_* 模式:              *)
(*   PRE 用 store_<array> sg l (整体 list 资源)                       *)
(*   body which implies 展开为 store_<array>_missing_i + Znth         *)
(*   POST 用 replace_Znth 表达"改一位"                                *)
(*                                                                    *)
(* which_implies_wit 用 store_array_split,return_wit 用               *)
(* store_array_merge (来自 SimpleC.SL ArrayLib,经 UCOS2_C_Rules).     *)
(* ================================================================== *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SumLib.ZRange.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
(* 用 Require Export 而非 Require Import,把 task.v 中的 *)
(* verification_slice_store_priotbl_list / verification_slice_prioTbl_to_addrs 等定义 re-export 给下游 *)
(* (goal.v 通过 Require array_abstraction 即可访问)             *)
Require Export Ucos2Verify.lib.task.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import SchedStateDef.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.
Local Open Scope sac_scope.

(* ================================================================== *)
(* 第 1 节:数组长度与字节布局                                         *)
(* ================================================================== *)

(* OS_LOWEST_PRIO <= 63 时,OSRdyTbl 与 OSEventTbl 长度均为 8 *)
Definition OS_RDY_TBL_SIZE   : Z := 8.
Definition OS_EVENT_TBL_SIZE : Z := 8.

Definition zero_event_tbl (_ : list Z) : list Z :=
  [0; 0; 0; 0; 0; 0; 0; 0].

(* OS_PRIO 为 INT8U,1 字节 *)
Definition sizeof_OS_PRIO : Z := 1.

(* sizeof_OSTCB_ptr / sizeof_OSTCB_ptr_pos / OS_PRIO_TBL_SIZE 已下沉到 *)
(* lib/task.v,因为 verification_slice_store_prio_tbl 的非透明 Definition 依赖它们           *)

(* ================================================================== *)
(* 第 2 节:通用 Znth Lemma                                            *)
(*                                                                    *)
(* 复制自 los_verify lib/sched.v:1144-1208,无修改。                   *)
(* 这些 Lemma 是 list 抽象的基石。                                    *)
(* ================================================================== *)

Lemma Zlength_replace_Znth_gen : forall {A} (l : list A) n a,
  n >= 0 -> Zlength (replace_Znth n a l) = Zlength l.
Proof.
  induction l;
  intros.
  - rewrite -> replace_Znth_nothing
      by (rewrite -> Zlength_nil; assumption).
    reflexivity.
  - destruct (Z.eq_dec n 0).
    + subst.
      reflexivity.
    + rewrite -> replace_Znth_cons by lia.
      rewrite -> Zlength_cons.
      rewrite -> IHl by lia.
      rewrite -> Zlength_cons.
      reflexivity.
Qed.

Lemma Znth_replace_Znth_eq_gen : forall {A} (l : list A) n a d,
  0 <= n < Zlength l -> Znth n (replace_Znth n a l) d = a.
Proof.
  induction l;
  intros.
  - rewrite -> Zlength_nil in H.
    lia.
  - destruct (Z.eq_dec n 0).
    + subst.
      reflexivity.
    + rewrite -> replace_Znth_cons by lia.
      rewrite -> Znth_cons by lia.
      apply IHl.
      rewrite -> Zlength_cons in H.
      lia.
Qed.

Lemma Znth_replace_Znth_neq_gen : forall {A} (l : list A) n m a d,
  n <> m ->
  0 <= n < Zlength l ->
  0 <= m < Zlength l ->
  Znth n (replace_Znth m a l) d = Znth n l d.
Proof.
  induction l;
  intros.
  - rewrite -> Zlength_nil in *.
    lia.
  - destruct (Z.eq_dec m 0);
    destruct (Z.eq_dec n 0);
    subst.
    + contradiction.
    + replace (replace_Znth 0 a0 (a :: l))
          with (a0 :: l)
          by reflexivity.
      rewrite -> Znth_cons by lia.
      rewrite -> Znth_cons by lia.
      reflexivity.
    + rewrite -> replace_Znth_cons by lia.
      reflexivity.
    + rewrite -> replace_Znth_cons by lia.
      rewrite -> Znth_cons by lia.
      rewrite -> Zlength_cons in H0.
      rewrite -> Zlength_cons in H1.
      rewrite -> IHl by lia.
      rewrite -> Znth_cons by lia.
      reflexivity.
Qed.

(* ================================================================== *)
(* 第 3 节:OSRdyTbl list 抽象                                         *)
(*                                                                    *)
(* C 声明:extern OS_PRIO OSRdyTbl[OS_RDY_TBL_SIZE];                   *)
(* 抽象层:list Z (8 个 OS_PRIO 值)                                    *)
(* ================================================================== *)

Definition osrdytbl_element_store (base : addr) (i : Z) (v : Z) : Assertion :=
  store_uchar (base + i * sizeof_OS_PRIO) v.

Definition store_osrdytbl (sg : StableGlobVars) (l : list Z) : Assertion :=
  store_array osrdytbl_element_store
              sg.(g_OSRdyTbl)
              OS_RDY_TBL_SIZE
              l.

Definition store_osrdytbl_missing_i (sg : StableGlobVars)
           (l : list Z) (i : Z) : Assertion :=
  store_array_missing_i_rec osrdytbl_element_store
                            sg.(g_OSRdyTbl)
                            i
                            0
                            OS_RDY_TBL_SIZE
                            l.

Definition osrdytbl_list_rel (sg : StableGlobVars)
           (tskSt : Glob_TaskAbstractState) (schedSt : SchedAbstractState)
           (l : list Z) : Prop :=
  Zlength l = OS_RDY_TBL_SIZE /\
  forall y, 0 <= y < OS_RDY_TBL_SIZE ->
    Znth y l 0 = encode_ready_tbl_at schedSt.(readyList) tskSt y.

Definition sched_ready_prio_snapshot_prop (sg : StableGlobVars)
  (tskSt : Glob_TaskAbstractState) (schedSt : SchedAbstractState)
  (rdyGrp : Z) (rdyTbl : list Z) (prioCur : Z) : Prop :=
  rdyGrp = encode_ready_grp schedSt.(readyList) tskSt /\
  osrdytbl_list_rel sg tskSt schedSt rdyTbl /\
  prioCur = match schedSt.(curSchedPrio) with Some p => p | None => 0xFF end.

(* range constraint for OSRdyTbl index *)
Definition osrdytbl_index_in_range (i : Z) : Prop :=
  0 <= i < OS_RDY_TBL_SIZE.

(* split Lemma:把整体 store 拆为"缺 i 位 + 第 i 位单元格" *)
(* 证明依赖 SimpleC.SL ArrayLibCore 的 store_array_split_to_missing_i *)
Lemma store_osrdytbl_split :
  forall sg l i,
    osrdytbl_index_in_range i ->
    Zlength l = OS_RDY_TBL_SIZE ->
    store_osrdytbl sg l |--
      (osrdytbl_element_store (sg.(g_OSRdyTbl)) i (Znth i l 0)) **
      store_osrdytbl_missing_i sg l i.
Proof.
  intros sg l i Hrange Hlen.
  unfold store_osrdytbl, store_osrdytbl_missing_i.
  apply store_array_split_to_missing_i.
  unfold osrdytbl_index_in_range in Hrange.
  assumption.
Qed.

(* merge Lemma:把"缺 i 位 + 新第 i 位值"合并为新整体 store *)
Lemma store_osrdytbl_merge :
  forall sg l i v,
    osrdytbl_index_in_range i ->
    Zlength l = OS_RDY_TBL_SIZE ->
    (osrdytbl_element_store (sg.(g_OSRdyTbl)) i v) **
    store_osrdytbl_missing_i sg l i
    |-- store_osrdytbl sg (replace_Znth i v l).
Proof.
  intros sg l i v Hrange Hlen.
  unfold store_osrdytbl, store_osrdytbl_missing_i.
  apply store_array_missing_i_merge_to_array.
  unfold osrdytbl_index_in_range in Hrange.
  assumption.
Qed.

(* ================================================================== *)
(* 第 4 节:OSTCBPrioTbl list 抽象                                     *)
(*                                                                    *)
(* C 声明:extern OS_TCB *OSTCBPrioTbl[OS_PRIO_TBL_SIZE];              *)
(* 抽象层:list addr (64 个 OS_TCB* 指针值)                            *)
(*                                                                    *)
(* 基础定义(priotbl_element_store / verification_slice_store_priotbl_list /               *)
(* verification_slice_store_priotbl_list_missing_i / sizeof_OSTCB_ptr /                   *)
(* verification_slice_prio_tbl_entry_to_addr / verification_slice_prioTbl_to_addrs)已下沉到 lib/task.v,      *)
(* 因为它们同时被 verification_slice_store_prio_tbl 的非透明 Definition 使用。             *)
(* 这里只保留本模块用的下标范围约束与 split/merge Lemma。             *)
(* ================================================================== *)

Definition priotbl_index_in_range (i : Z) : Prop :=
  0 <= i < OS_PRIO_TBL_SIZE.

Lemma verification_slice_store_priotbl_list_split :
  forall sg l i,
    priotbl_index_in_range i ->
    Zlength l = OS_PRIO_TBL_SIZE ->
    verification_slice_store_priotbl_list sg l |--
      (priotbl_element_store (sg.(g_OSTCBPrioTbl)) i (Znth i l 0)) **
      verification_slice_store_priotbl_list_missing_i sg l i.
Proof.
  intros sg l i Hrange Hlen.
  unfold verification_slice_store_priotbl_list, verification_slice_store_priotbl_list_missing_i.
  apply store_array_split_to_missing_i.
  unfold priotbl_index_in_range in Hrange.
  assumption.
Qed.

Lemma verification_slice_store_priotbl_list_merge :
  forall sg l i v,
    priotbl_index_in_range i ->
    Zlength l = OS_PRIO_TBL_SIZE ->
    (priotbl_element_store (sg.(g_OSTCBPrioTbl)) i v) **
    verification_slice_store_priotbl_list_missing_i sg l i
    |-- verification_slice_store_priotbl_list sg (replace_Znth i v l).
Proof.
  intros sg l i v Hrange Hlen.
  unfold verification_slice_store_priotbl_list, verification_slice_store_priotbl_list_missing_i.
  apply store_array_missing_i_merge_to_array.
  unfold priotbl_index_in_range in Hrange.
  assumption.
Qed.

(** Array-update arithmetic formerly local to TCBInit, shared by task
    reservation/publication and ready-row writes.  Spatial reasoning below
    remains QCP's PtrArray split/merge, not another array library. *)
Lemma map_Zrange_aux_update : forall n low p v (f : Z -> Z),
  0 <= p < Z.of_nat n ->
  map (fun q => if Z.eq_dec q (low + p) then v else f q) (Zrange_aux low n) =
  replace_Znth p v (map f (Zrange_aux low n)).
Proof.
  induction n as [|n IH]; intros low p v f Hp; [simpl in Hp; lia|].
  destruct (Z.eq_dec p 0) as [Hzero|Hpositive].
  - subst p; rewrite Z.add_0_r; cbn [Zrange_aux map replace_Znth replace_nth].
    destruct (Z.eq_dec low low); [|contradiction].
    cbn [Z.to_nat].
    f_equal; apply map_ext_in; intros q Hin.
    apply In_Zrange_aux in Hin.
    destruct (Z.eq_dec q low); [lia|reflexivity].
  - cbn [Zrange_aux map].
    destruct (Z.eq_dec low (low + p)); [lia|].
    rewrite replace_Znth_cons by lia; f_equal.
    replace (low + p) with ((low + 1) + (p - 1)) by lia.
    apply IH; lia.
Qed.

Lemma map_Zrange_update : forall count p v (f : Z -> Z),
  0 <= p < count ->
  map (fun q => if Z.eq_dec q p then v else f q) (Zrange 0 count) =
  replace_Znth p v (map f (Zrange 0 count)).
Proof.
  intros; unfold Zrange.
  pose proof (map_Zrange_aux_update (Z.to_nat (count - 0))
    0 p v f ltac:(rewrite Z2Nat.id; lia)) as Hmap.
  rewrite Z.add_0_l in Hmap; exact Hmap.
Qed.

Definition store_prio_tbl_missing_i (sg : StableGlobVars)
  (table : Priority -> PrioTblEntry) (p : Priority) : Assertion :=
  PtrArray.missing_i sg.(g_OSTCBPrioTbl) p 0 64
    (map (fun q => prio_tbl_entry_to_addr sg (table q)) (Zrange 0 64)).

Lemma store_prio_tbl_split_cell : forall sg table p,
  0 <= p < 64 -> store_prio_tbl sg table |--
    (sg.(g_OSTCBPrioTbl) + p * sizeof(PTR)) # Ptr |-> prio_tbl_entry_to_addr sg (table p) **
    store_prio_tbl_missing_i sg table p.
Proof.
  intros sg table p Hp; unfold store_prio_tbl, store_prio_tbl_missing_i.
  rewrite <- (prio_table_values_Znth sg table p Hp).
  apply PtrArray.full_split_to_missing_i; exact Hp.
Qed.

Lemma store_prio_tbl_merge_updated_cell : forall sg table p entry,
  0 <= p < 64 ->
  (sg.(g_OSTCBPrioTbl) + p * sizeof(PTR)) # Ptr |-> prio_tbl_entry_to_addr sg entry **
    store_prio_tbl_missing_i sg table p |-- store_prio_tbl sg (update_prio_tbl table p entry).
Proof.
  intros sg table p entry Hp; unfold store_prio_tbl_missing_i, store_prio_tbl.
  assert (Hmap : map
    (fun q => prio_tbl_entry_to_addr sg (update_prio_tbl table p entry q)) (Zrange 0 64) =
    replace_Znth p (prio_tbl_entry_to_addr sg entry)
      (map (fun q => prio_tbl_entry_to_addr sg (table q)) (Zrange 0 64))).
  { transitivity (map (fun q => if Z.eq_dec q p
      then prio_tbl_entry_to_addr sg entry
      else prio_tbl_entry_to_addr sg (table q)) (Zrange 0 64)).
    - apply map_ext; intro q; unfold update_prio_tbl; destruct Z.eq_dec; reflexivity.
    - exact (map_Zrange_update 64 p (prio_tbl_entry_to_addr sg entry)
        (fun q => prio_tbl_entry_to_addr sg (table q)) Hp). }
  rewrite Hmap; apply PtrArray.missing_i_merge_to_full; exact Hp.
Qed.

Lemma store_prio_tbl_merge_cell : forall sg table p,
  0 <= p < 64 ->
  (sg.(g_OSTCBPrioTbl) + p * sizeof(PTR)) # Ptr |-> prio_tbl_entry_to_addr sg (table p) **
    store_prio_tbl_missing_i sg table p |-- store_prio_tbl sg table.
Proof.
  intros sg table p Hp; eapply derivable1_trans;
    [apply store_prio_tbl_merge_updated_cell; exact Hp|].
  rewrite update_prio_tbl_put_back; reflexivity.
Qed.

(* ================================================================== *)
(* 第 5 节:OSEventTbl list 抽象 (per-event)                           *)
(*                                                                    *)
(* C 声明:typedef struct os_event { ... OS_PRIO OSEventTbl[8]; }      *)
(* 偏移:OSEventTbl_off = 12 (相对 OS_EVENT 基址)                     *)
(* 抽象层:list Z (8 个 OS_PRIO 值,per-event)                          *)
(* ================================================================== *)

Definition oseventtbl_element_store (base : addr) (i : Z) (v : Z) : Assertion :=
  store_uchar (base + i * sizeof_OS_PRIO) v.

Definition store_oseventtbl (sg : StableGlobVars)
           (event_base : addr) (l : list Z) : Assertion :=
  store_array oseventtbl_element_store
              (event_base + OSEventTbl_off)
              OS_EVENT_TBL_SIZE
              l.

Definition store_oseventtbl_missing_i (sg : StableGlobVars)
           (event_base : addr) (l : list Z) (i : Z) : Assertion :=
  store_array_missing_i_rec oseventtbl_element_store
                            (event_base + OSEventTbl_off)
                            i
                            0
                            OS_EVENT_TBL_SIZE
                            l.

Definition store_osprio_array (base : addr) (l : list Z) : Assertion :=
  store_array oseventtbl_element_store base OS_EVENT_TBL_SIZE l.

Definition store_osprio_array_missing_i
  (base : addr) (l : list Z) (i : Z) : Assertion :=
  store_array_missing_i_rec oseventtbl_element_store
                            base i 0 OS_EVENT_TBL_SIZE l.

Definition copy_prefix_list {A : Type}
  (src dst : list A) (n : Z) : list A :=
  firstn (Z.to_nat n) src ++ skipn (Z.to_nat n) dst.

Definition copied_prefix_rel {A : Type}
  (src dst_before dst_after : list A) (n : Z) : Prop :=
  0 <= n /\
  Zlength src = Zlength dst_before /\
  dst_after = copy_prefix_list src dst_before n.

(** Shared properties of the existing prefix representation.  In
    particular, Query loops can use option-valued destination arrays so
    that their untouched suffix need not be initialized.  Physical
    split/updated-merge remains the responsibility of QCP ArrayLib. *)
Lemma copy_prefix_list_length : forall (A : Type) (src dst : list A) i,
  Zlength src = Zlength dst -> Zlength (copy_prefix_list src dst i) = Zlength src.
Proof.
  intros A src dst i Hlength; unfold copy_prefix_list.
  rewrite !Zlength_correct in *.
  assert (Hsame : List.length src = List.length dst) by lia.
  rewrite length_app, firstn_length, skipn_length, Hsame.
  destruct (le_dec (Z.to_nat i) (List.length dst)).
  - rewrite Nat.min_l by lia; f_equal; lia.
  - rewrite Nat.min_r by lia; f_equal; lia.
Qed.

Lemma copy_prefix_list_step : forall (A : Type) (src dst : list A) i d,
  Zlength src = Zlength dst -> 0 <= i < Zlength src ->
  replace_Znth i (Znth i src d) (copy_prefix_list src dst i) =
  copy_prefix_list src dst (i + 1).
Proof.
  intros A src dst i d Hlength Hi; unfold copy_prefix_list, Znth, replace_Znth.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  assert (Hstep : forall (n : nat) (xs ys : list A),
    List.length xs = List.length ys -> (n < List.length xs)%nat ->
    replace_nth n (firstn n xs ++ skipn n ys) (nth n xs d) =
    firstn (S n) xs ++ skipn (S n) ys).
  { induction n as [|n IH]; intros xs ys Hsame Hbound;
      destruct xs as [|x xs]; destruct ys as [|y ys]; simpl in *; try lia.
    - reflexivity.
    - f_equal; apply IH; lia. }
  apply Hstep; rewrite !Zlength_correct in *; lia.
Qed.

Lemma copy_prefix_list_complete : forall (A : Type) (src dst : list A) i,
  Zlength src = Zlength dst -> Zlength src <= i -> copy_prefix_list src dst i = src.
Proof.
  intros A src dst i Hlength Hdone; unfold copy_prefix_list.
  rewrite !Zlength_correct in *.
  rewrite firstn_all2 by lia; rewrite skipn_all2 by lia; apply app_nil_r.
Qed.

Definition oseventtbl_list_rel (sg : StableGlobVars)
           (tskSt : Glob_TaskAbstractState) (e : OSEventAbstractState)
           (l : list Z) : Prop :=
  Zlength l = OS_EVENT_TBL_SIZE /\
  forall y, 0 <= y < OS_EVENT_TBL_SIZE ->
    Znth y l 0 = encode_event_wait_tbl_at e.(waitList) tskSt y.

Definition event_tbl_addr_list_rel (sg : StableGlobVars)
           (tskSt : Glob_TaskAbstractState) (evSt : Glob_EventAbstractState)
           (event_base : addr) (l : list Z) : Prop :=
  exists eid e,
    event_base = event_addr sg eid /\
    evSt.(inUsedEventStates) eid = Some e /\
    oseventtbl_list_rel sg tskSt e l.

Definition oseventtbl_index_in_range (i : Z) : Prop :=
  0 <= i < OS_EVENT_TBL_SIZE.

Lemma store_oseventtbl_split :
  forall sg event_base l i,
    oseventtbl_index_in_range i ->
    Zlength l = OS_EVENT_TBL_SIZE ->
    store_oseventtbl sg event_base l |--
      (oseventtbl_element_store (event_base + OSEventTbl_off) i (Znth i l 0)) **
      store_oseventtbl_missing_i sg event_base l i.
Proof.
  intros sg event_base l i Hrange Hlen.
  unfold store_oseventtbl, store_oseventtbl_missing_i.
  apply store_array_split_to_missing_i.
  unfold oseventtbl_index_in_range in Hrange.
  assumption.
Qed.

Lemma store_oseventtbl_merge :
  forall sg event_base l i v,
    oseventtbl_index_in_range i ->
    Zlength l = OS_EVENT_TBL_SIZE ->
    (oseventtbl_element_store (event_base + OSEventTbl_off) i v) **
    store_oseventtbl_missing_i sg event_base l i
    |-- store_oseventtbl sg event_base (replace_Znth i v l).
Proof.
  intros sg event_base l i v Hrange Hlen.
  unfold store_oseventtbl, store_oseventtbl_missing_i.
  apply store_array_missing_i_merge_to_array.
  unfold oseventtbl_index_in_range in Hrange.
  assumption.
Qed.
