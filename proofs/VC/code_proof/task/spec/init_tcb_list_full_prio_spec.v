Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_full_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Lemma map_const_Zrange_aux__full_prio : forall low n (x : Z),
  map (fun _ : Z => x) (Zrange_aux low n) = repeat x n.
Proof.
  intros low n x.
  revert low.
  revert x.
  induction n as [|n IH].
  - intros; cbn; reflexivity.
  - intros low x; cbn. rewrite IH; reflexivity.
Qed.

(** PTFree is the null pointer entry.  This is only the priority-table
    resource reconstruction from MemClr's byte postcondition, not the
    OS_InitTCBList control-flow or its complete global postcondition. *)
Lemma zero_bytes_to_full_prio_table : forall sg,
  init_tcb_list_full_layout sg ->
  UCharArray.full sg.(g_OSTCBPrioTbl) (4 * 64)
    (repeat_Z 0 (4 * 64)) |--
  store_prio_tbl sg (fun _ => PTFree).
Proof.
  intros sg Hlayout.
  destruct Hlayout as [_ [_ [_ [_ [_ [_ [_ Hmod]]]]]]].
  cbn [store_prio_tbl prio_tbl_entry_to_addr].
  change (UCharArray.full sg.(g_OSTCBPrioTbl) (4 * Z.of_nat 64)
    (repeat_Z 0 (4 * Z.of_nat 64)) |--
    PtrArray.full sg.(g_OSTCBPrioTbl) (Z.of_nat 64)
      (map (fun _ : Z => 0) (Zrange_aux 0 64))).
  pose proof (map_const_Zrange_aux__full_prio 0 64 0) as Hmap.
  rewrite Hmap.
  apply zero_bytes_to_ptr_array__tcb_zero_byte_reconstruction.
  exact Hmod.
Qed.
