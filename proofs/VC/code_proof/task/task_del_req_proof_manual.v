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
From Ucos2Verify.VC.code.task Require Import task_del_req_goal.
From Ucos2Verify.VC.code.task Require Import task_del_req_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_del_req_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskDelReq_entail_wit_1 : OSTaskDelReq_entail_wit_1.
Proof.
  unfold OSTaskDelReq_entail_wit_1; left; intros.
  pureIntros_without_rename.
  assert (Hrequest : request = 255) by lia.
  match goal with
  | Hadmit : task_del_req_admission critical sg invocation request before |- _ =>
      destruct (Hadmit Hrequest acquired_2 PreH1) as [tid [task Hcurrent]]
  end.
  match goal with
  | Hvalid : UCOS2_state_inv sg before |- _ =>
      pose proof (proj1 (critical_region_interval_transports_resources
        critical sg invocation before acquired_2 PreH1 Hvalid)) as Hacquired
  end.
  match goal with
  | Haddr : task_del_req_addresses sg _ _ |- _ =>
      pose proof Haddr as Hparts; destruct Hparts as [Htable [Hcur Hbase]]
  end.
  Exists tid task acquired_2.
  sep_apply_l_atomic (task_del_req_split_self sg acquired_2 tid task Hcurrent).
  cbn [tcb_field_address].
  rewrite Hcur in *; rewrite PreH7; entailer!.
  apply derivable1s_emp_sepcon_unfold; entailer!.
Qed.

Lemma proof_of_OSTaskDelReq_entail_wit_2 : OSTaskDelReq_entail_wit_2.
Proof.
  unfold OSTaskDelReq_entail_wit_2; left; intros.
  pureIntros_without_rename.
  match goal with
  | Haddr : task_del_req_addresses sg _ _ |- _ =>
      pose proof Haddr as Hparts; destruct Hparts as [Htable [Hcur Hbase]]
  end.
  assert (Hstep : task_del_req_step request acquired_2
    (encode_task_delete_request (delReq task)) acquired_2).
  { eapply TaskDelReqSelf; eassumption. }
  Exists acquired_2.
  rewrite Hcur in *.
  match goal with
  | Hvalid : UCOS2_state_inv sg acquired_2,
    Hcurrent : task_del_req_current acquired_2 tid task |- _ =>
      pose proof (task_del_req_merge_self sg acquired_2 tid task Hvalid Hcurrent) as Hmerge
  end.
  cbn [tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  asrt_simpl_pure.
  repeat match goal with
  | |- _ |-- “ ?P ” && _ =>
      apply derivable1s_coq_prop_andp_r; [|assumption]
  end.
  cancel (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2).
  cancel (UCOS2_inv sg acquired_2).
  repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskDelReq_entail_wit_3 : OSTaskDelReq_entail_wit_3.
Proof.
  unfold OSTaskDelReq_entail_wit_3; left; intros.
  pureIntros_without_rename.
  match goal with
  | Hvalid : UCOS2_state_inv sg before |- _ =>
      sep_apply_l_atomic (critical_region_interval_open_invariant
        critical sg invocation before acquired_2 PreH1 Hvalid)
  end.
  sep_apply_l_atomic (task_del_req_split_table sg acquired_2 request ltac:(lia)).
  pureIntros_without_rename.
  match goal with
  | Haddr : task_del_req_addresses sg _ _ |- _ =>
      pose proof Haddr as Hparts; destruct Hparts as [Htable [Hcur Hbase]]
  end.
  Exists acquired_2; rewrite Htable in *; rewrite PreH6; entailer!.
  repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskDelReq_entail_wit_4 : OSTaskDelReq_entail_wit_4.
Proof.
  unfold OSTaskDelReq_entail_wit_4; left; intros.
  pureIntros_without_rename.
  match goal with
  | Haddr : task_del_req_addresses sg _ _ |- _ =>
      pose proof Haddr as Hparts; destruct Hparts as [Htable [Hcur Hbase]]
  end.
  Exists acquired; rewrite Htable in *.
  match goal with
  | Hvalid : UCOS2_state_inv sg acquired |- _ =>
      sep_apply_l_atomic (task_del_req_merge_table sg acquired request ltac:(lia) Hvalid)
  end.
  entailer!.
Qed.

Lemma proof_of_OSTaskDelReq_entail_wit_5 : OSTaskDelReq_entail_wit_5.
Proof.
  unfold OSTaskDelReq_entail_wit_5; left; intros.
  pureIntros_without_rename.
  assert (Hfree : prioTbl (TskState acquired_2) request = PTFree).
  { match goal with
    | Hvalid : UCOS2_state_inv sg acquired_2,
      Haddr : task_del_req_addresses sg _ _ |- _ =>
        destruct (task_del_req_table_classify sg acquired_2 request _ _
          Hvalid Haddr ltac:(lia)) as
          [[Hnull Hentry]|[[Hreserved Hentry]|[tid [task [Hentry [Hlookup [Hpointer Hbound]]]]]]]
    end; try assumption; lia. }
  assert (Hstep : task_del_req_step request acquired_2 67 acquired_2).
  { apply TaskDelReqFree; [lia|exact Hfree]. }
  Exists acquired_2.
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "ptcb" )) ptcb).
  asrt_simpl_pure.
  repeat match goal with
  | |- _ |-- “ ?P ” && _ =>
      apply derivable1s_coq_prop_andp_r; [|assumption]
  end.
  cancel (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2).
  cancel (UCOS2_inv sg acquired_2).
  cancel ((&( "ptcb" )) # Ptr |->_).
  repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskDelReq_entail_wit_6 : OSTaskDelReq_entail_wit_6.
Proof.
  unfold OSTaskDelReq_entail_wit_6; left; intros.
  pureIntros_without_rename.
  assert (Hreserved : prioTbl (TskState acquired_2) request = PTReserved).
  { match goal with
    | Hvalid : UCOS2_state_inv sg acquired_2,
      Haddr : task_del_req_addresses sg _ _ |- _ =>
        destruct (task_del_req_table_classify sg acquired_2 request _ _
          Hvalid Haddr ltac:(lia)) as
          [[Hnull Hentry]|[[Hreserved Hentry]|[tid [task [Hentry [Hlookup [Hpointer Hbound]]]]]]]
    end; try assumption; lia. }
  assert (Hstep : task_del_req_step request acquired_2 61 acquired_2).
  { apply TaskDelReqReserved; [lia|exact Hreserved]. }
  Exists acquired_2.
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "ptcb" )) ptcb).
  asrt_simpl_pure.
  repeat match goal with
  | |- _ |-- “ ?P ” && _ =>
      apply derivable1s_coq_prop_andp_r; [|assumption]
  end.
  cancel (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2).
  cancel (UCOS2_inv sg acquired_2).
  cancel ((&( "ptcb" )) # Ptr |->_).
  repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskDelReq_entail_wit_7 : OSTaskDelReq_entail_wit_7.
Proof.
  unfold OSTaskDelReq_entail_wit_7; left; intros.
  pureIntros_without_rename.
  match goal with
  | Hvalid : UCOS2_state_inv sg acquired_2,
    Haddr : task_del_req_addresses sg _ _ |- _ =>
      destruct (task_del_req_table_classify sg acquired_2 request _ _
        Hvalid Haddr ltac:(lia)) as
        [[Hnull Hentry]|[[Hreserved Hentry]|[tid [task [Hentry [Hlookup [Hpointer Hbound]]]]]]]
  end; try lia.
  assert (Hptcb : ptcb = task_slot_addr sg tid) by lia.
  assert (Htarget : task_del_req_target acquired_2 request tid task).
  { split; assumption. }
  Exists task acquired_2 tid; rewrite Hptcb.
  unfold UCOS2_inv.
  pureIntros_without_rename.
  sep_apply_l_atomic (task_del_req_split_field sg acquired_2 tid task Hlookup).
  cbn [tcb_field_address]; entailer!.
Qed.

Lemma proof_of_OSTaskDelReq_entail_wit_8 : OSTaskDelReq_entail_wit_8.
Proof.
  unfold OSTaskDelReq_entail_wit_8; left; intros.
  pureIntros_without_rename.
  match goal with
  | Htarget : task_del_req_target acquired_2 request tid task |- _ =>
      destruct Htarget as [Hentry Hlookup]
  end.
  assert (Hstep : task_del_req_step request acquired_2 0
    (task_del_req_state acquired_2 tid task)).
  { apply TaskDelReqSet; [lia|exact Hentry|exact Hlookup]. }
  Exists (task_del_req_state acquired_2 tid task) acquired_2.
  sep_apply_l_atomic (store_ptr_undef_store_ptr (&( "ptcb" )) ptcb).
  rewrite PreH3.
  match goal with
  | Hvalid : UCOS2_state_inv sg acquired_2 |- _ =>
      pose proof (task_del_req_merge_updated_field sg acquired_2 tid task Hvalid Hlookup) as Hmerge
  end.
  cbn [tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge.
  asrt_simpl_pure.
  repeat match goal with
  | |- _ |-- “ ?P ” && _ =>
      apply derivable1s_coq_prop_andp_r; [|assumption]
  end.
  cancel (critical_region_masked platform critical sg invocation origin cpu_sr acquired_2).
  cancel (UCOS2_inv sg (task_del_req_state acquired_2 tid task)).
  cancel ((&( "ptcb" )) # Ptr |->_).
  repeat apply derivable1s_emp_sepcon_unfold; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTaskDelReq_return_wit_1 : OSTaskDelReq_return_wit_1.
Proof.
  pre_process.
  match goal with H : interrupt_saved_value _ _ |- _ =>
    destruct H as [_ Hmask]; rewrite Hmask
  end.
  unfold task_del_req_closed.
  Exists current_2.
  entailer!; try solve [apply derivable1_truep_intros; exact I].
  apply task_del_req_safe_return; [|assumption].
  unfold task_del_req_result; right; split; [right; lia|].
  exists acquired, released; auto.
Qed.

Lemma proof_of_OSTaskDelReq_return_wit_2 : OSTaskDelReq_return_wit_2.
Proof.
  pre_process.
  match goal with H : interrupt_saved_value _ _ |- _ =>
    destruct H as [_ Hmask]; rewrite Hmask
  end.
  unfold task_del_req_closed.
  Exists current_2.
  entailer!; try solve [apply derivable1_truep_intros; exact I].
  apply task_del_req_safe_return; [|assumption].
  unfold task_del_req_result; right; split; [right; lia|].
  exists acquired, acquired; auto.
Qed.

Lemma proof_of_OSTaskDelReq_return_wit_3 : OSTaskDelReq_return_wit_3.
Proof.
  pre_process.
  match goal with H : interrupt_saved_value _ _ |- _ =>
    destruct H as [_ Hmask]; rewrite Hmask
  end.
  unfold task_del_req_closed.
  Exists current_2.
  entailer!; try solve [apply derivable1_truep_intros; exact I].
  apply task_del_req_safe_return; [|assumption].
  unfold task_del_req_result; right; split; [right; lia|].
  exists acquired, acquired; auto.
Qed.

Lemma proof_of_OSTaskDelReq_return_wit_4 : OSTaskDelReq_return_wit_4.
Proof.
  pre_process.
  match goal with H : interrupt_saved_value _ _ |- _ =>
    destruct H as [_ Hmask]; rewrite Hmask
  end.
  unfold task_del_req_closed.
  Exists current_2.
  entailer!; try solve [apply derivable1_truep_intros; exact I].
  apply task_del_req_safe_return; [|assumption].
  unfold task_del_req_result; right; split; [left; assumption|].
  exists acquired, acquired; auto.
Qed.

Lemma proof_of_OSTaskDelReq_return_wit_5 : OSTaskDelReq_return_wit_5.
Proof.
  pre_process.
  Exists before.
  cancel.
  apply derivable1s_coq_prop_r.
  apply task_del_req_safe_return; [|assumption].
  unfold task_del_req_result; left; split; [right; lia|].
  split; [apply TaskDelReqInvalid; lia|reflexivity].
Qed.

Lemma proof_of_OSTaskDelReq_return_wit_6 : OSTaskDelReq_return_wit_6.
Proof.
  pre_process.
  Exists before.
  cancel.
  apply derivable1s_coq_prop_r.
  apply task_del_req_safe_return; [|assumption].
  unfold task_del_req_result; left; split; [left; lia|].
  split; [apply TaskDelReqIdle; lia|reflexivity].
Qed.

Lemma proof_of_OSTaskDelReq_which_implies_wit_1 : OSTaskDelReq_which_implies_wit_1.
Proof.
  unfold OSTaskDelReq_which_implies_wit_1; left; intros.
  unfold task_del_req_closed; entailer!.
Qed.

Lemma proof_of_OSTaskDelReq_which_implies_wit_2 : OSTaskDelReq_which_implies_wit_2.
Proof.
  unfold OSTaskDelReq_which_implies_wit_2; left; intros.
  unfold task_del_req_closed; entailer!.
Qed.

