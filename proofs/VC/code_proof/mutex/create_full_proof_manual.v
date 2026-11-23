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
From Ucos2Verify.VC.code.mutex Require Import create_full_goal.
From Ucos2Verify.VC.code.mutex Require Import create_full_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.mutex_create_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexCreate_full_safety_wit_30_disabled_nonempty : OSMutexCreate_full_safety_wit_30_disabled_nonempty.
Proof.
  pre_process.
  subst prio_pre.
  split_pures.
  all: dump_pre_spatial.
  all: vm_compute.
  all: discriminate.
Qed.

Lemma proof_of_OSMutexCreate_full_safety_wit_31_enabled_nonempty : OSMutexCreate_full_safety_wit_31_enabled_nonempty.
Proof.
  pre_process.
  subst prio_pre.
  assert (Hbits :
    signed_last_nbits (prio_in * 2 ^ 8) 32 = prio_in * 2 ^ 8).
  {
    apply signed_last_nbits_eq.
    - lia.
    - replace (2 ^ (32 - 1)) with 2147483648 by reflexivity.
      replace (2 ^ 8) with 256 by reflexivity.
      lia.
  }
  rewrite Hbits.
  split_pures.
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_OSMutexCreate_full_entail_wit_1_disabled_empty : OSMutexCreate_full_entail_wit_1_disabled_empty.
Proof.
  pre_process.
  Exists ls1_3.
  entailer!.
  - rewrite PreH11. entailer!.
  - rewrite <- PreH8. exact PreH16.
Qed.

Lemma proof_of_OSMutexCreate_full_entail_wit_2_disabled_nonempty : OSMutexCreate_full_entail_wit_2_disabled_nonempty.
Proof.
  pre_process.
  Exists ls1_3.
  entailer!.
  - rewrite PreH11. entailer!.
  - rewrite <- PreH8. exact PreH16.
Qed.

Lemma proof_of_OSMutexCreate_full_entail_wit_3_enabled_nonempty : OSMutexCreate_full_entail_wit_3_enabled_nonempty.
Proof.
  pre_process.
  Exists ls1_3.
  entailer!.
  - rewrite PreH15. entailer!.
  - rewrite <- PreH12. exact PreH20.
Qed.

Lemma proof_of_OSMutexCreate_full_entail_wit_4_enabled_empty : OSMutexCreate_full_entail_wit_4_enabled_empty.
Proof.
  pre_process.
  Exists ls1_3.
  entailer!.
  - rewrite PreH15. entailer!.
  - rewrite <- PreH12. exact PreH20.
Qed.

Lemma proof_of_OSMutexCreate_full_entail_wit_7_enabled_nonempty : OSMutexCreate_full_entail_wit_7_enabled_nonempty.
Proof.
  pre_process.
  Exists perr_in ls_post_3.
  entailer!.
  - unfold event_free_head_snapshot_prop in H10.
    tauto.
  - unfold event_free_head_snapshot_prop in H10.
    tauto.
  - pose proof H11 as Hsuccess.
    unfold mutex_create_success_transition_prop in Hsuccess.
    destruct Hsuccess as
      [Hfree [Hunref [Hpost [Hatomic Hcrit]]]].
    assert (Hpcp : prio_in <> sg.(osPrioMutexCeilDis)).
    {
      pose proof H9 as Hstable.
      unfold valid_stable_glob_vars in Hstable.
      destruct Hstable as
        [_ [_ [_ [_ [_ [_ [_ [_ [Hdisabled _]]]]]]]]].
      rewrite Hdisabled.
      exact PreH13.
    }
    assert (Hslot : ls0.(TskState).(prioTbl) prio_in = PTFree).
    {
      eapply atomic_mutex_create_enabled_slot_free__critical_state_threading.
      - exact Hpcp.
      - exact Hatomic.
    }
    assert (Hsem : OSMutexCreate_sem sg prio_in ls0
      (OS_ERR_NONE, Some eid) ls_post_3).
    {
      unfold OSMutexCreate_sem.
      right; right; right; right; right; right.
      exists eid.
      simpl.
      repeat split.
      - rewrite <- PreH8. exact PreH11.
      - right.
        destruct H8 as [Hdisabled | Hrange].
        + contradiction.
        + repeat split; tauto.
      - exact Hatomic.
    }
    eapply (mutex_accept_safe_return__restore_and_returns
      (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_in)
      (observe_mutex_create_ptr sg) ls0 ls_post_3
      (OS_ERR_NONE, Some eid) freelist_in X).
    + exact Hsem.
    + intros P.
      unfold observe_mutex_create_ptr.
      simpl.
      split.
      * unfold event_free_head_snapshot_prop in H10. tauto.
      * reflexivity.
    + exact PreH4.
Qed.

Lemma proof_of_OSMutexCreate_full_entail_wit_8_disabled_nonempty : OSMutexCreate_full_entail_wit_8_disabled_nonempty.
Proof.
  pre_process.
  assert (Hreturn : safeExec (LastSeen ls_post_3) (return freelist_in) X).
  {
    pose proof H11 as Htransition.
    unfold mutex_create_success_transition_prop in Htransition.
    destruct Htransition as
      [Hunused [Hunreferenced [Hstate [Hatomic Hcrit]]]].
    eapply (mutex_accept_safe_return__restore_and_returns
      (OSErrCode * option EventID) Z
      (OSMutexCreate_sem sg prio_in) (observe_mutex_create_ptr sg)
      ls0 ls_post_3 (OS_ERR_NONE, Some eid) freelist_in X).
    - unfold OSMutexCreate_sem.
      simpl.
      do 6 right.
      exists eid.
      split; [lia |].
      split.
      + pose proof H5 as Hslot.
        destruct Hslot as [Hdisabled | [Henabled _]].
        * left; exact Hdisabled.
        * right.
          split; [exact Henabled |].
          pose proof H8 as Hvalid.
          destruct Hvalid as [Hcontra | [_ Hbelow]].
          { contradiction. }
          split; [exact Hbelow |].
          pose proof Hatomic as Hatomic_copy.
          unfold atomic_mutex_create in Hatomic_copy.
          destruct Hatomic_copy as
            (ls_alloc & eid0 & ls_init & ls_reserve &
             Halloc & Hinit & Hreserve & Hoid & Hfinal).
          assert (Heqb : Z.eqb prio_in sg.(osPrioMutexCeilDis) = false).
          { apply Z.eqb_neq. exact Henabled. }
          rewrite Heqb in Hreserve.
          unfold atomic_priotbl_reserve in Hreserve.
          destruct Hreserve as [Hfree _].
          unfold atomic_event_alloc in Halloc.
          destruct Halloc as
            (free_eid & free_tail & Hfree_ids & Heid0 & Hls_alloc).
          subst ls_alloc.
          unfold atomic_mutex_init in Hinit.
          destruct Hinit as
            (e1 & e2 & m & He1 & He1type & Hm & He2 & Hls_init).
          subst ls_init.
          unfold update_event_field, replace_EventS in Hfree.
          simpl in Hfree.
          exact Hfree.
      + split; [exact Hatomic |].
        split; reflexivity.
    - intros P.
      pose proof H10 as Hsnapshot.
      unfold event_free_head_snapshot_prop in Hsnapshot.
      destruct Hsnapshot as [_ [Hhead _]].
      unfold observe_mutex_create_ptr.
      simpl.
      split; [exact Hhead | reflexivity].
    - exact PreH4.
  }
  Exists perr_in ls_post_3.
  entailer!.
  - unfold event_free_head_snapshot_prop in H10. tauto.
  - unfold event_free_head_snapshot_prop in H10. tauto.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_1_enabled_nonempty : OSMutexCreate_full_return_wit_1_enabled_nonempty.
Proof.
  aggressive_pre_process.
  Exists ls_post_3.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls_post_3).
    cancel (UCOS2_Verify_inv sg ls_post_3).
    entailer!.
  - split_pures.
    + dump_pre_spatial. exact PreH1.
    + dump_pre_spatial. exact PreH35.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; right; right; right.
      split; [exact H7 |].
      split; [exact PreH7 |].
      split; [exact H4 |].
      split; [exact PreH8 |].
      split; [exact PreH9 |].
      split; [exact PreH9 |].
      split; [reflexivity |].
      exact H10.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_2_disabled_nonempty : OSMutexCreate_full_return_wit_2_disabled_nonempty.
Proof.
  aggressive_pre_process.
  Exists ls_post_3.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls_post_3).
    cancel (UCOS2_Verify_inv sg ls_post_3).
    entailer!.
  - entailer!.
    unfold mutex_create_result_prop.
    do 4 right.
    split; [exact H7 |].
    split; [exact PreH7 |].
    split; [exact H4 |].
    split; [exact PreH8 |].
    split; [exact PreH9 |].
    split; [exact PreH9 |].
    split; [reflexivity |].
    exact H10.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_3_disabled_empty : OSMutexCreate_full_return_wit_3_disabled_empty.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  pose proof H1 as Hfree_shape.
  assert (Hunused_empty :
    (EventState ls0).(unUsedEventStates) = (@nil EventID)).
  {
    unfold mutex_create_free_snapshot_prop in Hfree_shape.
    destruct Hfree_shape as [[_ Hempty] | [Hnonzero _]].
    - unfold event_free_list_exact_prop in Hempty.
      exact Hempty.
    - exfalso. apply Hnonzero. exact PreH39.
  }
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_PEVENT_NULL, None) ls0).
      {
        unfold OSMutexCreate_sem.
        right; right; right; right; right; left.
        split; [rewrite Hdisabled; exact PreH29 |].
        split; [rewrite <- PreH35; exact PreH27 |].
        split; [exact Hunused_empty |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_PEVENT_NULL, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH38.
    + dump_pre_spatial. exact PreH30.
    + dump_pre_spatial. exact PreH34.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; right; right; left.
      split; [exact H3 |].
      split; [exact PreH27 |].
      split.
      * left. rewrite Hdisabled. reflexivity.
      * split; [exact PreH39 |].
        repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_4_enabled_empty : OSMutexCreate_full_return_wit_4_enabled_empty.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  pose proof H1 as Hfree_shape.
  assert (Hunused_empty :
    (EventState ls0).(unUsedEventStates) = (@nil EventID)).
  {
    unfold mutex_create_free_snapshot_prop in Hfree_shape.
    destruct Hfree_shape as [[_ Hempty] | [Hnonzero _]].
    - unfold event_free_list_exact_prop in Hempty.
      exact Hempty.
    - exfalso. apply Hnonzero. exact PreH43.
  }
  assert (Hsem : exists sem_err,
    OSMutexCreate_sem sg prio_pre ls0 (sem_err, None) ls0).
  {
    destruct ((TskState ls0).(prioTbl) prio_pre) eqn:Hslot.
    - exists OS_ERR_PEVENT_NULL.
      unfold OSMutexCreate_sem.
      right; right; right; left.
      split; [rewrite Hdisabled; exact PreH33 |].
      split; [rewrite Hlowest; exact PreH32 |].
      split; [rewrite <- PreH39; exact PreH30 |].
      split; [exact Hslot |].
      split; [exact Hunused_empty |].
      repeat split; reflexivity.
    - exists OS_ERR_PRIO_EXIST.
      unfold OSMutexCreate_sem.
      right; right; left.
      split; [rewrite Hdisabled; exact PreH33 |].
      split; [rewrite Hlowest; exact PreH32 |].
      split; [rewrite <- PreH39; exact PreH30 |].
      split; [rewrite Hslot; discriminate |].
      repeat split; reflexivity.
    - exists OS_ERR_PRIO_EXIST.
      unfold OSMutexCreate_sem.
      right; right; left.
      split; [rewrite Hdisabled; exact PreH33 |].
      split; [rewrite Hlowest; exact PreH32 |].
      split; [rewrite <- PreH39; exact PreH30 |].
      split; [rewrite Hslot; discriminate |].
      repeat split; reflexivity.
  }
  destruct Hsem as [sem_err Hsem].
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (sem_err, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH42.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH38.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; right; right; left.
      split; [exact H3 |].
      split; [exact PreH30 |].
      split.
      * right. split; [rewrite Hdisabled; exact PreH33 | exact PreH26].
      * split; [exact PreH43 |].
        repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_5 : OSMutexCreate_full_return_wit_5.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  pose proof H5 as Hrel_shape.
  unfold prio_tbl_list_rel in Hrel_shape.
  destruct Hrel_shape as [_ Hnth].
  specialize (Hnth prio_pre ltac:(unfold OS_PRIO_TBL_SIZE; lia)).
  assert (Hslot_nonfree :
    (TskState ls0).(prioTbl) prio_pre <> PTFree) by
    (intro Hfree; apply PreH2;
     transitivity
       (prio_tbl_entry_to_addr sg ((TskState ls0).(prioTbl) prio_pre));
     [exact Hnth | rewrite Hfree; reflexivity]).
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_PRIO_EXIST, None) ls0).
      {
        unfold OSMutexCreate_sem.
        right; right; left.
        split; [rewrite Hdisabled; exact PreH3 |].
        split; [rewrite Hlowest; exact PreH8 |].
        split; [rewrite <- PreH5; exact PreH6 |].
        split; [exact Hslot_nonfree |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_PRIO_EXIST, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH18.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; right; left.
      split; [rewrite Hdisabled; exact PreH3 |].
      split.
      * split; [exact PreH11 |].
        rewrite Hlowest. exact PreH8.
      * split; [exact PreH6 |].
        split; [exact PreH2 |].
        repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_6 : OSMutexCreate_full_return_wit_6.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  pose proof H6 as Hrel_shape.
  unfold prio_tbl_list_rel in Hrel_shape.
  destruct Hrel_shape as [_ Hnth].
  specialize (Hnth prio_pre ltac:(unfold OS_PRIO_TBL_SIZE; lia)).
  assert (Hslot_nonfree :
    (TskState ls0).(prioTbl) prio_pre <> PTFree) by
    (intro Hfree; apply PreH2;
     transitivity
       (prio_tbl_entry_to_addr sg ((TskState ls0).(prioTbl) prio_pre));
     [exact Hnth | rewrite Hfree; reflexivity]).
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_PRIO_EXIST, None) ls0).
      {
        unfold OSMutexCreate_sem.
        right; right; left.
        split; [rewrite Hdisabled; exact PreH3 |].
        split; [rewrite Hlowest; exact PreH8 |].
        split; [rewrite <- PreH5; exact PreH6 |].
        split; [exact Hslot_nonfree |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_PRIO_EXIST, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH18.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH14.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; right; left.
      split; [rewrite Hdisabled; exact PreH3 |].
      split.
      * split; [exact PreH11 |].
        rewrite Hlowest. exact PreH8.
      * split; [exact PreH6 |].
        split; [exact PreH2 |].
        repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_7 : OSMutexCreate_full_return_wit_7.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_CREATE_ISR, None) ls0).
      {
        unfold OSMutexCreate_sem.
        right; left.
        split; [rewrite Hlowest; exact PreH4 |].
        split; [rewrite <- PreH1; exact PreH2 |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_CREATE_ISR, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH14.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; left.
      split.
      * unfold valid_mutex_pcp.
        right. split; [exact PreH7 |].
        rewrite Hlowest. exact PreH4.
      * split; [exact PreH2 |].
        repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_8 : OSMutexCreate_full_return_wit_8.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_CREATE_ISR, None) ls0).
      {
        unfold OSMutexCreate_sem.
        right; left.
        split; [rewrite Hlowest; exact PreH4 |].
        split; [rewrite <- PreH1; exact PreH2 |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_CREATE_ISR, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH14.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH10.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; left.
      split.
      * unfold valid_mutex_pcp.
        right. split; [exact PreH7 |].
        rewrite Hlowest. exact PreH4.
      * split; [exact PreH2 |].
        repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_9 : OSMutexCreate_full_return_wit_9.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_CREATE_ISR, None) ls0).
      {
        unfold OSMutexCreate_sem.
        right; right; right; right; left.
        split; [rewrite Hdisabled; exact PreH4 |].
        split; [rewrite <- PreH1; exact PreH2 |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_CREATE_ISR, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH13.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; left.
      split.
      * unfold valid_mutex_pcp.
        left. rewrite Hdisabled. exact PreH4.
      * split; [exact PreH2 |].
        repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_10 : OSMutexCreate_full_return_wit_10.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_CREATE_ISR, None) ls0).
      {
        unfold OSMutexCreate_sem.
        right; right; right; right; left.
        split; [rewrite Hdisabled; exact PreH4 |].
        split; [rewrite <- PreH1; exact PreH2 |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_CREATE_ISR, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH13.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      right; left.
      split.
      * unfold valid_mutex_pcp.
        left. rewrite Hdisabled. exact PreH4.
      * split; [exact PreH2 |].
        repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_11 : OSMutexCreate_full_return_wit_11.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_PRIO_INVALID, None) ls0).
      {
        unfold OSMutexCreate_sem.
        left.
        split; [rewrite Hdisabled; exact PreH2 |].
        split; [rewrite Hlowest; exact PreH1 |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_PRIO_INVALID, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH11.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      left.
      split; [rewrite Hdisabled; exact PreH2 |].
      split; [rewrite Hlowest; exact PreH1 |].
      repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_return_wit_12 : OSMutexCreate_full_return_wit_12.
Proof.
  aggressive_pre_process.
  subst prio_in.
  subst pd.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable_shape;
      unfold valid_stable_glob_vars in Hstable_shape;
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]]
  end.
  Exists ls0.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls0).
    cancel (UCOS2_Verify_inv sg ls0).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexCreate_sem sg prio_pre
        ls0 (OS_ERR_PRIO_INVALID, None) ls0).
      {
        unfold OSMutexCreate_sem.
        left.
        split; [rewrite Hdisabled; exact PreH2 |].
        split; [rewrite Hlowest; exact PreH1 |].
        repeat split; reflexivity.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * option EventID) Z (OSMutexCreate_sem sg prio_pre)
        (observe_mutex_create_ptr sg) ls0 ls0
        (OS_ERR_PRIO_INVALID, None) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_create_ptr. simpl.
        split; reflexivity.
      * exact PreH11.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial.
      unfold mutex_create_result_prop.
      left.
      split; [rewrite Hdisabled; exact PreH2 |].
      split; [rewrite Hlowest; exact PreH1 |].
      repeat split; reflexivity.
Qed.

Lemma proof_of_OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_pure : OSMutexCreate_full_partial_solve_wit_60_enabled_nonempty_pure.
Proof.
  pre_process.
  dump_pre_spatial.
  apply mutex_create_pcp_cnt_encoding_exact__leaf_pure_and_global_localization.
  lia.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_1 : OSMutexCreate_full_which_implies_wit_1.
Proof.
  pre_process.
  unfold UCOS2_Verify_inv, UCOS2_Verify_inv_no_int_nesting.
  unfold os_int_nesting_addr, interrupt_inv, store_int_state,
    interrupt_inv_no_int_nesting.
  pureIntros.
  unfold os_int_nesting_addr in H.
  subst isr.
  rewrite H.
  entailer!.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_2 : OSMutexCreate_full_which_implies_wit_2.
Proof.
  pre_process.
  unfold UCOS2_Verify_inv, UCOS2_Verify_inv_no_int_nesting,
    os_int_nesting_addr, interrupt_inv, store_int_state,
    interrupt_inv_no_int_nesting.
  pureIntros.
  unfold os_int_nesting_addr in H.
  subst isr.
  rewrite H.
  entailer!.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_3 : OSMutexCreate_full_which_implies_wit_3.
Proof.
  pre_process.
  unfold UCOS2_Verify_inv, UCOS2_Verify_inv_no_int_nesting,
    os_int_nesting_addr, interrupt_inv, store_int_state,
    interrupt_inv_no_int_nesting.
  pureIntros.
  unfold os_int_nesting_addr in H.
  subst isr.
  rewrite H.
  entailer!.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_4 : OSMutexCreate_full_which_implies_wit_4.
Proof.
  pre_process.
  unfold crit_rel_no_os_state_change in H2.
  subst ls1_2.
  pose proof (prio_tbl_list_rel_eq__entry_and_critical_restore
    sg ls0.(TskState) prioL_in H1) as Hprio.
  unfold event_free_list_head_prop in H0.
  unfold os_event_free_list_addr in H.
  Exists ls0.
  unfold UCOS2_Verify_inv, mutex_create_head_open_inv.
  unfold task_inv, task_inv_no_priotbl, store_prio_tbl.
  unfold event_inv, event_inv_no_free_head, store_free_event_list.
  rewrite Hprio, H0, H.
  entailer!.
  rewrite <- Hprio.
  exact H1.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_5 : OSMutexCreate_full_which_implies_wit_5.
Proof.
  pre_process.
  prop_apply_p (store_array_Zlength Z priotbl_element_store
    (g_OSTCBPrioTbl sg) OS_PRIO_TBL_SIZE prioL_in).
  Intros_p Hlen.
  assert (Hidx : priotbl_index_in_range prio_in) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  sep_apply_l_atomic (store_priotbl_list_split sg prioL_in prio_in Hidx Hlen).
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  unfold os_tcb_prio_tbl_addr in H.
  rewrite H0.
  rewrite H.
  cbn [sizeof_front_end_type].
  entailer!.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_6 : OSMutexCreate_full_which_implies_wit_6.
Proof.
  pre_process.
  unfold store_priotbl_list_missing_i.
  prop_apply_p (store_array_missing_i_rec_Zlength Z priotbl_element_store
    (g_OSTCBPrioTbl sg) prio_in 0 OS_PRIO_TBL_SIZE prioL_in).
  Intros_p Hlen.
  fold (store_priotbl_list_missing_i sg prioL_in prio_in).
  assert (Hidx : priotbl_index_in_range prio_in) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  unfold os_tcb_prio_tbl_addr in H.
  unfold mutex_create_priority_input_prop in H0.
  subst prio.
  rewrite H.
  cbn [sizeof_front_end_type].
  sepcon_lift (store_priotbl_list_missing_i sg prioL_in prio_in).
  sepcon_lift
    ((g_OSTCBPrioTbl sg + prio_in * 4) # Ptr |-> Znth prio_in prioL_in 0).
  fold (store_priotbl_list_missing_i sg prioL_in prio_in).
  assert (Hlen' : Zlength prioL_in = OS_PRIO_TBL_SIZE) by lia.
  entailer!.
  sep_apply_l_atomic
    (store_priotbl_list_merge sg prioL_in prio_in
      (Znth prio_in prioL_in 0) Hidx Hlen').
  rewrite replace_Znth_Znth.
  entailer!.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_7 : OSMutexCreate_full_which_implies_wit_7.
Proof.
  pre_process.
  unfold crit_rel_no_os_state_change in H2.
  subst ls1_2.
  Exists ls0.
  cbn [mutex_create_restore_frame].
  sep_apply_l_atomic
    (mutex_create_head_open_rebuild__entry_and_critical_restore
      sg ls0 prioL_in freelist_in (&("OSEventFreeList")) H1 H0 H).
  unfold crit_rel_no_os_state_change.
  entailer!.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_8 : OSMutexCreate_full_which_implies_wit_8.
Proof.
  pre_process.
  unfold mutex_create_restore_transition_prop in H0.
  cbn in H0.
  destruct H0 as [_ Hpost].
  subst ls_post.
  cbn [mutex_create_restore_frame].
  sepcon_lift (UCOS2_Verify_inv sg ls0).
  sepcon_lift (OutsideCritical sg ls0).
  entailer!.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_9 : OSMutexCreate_full_which_implies_wit_9.
Proof.
  pre_process.
  unfold store_priotbl_list_missing_i.
  prop_apply_p (store_array_missing_i_rec_Zlength Z priotbl_element_store
    (g_OSTCBPrioTbl sg) prio_in 0 OS_PRIO_TBL_SIZE prioL_in).
  Intros_p Hlen.
  fold (store_priotbl_list_missing_i sg prioL_in prio_in).
  assert (Hidx : priotbl_index_in_range prio_in) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  unfold os_tcb_prio_tbl_addr in H.
  unfold mutex_create_priority_input_prop in H0.
  subst prio.
  rewrite H.
  cbn [sizeof_front_end_type].
  sepcon_lift (store_priotbl_list_missing_i sg prioL_in prio_in).
  sepcon_lift ((g_OSTCBPrioTbl sg + prio_in * 4) # Ptr |-> 1).
  fold (store_priotbl_list_missing_i sg prioL_in prio_in).
  assert (Hlen' : Zlength prioL_in = OS_PRIO_TBL_SIZE) by lia.
  entailer!.
  sep_apply_l_atomic
    (store_priotbl_list_merge sg prioL_in prio_in 1 Hidx Hlen').
  entailer!.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_10 : OSMutexCreate_full_which_implies_wit_10.
Proof.
  pre_process.
  pose proof H as Hvalid.
  unfold valid_stable_glob_vars in Hvalid.
  destruct Hvalid as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hdisabled & _).
  unfold valid_mutex_pcp, mutex_create_pcp_slot_available_prop,
    mutex_create_priotbl_after.
  rewrite Hdisabled.
  replace (prio_in =? 255) with false by
    (symmetry; apply Z.eqb_neq; exact PreH1).
  entailer!.
  - apply sepcon_cancel_end.
    + apply derivable1_truep_intros.
    + apply derivable1_truep_intros.
  - right.
    unfold valid_stable_glob_vars in H.
    lia.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_11 : OSMutexCreate_full_which_implies_wit_11.
Proof.
  pre_process.
  subst prio_in.
  pose proof H as Hvalid.
  unfold valid_stable_glob_vars in Hvalid.
  destruct Hvalid as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hdisabled & _).
  unfold valid_mutex_pcp, mutex_create_pcp_slot_available_prop,
    mutex_create_priotbl_after.
  rewrite Hdisabled.
  cbn.
  entailer!.
  unfold store_priotbl_list, store_array.
  cancel.
  apply sepcon_cancel_end.
  - apply derivable1_truep_intros.
  - apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_12 : OSMutexCreate_full_which_implies_wit_12.
Proof.
  pre_process.
  unfold store_priotbl_list.
  prop_apply_p (store_array_Zlength Z priotbl_element_store
    (g_OSTCBPrioTbl sg) OS_PRIO_TBL_SIZE
    (mutex_create_priotbl_after sg prio_in prioL_in)).
  Intros_p Hlen.
  fold (store_priotbl_list sg
    (mutex_create_priotbl_after sg prio_in prioL_in)).
  assert (Hidx : priotbl_index_in_range prio_in) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  pose proof H1 as Hvalid.
  unfold valid_stable_glob_vars in Hvalid.
  destruct Hvalid as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hdisabled & _).
  assert (Hcell :
    Znth prio_in (mutex_create_priotbl_after sg prio_in prioL_in) 0 = 1).
  {
    unfold mutex_create_priotbl_after.
    rewrite Hdisabled.
    replace (prio_in =? 255) with false by
      (symmetry; apply Z.eqb_neq; exact PreH3).
    apply Znth_replace_Znth_Same.
    unfold mutex_create_priotbl_after in Hlen.
    rewrite Hdisabled in Hlen.
    replace (prio_in =? 255) with false in Hlen by
      (symmetry; apply Z.eqb_neq; exact PreH3).
    rewrite Zlength_replace_Znth in Hlen.
    unfold OS_PRIO_TBL_SIZE in Hlen.
    exact (conj PreH1
      (eq_ind_r (fun z => prio_in < z) PreH2 Hlen)).
  }
  sep_apply_l_atomic
    (store_priotbl_list_split sg
      (mutex_create_priotbl_after sg prio_in prioL_in)
      prio_in Hidx Hlen).
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  unfold os_tcb_prio_tbl_addr in H.
  unfold mutex_create_priority_input_prop in H2.
  subst prio.
  rewrite H.
  cbn [sizeof_front_end_type].
  rewrite Hcell.
  entailer!.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_13 : OSMutexCreate_full_which_implies_wit_13.
Proof.
  pre_process.
  unfold store_priotbl_list_missing_i.
  prop_apply_p (store_array_missing_i_rec_Zlength Z priotbl_element_store
    (g_OSTCBPrioTbl sg) prio_in 0 OS_PRIO_TBL_SIZE
    (mutex_create_priotbl_after sg prio_in prioL_in)).
  Intros_p Hlen.
  fold (store_priotbl_list_missing_i sg
    (mutex_create_priotbl_after sg prio_in prioL_in) prio_in).
  assert (Hidx : priotbl_index_in_range prio_in) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  pose proof H1 as Hvalid.
  unfold valid_stable_glob_vars in Hvalid.
  destruct Hvalid as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hdisabled & _).
  assert (Hlookup : Znth prio_in prioL_in 0 = 0).
  {
    unfold mutex_create_pcp_slot_available_prop in H0.
    rewrite Hdisabled in H0.
    destruct H0 as [Heq | [_ Hlookup]].
    - exfalso. apply PreH3. exact Heq.
    - exact Hlookup.
  }
  assert (Hrollback :
    replace_Znth prio_in 0
      (mutex_create_priotbl_after sg prio_in prioL_in) = prioL_in).
  {
    unfold mutex_create_priotbl_after.
    rewrite Hdisabled.
    replace (prio_in =? 255) with false by
      (symmetry; apply Z.eqb_neq; exact PreH3).
    apply (replace_Znth_reserved_rollback__priority_table_localization
      Z prioL_in prio_in 0 1 0).
    exact Hlookup.
  }
  unfold os_tcb_prio_tbl_addr in H.
  unfold mutex_create_priority_input_prop in H2.
  subst prio.
  rewrite H.
  cbn [sizeof_front_end_type].
  sepcon_lift (store_priotbl_list_missing_i sg
    (mutex_create_priotbl_after sg prio_in prioL_in) prio_in).
  sepcon_lift ((g_OSTCBPrioTbl sg + prio_in * 4) # Ptr |-> 0).
  fold (store_priotbl_list_missing_i sg
    (mutex_create_priotbl_after sg prio_in prioL_in) prio_in).
  assert (Hlen' :
    Zlength (mutex_create_priotbl_after sg prio_in prioL_in) =
      OS_PRIO_TBL_SIZE) by exact Hlen.
  entailer!.
  sep_apply_l_atomic
    (store_priotbl_list_merge sg
      (mutex_create_priotbl_after sg prio_in prioL_in)
      prio_in 0 Hidx Hlen').
  refine
    (eq_ind
      (replace_Znth prio_in 0
        (mutex_create_priotbl_after sg prio_in prioL_in))
      (fun l =>
        store_priotbl_list sg
          (replace_Znth prio_in 0
            (mutex_create_priotbl_after sg prio_in prioL_in))
        |-- store_priotbl_list sg l)
      _
      prioL_in Hrollback).
  cancel.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_14 : OSMutexCreate_full_which_implies_wit_14.
Proof.
  pre_process.
  subst prio_in.
  unfold store_priotbl_list.
  prop_apply_p (store_array_Zlength Z priotbl_element_store
    (g_OSTCBPrioTbl sg) OS_PRIO_TBL_SIZE
    (mutex_create_priotbl_after sg 255 prioL_in)).
  Intros_p Hlen.
  fold (store_priotbl_list sg
    (mutex_create_priotbl_after sg 255 prioL_in)).
  assert (Hafter : mutex_create_priotbl_after sg 255 prioL_in = prioL_in).
  {
    unfold mutex_create_priotbl_after.
    destruct (255 =? osPrioMutexCeilDis sg) eqn:Heqb; [reflexivity |].
    rewrite replace_Znth_nothing.
    - reflexivity.
    - unfold mutex_create_priotbl_after in Hlen.
      rewrite Heqb in Hlen.
      rewrite Zlength_replace_Znth in Hlen.
      unfold OS_PRIO_TBL_SIZE in Hlen.
      rewrite Hlen.
      lia.
  }
  refine
    (eq_ind
      (mutex_create_priotbl_after sg 255 prioL_in)
      (fun l =>
        store_priotbl_list sg (mutex_create_priotbl_after sg 255 prioL_in)
        |-- store_priotbl_list sg l)
      _
      prioL_in Hafter).
  cancel.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_15 : OSMutexCreate_full_which_implies_wit_15.
Proof.
  pre_process.
  unfold crit_rel_no_os_state_change in H2.
  subst ls1_2.
  Exists ls0.
  unfold mutex_create_restore_frame, crit_rel_no_os_state_change.
  sep_apply_l_atomic
    (mutex_create_head_open_rebuild__entry_and_critical_restore
      sg ls0 prioL_in freelist_in (&( "OSEventFreeList")) H1 H0 H).
  apply derivable1s_truep_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - apply derivable1s_truep_intros.
    + apply derivable1s_coq_prop_r. reflexivity.
    + cancel (UCOS2_Verify_inv sg ls0).
      cancel (InsideCritical sg ls0).
      entailer!.
      apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_16 : OSMutexCreate_full_which_implies_wit_16.
Proof.
  pre_process.
  unfold mutex_create_restore_transition_prop in H.
  simpl in H.
  destruct H as [_ Hpost].
  subst ls_post.
  unfold mutex_create_restore_frame.
  unfold UCOS2_Verify_inv.
  pre_process.
  apply derivable1s_truep_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - cancel (OutsideCritical sg ls0).
    cancel (interrupt_inv sg (IntrState ls0)).
    cancel (task_inv sg (TskState ls0)).
    cancel (sched_inv sg (TskState ls0) (SchedState ls0)).
    cancel (event_inv sg (TskState ls0) (EventState ls0)).
    cancel (tick_inv sg (TickState ls0)).
    apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_17 : OSMutexCreate_full_which_implies_wit_17.
Proof.
  pre_process.
  Exists ls1_2.
  unfold mutex_create_free_snapshot_prop.
  sepcon_assoc_change.
  coq_prop_lift.
  pureIntros.
  unfold mutex_create_free_snapshot_prop in H.
  destruct H as [[Hzero _] | [Hnonzero [Hvalid [Hunref Hsnap]]]].
  - contradiction.
  - unfold crit_rel_no_os_state_change in H1.
    subst ls1_2.
    unfold event_free_head_snapshot_prop in Hsnap.
    destruct Hsnap as [Hfree [Hbase Hnext]].
    unfold event_core_fields_layout_prop in H2.
    destruct H2 as [Htype [Hptr Hcnt]].
    subst freelist_in.
    unfold mutex_create_head_open_inv, mutex_create_node_open_inv,
      event_inv_no_free_head, event_inv_free_head_rest.
    rewrite Hfree.
    simpl [store_free_event_nodes].
    rewrite Hptr, Hnext.
    unfold mutex_create_unused_event_no_ptr.
    entailer!.
    + simpl [encode_event_type].
      entailer!.
      eapply derivable1s_emp_sepcon_unfold.
      * apply derivable1_truep_intros.
      * apply derivable1_truep_intros.
    + unfold event_free_head_snapshot_prop.
      repeat split; auto.
    + unfold event_core_fields_layout_prop.
      repeat split; auto.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_18 : OSMutexCreate_full_which_implies_wit_18.
Proof.
  pre_process.
  sepcon_assoc_change.
  coq_prop_lift.
  unfold event_core_fields_layout_prop, event_free_head_snapshot_prop.
  pureIntros.
  unfold event_free_head_snapshot_prop in H.
  unfold event_core_fields_layout_prop in H0.
  destruct H as [Hfree [Hbase Hnext]].
  destruct H0 as [Htype [Hptr Hcnt]].
  subst freelist_in.
  unfold mutex_create_unused_event_no_ptr, unused_complete_event.
  rewrite Hptr.
  entailer!.
  apply store_ptr_undef_store_ptr.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_19 : OSMutexCreate_full_which_implies_wit_19.
Proof.
  pre_process.
  Exists ls1_2.
  sepcon_assoc_change.
  coq_prop_lift.
  pureIntros.
  unfold crit_rel_no_os_state_change in H7.
  subst ls1_2.
  unfold event_free_head_snapshot_prop in H5.
  destruct H5 as [Hfree [Hbase Hnext]].
  subst freelist_in.
  subst next_in.
  unfold stable_glob_vars.os_event_free_list_addr in H.
  rewrite H.
  unfold mutex_create_restore_frame.
  simpl.
  unfold mutex_create_transient_frame.
  entailer!.
  - repeat split; auto.
  - unfold event_free_head_snapshot_prop.
    repeat split; auto.
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_20 : OSMutexCreate_full_which_implies_wit_20.
Proof.
  pre_process.
  Exists ls_post_2.
  sepcon_assoc_change.
  coq_prop_lift.
  pureIntros.
  unfold mutex_create_restore_frame.
  simpl.
  unfold mutex_create_transient_frame.
  sepcon_assoc_change.
  coq_prop_lift.
  pureIntros.
  destruct H3 as
    [Hvalidsg [Hvalidpcp [Hvalideid [Hunref [Hfree [Hprio Hslot]]]]]].
  unfold mutex_create_restore_transition_prop in H1.
  simpl in H1.
  destruct H1 as [Hinside [Hsuccess Htaskevent]].
  unfold event_free_head_snapshot_prop in H0.
  destruct H0 as [Hfree' [Hbase Hnext]].
  subst freelist_in.
  subst next_in.
  unfold stable_glob_vars.os_event_free_list_addr in H.
  rewrite H.
  entailer!;
    try (unfold event_free_head_snapshot_prop; repeat split; auto).
  repeat first
    [ apply derivable1_truep_intros
    | eapply derivable1s_emp_sepcon_unfold ].
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_21 : OSMutexCreate_full_which_implies_wit_21.
Proof.
  pre_process.
  Exists ls_post_2.
  sepcon_assoc_change.
  coq_prop_lift.
  pureIntros.
  unfold event_free_head_snapshot_prop in H.
  destruct H as [Hfree [Hbase Hnext]].
  subst freelist_in.
  unfold event_core_fields_layout_prop in H1.
  destruct H1 as [Htype [Hptr Hcnt]].
  unfold unused_complete_event, mutex_create_wait_table_uninitialized.
  rewrite Htype, Hptr, Hcnt.
  simpl [encode_event_type].
  entailer!;
    try (unfold event_free_head_snapshot_prop; repeat split; auto).
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_22 : OSMutexCreate_full_which_implies_wit_22.
Proof.
  pre_process.
  Exists ls_post_2.
  sepcon_assoc_change.
  coq_prop_lift.
  pureIntros.
  pose proof H0 as Hsuccess.
  unfold mutex_create_success_transition_prop in H0.
  destruct H0 as [Hfree0 [Hunref [Hpost [Hatomic Hcrit]]]].
  subst ls_post_2.
  unfold event_free_head_snapshot_prop in H.
  destruct H as [Hfree [Hbase Hnext]].
  subst freelist_in.
  unfold event_core_fields_layout_prop in H1.
  destruct H1 as [Htype [Hptr Hcnt]].
  unfold mutex_create_initialized_event, used_complete_event,
    mutex_create_wait_table_zero, mutex_create_fresh_event.
  rewrite Htype, Hptr, Hcnt.
  unfold encode_event_type, encode_event_ptr_value, encode_event_cnt_value,
    encode_event_wait_grp, encode_event_wait_tbl_at.
  simpl.
  entailer!;
    try (unfold event_free_head_snapshot_prop; repeat split; auto).
Qed.

Lemma proof_of_OSMutexCreate_full_which_implies_wit_23 : OSMutexCreate_full_which_implies_wit_23.
Proof.
  pre_process.
  Exists ls_post_2.
  sepcon_assoc_change.
  coq_prop_lift.
  pureIntros.
  pose proof H6 as Hsuccess.
  unfold mutex_create_success_transition_prop in H6.
  destruct H6 as [Hfree [Hunref [Hpost [Hatomic Hcrit]]]].
  subst ls_post_2.
  unfold event_free_head_snapshot_prop in H5.
  destruct H5 as [Hfree_snapshot [Hhead Hnext]].
  subst freelist_in.
  subst next_in.
  unfold stable_glob_vars.os_event_free_list_addr in H.
  rewrite H.
  pose proof
    (mutex_create_priotbl_list_rel_after__event_detach_initialize_publish
      sg prio_in (TskState ls0) prioL_in H4 H3 H1) as Hafter_rel.
  pose proof
    (prio_tbl_list_rel_unique__event_detach_initialize_publish
      sg (mutex_create_task_after sg prio_in (TskState ls0))
      (mutex_create_priotbl_after sg prio_in prioL_in) Hafter_rel)
    as Hprio_list.
  rewrite Hprio_list.
  sep_apply_l_atomic
    (mutex_create_full_inv_after__event_detach_initialize_publish
      sg prio_in eid free_rest ls0 prioL_in
      H4 H3 H2 H1 H0 Hfree Hunref).
  entailer!.
  unfold event_free_head_snapshot_prop.
  repeat split; auto.
Qed.
