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
From Ucos2Verify.VC.code.mutex Require Import post_full_goal.
From Ucos2Verify.VC.code.mutex Require Import post_full_proof_auto.
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
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.mutex_rdyatprio_spec.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.mutex_post_spec.
Local Open Scope sac.

Lemma proof_of_OSMutexPost_full_safety_wit_8 : OSMutexPost_full_safety_wit_8.
Proof.
  pre_process.
  prop_apply_p
    (store_ushort_range
      (&( pevent0 # "os_event" ->ₛ "OSEventCnt")) ecnt_in).
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_1_1 : OSMutexPost_full_entail_wit_1_1.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&( "OSIntNesting")) isr).
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_1_2 : OSMutexPost_full_entail_wit_1_2.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&( "OSIntNesting")) isr).
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_1_3 : OSMutexPost_full_entail_wit_1_3.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&( "OSIntNesting")) isr).
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_2 : OSMutexPost_full_entail_wit_2.
Proof.
  pre_process.
  subst pevent_pre.
  subst pevent0.
  entailer!.
  unfold mutex_post_checked_entry_prop.
  split.
  - rewrite <- PreH15.
    exact PreH17.
  - exact PreH18.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_3 : OSMutexPost_full_entail_wit_3.
Proof.
  pre_process.
  unfold crit_rel_no_os_state_change in H13.
  subst ls1_2.
  destruct H0 as [Hmap [Htcb Hprio]].
  unfold task_prio_field_layout_prop in H.
  sep_apply_l_atomic
    (task_inv_split_prio_at__focus_and_pure
      sg (TskState ls0) cur_tid cur_t tcbcur tcbprio
      (&( tcbcur # "os_tcb" ->ₛ "OSTCBPrio"))
      Hmap Htcb Hprio H).
  unfold sched_tcb_cur_snapshot_prop in H1.
  sep_apply_l_atomic
    (sched_inv_split_tcb_cur_at__focus_and_pure
      sg (TskState ls0) (SchedState ls0)
      (&( "OSTCBCur")) tcbcur H8 H1).
  pose proof
    (debug_prio_canonical__relocation_semantics
      sg (TskState ls0) prioL_in H2) as HprioL.
  pose proof H11 as Hbundle.
  unfold UCOS2_validity_bundle in Hbundle.
  destruct Hbundle as [Htask_valid [_ [Hevent_valid _]]].
  pose proof H5 as Hsnapshot.
  unfold event_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as
    [Hused [Hencoded_type [Hencoded_count _]]].
  assert (Hevent_type : eventType e = OS_EVENT_TYPE_MUTEX).
  {
    rewrite PreH3 in Hencoded_type.
    destruct (eventType e); cbn in Hencoded_type; congruence.
  }
  unfold event_vaild_cond_prop, valid_GlobEventAbstractState,
    event_in_range in Hevent_valid.
  destruct Hevent_valid as
    [Hevent_ids [_ [_ [_ [_ [Hevent_payload _]]]]]].
  assert (Hvalid_event : valid_event_id sg eid).
  {
    unfold valid_event_id.
    eapply Hevent_ids; eassumption.
  }
  specialize (Hevent_payload eid e Hused).
  unfold event_payload_consistency in Hevent_payload.
  rewrite Hevent_type in Hevent_payload.
  destruct (mutexFields e) as [m |] eqn:Hmutex_fields;
    [| contradiction].
  destruct Hevent_payload as [Hmutex_consistent _].
  pose proof H12 as Hcross.
  unfold cross_module_consistency in Hcross.
  destruct Hcross as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hmutex_protocol _]]]]]]]]].
  pose proof
    (Hmutex_protocol eid e m Hused Hevent_type Hmutex_fields)
    as Hprotocol.
  destruct Hprotocol as [Hvalid_mpcp _].
  pose proof H9 as Hvsg.
  assert (Hmpcp_range : 0 <= mfPCP m < 256).
  {
    unfold valid_mutex_pcp in Hvalid_mpcp.
    destruct Hvalid_mpcp as [Hdisabled | Hrange].
    - unfold valid_stable_glob_vars in Hvsg.
      intuition lia.
    - unfold valid_stable_glob_vars in Hvsg.
      intuition lia.
  }
  assert (Hdecoded_pcp :
    decode_PCP_from_cnt ecnt_in = mfPCP m).
  {
    unfold decode_PCP_from_cnt.
    rewrite Hencoded_count.
    unfold encode_event_cnt_value.
    rewrite Hevent_type, Hmutex_fields.
    unfold mutex_fields_consistency in Hmutex_consistent.
    destruct (mfOwner m) as [owner |] eqn:Howner;
      destruct (mfOwnerOrigPrio m) as [op |] eqn:Horig;
      try contradiction.
    - destruct Hmutex_consistent as [Hop0 [Hoplt _]].
      assert (Hoprange : 0 <= op < 256).
      {
        pose proof H9 as Hvsg_op.
        unfold valid_stable_glob_vars in Hvsg_op.
        intuition lia.
      }
      change
        (unsigned_last_nbits
          (Z.shiftr (mfPCP m * 256 + op) 8) 8 = mfPCP m).
      rewrite Z.shiftr_div_pow2 by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      rewrite Z.add_comm, Z.div_add by lia.
      rewrite Z.div_small by exact Hoprange.
      rewrite Z.add_0_l.
      unfold unsigned_last_nbits.
      apply Z.mod_small.
      exact Hmpcp_range.
    - change
        (unsigned_last_nbits
          (Z.shiftr (mfPCP m * 256 + 255) 8) 8 = mfPCP m).
      rewrite Z.shiftr_div_pow2 by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      rewrite Z.add_comm, Z.div_add by lia.
      cbn.
      unfold unsigned_last_nbits.
      apply Z.mod_small.
      exact Hmpcp_range.
  }
  assert (Hvalid_pcp : valid_mutex_pcp sg pcp_idx).
  {
    rewrite PreH4, Hdecoded_pcp.
    exact Hvalid_mpcp.
  }
  assert (Htcb_nonzero : tcbcur <> 0).
  {
    unfold task_vaild_cond_prop in Htask_valid.
    destruct Htask_valid as [Htask_range _].
    unfold valid_GlobTaskAbstractState, task_in_range in Htask_range.
    destruct Htask_range as [Htask_ids _].
    specialize (Htask_ids cur_tid cur_t Hmap).
    assert (Hin :
      In (g_OSTCBTbl sg) (stable_global_addresses sg)).
    {
      unfold stable_global_addresses.
      simpl.
      tauto.
    }
    pose proof
      (valid_stable_address_pos sg (g_OSTCBTbl sg) H9 Hin)
      as Htcb_base.
    rewrite Htcb.
    unfold tcb_addr, sizeof_OS_TCB.
    lia.
  }
  unfold task_inv_no_tid, task_inv_no_tid_priotbl, store_prio_tbl.
  rewrite <- HprioL.
  Exists ls0.
  unfold decode_PCP_from_cnt, decode_OwnerPrio_from_cnt in *.
  unfold crit_rel_no_os_state_change.
  entailer!.
  - rewrite PreH3.
    entailer!.
    eapply sepcon_cancel_end.
    + apply derivable1_truep_intros.
    + apply derivable1_truep_intros.
  - rewrite PreH3 in H5.
    exact H5.
  - unfold task_prio_snapshot_of_prop.
    tauto.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_4 : OSMutexPost_full_entail_wit_4.
Proof.
  pre_process.
  unfold crit_rel_no_os_state_change in H13.
  subst ls1_2.
  pose proof H0 as Htask_snapshot.
  unfold task_prio_snapshot_of_prop in Htask_snapshot.
  destruct Htask_snapshot as [Htask_map [Htcb Htprio]].
  pose proof H1 as Hsched_snapshot.
  unfold sched_tcb_cur_snapshot_prop in Hsched_snapshot.
  pose proof H4 as Hevent_snapshot.
  unfold event_snapshot_of_prop in Hevent_snapshot.
  destruct Hevent_snapshot as
    [Hused [Hencoded_type [Hencoded_count
      [Hencoded_ptr [Hencoded_grp Hencoded_tbl]]]]].
  assert (Hevent_type : eventType e = OS_EVENT_TYPE_MUTEX).
  {
    destruct (eventType e); cbn in Hencoded_type; congruence.
  }
  pose proof H15 as Hbundle.
  unfold UCOS2_validity_bundle in Hbundle.
  destruct Hbundle as [_ [_ [Hevent_valid _]]].
  unfold event_vaild_cond_prop, valid_GlobEventAbstractState,
    event_in_range in Hevent_valid.
  destruct Hevent_valid as
    [_ [_ [_ [_ [_ [Hevent_payload _]]]]]].
  specialize (Hevent_payload eid e Hused).
  unfold event_payload_consistency in Hevent_payload.
  rewrite Hevent_type in Hevent_payload.
  destruct (mutexFields e) as [m |] eqn:Hmutex_fields;
    [| contradiction].
  destruct Hevent_payload as [Hmutex_consistent _].
  pose proof H10 as Hcross.
  unfold cross_module_consistency in Hcross.
  destruct Hcross as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hmutex_protocol _]]]]]]]]].
  pose proof
    (Hmutex_protocol eid e m Hused Hevent_type Hmutex_fields)
    as Hprotocol.
  destruct Hprotocol as [Hvalid_mpcp _].
  pose proof H9 as Hvsg.
  assert (Hmpcp_range : 0 <= mfPCP m < 256).
  {
    unfold valid_mutex_pcp in Hvalid_mpcp.
    destruct Hvalid_mpcp as [Hdisabled | Hrange].
    - unfold valid_stable_glob_vars in Hvsg.
      intuition lia.
    - unfold valid_stable_glob_vars in Hvsg.
      intuition lia.
  }
  unfold mutex_fields_consistency in Hmutex_consistent.
  destruct (mfOwner m) as [owner_tid |] eqn:Howner.
  - destruct (mfOwnerOrigPrio m) as [owner_orig |] eqn:Horig.
    + destruct Hmutex_consistent as [Horig_nonneg [Horig_lt _]].
      assert (Horig_range : 0 <= owner_orig < 256).
      {
        pose proof H9 as Hvsg_orig.
        unfold valid_stable_glob_vars in Hvsg_orig.
        intuition lia.
      }
      assert (Hdecoded_pcp :
        decode_PCP_from_cnt ecnt_in = mfPCP m).
      {
        unfold decode_PCP_from_cnt.
        rewrite Hencoded_count.
        unfold encode_event_cnt_value.
        rewrite Hevent_type, Hmutex_fields, Howner, Horig.
        change
          (unsigned_last_nbits
            (Z.shiftr (mfPCP m * 256 + owner_orig) 8) 8 =
           mfPCP m).
        rewrite Z.shiftr_div_pow2 by lia.
        replace (2 ^ 8) with 256 by reflexivity.
        rewrite Z.add_comm, Z.div_add by lia.
        rewrite Z.div_small by exact Horig_range.
        rewrite Z.add_0_l.
        unfold unsigned_last_nbits.
        apply Z.mod_small.
        exact Hmpcp_range.
      }
      assert (Hdecoded_owner :
        decode_OwnerPrio_from_cnt ecnt_in = owner_orig).
      {
        unfold decode_OwnerPrio_from_cnt.
        rewrite Hencoded_count.
        unfold encode_event_cnt_value.
        rewrite Hevent_type, Hmutex_fields, Howner, Horig.
        apply mutex_accept_land_low_byte__restore_and_returns.
        exact Horig_range.
      }
      assert (Howner_ptr :
        owner_ptr = tcb_addr sg owner_tid).
      {
        rewrite Hencoded_ptr.
        unfold encode_event_ptr_value.
        rewrite Hevent_type, Hmutex_fields, Howner.
        reflexivity.
      }
      assert (Howner_tid : owner_tid = cur_tid).
      {
        unfold tcb_addr, sizeof_OS_TCB in Howner_ptr, Htcb.
        lia.
      }
      subst owner_tid.
      destruct (curTaskID (SchedState ls0)) as [sched_tid |]
        eqn:Hsched_id.
      * assert (Hsched_tid : sched_tid = cur_tid).
        {
          unfold tcb_addr, sizeof_OS_TCB in Hsched_snapshot, Htcb.
          lia.
        }
        subst sched_tid.
        assert (Hpcp_eq : mfPCP m = pcp_idx).
        {
          rewrite <- Hdecoded_pcp.
          congruence.
        }
        assert (Horig_eq :
          mfOwnerOrigPrio m =
            Some (decode_OwnerPrio_from_cnt ecnt_in)).
        {
          rewrite Horig, Hdecoded_owner.
          reflexivity.
        }
        assert (Hentry :
          mutex_post_owner_entry_context_prop
            sg pevent0 eid ls0 ls0 pcp_idx
            (decode_OwnerPrio_from_cnt ecnt_in)
            tcbcur tcbprio).
        {
          unfold mutex_post_owner_entry_context_prop.
          split; [exact H9 |].
          split; [reflexivity |].
          split; [exact H12 |].
          split; [exact H14 |].
          exists e, m, cur_tid, cur_t.
          split; [exact PreH3 |].
          split; [exact Hused |].
          split; [exact Hevent_type |].
          split; [exact Hmutex_fields |].
          split; [exact Howner |].
          split; [exact Hpcp_eq |].
          split; [exact Horig_eq |].
          split; [exact Hsched_id |].
          split; [exact Htask_map |].
          split; [exact Htcb |].
          symmetry.
          exact Htprio.
        }
        Exists ls0.
        entailer!.
        apply derivable1_truep_intros.
      * exfalso.
        apply PreH4.
        exact Hsched_snapshot.
    + contradiction.
  - destruct (mfOwnerOrigPrio m) as [owner_orig |] eqn:Horig.
    + contradiction.
    + exfalso.
      apply PreH4.
      rewrite PreH1, Hencoded_ptr.
      unfold encode_event_ptr_value.
      rewrite Hevent_type, Hmutex_fields, Howner.
      reflexivity.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_5 : OSMutexPost_full_entail_wit_5.
Proof.
  pre_process.
  subst pcp_v.
  subst tcbprio.
  subst prio_v.
  Exists
    (result_state
      (LastSeen ls1)
      (bind
        (OSMutexPost_RdyAtPrio_atomic_cmd
          sg ls1 tcbcur (decode_OwnerPrio_from_cnt ecnt_in))
        observe_unit_void))
    ls1.
  entailer!.
  - sep_apply_l_atomic debug_truep_merge__relocation_semantics.
    exact debug_truep_merge__relocation_semantics.
  - rewrite PreH7 in H11.
    exact H11.
  - intro Hpcp.
    subst pcp_idx.
    rewrite unsigned_last_nbits_eq in PreH2 by (cbn; lia).
    contradiction.
  - apply safeExec_result_state.
    exists (RTrans_Abs ls1).
    unfold LastSeen.
    reflexivity.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_6_1 : OSMutexPost_full_entail_wit_6_1.
Proof.
  pre_process.
  subst pcp_v.
  subst prio_v.
  unfold mutex_post_owner_entry_context_prop in H11.
  destruct H11 as
    [Hstable [Hentry_eq [Hchecked [Hboundary
    [e0 [m [owner_tid [owner_t
    [Haddr [Hused [Htype [Hfields [Howner [Hpcp [Horig
    [Hcur [Howner_task [Htcb Howner_prio]]]]]]]]]]]]]]]]]].
  subst ls1.
  assert (Hstage :
    mutex_post_owner_disinherit_stage_prop
      sg pevent0 ls0 pcp_idx
      (decode_OwnerPrio_from_cnt ecnt_in) ls0).
  {
    unfold mutex_post_owner_disinherit_stage_prop.
    split; [exact Hchecked |].
    split; [exact Hboundary |].
    exists eid, e0, m, owner_tid.
    repeat split; try assumption.
    unfold OSMutexPost_disinherit_sem.
    exists owner_t.
    split; [exact Howner_task |].
    destruct (Z.eq_dec pcp_idx (osPrioMutexCeilDis sg)) as
      [Hdisabled | Henabled].
    - left.
      split.
      + rewrite Hpcp.
        exact Hdisabled.
      + reflexivity.
    - right; left.
      split.
      + rewrite Hpcp.
        exact Henabled.
      + split.
        * rewrite Howner_prio, Hpcp.
          exact PreH1.
        * reflexivity.
  }
  assert (Hpcp_not_disabled : pcp_idx <> 255).
  {
    intro Heq.
    subst pcp_idx.
    rewrite unsigned_last_nbits_eq in PreH2 by (cbn; lia).
    contradiction.
  }
  assert (Hpcp_range : 0 <= pcp_idx /\ pcp_idx < 64).
  {
    unfold valid_mutex_pcp in H4.
    destruct H4 as [Hdisabled | Hrange].
    - unfold valid_stable_glob_vars in Hstable.
      destruct Hstable as
        [_ [_ [_ [_ [_ [_ [_ [_ [Hceil _]]]]]]]]].
      rewrite Hceil in Hdisabled.
      exfalso.
      apply Hpcp_not_disabled.
      exact Hdisabled.
    - unfold valid_stable_glob_vars in Hstable.
      destruct Hstable as
        [_ [_ [_ [_ [_ [Hlowest _]]]]]].
      destruct Hrange as [Hnonneg Hlt].
      split; [exact Hnonneg | lia].
  }
  pose proof H12 as Hbundle.
  unfold UCOS2_validity_bundle in Hbundle.
  destruct Hbundle as
    [Htask_valid [Hsched_valid [Hevent_valid Hcross]]].
  assert (Hunique : task_priority_unique (TskState ls0)).
  {
    destruct Htask_valid as [Htask_range _].
    unfold valid_GlobTaskAbstractState, task_in_range in Htask_range.
    destruct Htask_range as
      [_ [_ [_ [_ [_ [_ Hunique]]]]]].
    exact Hunique.
  }
  assert (Hcanonical :
    Ucos2Verify.lib.event_wait.event_waitList_canonical
      sg (TskState ls0) (waitList e)).
  {
    pose proof H3 as Hsnapshot_facts.
    unfold event_snapshot_of_prop in Hsnapshot_facts.
    destruct Hsnapshot_facts as
      [Hused_e [Hetype_e [Hcnt_e [Hptr_e [Hgrp_e Htbl_e]]]]].
    unfold event_vaild_cond_prop, valid_GlobEventAbstractState,
      event_in_range in Hevent_valid.
    destruct Hevent_valid as
      [_ [_ [_ [_ [_ [_ [_ Hentries]]]]]]].
    specialize (Hentries eid e Hused_e).
    unfold Ucos2Verify.lib.event_wait.event_wait_entry_consistency
      in Hentries.
    exact (proj1 Hentries).
  }
  assert (Hraw :
    event_raw_snapshot_of_prop
      sg (TskState ls0) (EventState ls0) eid e
      4 ecnt_in owner_ptr egrp_in evtL_in).
  {
    apply
      (proj1
        (event_snapshot_of_prop_stable_iff_raw
          sg (TskState ls0) (EventState ls0) eid e
          4 ecnt_in owner_ptr egrp_in evtL_in
          Hcanonical Hunique)).
    exact H3.
  }
  Exists ls0.
  entailer!.
  pose proof H0 as Htask_snapshot.
  unfold task_prio_snapshot_of_prop in Htask_snapshot.
  destruct Htask_snapshot as
    [Hcur_used [Htcb_snapshot Hprio_snapshot]].
  pose proof
    (debug_prio_canonical__relocation_semantics
      sg (TskState ls0) prioL_in H) as Hprio_canonical.
  assert (Hmerge_task :
    (&( tcbcur # "os_tcb" ->ₛ "OSTCBPrio") # UChar |-> tcbprio **
     used_task_no_prio sg tcbcur cur_tid cur_t **
     task_inv_no_tid_priotbl sg (TskState ls0) cur_tid **
     store_priotbl_list sg prioL_in)
    |-- task_inv sg (TskState ls0)).
  {
    assert (Hselected_task :
      (&( tcbcur # "os_tcb" ->ₛ "OSTCBPrio") # UChar |-> tcbprio **
       used_task_no_prio sg tcbcur cur_tid cur_t)
      |--
      used_complete_task
        sg (tcb_addr sg cur_tid) cur_tid cur_t).
    {
      unfold used_complete_task, used_task_no_prio,
        task_prio_field_layout_prop in *.
      rewrite H5, Htcb_snapshot, Hprio_snapshot.
      entailer!.
    }
    sep_apply_l_atomic Hselected_task.
    rewrite Hprio_canonical.
    unfold task_inv_no_tid_priotbl, task_inv,
      store_used_task_map, store_used_task_map_missing_i,
      store_prio_tbl.
    pureIntros.
    sep_apply_l_atomic
      (store_map_merge
        (fun tid0 t0 =>
          used_complete_task sg (tcb_addr sg tid0) tid0 t0)
        cur_tid cur_t
        (inUsedTaskStates (TskState ls0)) Hcur_used).
    entailer!.
  }
  assert (Hmerge_sched :
    (&( "OSTCBCur") # Ptr |-> tcbcur **
     sched_inv_no_tcb_cur sg (TskState ls0) (SchedState ls0))
    |-- sched_inv sg (TskState ls0) (SchedState ls0)).
  {
    unfold sched_inv_no_tcb_cur, sched_inv.
    pureIntros.
    unfold store_sched_state_no_tcb_cur, store_sched_state,
      os_tcb_cur_addr in *.
    rewrite H7, Hcur, Htcb.
    entailer!.
  }
  sep_apply_l_atomic Hmerge_task.
  sep_apply_l_atomic Hmerge_sched.
  pose proof H3 as Hsnapshot_event.
  unfold event_snapshot_of_prop in Hsnapshot_event.
  destruct Hsnapshot_event as
    [Hevent_used [Hevent_type [Hevent_cnt [Hevent_ptr
    [Hevent_grp Hevent_tbl]]]]].
  pose proof H1 as Hwait_layout.
  unfold event_wait_fields_layout_prop in Hwait_layout.
  destruct Hwait_layout as [Hgrp_addr Htbl_addr].
  assert (Hmerge_wait_fields :
    (&( pevent0 # "os_event" ->ₛ "OSEventGrp") # UChar |-> egrp_in **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       0 * sizeof(UCHAR)) # UChar |-> Znth 0 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       1 * sizeof(UCHAR)) # UChar |-> Znth 1 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       2 * sizeof(UCHAR)) # UChar |-> Znth 2 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       3 * sizeof(UCHAR)) # UChar |-> Znth 3 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       4 * sizeof(UCHAR)) # UChar |-> Znth 4 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       5 * sizeof(UCHAR)) # UChar |-> Znth 5 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       6 * sizeof(UCHAR)) # UChar |-> Znth 6 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       7 * sizeof(UCHAR)) # UChar |-> Znth 7 evtL_in 0)
    |--
    used_event_rest_no_type_cnt_ptr
      sg (TskState ls0) (event_addr sg eid) eid e).
  {
    unfold used_event_rest_no_type_cnt_ptr.
    rewrite Hgrp_addr, Htbl_addr, Hevent_grp, Hevent_tbl.
    unfold encode_event_wait_tbl_values.
    cbn [Znth].
    entailer!.
  }
  sep_apply_l_atomic Hmerge_wait_fields.
  sep_apply_l_atomic
    (mutex_accept_event_rebuild__restore_and_returns
      sg (TskState ls0) (EventState ls0) eid e
      (event_addr sg eid)
      (&( pevent0 # "os_event" ->ₛ "OSEventType"))
      (&( pevent0 # "os_event" ->ₛ "OSEventPtr"))
      (&( pevent0 # "os_event" ->ₛ "OSEventCnt"))
      4 ecnt_in owner_ptr egrp_in evtL_in
      H3 H2 eq_refl).
  assert (Hmerge_global :
    (interrupt_inv sg (IntrState ls0) **
     task_inv sg (TskState ls0) **
     sched_inv sg (TskState ls0) (SchedState ls0) **
     event_inv sg (TskState ls0) (EventState ls0) **
     tick_inv sg (TickState ls0))
    |-- UCOS2_Verify_inv sg ls0).
  {
    unfold UCOS2_Verify_inv.
    entailer!.
    apply derivable1_truep_intros.
  }
  sep_apply_l_atomic Hmerge_global.
  sep_apply_l_atomic
    (UCOS2_Verify_inv_split_raw_validity sg ls0).
  unfold mutex_post_rep.
  Left.
  unfold UCOS2_raw_rep.
  entailer!.
  repeat
    sep_apply_l_atomic debug_truep_merge__relocation_semantics.
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_6_2 : OSMutexPost_full_entail_wit_6_2.
Proof.
  pre_process.
  subst pcp_v.
  subst prio_v.
  lazymatch goal with
  | Hentry :
      mutex_post_owner_entry_context_prop
        sg pevent0 eid ls0 ls_rdy_pre pcp_idx
        (decode_OwnerPrio_from_cnt ecnt_in) tcbcur tcbprio |- _ =>
      unfold mutex_post_owner_entry_context_prop in Hentry;
      destruct Hentry as
        [Hstable [Hentry_eq [Hchecked [Hboundary
        [e0 [m [owner_tid [owner_t
        [Haddr [Hused [Htype [Hfields [Howner [Hpcp [Horig
        [Hcur [Howner_task [Htcb Howner_prio]]]]]]]]]]]]]]]]]];
      subst ls_rdy_pre
  end.
  lazymatch goal with
  | Hbundle : UCOS2_validity_bundle sg ls0 |- _ =>
      pose proof Hbundle as Hbundle_facts
  end.
  unfold UCOS2_validity_bundle in Hbundle_facts.
  destruct Hbundle_facts as
    [Htask_valid [Hsched_valid [Hevent_valid Hcross]]].
  pose proof Hcross as Hcross_facts.
  unfold cross_module_consistency in Hcross_facts.
  destruct Hcross_facts as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hprotocol _]]]]]]]]].
  specialize (Hprotocol eid e0 m Hused Htype Hfields).
  destruct Hprotocol as [Hvalid_pcp _].
  rewrite Hpcp in Hvalid_pcp.
  assert (Hvalid_eid : valid_event_id sg eid).
  {
    unfold event_vaild_cond_prop, valid_GlobEventAbstractState,
      event_in_range in Hevent_valid.
    destruct Hevent_valid as [Hrange _].
    specialize (Hrange eid e0 Hused).
    exact Hrange.
  }
  assert (Hpcp_range : 0 <= pcp_idx /\ pcp_idx < 64).
  {
    unfold valid_mutex_pcp in Hvalid_pcp.
    destruct Hvalid_pcp as [Hdisabled | Hrange].
    - unfold valid_stable_glob_vars in Hstable.
      destruct Hstable as
        [_ [_ [_ [_ [_ [_ [_ [_ [Hceil _]]]]]]]]].
      rewrite Hceil in Hdisabled.
      contradiction.
    - unfold valid_stable_glob_vars in Hstable.
      destruct Hstable as
        [_ [_ [_ [_ [_ [Hlowest _]]]]]].
      destruct Hrange as [Hnonneg Hlt].
      split; [exact Hnonneg | lia].
  }
  Exists ls_rdy.
  entailer!.
  unfold mutex_post_rep.
  Right.
  exact
    (mutex_post_ready_stage_absorb_three_truep__disinherit_reservation
      sg ls0 ls_rdy).
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_7 : OSMutexPost_full_entail_wit_7.
Proof.
  pre_process.
  subst pcp_v.
  subst pevent0.
  lazymatch goal with
  | Hraw :
      event_raw_snapshot_of_prop
        sg (TskState ls_d_2) (EventState ls_d_2) eid e
        4 ecnt_in owner_ptr egrp_in evtL_in |- _ =>
      pose proof Hraw as Hraw_facts
  end.
  unfold event_raw_snapshot_of_prop in Hraw_facts.
  destruct Hraw_facts as
    [Hused [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  unfold encode_event_wait_tbl_values_or in Htbl.
  lazymatch goal with
  | Hcore :
      event_core_fields_layout_prop sg eid ?type_addr ?ptr_addr ?cnt_addr
      |- _ =>
      unfold event_core_fields_layout_prop in Hcore;
      destruct Hcore as [Htype_addr [Hptr_addr Hcnt_addr]]
  end.
  lazymatch goal with
  | Hwait :
      event_wait_fields_layout_prop sg eid ?grp_addr ?tbl_addr |- _ =>
      unfold event_wait_fields_layout_prop in Hwait;
      destruct Hwait as [Hgrp_addr Htbl_addr]
  end.
  pose proof
    (prioTbl_to_addrs_rel__disinherit_reservation
      sg (TskState ls_d_2)) as Hprio_rel.
  Exists
    (prioTbl_to_addrs sg (prioTbl (TskState ls_d_2)))
    ls_d_2.
  entailer!.
  assert (HaddTT : forall P : Assertion, P |-- TT ** P).
  {
    intro P.
    entailer!.
    apply derivable1_truep_intros.
  }
  unfold mutex_post_rep, mutex_post_rep_no_priotbl_no_event.
  unfold UCOS2_raw_rep, UCOS2_raw_ready_prio_stage.
  Split.
  - sep_apply_l_atomic
      (task_raw_rep_split_priotbl sg (TskState ls_d_2)).
    sep_apply_l_atomic
      (event_raw_rep_split_eid
        sg (TskState ls_d_2) (EventState ls_d_2) eid e Hused).
    unfold store_prio_tbl, used_complete_event_raw.
    Left.
    rewrite Htype_addr, Hptr_addr, Hcnt_addr, Hgrp_addr, Htbl_addr.
    rewrite <- Htype, <- Hcnt, <- Hptr, <- Hgrp.
    rewrite Htbl.
    cbn [Znth].
    entailer!.
    all: apply HaddTT.
  - sep_apply_l_atomic
      (task_raw_rep_split_priotbl sg (TskState ls_d_2)).
    sep_apply_l_atomic
      (event_raw_rep_split_eid
        sg (TskState ls_d_2) (EventState ls_d_2) eid e Hused).
    unfold store_prio_tbl, used_complete_event_raw.
    Right.
    rewrite Htype_addr, Hptr_addr, Hcnt_addr, Hgrp_addr, Htbl_addr.
    rewrite <- Htype, <- Hcnt, <- Hptr, <- Hgrp.
    rewrite Htbl.
    cbn [Znth].
    entailer!.
    all: apply HaddTT.
  - unfold event_core_fields_layout_prop.
    repeat split; assumption.
  - unfold event_wait_fields_layout_prop.
    split; assumption.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_8_1 : OSMutexPost_full_entail_wit_8_1.
Proof.
  left.
  pre_process.
  subst pcp_v.
  subst prio_v.
  unfold mutex_post_owner_entry_context_prop in H11.
  destruct H11 as
    [Hstable [Hentry_eq [Hchecked [Hboundary
    [e0 [m [owner_tid [owner_t
    [Haddr [Hused [Htype [Hfields [Howner [Hpcp [Horig
    [Hcur [Howner_task [Htcb Howner_prio]]]]]]]]]]]]]]]]]].
  subst ls1.
  assert (Hpcp_disabled : pcp_idx = osPrioMutexCeilDis sg).
  {
    unfold valid_mutex_pcp in H4.
    destruct H4 as [Hdisabled | Hrange].
    - exact Hdisabled.
    - destruct Hrange as [Hnonneg Hlt].
      unfold valid_stable_glob_vars in Hstable.
      destruct Hstable as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hceil _]]]]]]]]].
      rewrite unsigned_last_nbits_eq in PreH1.
      + rewrite Hlowest in Hlt.
        rewrite Hceil.
        lia.
      + split; [exact Hnonneg |].
        rewrite Hlowest in Hlt.
        change (pcp_idx < 4294967296).
        lia.
  }
  assert (Hstage :
    mutex_post_owner_disinherit_stage_prop
      sg pevent0 ls0 pcp_idx
      (decode_OwnerPrio_from_cnt ecnt_in) ls0).
  {
    unfold mutex_post_owner_disinherit_stage_prop.
    split; [exact Hchecked |].
    split; [exact Hboundary |].
    exists eid, e0, m, owner_tid.
    repeat split; try assumption.
    unfold OSMutexPost_disinherit_sem.
    exists owner_t.
    split; [exact Howner_task |].
    left.
    split.
    - rewrite Hpcp.
      exact Hpcp_disabled.
    - reflexivity.
  }
  assert (Hreservation :
    mutex_post_reservation_stage_prop sg eid ls0 ls0).
  {
    unfold mutex_post_reservation_stage_prop,
      OSMutexPost_reservation_sem.
    exists e0, m, owner_tid, (TskState ls0).
    repeat split; try assumption.
    - destruct (TskState ls0) as
        [used unused head tbl count] eqn:Htsk.
      cbn in *.
      f_equal.
      apply functional_extensionality.
      intro p.
      rewrite Hpcp, Hpcp_disabled, Z.eqb_refl.
      reflexivity.
    - destruct ls0.
      reflexivity.
  }
  pose proof H12 as Hbundle.
  unfold UCOS2_validity_bundle in Hbundle.
  destruct Hbundle as
    [Htask_valid [Hsched_valid [Hevent_valid Hcross]]].
  assert (Hunique : task_priority_unique (TskState ls0)).
  {
    destruct Htask_valid as [Htask_range _].
    unfold valid_GlobTaskAbstractState, task_in_range in Htask_range.
    destruct Htask_range as
      [_ [_ [_ [_ [_ [_ Hunique]]]]]].
    exact Hunique.
  }
  assert (Hcanonical :
    Ucos2Verify.lib.event_wait.event_waitList_canonical
      sg (TskState ls0) (waitList e)).
  {
    pose proof H3 as Hsnapshot_facts.
    unfold event_snapshot_of_prop in Hsnapshot_facts.
    destruct Hsnapshot_facts as
      [Hused_e [Hetype_e [Hcnt_e [Hptr_e [Hgrp_e Htbl_e]]]]].
    unfold event_vaild_cond_prop, valid_GlobEventAbstractState,
      event_in_range in Hevent_valid.
    destruct Hevent_valid as
      [_ [_ [_ [_ [_ [_ [_ Hentries]]]]]]].
    specialize (Hentries eid e Hused_e).
    unfold Ucos2Verify.lib.event_wait.event_wait_entry_consistency
      in Hentries.
    exact (proj1 Hentries).
  }
  assert (Hraw :
    event_raw_snapshot_of_prop
      sg (TskState ls0) (EventState ls0) eid e
      4 ecnt_in owner_ptr egrp_in evtL_in).
  {
    apply
      (proj1
        (event_snapshot_of_prop_stable_iff_raw
          sg (TskState ls0) (EventState ls0) eid e
          4 ecnt_in owner_ptr egrp_in evtL_in
          Hcanonical Hunique)).
    exact H3.
  }
  pose proof Hraw as Hraw_facts.
  unfold event_raw_snapshot_of_prop in Hraw_facts.
  destruct Hraw_facts as
    [Hraw_used [Hraw_type [Hraw_cnt
      [Hraw_ptr [Hraw_grp Hraw_tbl]]]]].
  unfold encode_event_wait_tbl_values_or in Hraw_tbl.
  pose proof H2 as Hcore_layout.
  unfold event_core_fields_layout_prop in Hcore_layout.
  destruct Hcore_layout as
    [Htype_addr [Hptr_addr Hcnt_addr]].
  pose proof H1 as Hwait_layout_raw.
  unfold event_wait_fields_layout_prop in Hwait_layout_raw.
  destruct Hwait_layout_raw as [Hgrp_addr_raw Htbl_addr_raw].
  pose proof H0 as Htask_snapshot.
  unfold task_prio_snapshot_of_prop in Htask_snapshot.
  destruct Htask_snapshot as
    [Hcur_used [Htcb_snapshot Hprio_snapshot]].
  pose proof
    (debug_prio_canonical__relocation_semantics
      sg (TskState ls0) prioL_in H) as Hprio_canonical.
  assert (Hmerge_task :
    (&( tcbcur # "os_tcb" ->ₛ "OSTCBPrio") # UChar |-> tcbprio **
     used_task_no_prio sg tcbcur cur_tid cur_t **
     task_inv_no_tid_priotbl sg (TskState ls0) cur_tid **
     store_priotbl_list sg prioL_in)
    |-- task_inv sg (TskState ls0)).
  {
    assert (Hselected_task :
      (&( tcbcur # "os_tcb" ->ₛ "OSTCBPrio") # UChar |-> tcbprio **
       used_task_no_prio sg tcbcur cur_tid cur_t)
      |--
      used_complete_task
        sg (tcb_addr sg cur_tid) cur_tid cur_t).
    {
      unfold used_complete_task, used_task_no_prio,
        task_prio_field_layout_prop in *.
      rewrite H5, Htcb_snapshot, Hprio_snapshot.
      entailer!.
    }
    sep_apply_l_atomic Hselected_task.
    rewrite Hprio_canonical.
    unfold task_inv_no_tid_priotbl, task_inv,
      store_used_task_map, store_used_task_map_missing_i,
      store_prio_tbl.
    pureIntros.
    sep_apply_l_atomic
      (store_map_merge
        (fun tid0 t0 =>
          used_complete_task sg (tcb_addr sg tid0) tid0 t0)
        cur_tid cur_t
        (inUsedTaskStates (TskState ls0)) Hcur_used).
    entailer!.
  }
  assert (Hmerge_sched :
    (&( "OSTCBCur") # Ptr |-> tcbcur **
     sched_inv_no_tcb_cur sg (TskState ls0) (SchedState ls0))
    |-- sched_inv sg (TskState ls0) (SchedState ls0)).
  {
    unfold sched_inv_no_tcb_cur, sched_inv.
    pureIntros.
    unfold store_sched_state_no_tcb_cur, store_sched_state,
      os_tcb_cur_addr in *.
    rewrite H7, Hcur, Htcb.
    entailer!.
  }
  sep_apply_l_atomic Hmerge_task.
  sep_apply_l_atomic Hmerge_sched.
  pose proof H3 as Hsnapshot_event.
  unfold event_snapshot_of_prop in Hsnapshot_event.
  destruct Hsnapshot_event as
    [Hevent_used [Hevent_type [Hevent_cnt [Hevent_ptr
    [Hevent_grp Hevent_tbl]]]]].
  pose proof H1 as Hwait_layout.
  unfold event_wait_fields_layout_prop in Hwait_layout.
  destruct Hwait_layout as [Hgrp_addr Htbl_addr].
  assert (Hmerge_wait_fields :
    (&( pevent0 # "os_event" ->ₛ "OSEventGrp") # UChar |-> egrp_in **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       0 * sizeof(UCHAR)) # UChar |-> Znth 0 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       1 * sizeof(UCHAR)) # UChar |-> Znth 1 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       2 * sizeof(UCHAR)) # UChar |-> Znth 2 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       3 * sizeof(UCHAR)) # UChar |-> Znth 3 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       4 * sizeof(UCHAR)) # UChar |-> Znth 4 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       5 * sizeof(UCHAR)) # UChar |-> Znth 5 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       6 * sizeof(UCHAR)) # UChar |-> Znth 6 evtL_in 0 **
     (&( pevent0 # "os_event" ->ₛ "OSEventTbl") +
       7 * sizeof(UCHAR)) # UChar |-> Znth 7 evtL_in 0)
    |--
    used_event_rest_no_type_cnt_ptr
      sg (TskState ls0) (event_addr sg eid) eid e).
  {
    unfold used_event_rest_no_type_cnt_ptr.
    rewrite Hgrp_addr, Htbl_addr, Hevent_grp, Hevent_tbl.
    unfold encode_event_wait_tbl_values.
    cbn [Znth].
    entailer!.
  }
  sep_apply_l_atomic Hmerge_wait_fields.
  sep_apply_l_atomic
    (mutex_accept_event_rebuild__restore_and_returns
      sg (TskState ls0) (EventState ls0) eid e
      (event_addr sg eid)
      (&( pevent0 # "os_event" ->ₛ "OSEventType"))
      (&( pevent0 # "os_event" ->ₛ "OSEventPtr"))
      (&( pevent0 # "os_event" ->ₛ "OSEventCnt"))
      4 ecnt_in owner_ptr egrp_in evtL_in
      H3 H2 eq_refl).
  assert (Hmerge_global :
    (interrupt_inv sg (IntrState ls0) **
     task_inv sg (TskState ls0) **
     sched_inv sg (TskState ls0) (SchedState ls0) **
     event_inv sg (TskState ls0) (EventState ls0) **
     tick_inv sg (TickState ls0))
    |-- UCOS2_Verify_inv sg ls0).
  {
    unfold UCOS2_Verify_inv.
    entailer!.
    apply derivable1_truep_intros.
  }
  sep_apply_l_atomic Hmerge_global.
  sep_apply_l_atomic
    (UCOS2_Verify_inv_split_raw_validity sg ls0).
  pureIntros.
  unfold UCOS2_raw_rep.
  sep_apply_l_atomic
    (event_raw_rep_split_eid
      sg (TskState ls0) (EventState ls0) eid e Hraw_used).
  unfold used_complete_event_raw.
  rewrite Htype_addr, Hptr_addr, Hcnt_addr,
    Hgrp_addr_raw, Htbl_addr_raw.
  rewrite <- Hraw_type, <- Hraw_cnt, <- Hraw_ptr, <- Hraw_grp.
  rewrite Hraw_tbl.
  cbn [Znth].
  repeat
    sep_apply_l_atomic debug_truep_merge__relocation_semantics.
  Exists ls0 ls0.
  entailer!.
  assert (HaddTT : forall P : Assertion, P |-- TT ** P).
  {
    intro P.
    entailer!.
    apply derivable1_truep_intros.
  }
  unfold mutex_post_rep_no_event.
  Left.
  entailer!.
  all: try solve
    [ repeat
        sep_apply_l_atomic debug_truep_merge__relocation_semantics;
      entailer!
    | unfold event_raw_snapshot_of_prop;
      repeat split; try assumption; try reflexivity
    | unfold event_core_fields_layout_prop;
      repeat split; reflexivity
    | unfold event_wait_fields_layout_prop;
      split; reflexivity ].
  repeat lazymatch goal with
  | |- ?P |-- TT ** ?Q =>
      apply
        (mutex_post_entail_add_truep__disinherit_reservation P Q)
  end.
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_8_2 : OSMutexPost_full_entail_wit_8_2.
Proof.
  right.
  pre_process.
  subst pcp_v.
  pose proof H4 as Hstage_facts.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage_facts.
  destruct Hstage_facts as
    [Hchecked [Hboundary
      [eid0 [e0 [m [owner_tid
        [Haddr [Hused0 [Htype0 [Hfields0 [Howner0 [Hpcp0
          [Horig0 [Hcur0 Hdis]]]]]]]]]]]]]].
  assert (Heid : eid0 = eid).
  {
    rewrite PreH5 in Haddr.
    unfold event_addr, sizeof_OS_EVENT in Haddr.
    lia.
  }
  subst eid0.
  assert (Hevent_preserved : EventState ls_d_2 = EventState ls0).
  {
    unfold OSMutexPost_disinherit_sem in Hdis.
    destruct Hdis as [cur_t [Hget Hbranch]].
    destruct Hbranch as
      [[Hdisabled Hpost] |
       [[Henabled [Hnot Hpost]] |
        [Henabled [Hat [orig [Horig Hexec]]]]]].
    - subst ls_d_2.
      reflexivity.
    - subst ls_d_2.
      reflexivity.
    - unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
      destruct Hexec as
        [t' [Hcur' [Hcurprio [Hget' [Hlo [Hhi [Ht' Hpost]]]]]]].
      cbv zeta in Hpost.
      rewrite Hpost.
      reflexivity.
  }
  assert (Hused_d :
    inUsedEventStates (EventState ls_d_2) eid = Some e0).
  {
    rewrite Hevent_preserved.
    exact Hused0.
  }
  assert (Hpcp_enabled : pcp_idx <> osPrioMutexCeilDis sg).
  {
    intro Heq.
    unfold valid_stable_glob_vars in H8.
    destruct H8 as
      [_ [_ [_ [_ [_ [_ [_ [_ [Hceil _]]]]]]]]].
    rewrite Hceil in Heq.
    contradiction.
  }
  set (tsk_reserved :=
    {| inUsedTaskStates := inUsedTaskStates (TskState ls_d_2);
       unUsedTaskStates := unUsedTaskStates (TskState ls_d_2);
       tcbListHead := tcbListHead (TskState ls_d_2);
       prioTbl := fun p =>
         if (negb (Z.eqb (mfPCP m) (osPrioMutexCeilDis sg)) &&
             Z.eqb p (mfPCP m))%bool
         then PTReserved
         else prioTbl (TskState ls_d_2) p;
       taskCount := taskCount (TskState ls_d_2) |}).
  set (ls2 := replace_TskS tsk_reserved ls_d_2).
  assert (Hreservation :
    mutex_post_reservation_stage_prop sg eid ls_d_2 ls2).
  {
    unfold mutex_post_reservation_stage_prop,
      OSMutexPost_reservation_sem.
    exists e0, m, owner_tid, tsk_reserved.
    repeat split; try assumption; reflexivity.
  }
  assert (Htbl_shape :
    prioTbl tsk_reserved =
      (fun q =>
        if Z.eqb q pcp_idx
        then PTReserved
        else prioTbl (TskState ls_d_2) q)).
  {
    subst tsk_reserved.
    cbn.
    apply functional_extensionality.
    intro q.
    rewrite Hpcp0.
    rewrite (proj2
      (Z.eqb_neq pcp_idx (osPrioMutexCeilDis sg)) Hpcp_enabled).
    cbn.
    reflexivity.
  }
  assert (Hrange : 0 <= pcp_idx < OS_PRIO_TBL_SIZE).
  {
    unfold OS_PRIO_TBL_SIZE.
    lia.
  }
  assert (Hrel_reserved :
    prio_tbl_list_rel sg tsk_reserved
      (replace_Znth pcp_idx 1 prioL_d)).
  {
    eapply
      prio_tbl_list_rel_update_reserved__disinherit_reservation.
    - exact Hrange.
    - exact Htbl_shape.
    - exact H3.
  }
  assert (Hraw_reserved :
    event_raw_snapshot_of_prop
      sg (TskState ls2) (EventState ls2) eid e
      4 ecnt_in owner_ptr egrp_in evtL_in).
  {
    pose proof H1 as Hraw_facts.
    unfold event_raw_snapshot_of_prop in Hraw_facts |- *.
    destruct Hraw_facts as
      [Hraw_used [Hraw_type [Hraw_cnt
        [Hraw_ptr [Hraw_grp Hraw_tbl]]]]].
    repeat split; try assumption.
    rewrite Hraw_grp.
    apply debug_event_grp_ext_in__relocation_semantics.
    intros tid Hin.
    subst ls2.
    reflexivity.
  }
  assert (Hlen : Zlength prioL_d = OS_PRIO_TBL_SIZE).
  {
    exact (proj1 H3).
  }
  unfold os_tcb_prio_tbl_addr in H7.
  rewrite H7.
  sep_apply_l_atomic
    (debug_store_priotbl_merge_c_cell__relocation_semantics
      sg prioL_d pcp_idx 1 Hrange Hlen).
  pose proof
    (debug_prio_canonical__relocation_semantics
      sg tsk_reserved (replace_Znth pcp_idx 1 prioL_d)
      Hrel_reserved) as Hcanonical_reserved.
  assert (Hstore_reserved :
    store_priotbl_list sg (replace_Znth pcp_idx 1 prioL_d)
    |-- store_prio_tbl sg (prioTbl tsk_reserved)).
  {
    unfold store_prio_tbl.
    rewrite <- Hcanonical_reserved.
    entailer!.
  }
  sep_apply_l_atomic Hstore_reserved.
  assert (Hmap :
    inUsedTaskStates (TskState ls_d_2) =
      inUsedTaskStates tsk_reserved).
  {
    subst tsk_reserved.
    reflexivity.
  }
  assert (Htask_no_eq :
    task_raw_rep_no_priotbl sg (TskState ls_d_2) =
      task_raw_rep_no_priotbl sg tsk_reserved).
  {
    subst tsk_reserved.
    unfold task_raw_rep_no_priotbl.
    reflexivity.
  }
  sep_apply_l_atomic
    (mutex_post_rep_reservation_merge__disinherit_reservation
      sg ls0 ls_d_2 tsk_reserved eid Hmap Htask_no_eq).
  Exists ls2 ls_d_2.
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_9 : OSMutexPost_full_entail_wit_9.
Proof.
  pre_process.
  pose proof
    (post_wake_returned_prio_range__handover_commit
      sg pevent0 ls0 pcp_idx (decode_OwnerPrio_from_cnt ecnt_in)
      ls_d eid ls retval canonical_waiter_2 table_owner_2 ls_wake_2
      H1 H2 H10 H9 H11) as Hretval.
  destruct
    (mutex_post_count_commit_snapshot__handover_commit
      sg pevent0 ls0 pcp_idx ecnt_in owner_ptr egrp_in evtL_in
      ls_d eid ls e retval canonical_waiter_2 table_owner_2
      ls_wake_2 e_h_2 cnt_out ptr_out egrp_out evtL_out
      H1 PreH1 H H10 H9 H8 H11 H7 Hretval)
    as [e_cnt Hcount_snapshot].
  cbn zeta in Hcount_snapshot.
  destruct Hcount_snapshot as [Hcount Hsnapshot].
  pose proof
    (prioTbl_to_addrs_rel__handover_commit sg (TskState ls_wake_2))
    as Hprio_rel.
  pose proof H11 as Hwake_detail.
  unfold mutex_post_wake_step_prop, OSMutexPost_wake_sem,
    atomic_event_task_rdy, atomic_event_task_rdy_one in Hwake_detail.
  destruct Hwake_detail as
    (e_before & e_after & canonical_t & table_t & table_t' &
     Hevent & Hpend & Hnonempty & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & He_after & Hls_wake).
  pose proof Hprio_rel as Hprio_lookup.
  unfold prio_tbl_list_rel in Hprio_lookup.
  destruct Hprio_lookup as [_ Hprio_lookup].
  specialize (Hprio_lookup retval Hretval).
  cbv zeta in Hls_wake.
  rewrite Hls_wake in Hprio_lookup.
  cbn in Hprio_lookup.
  rewrite Htable_slot in Hprio_lookup.
  cbn in Hprio_lookup.
  unfold mutex_post_handover_residual.
  sep_apply_l_atomic
    (task_raw_rep_split_priotbl sg (TskState ls_wake_2)).
  sep_apply_l_atomic
    (event_raw_rep_no_eid_update__handover_commit
      sg (TskState ls_wake_2) (EventState ls_wake_2) eid e_cnt).
  Exists (prioTbl_to_addrs sg
      (TaskStateDef.prioTbl (TskState ls_wake_2)))
    e_cnt
    (Z.lor (Z.land ecnt_in 65280)
      (unsigned_last_nbits retval 16))
    owner_ptr egrp_out evtL_out
    (replace_EventS
      (update_event_field_raw (EventState ls_wake_2) eid e_cnt)
      ls_wake_2)
    canonical_waiter_2 table_owner_2 ls_wake_2 ls ls_d.
  unfold mutex_post_handover_residual_no_priotbl.
  unfold store_prio_tbl.
  entailer!.
  - cbn [replace_EventS].
    unfold replace_EventS.
    cbn.
    repeat rewrite replace_EventS_other_Intr.
    repeat rewrite replace_EventS_other_Tsk.
    repeat rewrite replace_EventS_other_Sched.
    repeat rewrite replace_EventS_EventState.
    repeat rewrite replace_EventS_other_Tick.
    cancel
      (interrupt_inv sg (IntrState ls_wake_2)).
    cancel
      (task_raw_rep_no_priotbl sg (TskState ls_wake_2)).
    cancel
      (sched_raw_ready_prio_stage
        sg (SchedState ls0) (SchedState ls_wake_2)
        (TskState ls_wake_2)).
    cancel
      (event_raw_rep_no_eid
        sg (TskState ls_wake_2)
        (update_event_field_raw
          (EventState ls_wake_2) eid e_cnt) eid).
    cancel
      (tick_inv sg (TickState ls_wake_2)).
    apply derivable1_truep_intros.
  - rewrite Hls_wake.
    cbn.
    exact Hprio_lookup.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_10 : OSMutexPost_full_entail_wit_10.
Proof.
  pre_process.
  destruct
    (mutex_post_owner_commit_snapshot__handover_commit
      sg eid ls_d0 ls_r_2 prio_v canonical_waiter_2 table_owner_2
      ls_wake_2 ls_cnt_2 e_h_2 cnt_h_2 ptr_h_2 egrp_h evtL_h
      H8 H6 H5 H4) as [e_owner Howner_snapshot].
  cbn zeta in Howner_snapshot.
  destruct Howner_snapshot as [Howner Hsnapshot_owner].
  set (ls_owner :=
    replace_EventS
      (update_event_field_raw (EventState ls_cnt_2) eid e_owner)
      ls_cnt_2).
  assert (Hhandover :
    mutex_post_handover_step_prop
      sg eid ls_d0 prio_v canonical_waiter_2 table_owner_2 ls_owner).
  {
    unfold mutex_post_handover_step_prop, OSMutexPost_handover_sem.
    exists ls_r_2, ls_wake_2, ls_cnt_2.
    split; [exact H8|].
    split; [exact H6|].
    split; [exact H5|].
    unfold ls_owner.
    exact Howner.
  }
  assert (Hcrit : crit_rel_task_event_sched ls0 ls_owner).
  {
    unfold ls_owner.
    eapply mutex_post_handover_crit_rel__handover_commit;
      eassumption.
  }
  pose proof H2 as Hprio.
  unfold prio_tbl_list_rel in Hprio.
  destruct Hprio as [Hlen Hlookup].
  assert (Hrange : priotbl_index_in_range prio_v) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  unfold os_tcb_prio_tbl_addr in H11.
  rewrite H11.
  cbn [sizeof_front_end_type].
  sepcon_lift (store_priotbl_list_missing_i sg prioL_h prio_v).
  sepcon_lift
    ((g_OSTCBPrioTbl sg + prio_v * 4) # Ptr |->
      tcb_addr sg table_owner_2).
  pose proof
    (store_priotbl_list_merge
      sg prioL_h prio_v (tcb_addr sg table_owner_2) Hrange Hlen)
    as Hmerge_prio.
  unfold priotbl_element_store, sizeof_OSTCB_ptr in Hmerge_prio.
  cbn [sizeof_front_end_type] in Hmerge_prio.
  sep_apply_l_atomic Hmerge_prio.
  assert (Hreplace :
    replace_Znth prio_v (tcb_addr sg table_owner_2) prioL_h = prioL_h).
  {
    rewrite <- PreH6.
    apply replace_Znth_Znth.
  }
  rewrite Hreplace.
  unfold mutex_post_handover_residual_no_priotbl.
  sep_apply_l_atomic
    (event_raw_rep_no_eid_update__handover_commit
      sg (TskState ls_cnt_2) (EventState ls_cnt_2) eid e_owner).
  pose proof Hsnapshot_owner as Hsnap.
  unfold event_raw_snapshot_of_prop in Hsnap.
  destruct Hsnap as
    [Hget_owner [Htype_owner [Hcnt_owner
      [Hptr_owner [Hgrp_owner Htbl_owner]]]]].
  unfold event_core_fields_layout_prop in H0.
  destruct H0 as [Htype_addr [Hptr_addr Hcnt_addr]].
  unfold event_wait_fields_layout_prop in H.
  destruct H as [Hgrp_addr Htbl_addr].
  Exists e_owner cnt_h_2 (tcb_addr sg table_owner_2) egrp_h evtL_h
    ls_owner ls_cnt_2 canonical_waiter_2 table_owner_2
    ls_wake_2 ls_r_2 ls_d0.
  entailer!.
  - unfold UCOS2_raw_ready_prio_stage.
    unfold used_complete_event_raw.
    unfold encode_event_wait_tbl_values_or in Htbl_owner.
    cbn [Znth] in Htbl_owner.
    rewrite Htype_addr, Hptr_addr, Hcnt_addr, Hgrp_addr, Htbl_addr.
    rewrite Hcnt_owner, Hptr_owner, Hgrp_owner.
    inversion Htbl_owner.
    subst evtL_h.
    cbn [Znth].
    repeat rewrite Z.mul_1_r.
    repeat rewrite replace_EventS_other_Tsk.
    match goal with
    | |- context [Znth 0 ?l 0] =>
        assert (Hnth0 : Znth 0 l 0 =
          encode_event_wait_tbl_at_or (waitList e_owner)
            (TskState ls_cnt_2) 0) by reflexivity;
        rewrite Hnth0
    end.
    match goal with
    | |- context [Znth 1 ?l 0] =>
        assert (Hnth1 : Znth 1 l 0 =
          encode_event_wait_tbl_at_or (waitList e_owner)
            (TskState ls_cnt_2) 1) by reflexivity;
        rewrite Hnth1
    end.
    match goal with
    | |- context [Znth 2 ?l 0] =>
        assert (Hnth2 : Znth 2 l 0 =
          encode_event_wait_tbl_at_or (waitList e_owner)
            (TskState ls_cnt_2) 2) by reflexivity;
        rewrite Hnth2
    end.
    match goal with
    | |- context [Znth 3 ?l 0] =>
        assert (Hnth3 : Znth 3 l 0 =
          encode_event_wait_tbl_at_or (waitList e_owner)
            (TskState ls_cnt_2) 3) by reflexivity;
        rewrite Hnth3
    end.
    match goal with
    | |- context [Znth 4 ?l 0] =>
        assert (Hnth4 : Znth 4 l 0 =
          encode_event_wait_tbl_at_or (waitList e_owner)
            (TskState ls_cnt_2) 4) by reflexivity;
        rewrite Hnth4
    end.
    match goal with
    | |- context [Znth 5 ?l 0] =>
        assert (Hnth5 : Znth 5 l 0 =
          encode_event_wait_tbl_at_or (waitList e_owner)
            (TskState ls_cnt_2) 5) by reflexivity;
        rewrite Hnth5
    end.
    match goal with
    | |- context [Znth 6 ?l 0] =>
        assert (Hnth6 : Znth 6 l 0 =
          encode_event_wait_tbl_at_or (waitList e_owner)
            (TskState ls_cnt_2) 6) by reflexivity;
        rewrite Hnth6
    end.
    match goal with
    | |- context [Znth 7 ?l 0] =>
        assert (Hnth7 : Znth 7 l 0 =
          encode_event_wait_tbl_at_or (waitList e_owner)
            (TskState ls_cnt_2) 7) by reflexivity;
        rewrite Hnth7
    end.
    assert (Hget_owner_raw :
      inUsedEventStates
        (update_event_field_raw (EventState ls_cnt_2) eid e_owner) eid =
      Some e_owner).
    {
      unfold update_event_field_raw.
      cbn.
      rewrite Z.eqb_refl.
      reflexivity.
    }
    pose proof
      (event_raw_rep_merge_eid
        sg (TskState ls_cnt_2)
        (update_event_field_raw (EventState ls_cnt_2) eid e_owner)
        eid e_owner Hget_owner_raw) as Hevent_merge.
    unfold used_complete_event_raw in Hevent_merge.
    rewrite <- Htype_owner in Hevent_merge.
    L_sepcon_lift'
      (event_raw_rep_no_eid sg (TskState ls_cnt_2)
        (update_event_field_raw (EventState ls_cnt_2) eid e_owner) eid).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventTbl_off + 7) # UChar |->
        encode_event_wait_tbl_at_or (waitList e_owner)
          (TskState ls_cnt_2) 7).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventTbl_off + 6) # UChar |->
        encode_event_wait_tbl_at_or (waitList e_owner)
          (TskState ls_cnt_2) 6).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventTbl_off + 5) # UChar |->
        encode_event_wait_tbl_at_or (waitList e_owner)
          (TskState ls_cnt_2) 5).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventTbl_off + 4) # UChar |->
        encode_event_wait_tbl_at_or (waitList e_owner)
          (TskState ls_cnt_2) 4).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventTbl_off + 3) # UChar |->
        encode_event_wait_tbl_at_or (waitList e_owner)
          (TskState ls_cnt_2) 3).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventTbl_off + 2) # UChar |->
        encode_event_wait_tbl_at_or (waitList e_owner)
          (TskState ls_cnt_2) 2).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventTbl_off + 1) # UChar |->
        encode_event_wait_tbl_at_or (waitList e_owner)
          (TskState ls_cnt_2) 1).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventTbl_off + 0) # UChar |->
        encode_event_wait_tbl_at_or (waitList e_owner)
          (TskState ls_cnt_2) 0).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventGrp_off) # UChar |->
        encode_event_wait_grp (waitList e_owner) (TskState ls_cnt_2)).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventCnt_off) # UShort |->
        encode_event_cnt_value e_owner).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventPtr_off) # Ptr |->
        encode_event_ptr_value sg e_owner).
    L_sepcon_lift'
      ((event_addr sg eid + OSEventType_off) # UChar |-> 4).
    repeat rewrite derivable1_sepcon_assoc1.
    rewrite Hevent_merge.
    pose proof
      (prioTbl_to_addrs_rel__handover_commit sg (TskState ls_cnt_2))
      as Hcanonical_prio.
    unfold prio_tbl_list_rel in Hcanonical_prio.
    destruct Hcanonical_prio as [Hcanonical_len Hcanonical_lookup].
    assert (HprioL_eq :
      prioL_h =
      prioTbl_to_addrs sg (TaskStateDef.prioTbl (TskState ls_cnt_2))).
    {
      apply (proj2
        (list_eq_ext prioL_h
          (prioTbl_to_addrs sg
            (TaskStateDef.prioTbl (TskState ls_cnt_2))) 0)).
      split.
      - transitivity OS_PRIO_TBL_SIZE.
        + exact Hlen.
        + symmetry. exact Hcanonical_len.
      - intros i Hi.
        assert (Hirange : 0 <= i < OS_PRIO_TBL_SIZE).
        {
          rewrite <- Hlen.
          exact Hi.
        }
        rewrite Hlookup by exact Hirange.
        rewrite Hcanonical_lookup by exact Hirange.
        reflexivity.
    }
    rewrite HprioL_eq.
    unfold ls_owner.
    repeat rewrite replace_EventS_other_Intr.
    repeat rewrite replace_EventS_other_Tsk.
    repeat rewrite replace_EventS_other_Sched.
    repeat rewrite replace_EventS_EventState.
    repeat rewrite replace_EventS_other_Tick.
    unfold task_raw_rep, task_raw_rep_no_priotbl, store_prio_tbl.
    entailer!.
  - unfold event_core_fields_layout_prop.
    auto.
  - unfold event_wait_fields_layout_prop.
    auto.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_11 : OSMutexPost_full_entail_wit_11.
Proof.
  pre_process.
  Exists e_h_2 cnt_h_2 ptr_h_2 grp_h_2 tbl_h
    canonical_waiter_2 table_owner_2 ls_h_2 ls_r_2 ls_d_2.
  entailer!.
  - unfold UCOS2_raw_ready_prio_stage.
    cancel (interrupt_inv sg (IntrState ls_h_2)).
    cancel (task_raw_rep sg (TskState ls_h_2)).
    cancel (sched_raw_ready_prio_stage
      sg (SchedState ls0) (SchedState ls_h_2) (TskState ls_h_2)).
    cancel (event_raw_rep sg (TskState ls_h_2) (EventState ls_h_2)).
    cancel (tick_inv sg (TickState ls_h_2)).
    apply derivable1_truep_intros.
  - subst pcp_idx.
    intro Hpcp.
    subst pcp_v.
    cbv [unsigned_last_nbits] in PreH3.
    contradiction.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_12_1 : OSMutexPost_full_entail_wit_12_1.
Proof.
  pre_process.
  Left.
  Exists e_h_2 cnt_h_2 ptr_h_2 grp_h_2 tbl_h
    canonical_waiter_2 table_owner_2 ls_h_2 ls_r_2 ls_d_2.
  entailer!.
  unfold UCOS2_raw_ready_prio_stage.
  cancel (interrupt_inv sg (IntrState ls_h_2)).
  cancel (task_raw_rep sg (TskState ls_h_2)).
  cancel (sched_raw_ready_prio_stage
    sg (SchedState ls0) (SchedState ls_h_2) (TskState ls_h_2)).
  cancel (event_raw_rep sg (TskState ls_h_2) (EventState ls_h_2)).
  cancel (tick_inv sg (TickState ls_h_2)).
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_12_2 : OSMutexPost_full_entail_wit_12_2.
Proof.
  pre_process.
  match goal with
  | Hvalid : UCOS2_validity_bundle sg ls0 |- _ =>
      pose proof Hvalid as Hvalid0
  end.
  match goal with
  | Hstage :
      mutex_post_owner_disinherit_stage_prop
        sg pevent0 ls0 pcp_idx _ _ |- _ =>
      pose proof Hstage as Hstage0
  end.
  unfold UCOS2_validity_bundle in Hvalid0.
  destruct Hvalid0 as [_ [_ [_ Hcross]]].
  unfold cross_module_consistency in Hcross.
  destruct Hcross as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hprotocol _]]]]]]]]].
  unfold mutex_post_owner_disinherit_stage_prop in Hstage0.
  destruct Hstage0 as
    [_ [_ [eid0 [e0 [m0 [cur_tid0
      [_ [Hevent0 [Htype0 [Hfields0
        [_ [Hpcp0 [_ [_ _]]]]]]]]]]]]]].
  specialize (Hprotocol eid0 e0 m0 Hevent0 Htype0 Hfields0).
  destruct Hprotocol as [Hpcp_valid _].
  rewrite Hpcp0 in Hpcp_valid.
  match goal with
  | Hstable : valid_stable_glob_vars sg |- _ =>
      pose proof Hstable as Hstable0
  end.
  unfold valid_stable_glob_vars in Hstable0.
  destruct Hstable0 as
    [_ [_ [_ [_ [Hlowest_range
      [_ [_ [_ [Hdisabled _]]]]]]]]].
  assert (Hpcp255 : pcp_idx = 255).
  {
    subst pcp_idx.
    unfold valid_mutex_pcp in Hpcp_valid.
    destruct Hpcp_valid as [Hdisabled_case | Hpcp_range].
    - rewrite Hdisabled in Hdisabled_case.
      exact Hdisabled_case.
    - rewrite unsigned_last_nbits_eq in PreH2.
      + lia.
      + split.
        * lia.
        * change (pcp_v < 4294967296).
          lia.
  }
  Right.
  Exists e_h_2 cnt_h_2 ptr_h_2 grp_h_2 tbl_h
    canonical_waiter_2 table_owner_2 ls_h_2 ls_r_2 ls_d_2.
  entailer!.
  unfold UCOS2_raw_ready_prio_stage.
  cancel (interrupt_inv sg (IntrState ls_h_2)).
  cancel (task_raw_rep sg (TskState ls_h_2)).
  cancel (sched_raw_ready_prio_stage
    sg (SchedState ls0) (SchedState ls_h_2) (TskState ls_h_2)).
  cancel (event_raw_rep sg (TskState ls_h_2) (EventState ls_h_2)).
  cancel (tick_inv sg (TickState ls_h_2)).
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPost_full_entail_wit_13 : OSMutexPost_full_entail_wit_13.
Proof.
  left.
  pre_process.
  assert (Horig_byte :
    0 <= decode_OwnerPrio_from_cnt ecnt_in <= 255).
  {
    unfold decode_OwnerPrio_from_cnt.
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    replace (2 ^ 8) with 256 by reflexivity.
    split.
    - exact (proj1 (Z.mod_pos_bound ecnt_in 256 ltac:(lia))).
    - apply (proj1 (Z.lt_succ_r (ecnt_in mod 256) 255)).
      exact (proj2 (Z.mod_pos_bound ecnt_in 256 ltac:(lia))).
  }
  pose proof
    (mutex_post_zero_group_empty_waitlist__handover_commit
      sg pevent0 ls0 pcp_idx
      (decode_OwnerPrio_from_cnt ecnt_in)
      ls_d_2 eid ls2 e 4 ecnt_in owner_ptr egrp_in evtL_in
      H5 H8 H7 H6 H2 PreH1) as Hwait.
  destruct
    (mutex_post_empty_release_snapshot__handover_commit
      sg pevent0 ls0 pcp_idx
      (decode_OwnerPrio_from_cnt ecnt_in)
      ls_d_2 eid ls2 e ecnt_in owner_ptr egrp_in evtL_in
      H5 H3 Horig_byte PreH3 H7 H6 H2 Hwait)
    as (e_available & e_r & ls_available & ls_r &
        Hcount & Howner & Hrelease & Hcrit &
        Hls_available & Hls_r & Hsnapshot_r).
  pose proof Hsnapshot_r as Hsnap_r.
  unfold event_raw_snapshot_of_prop in Hsnap_r.
  destruct Hsnap_r as
    [Hget_r [Htype_r [Hcnt_r
      [Hptr_r [Hgrp_r Htbl_r]]]]].
  unfold event_core_fields_layout_prop in H1.
  destruct H1 as [Htype_addr [Hptr_addr Hcnt_addr]].
  unfold event_wait_fields_layout_prop in H0.
  destruct H0 as [Hgrp_addr Htbl_addr].
  rewrite Hls_r, Hls_available in Hgrp_r, Htbl_r.
  repeat rewrite replace_EventS_other_Tsk in Hgrp_r, Htbl_r.
  Exists e_r
    (Z.lor (unsigned_last_nbits ecnt_in 16) 255)
    0 egrp_in evtL_in ls_r ls_available ls2 ls_d_2.
  entailer!.
  unfold mutex_post_rep_no_event, mutex_post_rep.
  pre_process.
  apply derivable1_orp_elim.
  all: entailer!.
  all: try (rewrite Hls_r, Hls_available).
  all: try cbn.
  all: try (
    match goal with
    | |- context [
        sched_raw_ready_prio_stage ?sg0 ?ss0 ?ss1 ?ts0] =>
        Right; unfold UCOS2_raw_ready_prio_stage
    | |- context [sched_raw_rep ?sg0 ?ts0 ?ss0] =>
        Left; unfold UCOS2_raw_rep
    end).
  all: try solve [
    entailer!
  | apply sepcon_cancel_end; entailer!
  ].
  all: try solve [
    unfold event_core_fields_layout_prop;
    repeat split; assumption
  ].
  all: try solve [
    unfold event_wait_fields_layout_prop;
    split; assumption
  ].
  all: repeat rewrite replace_EventS_other_Intr.
  all: repeat rewrite replace_EventS_other_Tsk.
  all: repeat rewrite replace_EventS_other_Sched.
  all: repeat rewrite replace_EventS_EventState.
  all: repeat rewrite replace_EventS_other_Tick.
  all: rewrite Htype_addr, Hptr_addr, Hcnt_addr, Hgrp_addr, Htbl_addr.
  all: unfold encode_event_wait_tbl_values_or in Htbl_r.
  all: cbn [Znth] in Htbl_r.
  all: inversion Htbl_r.
  all: subst evtL_in.
  all: cbn [Znth sizeof_front_end_type].
  all: repeat rewrite Z.mul_1_r.
  all: match goal with
    | |- context [Znth 0 ?l 0] =>
        assert (Hnth0 : Znth 0 l 0 =
          encode_event_wait_tbl_at_or (waitList e_r)
            (TskState ls2) 0) by reflexivity;
        rewrite Hnth0
    end.
  all: match goal with
    | |- context [Znth 1 ?l 0] =>
        assert (Hnth1 : Znth 1 l 0 =
          encode_event_wait_tbl_at_or (waitList e_r)
            (TskState ls2) 1) by reflexivity;
        rewrite Hnth1
    end.
  all: match goal with
    | |- context [Znth 2 ?l 0] =>
        assert (Hnth2 : Znth 2 l 0 =
          encode_event_wait_tbl_at_or (waitList e_r)
            (TskState ls2) 2) by reflexivity;
        rewrite Hnth2
    end.
  all: match goal with
    | |- context [Znth 3 ?l 0] =>
        assert (Hnth3 : Znth 3 l 0 =
          encode_event_wait_tbl_at_or (waitList e_r)
            (TskState ls2) 3) by reflexivity;
        rewrite Hnth3
    end.
  all: match goal with
    | |- context [Znth 4 ?l 0] =>
        assert (Hnth4 : Znth 4 l 0 =
          encode_event_wait_tbl_at_or (waitList e_r)
            (TskState ls2) 4) by reflexivity;
        rewrite Hnth4
    end.
  all: match goal with
    | |- context [Znth 5 ?l 0] =>
        assert (Hnth5 : Znth 5 l 0 =
          encode_event_wait_tbl_at_or (waitList e_r)
            (TskState ls2) 5) by reflexivity;
        rewrite Hnth5
    end.
  all: match goal with
    | |- context [Znth 6 ?l 0] =>
        assert (Hnth6 : Znth 6 l 0 =
          encode_event_wait_tbl_at_or (waitList e_r)
            (TskState ls2) 6) by reflexivity;
        rewrite Hnth6
    end.
  all: match goal with
    | |- context [Znth 7 ?l 0] =>
        assert (Hnth7 : Znth 7 l 0 =
          encode_event_wait_tbl_at_or (waitList e_r)
            (TskState ls2) 7) by reflexivity;
        rewrite Hnth7
    end.
  all: pose proof
      (event_raw_rep_merge_eid_two_updates__handover_commit
        sg (TskState ls2) (EventState ls2) eid
        e_available e_r) as Hevent_merge.
  all: unfold used_complete_event_raw in Hevent_merge.
  all: rewrite <- Htype_r, <- Hcnt_r, <- Hptr_r, <- Hgrp_r
      in Hevent_merge.
  all: L_sepcon_lift'
      (event_raw_rep_no_eid
        sg (TskState ls2) (EventState ls2) eid).
  all: try (match goal with
    | |- context [
        (?addr # UChar |->
          encode_event_wait_tbl_at_or ?wl ?ts 7)] =>
        L_sepcon_lift'
          (addr # UChar |->
            encode_event_wait_tbl_at_or wl ts 7)
    end).
  all: try (match goal with
    | |- context [
        (?addr # UChar |->
          encode_event_wait_tbl_at_or ?wl ?ts 6)] =>
        L_sepcon_lift'
          (addr # UChar |->
            encode_event_wait_tbl_at_or wl ts 6)
    end).
  all: try (match goal with
    | |- context [
        (?addr # UChar |->
          encode_event_wait_tbl_at_or ?wl ?ts 5)] =>
        L_sepcon_lift'
          (addr # UChar |->
            encode_event_wait_tbl_at_or wl ts 5)
    end).
  all: try (match goal with
    | |- context [
        (?addr # UChar |->
          encode_event_wait_tbl_at_or ?wl ?ts 4)] =>
        L_sepcon_lift'
          (addr # UChar |->
            encode_event_wait_tbl_at_or wl ts 4)
    end).
  all: try (match goal with
    | |- context [
        (?addr # UChar |->
          encode_event_wait_tbl_at_or ?wl ?ts 3)] =>
        L_sepcon_lift'
          (addr # UChar |->
            encode_event_wait_tbl_at_or wl ts 3)
    end).
  all: try (match goal with
    | |- context [
        (?addr # UChar |->
          encode_event_wait_tbl_at_or ?wl ?ts 2)] =>
        L_sepcon_lift'
          (addr # UChar |->
            encode_event_wait_tbl_at_or wl ts 2)
    end).
  all: try (match goal with
    | |- context [
        (?addr # UChar |->
          encode_event_wait_tbl_at_or ?wl ?ts 1)] =>
        L_sepcon_lift'
          (addr # UChar |->
            encode_event_wait_tbl_at_or wl ts 1)
    end).
  all: try (match goal with
    | |- context [
        (?addr # UChar |->
          encode_event_wait_tbl_at_or ?wl ?ts 0)] =>
        L_sepcon_lift'
          (addr # UChar |->
            encode_event_wait_tbl_at_or wl ts 0)
    end).
  all: try (match goal with
    | |- context [
        ((event_addr ?sg1 ?eid1 + OSEventGrp_off)
          # UChar |-> ?grp)] =>
        L_sepcon_lift'
          ((event_addr sg1 eid1 + OSEventGrp_off)
            # UChar |-> grp)
    end).
  all: try (match goal with
    | |- context [
        ((event_addr ?sg1 ?eid1 + OSEventCnt_off)
          # UShort |-> ?cnt)] =>
        L_sepcon_lift'
          ((event_addr sg1 eid1 + OSEventCnt_off)
            # UShort |-> cnt)
    end).
  all: try (match goal with
    | |- context [
        ((event_addr ?sg1 ?eid1 + OSEventPtr_off)
          # Ptr |-> ?ptr)] =>
        L_sepcon_lift'
          ((event_addr sg1 eid1 + OSEventPtr_off)
            # Ptr |-> ptr)
    end).
  all: try (match goal with
    | |- context [
        ((event_addr ?sg1 ?eid1 + OSEventType_off)
          # UChar |-> ?typ)] =>
        L_sepcon_lift'
          ((event_addr sg1 eid1 + OSEventType_off)
            # UChar |-> typ)
    end).
  all: try (repeat rewrite derivable1_sepcon_assoc1).
  all: try (rewrite Hevent_merge).
  all: try solve [entailer!].
  all: try solve [apply sepcon_cancel_end; entailer!].
  all: L_sepcon_lift' (interrupt_inv sg (IntrState ls2)).
  all: L_sepcon_lift' (task_raw_rep sg (TskState ls2)).
  all: match goal with
    | |- context [
        sched_raw_ready_prio_stage ?sg1 ?ss0 ?ss1 ?ts0] =>
        L_sepcon_lift'
          (sched_raw_ready_prio_stage sg1 ss0 ss1 ts0)
    | |- context [sched_raw_rep ?sg1 ?ts0 ?ss0] =>
        L_sepcon_lift' (sched_raw_rep sg1 ts0 ss0)
    end.
  all: L_sepcon_lift'
    (event_raw_rep sg (TskState ls2)
      (update_event_field_raw
        (update_event_field_raw (EventState ls2) eid e_available)
        eid e_r)).
  all: L_sepcon_lift' (tick_inv sg (TickState ls2)).
  all: repeat rewrite derivable1_sepcon_assoc1.
  all: entailer!.
  all: apply sepcon_cancel_end; entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_return_wit_1 : OSMutexPost_full_return_wit_1.
Proof.
  pre_process.
  match goal with
  | H : UCOS2_validity_bundle sg ls0 |- _ =>
      rename H into Hentry_valid
  end.
  match goal with
  | H : mutex_post_owner_disinherit_stage_prop
          sg pevent0 ls0 pcp_idx
          (decode_OwnerPrio_from_cnt ecnt_in) ls_d |- _ =>
      rename H into Hstage
  end.
  match goal with
  | H : mutex_post_release_step_prop sg eid ls_d ls_r |- _ =>
      rename H into Hrelease
  end.
  match goal with
  | H : valid_stable_glob_vars sg |- _ =>
      rename H into Hstable
  end.
  assert (Hsem :
    OSMutexPost_sem sg pevent0 ls0 OS_ERR_NONE ls_r).
  {
    eapply mutex_post_empty_sem_from_stages__return_semantics.
    - exact PreH3.
    - exact Hstage.
    - exact Hrelease.
  }
  assert (Hsafe :
    safeExec
      (OSMutexPost_LastSeen
         sg pevent0 ls0 OS_ERR_NONE ls_r)
      (return encode_os_err_code OS_ERR_NONE) X).
  {
    eapply OSMutexPost_safe_return.
    - exact Hsem.
    - exact PreH2.
  }
  assert (Hresult :
    mutex_post_result_prop sg pevent0 ls0 ls_r 0).
  {
    unfold mutex_post_result_prop.
    exists OS_ERR_NONE.
    split; [exact Hsem | reflexivity].
  }
  assert (Hconditional :
    mutex_post_conditional_validity_prop sg pevent0 ls0 ls_r).
  {
    unfold mutex_post_conditional_validity_prop.
    intro Hrelocations.
    pose proof
      (mutex_post_disinherit_validity__return_semantics
         sg pevent0 ls0 pcp_idx
         (decode_OwnerPrio_from_cnt ecnt_in) ls_d
         Hstable Hentry_valid Hstage Hrelocations)
      as Hdisinherited_valid.
    eapply mutex_post_empty_release_validity__return_semantics.
    - exact PreH3.
    - exact Hentry_valid.
    - exact Hdisinherited_valid.
    - exact Hstage.
    - exact Hrelease.
  }
  Exists ls_r OS_ERR_NONE.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls_r).
    cancel (mutex_post_rep sg ls0 ls_r).
    entailer!.
    apply derivable1_truep_intros.
  - entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_return_wit_2 : OSMutexPost_full_return_wit_2.
Proof.
  pre_process.
  match goal with
  | H : UCOS2_validity_bundle sg ls0 |- _ =>
      rename H into Hentry_valid
  end.
  match goal with
  | H : mutex_post_owner_disinherit_stage_prop
          sg pevent0 ls0 pcp_idx
          (decode_OwnerPrio_from_cnt ecnt_in) ls_d |- _ =>
      rename H into Hstage
  end.
  match goal with
  | H : mutex_post_handover_step_prop
          sg eid ls_d prio_o canonical_waiter table_owner ls_h |- _ =>
      rename H into Hhandover
  end.
  match goal with
  | H : mutex_post_sched_step_prop ls_h ls_sched |- _ =>
      rename H into Hsched
  end.
  match goal with
  | H : valid_stable_glob_vars sg |- _ =>
      rename H into Hstable
  end.
  assert (Hsem :
    OSMutexPost_sem sg pevent0 ls0 OS_ERR_NONE ls_sched).
  {
    eapply mutex_post_handover_sem_from_stages__return_semantics.
    - exact PreH2.
    - exact Hstage.
    - exact Hhandover.
    - exact Hsched.
    - right.
      split.
      + right. exact PreH4.
      + reflexivity.
  }
  assert (Hsafe :
    safeExec
      (OSMutexPost_LastSeen
         sg pevent0 ls0 OS_ERR_NONE ls_sched)
      (return encode_os_err_code OS_ERR_NONE) X).
  {
    eapply OSMutexPost_safe_return.
    - exact Hsem.
    - exact PreH1.
  }
  assert (Hresult :
    mutex_post_result_prop sg pevent0 ls0 ls_sched 0).
  {
    unfold mutex_post_result_prop.
    exists OS_ERR_NONE.
    split; [exact Hsem | reflexivity].
  }
  assert (Hconditional :
    mutex_post_conditional_validity_prop
      sg pevent0 ls0 ls_sched).
  {
    unfold mutex_post_conditional_validity_prop.
    intro Hrelocations.
    eapply mutex_post_handover_sched_validity__return_semantics.
    - exact Hstable.
    - exact Hentry_valid.
    - exact PreH2.
    - exact Hstage.
    - exact Hhandover.
    - exact Hsched.
    - exact Hrelocations.
  }
  Exists ls_sched OS_ERR_NONE.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls_sched).
    cancel (mutex_post_rep sg ls0 ls_sched).
    entailer!.
    apply derivable1_truep_intros.
  - entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_return_wit_3 : OSMutexPost_full_return_wit_3.
Proof.
  pre_process.
  match goal with
  | H : UCOS2_validity_bundle sg ls0 |- _ =>
      rename H into Hentry_valid
  end.
  match goal with
  | H : mutex_post_owner_disinherit_stage_prop
          sg pevent0 ls0 pcp_idx
          (decode_OwnerPrio_from_cnt ecnt_in) ls_d |- _ =>
      rename H into Hstage
  end.
  match goal with
  | H : mutex_post_handover_step_prop
          sg eid ls_d prio_o canonical_waiter table_owner ls_h |- _ =>
      rename H into Hhandover
  end.
  match goal with
  | H : mutex_post_sched_step_prop ls_h ls_sched |- _ =>
      rename H into Hsched
  end.
  match goal with
  | H : valid_stable_glob_vars sg |- _ =>
      rename H into Hstable
  end.
  assert (Hceil :
    sg.(osPrioMutexCeilDis) = 0xFF).
  {
    unfold valid_stable_glob_vars in Hstable.
    tauto.
  }
  assert (Hsem :
    OSMutexPost_sem sg pevent0 ls0 OS_ERR_NONE ls_sched).
  {
    eapply mutex_post_handover_sem_from_stages__return_semantics.
    - exact PreH2.
    - exact Hstage.
    - exact Hhandover.
    - exact Hsched.
    - right.
      split.
      + left. lia.
      + reflexivity.
  }
  assert (Hsafe :
    safeExec
      (OSMutexPost_LastSeen
         sg pevent0 ls0 OS_ERR_NONE ls_sched)
      (return encode_os_err_code OS_ERR_NONE) X).
  {
    eapply OSMutexPost_safe_return.
    - exact Hsem.
    - exact PreH1.
  }
  assert (Hresult :
    mutex_post_result_prop sg pevent0 ls0 ls_sched 0).
  {
    unfold mutex_post_result_prop.
    exists OS_ERR_NONE.
    split; [exact Hsem | reflexivity].
  }
  assert (Hconditional :
    mutex_post_conditional_validity_prop
      sg pevent0 ls0 ls_sched).
  {
    unfold mutex_post_conditional_validity_prop.
    intro Hrelocations.
    eapply mutex_post_handover_sched_validity__return_semantics.
    - exact Hstable.
    - exact Hentry_valid.
    - exact PreH2.
    - exact Hstage.
    - exact Hhandover.
    - exact Hsched.
    - exact Hrelocations.
  }
  Exists ls_sched OS_ERR_NONE.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls_sched).
    cancel (mutex_post_rep sg ls0 ls_sched).
    entailer!.
    apply derivable1_truep_intros.
  - entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_return_wit_4 : OSMutexPost_full_return_wit_4.
Proof.
  pre_process.
  match goal with
  | H : UCOS2_validity_bundle sg ls0 |- _ =>
      rename H into Hentry_valid
  end.
  match goal with
  | H : mutex_post_owner_disinherit_stage_prop
          sg pevent0 ls0 pcp_idx
          (decode_OwnerPrio_from_cnt ecnt_in) ls_d |- _ =>
      rename H into Hstage
  end.
  match goal with
  | H : mutex_post_handover_step_prop
          sg eid ls_d prio_o canonical_waiter table_owner ls_h |- _ =>
      rename H into Hhandover
  end.
  match goal with
  | H : mutex_post_sched_step_prop ls_h ls_sched |- _ =>
      rename H into Hsched
  end.
  match goal with
  | H : valid_stable_glob_vars sg |- _ =>
      rename H into Hstable
  end.
  assert (Hceil :
    sg.(osPrioMutexCeilDis) = 0xFF).
  {
    unfold valid_stable_glob_vars in Hstable.
    tauto.
  }
  assert (Hnot_disabled :
    pcp_idx <> sg.(osPrioMutexCeilDis)).
  {
    lia.
  }
  assert (Hsem :
    OSMutexPost_sem
      sg pevent0 ls0 OS_ERR_PCP_LOWER ls_sched).
  {
    eapply mutex_post_handover_sem_from_stages__return_semantics.
    - exact PreH2.
    - exact Hstage.
    - exact Hhandover.
    - exact Hsched.
    - left.
      repeat split; try assumption; reflexivity.
  }
  assert (Hsafe :
    safeExec
      (OSMutexPost_LastSeen
         sg pevent0 ls0 OS_ERR_PCP_LOWER ls_sched)
      (return encode_os_err_code OS_ERR_PCP_LOWER) X).
  {
    eapply OSMutexPost_safe_return.
    - exact Hsem.
    - exact PreH1.
  }
  assert (Hresult :
    mutex_post_result_prop sg pevent0 ls0 ls_sched 120).
  {
    unfold mutex_post_result_prop.
    exists OS_ERR_PCP_LOWER.
    split; [exact Hsem | reflexivity].
  }
  assert (Hconditional :
    mutex_post_conditional_validity_prop
      sg pevent0 ls0 ls_sched).
  {
    unfold mutex_post_conditional_validity_prop.
    intro Hrelocations.
    eapply mutex_post_handover_sched_validity__return_semantics.
    - exact Hstable.
    - exact Hentry_valid.
    - exact PreH2.
    - exact Hstage.
    - exact Hhandover.
    - exact Hsched.
    - exact Hrelocations.
  }
  Exists ls_sched OS_ERR_PCP_LOWER.
  split_pure_spatial.
  - cancel (OutsideCritical sg ls_sched).
    cancel (mutex_post_rep sg ls0 ls_sched).
    entailer!.
    apply derivable1_truep_intros.
  - entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_return_wit_5 : OSMutexPost_full_return_wit_5.
Proof.
  pre_process.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls1 |- _ =>
      unfold crit_rel_no_os_state_change in Hrel;
      subst ls1
  end.
  pose proof H14 as Hvalid_parts.
  unfold UCOS2_validity_bundle in Hvalid_parts.
  destruct Hvalid_parts as
    [Htask_valid [Hsched_valid [Hevent_valid Hcross]]].
  pose proof H4 as Hsnapshot.
  unfold event_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as
    [Hevent_used [Hetype [Hecnt [Heptr [Hegrp Hetbl]]]]].
  assert (Hevent_type : eventType e = OS_EVENT_TYPE_MUTEX).
  {
    destruct (eventType e); cbn in Hetype; congruence.
  }
  unfold event_vaild_cond_prop, valid_GlobEventAbstractState,
    event_in_range in Hevent_valid.
  destruct Hevent_valid as
    [_ [_ [_ [_ [_ [Hpayload _]]]]]].
  specialize (Hpayload eid e Hevent_used).
  unfold event_payload_consistency in Hpayload.
  rewrite Hevent_type in Hpayload.
  destruct (mutexFields e) as [m |] eqn:Hmutex_fields;
    [| contradiction].
  destruct Hpayload as [Hmutex_consistent Howner_wait].
  pose proof H0 as Htask_snapshot.
  unfold task_prio_snapshot_of_prop in Htask_snapshot.
  destruct Htask_snapshot as [Htask_used [Htcb Hprio]].
  assert (Hcur : curTaskID (SchedState ls0) = Some cur_tid).
  {
    unfold sched_tcb_cur_snapshot_prop in H1.
    destruct (curTaskID (SchedState ls0)) as [tid0 |] eqn:Hcur0.
    - simpl in H1.
      assert (tid0 = cur_tid).
      {
        unfold tcb_addr, sizeof_OS_TCB in H1, Htcb.
        lia.
      }
      subst tid0.
      reflexivity.
    - simpl in H1.
      exfalso.
      apply PreH5.
      exact H1.
  }
  unfold mutex_post_checked_entry_prop in H12.
  destruct H12 as [Hint_nesting Hpevent_nonnull].
  assert (Hsem :
    OSMutexPost_sem
      sg pevent0 ls0 OS_ERR_NOT_MUTEX_OWNER ls0).
  {
    destruct (mfOwner m) as [owner_tid |] eqn:Howner.
    - assert (Howner_ptr : owner_ptr = tcb_addr sg owner_tid).
      {
        unfold encode_event_ptr_value in Heptr.
        rewrite Hevent_type, Hmutex_fields, Howner in Heptr.
        exact Heptr.
      }
      assert (Hneq_owner : cur_tid <> owner_tid).
      {
        intros Heq.
        subst owner_tid.
        apply PreH2.
        rewrite Htcb, Howner_ptr.
        reflexivity.
      }
      unfold OSMutexPost_sem.
      right; right; right; right; left.
      split; [exact Hint_nesting |].
      split; [exact Hpevent_nonnull |].
      exists eid, e, m, cur_tid, owner_tid.
      split; [exact PreH4 |].
      split; [exact Hevent_used |].
      split; [exact Hevent_type |].
      split; [exact Hmutex_fields |].
      split; [exact Howner |].
      split; [exact Hcur |].
      split; [exact Hneq_owner |].
      split; reflexivity.
    - unfold OSMutexPost_sem.
      right; right; right; right; right; left.
      split; [exact Hint_nesting |].
      split; [exact Hpevent_nonnull |].
      exists eid, e, m, cur_tid, cur_t.
      split; [exact PreH4 |].
      split; [exact Hevent_used |].
      split; [exact Hevent_type |].
      split; [exact Hmutex_fields |].
      split; [exact Howner |].
      split; [exact Hcur |].
      split; [exact Htask_used |].
      split; reflexivity.
  }
  assert (Hsafe :
    safeExec
      (OSMutexPost_LastSeen
         sg pevent0 ls0 OS_ERR_NOT_MUTEX_OWNER ls0)
      (return encode_os_err_code OS_ERR_NOT_MUTEX_OWNER) X).
  {
    eapply OSMutexPost_safe_return.
    - exact Hsem.
    - exact PreH3.
  }
  assert (Hresult :
    mutex_post_result_prop sg pevent0 ls0 ls0 100).
  {
    unfold mutex_post_result_prop.
    exists OS_ERR_NOT_MUTEX_OWNER.
    split; [exact Hsem | reflexivity].
  }
  assert (Hconditional :
    mutex_post_conditional_validity_prop sg pevent0 ls0 ls0).
  {
    unfold mutex_post_conditional_validity_prop.
    intros Hreloc.
    exact H14.
  }
  assert (Htask_raw_rebuild :
    forall sg0 st tid t tcb prio prio_addr prio_list,
      task_prio_snapshot_of_prop sg0 st tid t tcb prio ->
      task_prio_field_layout_prop tcb prio_addr ->
      prio_tbl_list_rel sg0 st prio_list ->
      prio_addr # UChar |-> prio **
      used_task_no_prio sg0 tcb tid t **
      task_inv_no_tid_priotbl sg0 st tid **
      store_priotbl_list sg0 prio_list |--
        task_raw_rep sg0 st).
  {
    intros sg0 st tid t tcb prio prio_addr prio_list
      Hsnapshot0 Hlayout Hprio_list.
    pose proof Hsnapshot0 as Hsnapshot1.
    unfold task_prio_snapshot_of_prop in Hsnapshot1.
    destruct Hsnapshot1 as [Hused _].
    sep_apply_l_atomic
      (mutex_accept_complete_task__restore_and_returns
         sg0 st tid t tcb prio prio_addr Hsnapshot0 Hlayout).
    rewrite
      (debug_prio_canonical__relocation_semantics
         sg0 st prio_list Hprio_list).
    unfold task_inv_no_tid_priotbl.
    pureIntros.
    unfold task_raw_rep, store_used_task_map,
      store_used_task_map_missing_i, store_prio_tbl.
    sep_apply_l_atomic
      (store_map_merge
         (fun tid0 t0 =>
            used_complete_task sg0 (tcb_addr sg0 tid0) tid0 t0)
         tid t (inUsedTaskStates st) Hused).
    entailer!.
  }
  assert (Hevent_wait_rebuild :
    forall sg0 tskSt evSt eid0 e0 base grp_addr tbl_addr
           etype ecnt eptr egrp etbl,
      event_snapshot_of_prop
        sg0 tskSt evSt eid0 e0 etype ecnt eptr egrp etbl ->
      event_wait_fields_layout_prop sg0 eid0 grp_addr tbl_addr ->
      base = event_addr sg0 eid0 ->
      grp_addr # UChar |-> egrp **
      (tbl_addr + 0 * sizeof (UCHAR)) # UChar |-> Znth 0 etbl 0 **
      (tbl_addr + 1 * sizeof (UCHAR)) # UChar |-> Znth 1 etbl 0 **
      (tbl_addr + 2 * sizeof (UCHAR)) # UChar |-> Znth 2 etbl 0 **
      (tbl_addr + 3 * sizeof (UCHAR)) # UChar |-> Znth 3 etbl 0 **
      (tbl_addr + 4 * sizeof (UCHAR)) # UChar |-> Znth 4 etbl 0 **
      (tbl_addr + 5 * sizeof (UCHAR)) # UChar |-> Znth 5 etbl 0 **
      (tbl_addr + 6 * sizeof (UCHAR)) # UChar |-> Znth 6 etbl 0 **
      (tbl_addr + 7 * sizeof (UCHAR)) # UChar |-> Znth 7 etbl 0 |--
        used_event_rest_no_type_cnt_ptr sg0 tskSt base eid0 e0).
  {
    intros sg0 tskSt evSt eid0 e0 base grp_addr tbl_addr
      etype ecnt eptr egrp etbl Hsnapshot0 Hwait Hbase.
    unfold event_snapshot_of_prop in Hsnapshot0.
    destruct Hsnapshot0 as
      [Hused [Hetype0 [Hecnt0 [Heptr0 [Hegrp0 Hetbl0]]]]].
    unfold event_wait_fields_layout_prop in Hwait.
    destruct Hwait as [Hgrp Htbl].
    subst base. subst grp_addr. subst tbl_addr.
    subst egrp. subst etbl.
    unfold used_event_rest_no_type_cnt_ptr,
      encode_event_wait_tbl_values.
    entailer!.
  }
  assert (Hevent_raw_rebuild :
    forall sg0 tskSt evSt eid0 e0 base
           type_addr ptr_addr cnt_addr grp_addr tbl_addr
           etype ecnt eptr egrp etbl,
      task_vaild_cond_prop sg0 tskSt ->
      event_snapshot_of_prop
        sg0 tskSt evSt eid0 e0 etype ecnt eptr egrp etbl ->
      event_core_fields_layout_prop
        sg0 eid0 type_addr ptr_addr cnt_addr ->
      event_wait_fields_layout_prop sg0 eid0 grp_addr tbl_addr ->
      base = event_addr sg0 eid0 ->
      type_addr # UChar |-> etype **
      cnt_addr # UShort |-> ecnt **
      ptr_addr # Ptr |-> eptr **
      grp_addr # UChar |-> egrp **
      (tbl_addr + 0 * sizeof (UCHAR)) # UChar |-> Znth 0 etbl 0 **
      (tbl_addr + 1 * sizeof (UCHAR)) # UChar |-> Znth 1 etbl 0 **
      (tbl_addr + 2 * sizeof (UCHAR)) # UChar |-> Znth 2 etbl 0 **
      (tbl_addr + 3 * sizeof (UCHAR)) # UChar |-> Znth 3 etbl 0 **
      (tbl_addr + 4 * sizeof (UCHAR)) # UChar |-> Znth 4 etbl 0 **
      (tbl_addr + 5 * sizeof (UCHAR)) # UChar |-> Znth 5 etbl 0 **
      (tbl_addr + 6 * sizeof (UCHAR)) # UChar |-> Znth 6 etbl 0 **
      (tbl_addr + 7 * sizeof (UCHAR)) # UChar |-> Znth 7 etbl 0 **
      event_inv_no_eid sg0 tskSt evSt eid0 |--
        event_raw_rep sg0 tskSt evSt).
  {
    intros sg0 tskSt evSt eid0 e0 base
      type_addr ptr_addr cnt_addr grp_addr tbl_addr
      etype ecnt eptr egrp etbl
      Htask_valid0 Hsnapshot0 Hcore Hwait Hbase.
    sep_apply_l_atomic
      (Hevent_wait_rebuild
         sg0 tskSt evSt eid0 e0 base grp_addr tbl_addr
         etype ecnt eptr egrp etbl Hsnapshot0 Hwait Hbase).
    sep_apply_l_atomic
      (mutex_accept_event_rebuild__restore_and_returns
         sg0 tskSt evSt eid0 e0 base
         type_addr ptr_addr cnt_addr etype ecnt eptr egrp etbl
         Hsnapshot0 Hcore Hbase).
    sep_apply_l_atomic
      (event_inv_split_raw_validity
         sg0 tskSt evSt Htask_valid0).
    entailer!.
  }
  Exists ls0 OS_ERR_NOT_MUTEX_OWNER.
  split_pure_spatial.
  - unfold mutex_post_rep, UCOS2_raw_rep.
    Left.
    sep_apply_l_atomic
      (Htask_raw_rebuild
         sg (TskState ls0) cur_tid cur_t tcbcur tcbprio
         (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio")) prioL_in
         H0 H6 H).
    sep_apply_l_atomic
      (mutex_accept_sched_rebuild__restore_and_returns
         sg (TskState ls0) (SchedState ls0)
         (&("OSTCBCur")) tcbcur H8 H1).
    sep_apply_l_atomic
      (sched_inv_split_raw_validity
         sg (TskState ls0) (SchedState ls0) Htask_valid).
    Intros_p Hsched_valid_again.
    sep_apply_l_atomic
      (Hevent_raw_rebuild
         sg (TskState ls0) (EventState ls0) eid e pevent0
         (&(pevent0 # "os_event" ->ₛ "OSEventType"))
         (&(pevent0 # "os_event" ->ₛ "OSEventPtr"))
         (&(pevent0 # "os_event" ->ₛ "OSEventCnt"))
         (&(pevent0 # "os_event" ->ₛ "OSEventGrp"))
         (&(pevent0 # "os_event" ->ₛ "OSEventTbl"))
         4 ecnt_in owner_ptr egrp_in evtL_in
         Htask_valid H4 H3 H2 PreH4).
    cancel (OutsideCritical sg ls0).
    cancel (interrupt_inv sg (IntrState ls0)).
    cancel (task_raw_rep sg (TskState ls0)).
    cancel (sched_raw_rep sg (TskState ls0) (SchedState ls0)).
    cancel (event_raw_rep sg (TskState ls0) (EventState ls0)).
    cancel (tick_inv sg (TickState ls0)).
    entailer!.
    apply derivable1_truep_intros.
  - entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_return_wit_6 : OSMutexPost_full_return_wit_6.
Proof.
  pre_process.
  sep_apply_l_atomic
    (UCOS2_Verify_inv_split_raw_validity sg ls0).
  Intros_p Hvalid.
  assert (Hsem :
    OSMutexPost_sem sg pevent0 ls0 OS_ERR_EVENT_TYPE ls0).
  {
    unfold mutex_post_public_event_domain_prop in H4.
    destruct H4 as [Hpevent Hdomain].
    destruct Hdomain as
      [[Hrange [Hsnapshot [Hwait [Hnot_mutex | Hmutex]]]] | Hfree].
    - unfold event_snapshot_of_prop in Hsnapshot.
      destruct Hsnapshot as
        [Hused [Hetype [Hecnt [Howner [Hegrp Hetbl]]]]].
      unfold OSMutexPost_sem.
      right; right; right; left.
      split; [rewrite <- PreH11; exact PreH13 |].
      split; [exact PreH14 |].
      exists eid, e.
      split; [exact PreH15 |].
      split; [exact Hused |].
      split.
      + subst etype.
        destruct (eventType e); cbn in Hnot_mutex; congruence.
      + split; reflexivity.
    - destruct Hmutex as
        [Hetype [Hscenario [Htcb [Hpcp [Hprio_tbl [Hlookup
         [Hsched [Htask Hprio_layout]]]]]]]].
      unfold event_snapshot_of_prop in Hsnapshot.
      destruct Hsnapshot as
        [Hused [Hencode [Hecnt [Howner [Hegrp Hetbl]]]]].
      exfalso.
      unfold event_slot_type_value in PreH1.
      rewrite Hused in PreH1.
      rewrite Hetype in Hencode.
      destruct (eventType e); cbn in Hencode, PreH1; congruence.
    - unfold OSMutexPost_sem.
      right; right; left.
      split; [rewrite <- PreH11; exact PreH13 |].
      split; [exact PreH14 |].
      exists eid.
      split; [exact PreH15 |].
      unfold event_slot_unused_prop in Hfree.
      split; [exact Hfree |].
      split; reflexivity.
  }
  assert (Hsafe :
    safeExec
      (OSMutexPost_LastSeen
         sg pevent0 ls0 OS_ERR_EVENT_TYPE ls0)
      (return encode_os_err_code OS_ERR_EVENT_TYPE) X).
  {
    eapply OSMutexPost_safe_return.
    - exact Hsem.
    - exact PreH12.
  }
  assert (Hresult :
    mutex_post_result_prop sg pevent0 ls0 ls0 1).
  {
    unfold mutex_post_result_prop.
    exists OS_ERR_EVENT_TYPE.
    split; [exact Hsem | reflexivity].
  }
  assert (Hconditional :
    mutex_post_conditional_validity_prop sg pevent0 ls0 ls0).
  {
    unfold mutex_post_conditional_validity_prop.
    intros Hreloc.
    exact Hvalid.
  }
  Exists ls0 OS_ERR_EVENT_TYPE.
  split_pure_spatial.
  - unfold mutex_post_rep.
    Left.
    cancel (OutsideCritical sg ls0).
    cancel (UCOS2_raw_rep sg ls0).
    entailer!.
    apply derivable1_truep_intros.
  - entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_return_wit_7 : OSMutexPost_full_return_wit_7.
Proof.
  pre_process.
  unfold os_int_nesting_addr in H2.
  rewrite H2.
  unfold UCOS2_Verify_inv_no_int_nesting.
  sep_apply_l_atomic
    (mutex_accept_interrupt_rebuild__restore_and_returns
       sg (IntrState ls0) isr PreH7).
  unfold UCOS2_Verify_inv.
  pureIntros.
  sep_apply_l_atomic
    (task_inv_split_raw_validity sg (TskState ls0)).
  Intros_p Htask_valid.
  sep_apply_l_atomic
    (sched_inv_split_raw_validity
       sg (TskState ls0) (SchedState ls0) Htask_valid).
  Intros_p Hsched_valid.
  sep_apply_l_atomic
    (event_inv_split_raw_validity
       sg (TskState ls0) (EventState ls0) Htask_valid).
  Intros_p Hevent_valid.
  assert (Hvalid : UCOS2_validity_bundle sg ls0).
  {
    unfold UCOS2_validity_bundle.
    split; [exact Htask_valid |].
    split; [exact Hsched_valid |].
    split; [exact Hevent_valid | exact H3].
  }
  assert (Hsem :
    OSMutexPost_sem sg pevent0 ls0 OS_ERR_PEVENT_NULL ls0).
  {
    unfold OSMutexPost_sem.
    right; left.
    repeat split; auto.
    rewrite <- PreH7.
    exact PreH11.
  }
  assert (Hsafe :
    safeExec
      (OSMutexPost_LastSeen
         sg pevent0 ls0 OS_ERR_PEVENT_NULL ls0)
      (return encode_os_err_code OS_ERR_PEVENT_NULL) X).
  {
    eapply OSMutexPost_safe_return.
    - exact Hsem.
    - exact PreH10.
  }
  assert (Hresult :
    mutex_post_result_prop sg pevent0 ls0 ls0 4).
  {
    unfold mutex_post_result_prop.
    exists OS_ERR_PEVENT_NULL.
    split; [exact Hsem | reflexivity].
  }
  assert (Hconditional :
    mutex_post_conditional_validity_prop sg pevent0 ls0 ls0).
  {
    unfold mutex_post_conditional_validity_prop.
    intros Hreloc.
    exact Hvalid.
  }
  Exists ls0 OS_ERR_PEVENT_NULL.
  split_pure_spatial.
  -
    unfold mutex_post_rep, UCOS2_raw_rep, UCOS2_Verify_inv.
    Left.
    cancel (OutsideCritical sg ls0).
    entailer!.
    apply derivable1_truep_intros.
  - entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_return_wit_8 : OSMutexPost_full_return_wit_8.
Proof.
  pre_process.
  unfold os_int_nesting_addr in H2.
  rewrite H2.
  unfold UCOS2_Verify_inv_no_int_nesting.
  sep_apply_l_atomic
    (mutex_accept_interrupt_rebuild__restore_and_returns
       sg (IntrState ls0) isr PreH6).
  unfold UCOS2_Verify_inv.
  pureIntros.
  sep_apply_l_atomic
    (task_inv_split_raw_validity sg (TskState ls0)).
  Intros_p Htask_valid.
  sep_apply_l_atomic
    (sched_inv_split_raw_validity
       sg (TskState ls0) (SchedState ls0) Htask_valid).
  Intros_p Hsched_valid.
  sep_apply_l_atomic
    (event_inv_split_raw_validity
       sg (TskState ls0) (EventState ls0) Htask_valid).
  Intros_p Hevent_valid.
  assert (Hvalid : UCOS2_validity_bundle sg ls0).
  {
    unfold UCOS2_validity_bundle.
    split; [exact Htask_valid |].
    split; [exact Hsched_valid |].
    split; [exact Hevent_valid | exact H3].
  }
  assert (Hsem :
    OSMutexPost_sem sg pevent0 ls0 OS_ERR_POST_ISR ls0).
  {
    unfold OSMutexPost_sem.
    left.
    repeat split; auto.
    rewrite <- PreH6.
    exact PreH10.
  }
  assert (Hsafe :
    safeExec
      (OSMutexPost_LastSeen
         sg pevent0 ls0 OS_ERR_POST_ISR ls0)
      (return encode_os_err_code OS_ERR_POST_ISR) X).
  {
    eapply OSMutexPost_safe_return.
    - exact Hsem.
    - exact PreH9.
  }
  assert (Hresult :
    mutex_post_result_prop sg pevent0 ls0 ls0 5).
  {
    unfold mutex_post_result_prop.
    exists OS_ERR_POST_ISR.
    split; [exact Hsem | reflexivity].
  }
  assert (Hconditional :
    mutex_post_conditional_validity_prop sg pevent0 ls0 ls0).
  {
    unfold mutex_post_conditional_validity_prop.
    intros Hreloc.
    exact Hvalid.
  }
  Exists ls0 OS_ERR_POST_ISR.
  split_pure_spatial.
  -
    unfold mutex_post_rep, UCOS2_raw_rep, UCOS2_Verify_inv.
    Left.
    cancel (OutsideCritical sg ls0).
    entailer!.
    apply derivable1_truep_intros.
  - entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_partial_solve_wit_16_pure : OSMutexPost_full_partial_solve_wit_16_pure.
Proof.
  pre_process.
  entailer!.
  intro Hegrp.
  subst egrp_in.
  cbn in PreH1.
  contradiction.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_1 : OSMutexPost_full_which_implies_wit_1.
Proof.
  pre_process.
  unfold UCOS2_Verify_inv, UCOS2_Verify_inv_no_int_nesting.
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  unfold os_int_nesting_addr in H.
  rewrite H, PreH1.
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_2 : OSMutexPost_full_which_implies_wit_2.
Proof.
  pre_process.
  unfold UCOS2_Verify_inv, UCOS2_Verify_inv_no_int_nesting.
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  unfold os_int_nesting_addr in H.
  rewrite H, PreH1.
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_3 : OSMutexPost_full_which_implies_wit_3.
Proof.
  pre_process.
  pose proof H as Hlayout.
  unfold event_core_fields_layout_prop in Hlayout.
  destruct Hlayout as [Htype _].
  sep_apply_l_atomic
    (UCOS2_Verify_inv_split_event_type_total sg ls0 eid H0).
  rewrite Htype.
  entailer!.
  rewrite <- Htype.
  exact H.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_4 : OSMutexPost_full_which_implies_wit_4.
Proof.
  pre_process.
  unfold mutex_post_public_event_domain_prop in H0.
  destruct H0 as [Hpevent Hdomain].
  subst pevent_v.
  unfold event_core_fields_layout_prop in H.
  destruct H as [Htype_addr [Hptr_addr Hcnt_addr]].
  rewrite Htype_addr.
  entailer!.
  sep_apply_l_atomic
    (UCOS2_Verify_inv_merge_event_type_total sg ls0 eid H1).
  - unfold UCOS2_Verify_inv.
    entailer!.
    exact debug_truep_merge__relocation_semantics.
  - unfold mutex_post_public_event_domain_prop.
    split; [reflexivity | exact Hdomain].
  - unfold event_core_fields_layout_prop.
    repeat split; assumption.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_5 : OSMutexPost_full_which_implies_wit_5.
Proof.
  pre_process.
  unfold mutex_post_public_event_domain_prop in H0.
  destruct H0 as [Hpevent Hdomain].
  subst pevent_v.
  unfold event_core_fields_layout_prop in H.
  destruct H as [Htype_addr [Hptr_addr Hcnt_addr]].
  rewrite Htype_addr.
  entailer!.
  sep_apply_l_atomic
    (UCOS2_Verify_inv_merge_event_type_total sg ls0 eid H1).
  - unfold UCOS2_Verify_inv.
    entailer!.
    exact debug_truep_merge__relocation_semantics.
  - unfold mutex_post_public_event_domain_prop.
    split; [reflexivity | exact Hdomain].
  - unfold event_core_fields_layout_prop.
    repeat split; assumption.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_6 : OSMutexPost_full_which_implies_wit_6.
Proof.
  pre_process.
  pose proof
    (mutex_post_public_event_domain_select_mutex
      sg ls0 pevent eid e etype ecnt_in owner_ptr egrp_in evtL_in
      pcp_idx prio_tbl_pcp tcbcur tcbprio prioL_in cur_tid cur_t
      _ _ _ PreH1 H) as Hmutex.
  destruct Hmutex as
    [Hetype [Hboundary [Htcbcur [Hpcp [Hprio_rel [Hlookup
    [Hsched [Htask [Hlayout [Hevent Hwait]]]]]]]]]].
  pose proof H as Hdomain.
  unfold mutex_post_public_event_domain_prop in Hdomain.
  destruct Hdomain as [Hpevent _].
  assert (pevent = pevent0) by congruence.
  subst pevent0.
  entailer!.
  rewrite Hpevent.
  cancel.
  repeat (apply derivable1s_emp_sepcon_unfold;
    [apply derivable1_truep_intros |]).
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_7 : OSMutexPost_full_which_implies_wit_7.
Proof.
  pre_process.
  pureIntros.
  match goal with
  | Hsnapshot :
      event_snapshot_of_prop sg (TskState ls0) (EventState ls0)
        eid e etype ecnt_in owner_ptr egrp_in evtL_in |- _ =>
      unfold event_snapshot_of_prop in Hsnapshot;
      destruct Hsnapshot as
        [Hmap [Htype [Hcnt [Hptr [Hgrp Htbl]]]]]
  end.
  match goal with
  | Hcore :
      event_core_fields_layout_prop sg eid ?type_addr ?ptr_addr ?cnt_addr
      |- _ =>
      unfold event_core_fields_layout_prop in Hcore;
      destruct Hcore as [Htype_addr [Hptr_addr Hcnt_addr]]
  end.
  match goal with
  | Hwait :
      event_wait_fields_layout_prop sg eid ?grp_addr ?tbl_addr |- _ =>
      unfold event_wait_fields_layout_prop in Hwait;
      destruct Hwait as [Hgrp_addr Htbl_addr]
  end.
  unfold UCOS2_Verify_inv, task_inv, sched_inv, event_inv,
    store_used_event_map.
  pureIntros.
  sepcon_lift (store_map
    (fun eid0 e0 => used_complete_event sg (TskState ls0)
      (event_addr sg eid0) eid0 e0)
    (inUsedEventStates (EventState ls0))).
  sep_apply_l_atomic (store_map_split
    (fun eid0 e0 => used_complete_event sg (TskState ls0)
      (event_addr sg eid0) eid0 e0)
    eid e (inUsedEventStates (EventState ls0)) Hmap).
  unfold event_inv_no_eid, store_used_event_map_missing_i,
    used_complete_event.
  rewrite Htype_addr, Hptr_addr, Hcnt_addr, Hgrp_addr, Htbl_addr,
    Htype, Hcnt, Hptr, Hgrp, Htbl.
  unfold UCOS2_validity_bundle.
  cbn [sizeof_front_end_type].
  entailer!.
  - unfold encode_event_wait_tbl_values.
    unfold Znth.
    simpl.
    entailer!.
    apply derivable1_truep_intros.
  - unfold event_snapshot_of_prop.
    repeat split; assumption.
  - unfold event_core_fields_layout_prop.
    repeat split; reflexivity.
  - unfold event_wait_fields_layout_prop.
    split; reflexivity.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_8 : OSMutexPost_full_which_implies_wit_8.
Proof.
  pre_process.
  pureIntros.
  match goal with
  | Hrel : crit_rel_no_os_state_change ls0 ls_cs |- _ =>
      unfold crit_rel_no_os_state_change in Hrel;
      subst ls_cs
  end.
  unfold crit_rel_task_event_sched.
  destruct ls0.
  entailer!.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_9 : OSMutexPost_full_which_implies_wit_9.
Proof.
  pre_process.
  pureIntros.
  prop_apply_p (store_array_Zlength Z priotbl_element_store
    (g_OSTCBPrioTbl sg) OS_PRIO_TBL_SIZE prioL_d).
  Intros_p Hlen.
  assert (Hidx : priotbl_index_in_range pcp_idx) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  sep_apply_l_atomic
    (store_priotbl_list_split sg prioL_d pcp_idx Hidx Hlen).
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  match goal with
  | Haddr : os_tcb_prio_tbl_addr sg _ |- _ =>
      unfold os_tcb_prio_tbl_addr in Haddr;
      rewrite Haddr
  end.
  cbn [sizeof_front_end_type].
  entailer!.
Qed.

Lemma proof_of_OSMutexPost_full_which_implies_wit_10 : OSMutexPost_full_which_implies_wit_10.
Proof.
  pre_process.
  pureIntros.
  prop_apply_p (store_array_Zlength Z priotbl_element_store
    (g_OSTCBPrioTbl sg) OS_PRIO_TBL_SIZE prioL_h).
  Intros_p Hlen.
  assert (Hidx : priotbl_index_in_range prio_v) by
    (unfold priotbl_index_in_range, OS_PRIO_TBL_SIZE; lia).
  sep_apply_l_atomic
    (store_priotbl_list_split sg prioL_h prio_v Hidx Hlen).
  unfold priotbl_element_store, sizeof_OSTCB_ptr.
  match goal with
  | Haddr : os_tcb_prio_tbl_addr sg _ |- _ =>
      unfold os_tcb_prio_tbl_addr in Haddr;
      rewrite Haddr
  end.
  cbn [sizeof_front_end_type].
  entailer!.
  rewrite <- PreH3.
  entailer!.
Qed.
