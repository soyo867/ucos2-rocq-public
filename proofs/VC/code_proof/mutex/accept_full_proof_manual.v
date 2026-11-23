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
From Ucos2Verify.VC.code.mutex Require Import accept_full_goal.
From Ucos2Verify.VC.code.mutex Require Import accept_full_proof_auto.
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
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.array_abstraction.
Local Open Scope sac.

Lemma proof_of_OSMutexAccept_full_safety_wit_5 : OSMutexAccept_full_safety_wit_5.
Proof.
  pre_process.
  split_pures.
  all: dump_pre_spatial.
  all: unfold event_count_value_range_prop in *; lia.
Qed.

Lemma proof_of_OSMutexAccept_full_return_wit_1 : OSMutexAccept_full_return_wit_1.
Proof.
  pre_process.
  unfold mutex_accept_restore_transition_prop in H9.
  destruct H9 as [_ Hrestore].
  simpl in Hrestore.
  subst ls_next.
  Exists ls0 0.
  split_pure_spatial.
  - sep_apply_l_atomic
      (mutex_accept_task_rebuild__restore_and_returns
         sg (TskState ls0) cur_tid cur_t tcbcur tcbprio
         (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio")) H7 H5).
    sep_apply_l_atomic
      (mutex_accept_sched_rebuild__restore_and_returns
         sg (TskState ls0) (SchedState ls0) (&( "OSTCBCur"))
         tcbcur H6 H8).
    sep_apply_l_atomic
      (mutex_accept_event_rebuild__restore_and_returns
         sg (TskState ls0) (EventState ls0) eid e pe
         (&(pe # "os_event" ->ₛ "OSEventType"))
         (&(pe # "os_event" ->ₛ "OSEventPtr"))
         (&(pe # "os_event" ->ₛ "OSEventCnt"))
         etype ecnt_in eptr_in egrp_in evtL_in H2 H1
         (eq_trans PreH19 PreH22)).
    unfold UCOS2_Verify_inv.
    cancel (ucos2_rules_lib.OutsideCritical sg ls0).
    cancel (interrupt.interrupt_inv sg (IntrState ls0)).
    cancel (task_inv sg (TskState ls0)).
    cancel (sched.sched_inv sg (TskState ls0) (SchedState ls0)).
    cancel (event_inv sg (TskState ls0) (EventState ls0)).
    cancel (tick.tick_inv sg (TickState ls0)).
    cancel ((perr_pre) # UChar |-> 0).
    entailer!.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial.
      pose proof H2 as Hsnap.
      unfold event_snapshot_of_prop in Hsnap.
      destruct Hsnap as [Heid [Henc _]].
      assert (Htype : eventType e = OS_EVENT_TYPE_MUTEX).
      {
        destruct (eventType e); simpl in Henc;
          rewrite PreH13 in Henc; try lia; reflexivity.
      }
      destruct (mutex_accept_unavailable_payload__restore_and_returns
        sg (TskState ls0) (EventState ls0) eid e etype ecnt_in
        eptr_in egrp_in evtL_in H11 H2 PreH13 PreH2)
        as [m [Hmf Howner]].
      assert (Hsem : OSMutexAccept_sem sg pevent_pre
        ls0 (OS_ERR_NONE, false) ls0).
      {
        unfold OSMutexAccept_sem.
        right; right; right; right; right.
        split; [exact PreH21 |].
        split.
        - rewrite <- PreH16. exact PreH5.
        - exists eid, e, m.
          repeat split; auto.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * bool) Z (OSMutexAccept_sem sg pevent_pre)
        observe_mutex_accept_bool ls0 ls0
        (OS_ERR_NONE, false) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_accept_bool. simpl.
        split; reflexivity.
      * exact PreH20.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH19.
    + dump_pre_spatial. exact PreH18.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH21.
    + dump_pre_spatial. exact PreH13.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH2.
    + entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_return_wit_2 : OSMutexAccept_full_return_wit_2.
Proof.
  pre_process.
  prop_apply_p
    (store_uchar_range (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio")) tcbprio).
  Intros_p Hprio_byte.
  change (0 <= tcbprio <= 255) in Hprio_byte.
  destruct (mutex_accept_available_payload__restore_and_returns
    sg (TskState ls0) (EventState ls0) eid e etype ecnt_in
    eptr_in egrp_in evtL_in H0 H11 H2 PreH14 PreH3)
    as [m [Htype [Hmf [Howner Horig]]]].
  pose proof H7 as Hready.
  unfold task_runnable_prio_snapshot_prop,
    task_prio_snapshot_of_prop in Hready.
  destruct Hready as [[Htask [Htcb Hprio]] Hpend].
  assert (Hcur : curTaskID (SchedState ls0) = Some cur_tid).
  {
    unfold sched_tcb_cur_snapshot_prop in H8.
    destruct (curTaskID (SchedState ls0)) as [tid0 |] eqn:Hcur0.
    - simpl in H8.
      assert (tid0 = cur_tid).
      { unfold tcb_addr, sizeof_OS_TCB in H8, Htcb. lia. }
      subst tid0. reflexivity.
    - simpl in H8. exfalso. apply PreH7. exact H8.
  }
  assert (Hprio16 : unsigned_last_nbits tcbprio 16 = tcbprio).
  { apply mutex_accept_u16_raw__restore_and_returns. exact Hprio_byte. }
  assert (Hhighraw : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 =
      Z.shiftr ecnt_in 8).
  { apply mutex_accept_high_byte_raw__restore_and_returns. exact H10. }
  assert (Hhigh255 : Z.shiftr ecnt_in 8 = 255) by lia.
  assert (Hpcpraw : mfPCP m = Z.shiftr ecnt_in 8).
  {
    eapply mutex_accept_pcp_decode__restore_and_returns;
      eauto.
  }
  pose proof H0 as Hvsg.
  unfold valid_stable_glob_vars in Hvsg.
  destruct Hvsg as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hceil _]]]]]]]]].
  assert (Hpcpceil : mfPCP m = osPrioMutexCeilDis sg) by lia.
  set (e_post :=
    {| eventGeneration := e.(eventGeneration);
       eventType := eventType e;
       mutexFields := Some
         {| mfPCP := mfPCP m; mfOwner := Some cur_tid;
            mfOwnerOrigPrio := Some tcbprio |};
       semFields := semFields e; mboxFields := mboxFields e;
       queueFields := queueFields e;
       waitList := waitList e;
       eventName := e.(eventName);
       eventPadding1 := e.(eventPadding1);
       eventPadding2 := e.(eventPadding2);
       eventPadding3 := e.(eventPadding3);
       eventPadding19 := e.(eventPadding19) |}).
  set (ecnt_post := Z.lor (Z.land ecnt_in 65280) tcbprio).
  set (ls_post := replace_EventS
    (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio) ls0).
  assert (Hpost_snapshot : event_snapshot_of_prop sg (TskState ls0)
    (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio)
    eid e_post 4 ecnt_post tcbcur egrp_in evtL_in).
  {
    unfold e_post, ecnt_post.
    eapply mutex_accept_acquire_snapshot__restore_and_returns;
      eauto.
  }
  unfold mutex_accept_restore_transition_prop in H9.
  destruct H9 as [_ Hrestore].
  simpl in Hrestore.
  unfold mutex_accept_acquire_post_state in Hrestore.
  rewrite Hmf in Hrestore.
  change (ls_next = ls_post) in Hrestore.
  subst ls_next.
  Right.
  Exists e_post ecnt_post ls_post 1.
  split_pure_spatial.
  - sep_apply_l_atomic
      (mutex_accept_task_rebuild__restore_and_returns
         sg (TskState ls0) cur_tid cur_t tcbcur tcbprio
         (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio")) H7 H5).
    prop_apply_p
      (mutex_accept_task_inv_valid_prio__restore_and_returns
         sg (TskState ls0) cur_tid cur_t tcbcur tcbprio H7).
    Intros_p Hvalidprio.
    prop_apply_p
      (task_inv_entails_current_prio_registered sg (TskState ls0)).
    Intros_p Hregistered.
    sep_apply_l_atomic
      (mutex_accept_sched_rebuild__restore_and_returns
         sg (TskState ls0) (SchedState ls0) (&( "OSTCBCur"))
         tcbcur H6 H8).
    unfold ls_post at 1.
    unfold event_inv_no_eid at 1.
    Intros_p Hpostvalid.
    simpl in Hpostvalid.
    simpl.
    unfold ecnt_post.
    rewrite PreH5, Hprio16.
    assert (Hpostcross : cross_module_consistency sg ls_post).
    {
      pose proof H2 as Hsnapshot0.
      unfold event_snapshot_of_prop in Hsnapshot0.
      destruct Hsnapshot0 as [Hget _].
      unfold ls_post.
      eapply cross_module_consistency_preserved_by_acquire.
      - exact Hget.
      - exact Htype.
      - exact Hmf.
      - exact Howner.
      - exact Htask.
      - symmetry. exact Hprio.
      - exact Hpend.
      - exact Hvalidprio.
      - exact Hregistered.
      - exact H3.
    }
    unfold UCOS2_Verify_inv.
    unfold ls_post; simpl.
    cancel (ucos2_rules_lib.OutsideCritical sg
      (replace_EventS
        (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio)
        ls0)).
    cancel (interrupt.interrupt_inv sg (IntrState ls0)).
    cancel (task_inv sg (TskState ls0)).
    cancel (sched.sched_inv sg (TskState ls0) (SchedState ls0)).
    cancel (tick.tick_inv sg (TickState ls0)).
    cancel ((perr_pre) # UChar |-> 0).
    pose proof
      (mutex_accept_acquire_event_rebuild__restore_and_returns
         sg (TskState ls0) (EventState ls0) eid e m cur_tid tcbprio
         tcbcur pe
         (&(pe # "os_event" ->ₛ "OSEventType"))
         (&(pe # "os_event" ->ₛ "OSEventPtr"))
         (&(pe # "os_event" ->ₛ "OSEventCnt"))
         ecnt_post egrp_in evtL_in Hpostvalid Hpost_snapshot Htcb H1
         (eq_trans PreH20 PreH23)) as Hevent_rebuild.
    unfold ecnt_post in Hevent_rebuild.
    simpl in Hevent_rebuild.
    lazymatch type of Hevent_rebuild with
    | ?P |-- _ =>
        let L := sepconlistasrts P in
        asrt_simpl; sep_lift_L L
    end.
    lazymatch type of Hevent_rebuild with
    | ?P |-- _ =>
        let L := sepconlistasrts P in
        lazymatch L with
        | ?A :: ?B :: ?C :: ?D :: ?SU :: ?SF :: nil =>
            L_sepcon_lift' SF;
            L_sepcon_lift' SU
        end
    end.
    L_sepcon_lift'
      (used_event_rest_no_type_cnt_ptr sg (TskState ls0) pe eid e).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventCnt") # UShort |->
        Z.lor (Z.land ecnt_in 65280) tcbprio).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventPtr") # Ptr |-> tcbcur).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    repeat rewrite derivable1_sepcon_assoc1.
    rewrite Hevent_rebuild.
    entailer!.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial.
      assert (Hatomic : atomic_mutex_acquire eid cur_tid tcbprio
        ls0 tt ls_post).
      {
        pose proof H2 as Hsnapshot_atomic.
        unfold event_snapshot_of_prop in Hsnapshot_atomic.
        destruct Hsnapshot_atomic as [Hget_atomic _].
        unfold atomic_mutex_acquire.
        exists e, e_post, m,
          {| mfPCP := mfPCP m; mfOwner := Some cur_tid;
             mfOwnerOrigPrio := Some tcbprio |}, cur_t.
        repeat split.
        - exact Hget_atomic.
        - exact Htype.
        - exact Hmf.
        - exact Howner.
        - exact Hcur.
        - exact Htask.
        - symmetry. exact Hprio.
        - exact Hpend.
      }
      assert (Hsem : OSMutexAccept_sem sg pevent_pre
        ls0 (OS_ERR_NONE, true) ls_post).
      {
        unfold OSMutexAccept_sem.
        right; right; right; right; left.
        split; [exact PreH22 |].
        split.
        - rewrite <- PreH17. exact PreH6.
        - exists eid, e, m, cur_tid, tcbprio, ls_post.
          repeat split; auto.
          + pose proof H2 as Hsnapshot_sem.
            unfold event_snapshot_of_prop in Hsnapshot_sem.
            tauto.
          + exists cur_t. repeat split; auto.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * bool) Z (OSMutexAccept_sem sg pevent_pre)
        observe_mutex_accept_bool ls0 ls_post
        (OS_ERR_NONE, true) 1 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_accept_bool. simpl.
        split; reflexivity.
      * exact PreH21.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH20.
    + dump_pre_spatial. exact PreH19.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH22.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. unfold ecnt_post. reflexivity.
    + dump_pre_spatial. exact Hhigh255.
    + entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_return_wit_3 : OSMutexAccept_full_return_wit_3.
Proof.
  pre_process.
  prop_apply_p
    (store_uchar_range (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio")) tcbprio).
  Intros_p Hprio_byte.
  change (0 <= tcbprio <= 255) in Hprio_byte.
  destruct (mutex_accept_available_payload__restore_and_returns
    sg (TskState ls0) (EventState ls0) eid e etype ecnt_in
    eptr_in egrp_in evtL_in H0 H11 H2 PreH15 PreH4)
    as [m [Htype [Hmf [Howner Horig]]]].
  pose proof H7 as Hready.
  unfold task_runnable_prio_snapshot_prop,
    task_prio_snapshot_of_prop in Hready.
  destruct Hready as [[Htask [Htcb Hprio]] Hpend].
  assert (Hcur : curTaskID (SchedState ls0) = Some cur_tid).
  {
    unfold sched_tcb_cur_snapshot_prop in H8.
    destruct (curTaskID (SchedState ls0)) as [tid0 |] eqn:Hcur0.
    - simpl in H8.
      assert (tid0 = cur_tid).
      { unfold tcb_addr, sizeof_OS_TCB in H8, Htcb. lia. }
      subst tid0. reflexivity.
    - simpl in H8. exfalso. apply PreH8. exact H8.
  }
  assert (Hprio16 : unsigned_last_nbits tcbprio 16 = tcbprio).
  { apply mutex_accept_u16_raw__restore_and_returns. exact Hprio_byte. }
  assert (Hhighraw : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 =
      Z.shiftr ecnt_in 8).
  { apply mutex_accept_high_byte_raw__restore_and_returns. exact H10. }
  assert (Hhighneq : Z.shiftr ecnt_in 8 <> 255) by lia.
  assert (Hgt : tcbprio > Z.shiftr ecnt_in 8) by lia.
  assert (Hpcpraw : mfPCP m = Z.shiftr ecnt_in 8).
  {
    eapply mutex_accept_pcp_decode__restore_and_returns;
      eauto.
  }
  assert (Hpcpgt : tcbprio > mfPCP m) by lia.
  set (e_post :=
    {| eventGeneration := e.(eventGeneration);
       eventType := eventType e;
       mutexFields := Some
         {| mfPCP := mfPCP m; mfOwner := Some cur_tid;
            mfOwnerOrigPrio := Some tcbprio |};
       semFields := semFields e; mboxFields := mboxFields e;
       queueFields := queueFields e;
       waitList := waitList e;
       eventName := e.(eventName);
       eventPadding1 := e.(eventPadding1);
       eventPadding2 := e.(eventPadding2);
       eventPadding3 := e.(eventPadding3);
       eventPadding19 := e.(eventPadding19) |}).
  set (ecnt_post := Z.lor (Z.land ecnt_in 65280) tcbprio).
  set (ls_post := replace_EventS
    (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio) ls0).
  assert (Hpost_snapshot : event_snapshot_of_prop sg (TskState ls0)
    (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio)
    eid e_post 4 ecnt_post tcbcur egrp_in evtL_in).
  {
    unfold e_post, ecnt_post.
    eapply mutex_accept_acquire_snapshot__restore_and_returns;
      eauto.
  }
  unfold mutex_accept_restore_transition_prop in H9.
  destruct H9 as [_ Hrestore].
  simpl in Hrestore.
  unfold mutex_accept_acquire_post_state in Hrestore.
  rewrite Hmf in Hrestore.
  change (ls_next = ls_post) in Hrestore.
  subst ls_next.
  Left. Right.
  Exists e_post ecnt_post ls_post 1.
  split_pure_spatial.
  - sep_apply_l_atomic
      (mutex_accept_task_rebuild__restore_and_returns
         sg (TskState ls0) cur_tid cur_t tcbcur tcbprio
         (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio")) H7 H5).
    prop_apply_p
      (mutex_accept_task_inv_valid_prio__restore_and_returns
         sg (TskState ls0) cur_tid cur_t tcbcur tcbprio H7).
    Intros_p Hvalidprio.
    prop_apply_p
      (task_inv_entails_current_prio_registered sg (TskState ls0)).
    Intros_p Hregistered.
    sep_apply_l_atomic
      (mutex_accept_sched_rebuild__restore_and_returns
         sg (TskState ls0) (SchedState ls0) (&( "OSTCBCur"))
         tcbcur H6 H8).
    unfold ls_post at 1.
    unfold event_inv_no_eid at 1.
    Intros_p Hpostvalid.
    simpl in Hpostvalid.
    simpl.
    unfold ecnt_post.
    rewrite PreH6, Hprio16.
    assert (Hpostcross : cross_module_consistency sg ls_post).
    {
      pose proof H2 as Hsnapshot0.
      unfold event_snapshot_of_prop in Hsnapshot0.
      destruct Hsnapshot0 as [Hget _].
      unfold ls_post.
      eapply cross_module_consistency_preserved_by_acquire.
      - exact Hget.
      - exact Htype.
      - exact Hmf.
      - exact Howner.
      - exact Htask.
      - symmetry. exact Hprio.
      - exact Hpend.
      - exact Hvalidprio.
      - exact Hregistered.
      - exact H3.
    }
    unfold UCOS2_Verify_inv.
    unfold ls_post; simpl.
    cancel (ucos2_rules_lib.OutsideCritical sg
      (replace_EventS
        (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio)
        ls0)).
    cancel (interrupt.interrupt_inv sg (IntrState ls0)).
    cancel (task_inv sg (TskState ls0)).
    cancel (sched.sched_inv sg (TskState ls0) (SchedState ls0)).
    cancel (tick.tick_inv sg (TickState ls0)).
    cancel ((perr_pre) # UChar |-> 0).
    pose proof
      (mutex_accept_acquire_event_rebuild__restore_and_returns
         sg (TskState ls0) (EventState ls0) eid e m cur_tid tcbprio
         tcbcur pe
         (&(pe # "os_event" ->ₛ "OSEventType"))
         (&(pe # "os_event" ->ₛ "OSEventPtr"))
         (&(pe # "os_event" ->ₛ "OSEventCnt"))
         ecnt_post egrp_in evtL_in Hpostvalid Hpost_snapshot Htcb H1
         (eq_trans PreH21 PreH24)) as Hevent_rebuild.
    unfold ecnt_post in Hevent_rebuild.
    simpl in Hevent_rebuild.
    lazymatch type of Hevent_rebuild with
    | ?P |-- _ =>
        let L := sepconlistasrts P in
        asrt_simpl; sep_lift_L L
    end.
    lazymatch type of Hevent_rebuild with
    | ?P |-- _ =>
        let L := sepconlistasrts P in
        lazymatch L with
        | ?A :: ?B :: ?C :: ?D :: ?SU :: ?SF :: nil =>
            L_sepcon_lift' SF;
            L_sepcon_lift' SU
        end
    end.
    L_sepcon_lift'
      (used_event_rest_no_type_cnt_ptr sg (TskState ls0) pe eid e).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventCnt") # UShort |->
        Z.lor (Z.land ecnt_in 65280) tcbprio).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventPtr") # Ptr |-> tcbcur).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    repeat rewrite derivable1_sepcon_assoc1.
    rewrite Hevent_rebuild.
    entailer!.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial.
      assert (Hatomic : atomic_mutex_acquire eid cur_tid tcbprio
        ls0 tt ls_post).
      {
        pose proof H2 as Hsnapshot_atomic.
        unfold event_snapshot_of_prop in Hsnapshot_atomic.
        destruct Hsnapshot_atomic as [Hget_atomic _].
        unfold atomic_mutex_acquire.
        exists e, e_post, m,
          {| mfPCP := mfPCP m; mfOwner := Some cur_tid;
             mfOwnerOrigPrio := Some tcbprio |}, cur_t.
        repeat split.
        - exact Hget_atomic.
        - exact Htype.
        - exact Hmf.
        - exact Howner.
        - exact Hcur.
        - exact Htask.
        - symmetry. exact Hprio.
        - exact Hpend.
      }
      assert (Hsem : OSMutexAccept_sem sg pevent_pre
        ls0 (OS_ERR_NONE, true) ls_post).
      {
        unfold OSMutexAccept_sem.
        right; right; right; right; left.
        split; [exact PreH23 |].
        split.
        - rewrite <- PreH18. exact PreH7.
        - exists eid, e, m, cur_tid, tcbprio, ls_post.
          repeat split; auto.
          + pose proof H2 as Hsnapshot_sem.
            unfold event_snapshot_of_prop in Hsnapshot_sem.
            tauto.
          + exists cur_t. repeat split; auto.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * bool) Z (OSMutexAccept_sem sg pevent_pre)
        observe_mutex_accept_bool ls0 ls_post
        (OS_ERR_NONE, true) 1 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_accept_bool. simpl.
        split; reflexivity.
      * exact PreH22.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH21.
    + dump_pre_spatial. exact PreH20.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH23.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. unfold ecnt_post. reflexivity.
    + dump_pre_spatial. exact Hgt.
    + entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_return_wit_4 : OSMutexAccept_full_return_wit_4.
Proof.
  pre_process.
  prop_apply_p
    (store_uchar_range (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio")) tcbprio).
  Intros_p Hprio_byte.
  change (0 <= tcbprio <= 255) in Hprio_byte.
  destruct (mutex_accept_available_payload__restore_and_returns
    sg (TskState ls0) (EventState ls0) eid e etype ecnt_in
    eptr_in egrp_in evtL_in H0 H11 H2 PreH15 PreH4)
    as [m [Htype [Hmf [Howner Horig]]]].
  pose proof H7 as Hready.
  unfold task_runnable_prio_snapshot_prop,
    task_prio_snapshot_of_prop in Hready.
  destruct Hready as [[Htask [Htcb Hprio]] Hpend].
  assert (Hcur : curTaskID (SchedState ls0) = Some cur_tid).
  {
    unfold sched_tcb_cur_snapshot_prop in H8.
    destruct (curTaskID (SchedState ls0)) as [tid0 |] eqn:Hcur0.
    - simpl in H8.
      assert (tid0 = cur_tid).
      { unfold tcb_addr, sizeof_OS_TCB in H8, Htcb. lia. }
      subst tid0. reflexivity.
    - simpl in H8. exfalso. apply PreH8. exact H8.
  }
  assert (Hprio16 : unsigned_last_nbits tcbprio 16 = tcbprio).
  { apply mutex_accept_u16_raw__restore_and_returns. exact Hprio_byte. }
  assert (Hhighraw : unsigned_last_nbits (Z.shiftr ecnt_in 8) 8 =
      Z.shiftr ecnt_in 8).
  { apply mutex_accept_high_byte_raw__restore_and_returns. exact H10. }
  assert (Hhighneq : Z.shiftr ecnt_in 8 <> 255) by lia.
  assert (Hle : tcbprio <= Z.shiftr ecnt_in 8) by lia.
  assert (Hpcpraw : mfPCP m = Z.shiftr ecnt_in 8).
  {
    eapply mutex_accept_pcp_decode__restore_and_returns;
      eauto.
  }
  pose proof H0 as Hvsg.
  unfold valid_stable_glob_vars in Hvsg.
  destruct Hvsg as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hceil _]]]]]]]]].
  assert (Hpcpneqceil : mfPCP m <> osPrioMutexCeilDis sg) by lia.
  assert (Hpcple : tcbprio <= mfPCP m) by lia.
  set (e_post :=
    {| eventGeneration := e.(eventGeneration);
       eventType := eventType e;
       mutexFields := Some
         {| mfPCP := mfPCP m; mfOwner := Some cur_tid;
            mfOwnerOrigPrio := Some tcbprio |};
       semFields := semFields e; mboxFields := mboxFields e;
       queueFields := queueFields e;
       waitList := waitList e;
       eventName := e.(eventName);
       eventPadding1 := e.(eventPadding1);
       eventPadding2 := e.(eventPadding2);
       eventPadding3 := e.(eventPadding3);
       eventPadding19 := e.(eventPadding19) |}).
  set (ecnt_post := Z.lor (Z.land ecnt_in 65280) tcbprio).
  set (ls_post := replace_EventS
    (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio) ls0).
  assert (Hpost_snapshot : event_snapshot_of_prop sg (TskState ls0)
    (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio)
    eid e_post 4 ecnt_post tcbcur egrp_in evtL_in).
  {
    unfold e_post, ecnt_post.
    eapply mutex_accept_acquire_snapshot__restore_and_returns;
      eauto.
  }
  unfold mutex_accept_restore_transition_prop in H9.
  destruct H9 as [_ Hrestore].
  simpl in Hrestore.
  unfold mutex_accept_acquire_post_state in Hrestore.
  rewrite Hmf in Hrestore.
  change (ls_next = ls_post) in Hrestore.
  subst ls_next.
  Left. Left.
  Exists e_post ecnt_post ls_post 1.
  split_pure_spatial.
  - sep_apply_l_atomic
      (mutex_accept_task_rebuild__restore_and_returns
         sg (TskState ls0) cur_tid cur_t tcbcur tcbprio
         (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio")) H7 H5).
    prop_apply_p
      (mutex_accept_task_inv_valid_prio__restore_and_returns
         sg (TskState ls0) cur_tid cur_t tcbcur tcbprio H7).
    Intros_p Hvalidprio.
    prop_apply_p
      (task_inv_entails_current_prio_registered sg (TskState ls0)).
    Intros_p Hregistered.
    sep_apply_l_atomic
      (mutex_accept_sched_rebuild__restore_and_returns
         sg (TskState ls0) (SchedState ls0) (&( "OSTCBCur"))
         tcbcur H6 H8).
    unfold ls_post at 1.
    unfold event_inv_no_eid at 1.
    Intros_p Hpostvalid.
    simpl in Hpostvalid.
    simpl.
    unfold ecnt_post.
    rewrite PreH6, Hprio16.
    assert (Hpostcross : cross_module_consistency sg ls_post).
    {
      pose proof H2 as Hsnapshot0.
      unfold event_snapshot_of_prop in Hsnapshot0.
      destruct Hsnapshot0 as [Hget _].
      unfold ls_post.
      eapply cross_module_consistency_preserved_by_acquire.
      - exact Hget.
      - exact Htype.
      - exact Hmf.
      - exact Howner.
      - exact Htask.
      - symmetry. exact Hprio.
      - exact Hpend.
      - exact Hvalidprio.
      - exact Hregistered.
      - exact H3.
    }
    unfold UCOS2_Verify_inv.
    unfold ls_post; simpl.
    cancel (ucos2_rules_lib.OutsideCritical sg
      (replace_EventS
        (owner_acquire_update (EventState ls0) eid e m cur_tid tcbprio)
        ls0)).
    cancel (interrupt.interrupt_inv sg (IntrState ls0)).
    cancel (task_inv sg (TskState ls0)).
    cancel (sched.sched_inv sg (TskState ls0) (SchedState ls0)).
    cancel (tick.tick_inv sg (TickState ls0)).
    cancel ((perr_pre) # UChar |-> 120).
    pose proof
      (mutex_accept_acquire_event_rebuild__restore_and_returns
         sg (TskState ls0) (EventState ls0) eid e m cur_tid tcbprio
         tcbcur pe
         (&(pe # "os_event" ->ₛ "OSEventType"))
         (&(pe # "os_event" ->ₛ "OSEventPtr"))
         (&(pe # "os_event" ->ₛ "OSEventCnt"))
         ecnt_post egrp_in evtL_in Hpostvalid Hpost_snapshot Htcb H1
         (eq_trans PreH21 PreH24)) as Hevent_rebuild.
    unfold ecnt_post in Hevent_rebuild.
    simpl in Hevent_rebuild.
    lazymatch type of Hevent_rebuild with
    | ?P |-- _ =>
        let L := sepconlistasrts P in
        asrt_simpl; sep_lift_L L
    end.
    lazymatch type of Hevent_rebuild with
    | ?P |-- _ =>
        let L := sepconlistasrts P in
        lazymatch L with
        | ?A :: ?B :: ?C :: ?D :: ?SU :: ?SF :: nil =>
            L_sepcon_lift' SF;
            L_sepcon_lift' SU
        end
    end.
    L_sepcon_lift'
      (used_event_rest_no_type_cnt_ptr sg (TskState ls0) pe eid e).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventCnt") # UShort |->
        Z.lor (Z.land ecnt_in 65280) tcbprio).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventPtr") # Ptr |-> tcbcur).
    L_sepcon_lift'
      (&(pe # "os_event" ->ₛ "OSEventType") # UChar |-> 4).
    repeat rewrite derivable1_sepcon_assoc1.
    rewrite Hevent_rebuild.
    entailer!.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial.
      assert (Hatomic : atomic_mutex_acquire eid cur_tid tcbprio
        ls0 tt ls_post).
      {
        pose proof H2 as Hsnapshot_atomic.
        unfold event_snapshot_of_prop in Hsnapshot_atomic.
        destruct Hsnapshot_atomic as [Hget_atomic _].
        unfold atomic_mutex_acquire.
        exists e, e_post, m,
          {| mfPCP := mfPCP m; mfOwner := Some cur_tid;
             mfOwnerOrigPrio := Some tcbprio |}, cur_t.
        repeat split.
        - exact Hget_atomic.
        - exact Htype.
        - exact Hmf.
        - exact Howner.
        - exact Hcur.
        - exact Htask.
        - symmetry. exact Hprio.
        - exact Hpend.
      }
      assert (Hsem : OSMutexAccept_sem sg pevent_pre
        ls0 (OS_ERR_PCP_LOWER, true) ls_post).
      {
        unfold OSMutexAccept_sem.
        right; right; right; right; left.
        split; [exact PreH23 |].
        split.
        - rewrite <- PreH18. exact PreH7.
        - exists eid, e, m, cur_tid, tcbprio, ls_post.
          repeat split; auto.
          + pose proof H2 as Hsnapshot_sem.
            unfold event_snapshot_of_prop in Hsnapshot_sem.
            tauto.
          + exists cur_t. repeat split; auto.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * bool) Z (OSMutexAccept_sem sg pevent_pre)
        observe_mutex_accept_bool ls0 ls_post
        (OS_ERR_PCP_LOWER, true) 1 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_accept_bool. simpl.
        split; reflexivity.
      * exact PreH22.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH21.
    + dump_pre_spatial. exact PreH20.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH23.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. unfold ecnt_post. reflexivity.
    + dump_pre_spatial. exact Hhighneq.
    + dump_pre_spatial. exact Hle.
    + entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_return_wit_5 : OSMutexAccept_full_return_wit_5.
Proof.
  pre_process.
  prop_apply_p (store_uchar_range (&( "OSIntNesting")) isr).
  Intros_p Hisr_range.
  change (0 <= isr <= 255) in Hisr_range.
  assert (Hisr_bits : unsigned_last_nbits isr 32 = isr).
  {
    apply unsigned_last_nbits_eq.
    replace (2 ^ 32) with 4294967296 by reflexivity.
    lia.
  }
  assert (Hisrpos : isr > 0) by lia.
  Right.
  Exists ls0 0.
  split_pure_spatial.
  - unfold os_int_nesting_addr in H9.
    rewrite H9.
    sep_apply_l_atomic
      (mutex_accept_interrupt_rebuild__restore_and_returns
         sg (IntrState ls0) isr PreH6).
    sep_apply_l_atomic
      (mutex_accept_event_rebuild__restore_and_returns
         sg (TskState ls0) (EventState ls0) eid e pe
         (&(pe # "os_event" ->ₛ "OSEventType"))
         (&(pe # "os_event" ->ₛ "OSEventPtr"))
         (&(pe # "os_event" ->ₛ "OSEventCnt"))
         etype ecnt_in eptr_in egrp_in evtL_in H7 H5
         (eq_trans PreH9 PreH12)).
    unfold UCOS2_Verify_inv.
    cancel (ucos2_rules_lib.OutsideCritical sg ls0).
    cancel (interrupt.interrupt_inv sg (IntrState ls0)).
    cancel (task_inv sg (TskState ls0)).
    cancel (sched.sched_inv sg (TskState ls0) (SchedState ls0)).
    cancel (event_inv sg (TskState ls0) (EventState ls0)).
    cancel (tick.tick_inv sg (TickState ls0)).
    cancel ((perr_pre) # UChar |-> 2).
    entailer!.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial.
      pose proof H7 as Hsnap.
      unfold event_snapshot_of_prop in Hsnap.
      destruct Hsnap as [Heid [Henc _]].
      assert (Htype : eventType e = OS_EVENT_TYPE_MUTEX).
      {
        destruct (eventType e); simpl in Henc;
          rewrite PreH3 in Henc; try lia; reflexivity.
      }
      assert (Hsem : OSMutexAccept_sem sg pevent_pre
        ls0 (OS_ERR_PEND_ISR, false) ls0).
      {
        unfold OSMutexAccept_sem.
        right; right; right; left.
        split; [exact PreH11 |].
        split.
        - rewrite <- PreH6. exact Hisrpos.
        - exists eid, e.
          repeat split; auto.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * bool) Z (OSMutexAccept_sem sg pevent_pre)
        observe_mutex_accept_bool ls0 ls0
        (OS_ERR_PEND_ISR, false) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_accept_bool. simpl.
        split; reflexivity.
      * exact PreH10.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. exact PreH8.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH11.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact Hisrpos.
    + entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_return_wit_6 : OSMutexAccept_full_return_wit_6.
Proof.
  pre_process.
  Exists ls0 0.
  split_pure_spatial.
  - sep_apply_l_atomic
      (mutex_accept_event_rebuild__restore_and_returns
         sg (TskState ls0) (EventState ls0) eid e pe
         (&(pe # "os_event" ->ₛ "OSEventType"))
         (&(pe # "os_event" ->ₛ "OSEventPtr"))
         (&(pe # "os_event" ->ₛ "OSEventCnt"))
         etype ecnt_in eptr_in egrp_in evtL_in H8 H6
         (eq_trans PreH7 PreH10)).
    unfold UCOS2_Verify_inv.
    cancel (ucos2_rules_lib.OutsideCritical sg ls0).
    cancel (interrupt.interrupt_inv sg (IntrState ls0)).
    cancel (task_inv sg (TskState ls0)).
    cancel (sched.sched_inv sg (TskState ls0) (SchedState ls0)).
    cancel (event_inv sg (TskState ls0) (EventState ls0)).
    cancel (tick.tick_inv sg (TickState ls0)).
    cancel ((perr_pre) # UChar |-> 1).
    entailer!.
    apply derivable1_truep_intros.
  - split_pures.
    + dump_pre_spatial.
      pose proof H8 as Hsnap.
      unfold event_snapshot_of_prop in Hsnap.
      destruct Hsnap as [Heid [Henc _]].
      assert (Hneqtype : eventType e <> OS_EVENT_TYPE_MUTEX).
      {
        intro Heq.
        rewrite Heq in Henc.
        simpl in Henc.
        lia.
      }
      assert (Hsem : OSMutexAccept_sem sg pevent_pre
        ls0 (OS_ERR_EVENT_TYPE, false) ls0).
      {
        unfold OSMutexAccept_sem.
        right; right; left.
        split; [exact PreH9 |].
        exists eid, e.
        repeat split; auto.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * bool) Z (OSMutexAccept_sem sg pevent_pre)
        observe_mutex_accept_bool ls0 ls0
        (OS_ERR_EVENT_TYPE, false) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_accept_bool. simpl.
        split; reflexivity.
      * exact PreH8.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH9.
    + dump_pre_spatial. exact PreH1.
    + entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_return_wit_7 : OSMutexAccept_full_return_wit_7.
Proof.
  pre_process.
  Exists ls0 0.
  split_pure_spatial.
  - unfold UCOS2_Verify_inv.
    cancel (ucos2_rules_lib.OutsideCritical sg ls0).
    cancel (interrupt.interrupt_inv sg (IntrState ls0)).
    cancel (task_inv sg (TskState ls0)).
    cancel (sched.sched_inv sg (TskState ls0) (SchedState ls0)).
    cancel (event_inv sg (TskState ls0) (EventState ls0)).
    cancel (tick.tick_inv sg (TickState ls0)).
    cancel ((perr_pre) # UChar |-> 4).
    entailer!.
  - split_pures.
    + dump_pre_spatial.
      assert (Hsem : OSMutexAccept_sem sg pevent_pre
        ls0 (OS_ERR_PEVENT_NULL, false) ls0).
      {
        unfold OSMutexAccept_sem.
        left.
        repeat split; auto.
      }
      eapply (mutex_accept_safe_return__restore_and_returns
        (OSErrCode * bool) Z (OSMutexAccept_sem sg pevent_pre)
        observe_mutex_accept_bool ls0 ls0
        (OS_ERR_PEVENT_NULL, false) 0 X).
      * exact Hsem.
      * intros P. unfold observe_mutex_accept_bool. simpl.
        split; reflexivity.
      * exact PreH7.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact PreH8.
Qed.

Lemma proof_of_OSMutexAccept_full_partial_solve_wit_1_pure : OSMutexAccept_full_partial_solve_wit_1_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_OSMutexAccept_full_partial_solve_wit_3_pure : OSMutexAccept_full_partial_solve_wit_3_pure.
Proof.
  pre_process.
  sepcon_lift ((&("OSIntNesting")) # UChar |-> isr).
  prop_apply_p (store_uchar_range (&("OSIntNesting")) isr).
  Intros_p Hisr_range.
  change (0 <= isr <= 255) in Hisr_range.
  assert (Hisr_nonpos : isr <= 0).
  {
    eapply unsigned_last_nbits_32_nonpositive_uchar__focus_and_pure.
    - exact Hisr_range.
    - exact PreH1.
  }
  split_pures.
  all: dump_pre_spatial.
  all: subst; lia.
Qed.

Lemma proof_of_OSMutexAccept_full_which_implies_wit_1 : OSMutexAccept_full_which_implies_wit_1.
Proof.
  pre_process.
  unfold event_snapshot_of_prop, event_core_fields_layout_prop.
  pureIntros.
  unfold event_snapshot_of_prop in H0.
  unfold event_core_fields_layout_prop in H.
  destruct H0 as [Hmap [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  destruct H as [Htype_addr [Hptr_addr Hcnt_addr]].
  unfold UCOS2_Verify_inv, event_inv, store_used_event_map.
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
    used_complete_event, used_event_rest_no_type_cnt_ptr.
  rewrite Htype_addr, Hptr_addr, Hcnt_addr, Htype, Hcnt, Hptr, PreH2.
  sepcon_lift
    ((event_addr sg eid + OSEventCnt_off)
       # UShort |-> encode_event_cnt_value e).
  prop_apply_p
    (store_ushort_range
       (event_addr sg eid + OSEventCnt_off)
       (encode_event_cnt_value e)).
  Intros_p Hcnt_range.
  entailer!.
  apply sepcon_cancel_end.
  - apply derivable1_truep_intros.
  - apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexAccept_full_which_implies_wit_2 : OSMutexAccept_full_which_implies_wit_2.
Proof.
  pre_process.
  unfold os_int_nesting_addr, interrupt_inv, store_int_state,
    interrupt_inv_no_int_nesting.
  pureIntros.
  unfold os_int_nesting_addr in H.
  subst isr.
  rewrite H.
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_which_implies_wit_3 : OSMutexAccept_full_which_implies_wit_3.
Proof.
  pre_process.
  apply derivable1s_coq_prop_l.
  intros Hguard.
  unfold mutex_accept_task_sched_guard_prop in Hguard.
  destruct Hguard as [Htype_bad | [Hisr_bad | Hguard]].
  - congruence.
  - lia.
  - destruct Hguard as [Hetype [Hisr [Htcbcur [Hsched Htask]]]].
    entailer!.
    apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexAccept_full_which_implies_wit_4 : OSMutexAccept_full_which_implies_wit_4.
Proof.
  pre_process.
  unfold os_int_nesting_addr, interrupt_inv, store_int_state,
    interrupt_inv_no_int_nesting.
  pureIntros.
  unfold os_int_nesting_addr in H.
  subst isr.
  rewrite H.
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_which_implies_wit_5 : OSMutexAccept_full_which_implies_wit_5.
Proof.
  pre_process.
  pureIntros.
  match goal with
  | Htask : task_runnable_prio_snapshot_prop _ _ _ _ _ _ |- _ =>
      pose proof Htask as Htask_facts;
      unfold task_runnable_prio_snapshot_prop,
        task_prio_snapshot_of_prop in Htask_facts;
      destruct Htask_facts as [[Hmap [Htcb Hprio]] Hpend]
  end.
  match goal with
  | Hlayout : task_prio_field_layout_prop _ _ |- _ =>
      pose proof Hlayout as Hlayout_eq;
      unfold task_prio_field_layout_prop in Hlayout_eq
  end.
  match goal with
  | Haddr : os_tcb_cur_addr _ _ |- _ =>
      pose proof Haddr as Haddr_eq;
      unfold os_tcb_cur_addr in Haddr_eq
  end.
  sep_apply_l_atomic
    (task_inv_split_prio_at__focus_and_pure
       sg (TskState ls0) cur_tid cur_t tcbcur tcbprio
       (&(tcbcur # "os_tcb" ->ₛ "OSTCBPrio"))
       Hmap Htcb Hprio Hlayout_eq).
  sep_apply_l_atomic
    (sched_inv_split_tcb_cur_at__focus_and_pure
       sg (TskState ls0) (SchedState ls0)
       (&("OSTCBCur")) tcbcur Haddr_eq H2).
  entailer!.
Qed.

Lemma proof_of_OSMutexAccept_full_which_implies_wit_6 : OSMutexAccept_full_which_implies_wit_6.
Proof.
  pre_process.
  Exists (mutex_accept_acquire_post_state ls0 eid e cur_tid tcbprio) ls_cs_2.
  unfold mutex_accept_restore_transition_prop,
    crit_rel_no_os_state_change, crit_rel_event_only,
    mutex_accept_acquire_post_state.
  destruct (mutexFields e); entailer!.
  all: unfold crit_rel_no_os_state_change in H; subst ls_cs_2;
    unfold replace_EventS; destruct ls0; reflexivity.
Qed.

Lemma proof_of_OSMutexAccept_full_which_implies_wit_7 : OSMutexAccept_full_which_implies_wit_7.
Proof.
  pre_process.
  Exists (mutex_accept_acquire_post_state ls0 eid e cur_tid tcbprio) ls_cs_2.
  unfold mutex_accept_restore_transition_prop,
    crit_rel_no_os_state_change, crit_rel_event_only,
    mutex_accept_acquire_post_state.
  destruct (mutexFields e); entailer!.
  all: unfold crit_rel_no_os_state_change in H; subst ls_cs_2;
    unfold replace_EventS; destruct ls0; reflexivity.
Qed.

Lemma proof_of_OSMutexAccept_full_which_implies_wit_8 : OSMutexAccept_full_which_implies_wit_8.
Proof.
  pre_process.
  Exists ls0 ls_cs_2.
  unfold mutex_accept_restore_transition_prop,
    crit_rel_no_os_state_change, crit_rel_event_only.
  entailer!.
  unfold crit_rel_no_os_state_change in H.
  subst ls_cs_2.
  unfold replace_EventS.
  destruct ls0.
  reflexivity.
Qed.
