Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.

Import ListNotations.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(* L5 public value: a newly created semaphore owns the exact input count and
   has no payload pointer or waiters. *)
Definition sem_create_fresh_event (cnt : Z) : OSEventAbstractState :=
  {| eventGeneration := 0%nat;
     eventName := 0; eventPadding1 := None; eventPadding2 := None;
     eventPadding3 := None; eventPadding19 := None;
     eventType   := OS_EVENT_TYPE_SEM;
     mutexFields := None;
     semFields   := Some {| semCount := cnt |};
     mboxFields  := None;
     queueFields := None;
     waitList    := [] |}.

Definition sem_create_event_after
  (cnt : Z) (eid : EventID) (rest : list EventID)
  (before : Glob_EventAbstractState) : Glob_EventAbstractState :=
  {| inUsedEventStates := fun eid' =>
       if Z.eqb eid' eid
       then Some (sem_create_fresh_event cnt)
       else before.(inUsedEventStates) eid';
     eventLifecycle := before.(eventLifecycle);
     publishedQueueBytes := before.(publishedQueueBytes);
     unUsedEventStates := rest |}.

Definition sem_create_state_after
  (cnt : Z) (eid : EventID) (rest : list EventID)
  (before : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_EventS
    (sem_create_event_after cnt eid rest before.(EventState)) before.

Definition sem_create_entry_snapshot_prop
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (isr free_head : Z) : Prop :=
  isr = ls0.(IntrState).(intNesting) /\
  event_free_list_head_prop sg ls0.(EventState) free_head.

Definition sem_create_nonempty_snapshot_prop
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (eid : EventID) (rest : list EventID) (free_head : Z) : Prop :=
  event_free_head_snapshot_prop sg ls0.(EventState) eid rest
    free_head (free_event_head sg rest).

(* L3 residuals. The free-list head cell is deliberately outside these
   assertions, so the C load/store can own it explicitly. *)
Definition sem_create_head_open_inv
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  verification_slice_task_inv sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv_no_free_head sg s.(TskState) s.(EventState) **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

Definition sem_create_node_open_inv
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (rest : list EventID) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  verification_slice_task_inv sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv_free_head_rest
    sg s.(TskState) s.(EventState) rest **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

Definition sem_create_free_head_event
  (sg : StableGlobVars) (eid : EventID) (rest : list EventID) : Assertion :=
  (event_addr sg eid + OSEventType_off) # UChar |->
    encode_event_type OS_EVENT_TYPE_UNUSED **
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> free_event_head sg rest **
  (event_addr sg eid + OSEventCnt_off) # UShort |->_ **
  (event_addr sg eid + OSEventGrp_off) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 0) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 1) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 2) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 3) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 4) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 5) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 6) # UChar |->_ **
  (event_addr sg eid + OSEventTbl_off + 7) # UChar |->_ .

Definition sem_create_wait_table_uninitialized (base : addr) : Assertion :=
  (base + OSEventGrp_off) # UChar |->_ **
  (base + OSEventTbl_off + 0) # UChar |->_ **
  (base + OSEventTbl_off + 1) # UChar |->_ **
  (base + OSEventTbl_off + 2) # UChar |->_ **
  (base + OSEventTbl_off + 3) # UChar |->_ **
  (base + OSEventTbl_off + 4) # UChar |->_ **
  (base + OSEventTbl_off + 5) # UChar |->_ **
  (base + OSEventTbl_off + 6) # UChar |->_ **
  (base + OSEventTbl_off + 7) # UChar |->_ .

Definition sem_create_wait_table_zero (base : addr) : Assertion :=
  (base + OSEventGrp_off) # UChar |-> 0 **
  (base + OSEventTbl_off + 0) # UChar |-> 0 **
  (base + OSEventTbl_off + 1) # UChar |-> 0 **
  (base + OSEventTbl_off + 2) # UChar |-> 0 **
  (base + OSEventTbl_off + 3) # UChar |-> 0 **
  (base + OSEventTbl_off + 4) # UChar |-> 0 **
  (base + OSEventTbl_off + 5) # UChar |-> 0 **
  (base + OSEventTbl_off + 6) # UChar |-> 0 **
  (base + OSEventTbl_off + 7) # UChar |-> 0.

(* L5 transient ownership after the free head has been detached. This is
   intentionally not [UCOS2_verification_slice_inv]: the node is private and not yet a
   valid published semaphore. *)
Definition sem_create_transient_frame
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (cnt : Z) (eid : EventID) (rest : list EventID) : Assertion :=
  coq_prop
    (valid_stable_glob_vars sg /\
     event_count_value_range_prop cnt /\
     valid_event_id sg eid /\
     ls0.(EventState).(unUsedEventStates) = eid :: rest) &&
  sem_create_node_open_inv sg ls0 rest **
  sg.(g_OSEventFreeList) # Ptr |-> free_event_head sg rest **
  unused_complete_event sg (event_addr sg eid) eid.

Definition sem_create_restore_frame
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (cnt : Z) (eid : EventID) (rest : list EventID)
  (selected : Z) : Assertion :=
  if Z.eqb selected 0
  then UCOS2_verification_slice_inv sg ls0
  else sem_create_transient_frame sg ls0 cnt eid rest.

Definition sem_create_initialized_event
  (sg : StableGlobVars) (ls_post : UCOS2_Verify_State)
  (cnt : Z) (eid : EventID) : Assertion :=
  used_complete_event sg ls_post.(TskState) (event_addr sg eid) eid
    (sem_create_fresh_event cnt).

Definition sem_create_success_transition_prop
  (sg : StableGlobVars) (ls0 ls_post : UCOS2_Verify_State)
  (cnt : Z) (eid : EventID) (rest : list EventID) : Prop :=
  event_count_value_range_prop cnt /\
  valid_event_id sg eid /\
  ls0.(EventState).(unUsedEventStates) = eid :: rest /\
  ls_post = sem_create_state_after cnt eid rest ls0 /\
  crit_rel_event_only ls0 ls_post.

Definition sem_create_restore_transition_prop
  (sg : StableGlobVars)
  (ls0 ls_inside ls_post : UCOS2_Verify_State)
  (cnt : Z) (eid : EventID) (rest : list EventID)
  (success : bool) : Prop :=
  valid_stable_glob_vars sg /\
  crit_rel_no_os_state_change ls0 ls_inside /\
  if success
  then sem_create_success_transition_prop
         sg ls0 ls_post cnt eid rest /\
       crit_rel_event_only ls_inside ls_post
  else ls_post = ls0.

(* Ordered public observation. Every later arm includes the negation of the
   earlier source guard. *)
Definition sem_create_result_prop
  (sg : StableGlobVars) (ls0 ls_post : UCOS2_Verify_State)
  (cnt isr free_head : Z) (eid : EventID) (rest : list EventID)
  (ret : Z) : Prop :=
  (isr > 0 /\ ret = 0 /\ ls_post = ls0) \/
  (isr <= 0 /\ free_head = 0 /\ ret = 0 /\ ls_post = ls0) \/
  (isr <= 0 /\ free_head <> 0 /\
   free_head = event_addr sg eid /\ ret = event_addr sg eid /\
   sem_create_success_transition_prop
     sg ls0 ls_post cnt eid rest).

Definition OSSemCreate_sem (sg : StableGlobVars) (cnt : Z)
  : program UCOS2_Verify_State (option EventID) :=
  fun ls0 oid ls_post =>
    (ls0.(IntrState).(intNesting) > 0 /\
     oid = None /\ ls_post = ls0) \/
    (ls0.(IntrState).(intNesting) <= 0 /\
     ls0.(EventState).(unUsedEventStates) = [] /\
     oid = None /\ ls_post = ls0) \/
    (exists eid rest,
       ls0.(IntrState).(intNesting) <= 0 /\
       ls0.(EventState).(unUsedEventStates) = eid :: rest /\
       oid = Some eid /\
       sem_create_success_transition_prop
         sg ls0 ls_post cnt eid rest).

Definition observe_sem_create_ptr (sg : StableGlobVars)
  (oid : option EventID)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 p X2 =>
    p = match oid with
        | Some eid => event_addr sg eid
        | None => 0
        end /\ X2 = X1.

(* Reusable L3/L5 publication facts for the semaphore event extension. *)
Lemma sem_create_old_event_none__event_detach_initialize_publish :
  forall sg before_t before_e eid rest,
    EventStateDef.unUsedEventStates before_e = eid :: rest ->
    verification_slice_event_in_range sg before_t before_e ->
    EventStateDef.inUsedEventStates before_e eid = None.
Proof.
  intros sg before_t before_e eid rest Hfree Hvalid.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hvalid.
  destruct Hvalid as [_ [_ [_ [Hpartition _]]]].
  eapply event_slot_partition_free_lookup; eauto.
  rewrite Hfree. simpl. auto.
Qed.

Lemma sem_create_event_valid_after__event_detach_initialize_publish :
  forall sg cnt eid rest before_t before_e,
    event_count_value_range_prop cnt ->
    stable_glob_vars.valid_event_id sg eid ->
    EventStateDef.unUsedEventStates before_e = eid :: rest ->
    verification_slice_event_in_range sg before_t before_e ->
    verification_slice_event_in_range sg before_t
      (sem_create_event_after cnt eid rest before_e).
Proof.
  intros sg cnt eid rest before_t before_e Hcnt Heid Hfree Hvalid.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in *.
  destruct Hvalid as
    [Hids [Hnodup [Hfreeids [Hnone [Hfields [Hpayload [Hqueue Hwait]]]]]]].
  rewrite Hfree in Hnodup, Hfreeids.
  apply NoDup_cons_iff in Hnodup.
  destruct Hnodup as [Heid_notin Hrest_nodup].
  inversion Hfreeids as [|? ? Heid_range Hrest_range]; subst.
  unfold sem_create_event_after.
  refine (conj _
    (conj Hrest_nodup
      (conj Hrest_range
        (conj _
          (conj _
            (conj _ (conj _ _))))))).
  - intros eid0 e Hget.
    unfold sem_create_event_after in Hget. simpl in Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0. exact Heid.
    + exact (Hids _ _ Hget).
  - eapply event_slot_partition_preserved_create; eauto.
  - intros eid0 e Hget.
    unfold sem_create_event_after in Hget. simpl in Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget.
      unfold sem_create_fresh_event, event_fields_consistency.
      simpl. repeat split; try reflexivity; discriminate.
    + eapply Hfields; eauto.
  - intros eid0 e Hget.
    unfold sem_create_event_after in Hget. simpl in Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget.
      unfold sem_create_fresh_event, event_payload_consistency,
        sem_fields_consistency.
      unfold event_count_value_range_prop in Hcnt.
      simpl. split; [exact Hcnt |].
      intro Hnil. exfalso. apply Hnil. reflexivity.
    + eapply Hpayload; eauto.
  - intros eid1 eid2 e1 e2 qid Hget1 Hget2 Hq1 Hq2.
    unfold sem_create_event_after in Hget1, Hget2. simpl in Hget1, Hget2.
    destruct (Z.eqb eid1 eid) eqn:Heq1.
    + inversion Hget1; subst e1.
      unfold sem_create_fresh_event, event_queue_id in Hq1.
      discriminate.
    + destruct (Z.eqb eid2 eid) eqn:Heq2.
      * inversion Hget2; subst e2.
        unfold sem_create_fresh_event, event_queue_id in Hq2.
        discriminate.
      * eapply Hqueue; eauto.
  - intros eid0 e Hget.
    unfold sem_create_event_after in Hget. simpl in Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0.
      inversion Hget; subst e.
      apply verification_slice_event_wait_entry_consistency_empty_waitList_general.
      reflexivity.
    + eapply Hwait; eauto.
Qed.

Lemma sem_create_waitlist_consistency__event_detach_initialize_publish :
  forall sg cnt eid rest ls0,
    task_event_id_unreferenced_prop ls0 eid ->
    verification_slice_event_wait_object_consistency sg ls0 ->
    verification_slice_event_wait_object_consistency sg
      (sem_create_state_after cnt eid rest ls0).
Proof.
  intros sg cnt eid rest ls0 Hunref Hwait.
  unfold verification_slice_event_wait_object_consistency in *.
  destruct Hwait as [Hforward [Hrefback Hclosed]].
  split.
  - intros eid0 e Hget.
    unfold sem_create_state_after, sem_create_event_after in Hget |- *.
    simpl in *.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget; subst e.
      apply verification_slice_event_wait_entry_consistency_empty_waitList_general.
      reflexivity.
    + eapply Hforward; eauto.
  - split.
    + intros tid t eid0 e Htask Hget Href.
      unfold sem_create_state_after, sem_create_event_after in Htask, Hget.
      simpl in Htask, Hget.
      destruct (Z.eqb eid0 eid) eqn:Heq.
      * apply Z.eqb_eq in Heq; subst eid0.
        destruct (Hunref tid t Htask) as [Hsingle Hmulti].
        destruct Href; contradiction.
      * eapply Hrefback; eauto.
    + eapply
      (event_wait.task_event_reference_closure_preserved_by_event_extension
        ls0.(TskState) ls0.(EventState)
        (sem_create_state_after cnt eid rest ls0).(EventState)).
      * intros eid0 [e Hget].
        unfold sem_create_state_after, sem_create_event_after. simpl.
        destruct (Z.eqb eid0 eid); [|eexists; exact Hget]. eexists. reflexivity.
      * exact Hclosed.
Qed.

Lemma sem_create_cross_consistency__event_detach_initialize_publish :
  forall sg cnt eid rest ls0,
    event_count_value_range_prop cnt ->
    EventStateDef.unUsedEventStates ls0.(EventState) = eid :: rest ->
    verification_slice_event_in_range sg ls0.(TskState) ls0.(EventState) ->
    task_event_id_unreferenced_prop ls0 eid ->
    verification_slice_cross_module_consistency sg ls0 ->
    verification_slice_cross_module_consistency sg
      (sem_create_state_after cnt eid rest ls0).
Proof.
  intros sg cnt eid rest ls0 Hcnt Hfree Hevent Hunref Hcross.
  pose proof (sem_create_old_event_none__event_detach_initialize_publish
    sg ls0.(TskState) ls0.(EventState) eid rest Hfree Hevent) as Hnone.
  assert (Hlookup : forall mid e,
    ls0.(EventState).(inUsedEventStates) mid = Some e ->
    (if Z.eqb mid eid then Some (sem_create_fresh_event cnt)
     else ls0.(EventState).(inUsedEventStates) mid) = Some e).
  { intros mid e Hget. destruct (Z.eqb mid eid) eqn:Hmid.
    - apply Z.eqb_eq in Hmid. subst mid.
      rewrite Hnone in Hget. discriminate.
    - exact Hget. }
  unfold verification_slice_cross_module_consistency in Hcross |- *.
  destruct Hcross as
    [Hos [Hpt [Howner [Hwait [Hready [Horder
      [Hceiling [Hunique [Hprotocol Hpcp_unique]]]]]]]]].
  refine (conj _
    (conj _
      (conj _
        (conj _
          (conj _
            (conj _ (conj _ (conj _ (conj _ _))))))))).
  - unfold osprio_cur_consistency, sem_create_state_after. simpl. exact Hos.
  - intros p.
    specialize (Hpt p).
    unfold sem_create_state_after, sem_create_event_after. simpl.
    destruct (ls0.(TskState).(prioTbl) p); simpl in Hpt |- *.
    + destruct Hpt as [Hnoready Hnomutex]. split; [exact Hnoready|].
      intros [mid [e [m [Hget [Htype [Hfields Hreserve]]]]]].
      unfold sem_create_event_after in Hget. simpl in Hget.
      destruct (Z.eqb mid eid) eqn:Hmid.
      * inversion Hget; subst e.
        unfold sem_create_fresh_event in Htype, Hfields. simpl in *.
        discriminate.
      * apply Hnomutex. exists mid, e, m. repeat split; auto.
        unfold mutex.mutex_reserves_priority_slot in Hreserve.
        exact (proj1 Hreserve).
        exact (proj2 Hreserve).
    + destruct Hpt as [mid [e [m [Hget [Htype [Hfields [Hpcp Howner']]]]]]].
      exists mid, e, m. repeat split; auto.
    + destruct Hpt as [t [Htask [Hcur | Hmutex]]].
      * exists t. split; [exact Htask | left; exact Hcur].
      * destruct Hmutex as
          [mid [e [m [Hget [Htype [Hfields [Howner' Hsource]]]]]]].
        exists t. split.
        -- exact Htask.
        -- right. exists mid, e, m. split.
           ++ apply Hlookup. exact Hget.
           ++ repeat split; auto.
  - intros mid e m [Hget [Htype Hfields]].
    unfold sem_create_state_after, sem_create_event_after in Hget. simpl in Hget.
    destruct (Z.eqb mid eid) eqn:Hmid.
    + inversion Hget; subst e.
      unfold sem_create_fresh_event in Htype, Hfields. simpl in *. discriminate.
    + eapply Howner; eauto.
  - eapply sem_create_waitlist_consistency__event_detach_initialize_publish;
      eauto.
  - unfold ready_list_completeness, sem_create_state_after. simpl. exact Hready.
  - unfold ready_list_order, sem_create_state_after. simpl. exact Horder.
  - unfold ceiling_priotbl_free, sem_create_state_after. simpl. exact Hceiling.
  - unfold task_priority_unique_prop, sem_create_state_after. simpl. exact Hunique.
  - intros mid e m Hget Htype Hfields.
    unfold sem_create_state_after, sem_create_event_after in Hget. simpl in Hget.
    destruct (Z.eqb mid eid) eqn:Hmid.
    + inversion Hget; subst e.
      unfold sem_create_fresh_event in Htype, Hfields. simpl in *. discriminate.
    + eapply Hprotocol; eauto.
  - eapply mutex_enabled_pcp_unique_transport with (lvs1 := ls0).
    + intros mid e m Hget Htype Hfields.
      unfold sem_create_state_after, sem_create_event_after in Hget.
      simpl in Hget.
      destruct (Z.eqb mid eid) eqn:Hmid.
      * inversion Hget; subst e.
        unfold sem_create_fresh_event in Htype, Hfields.
        simpl in *. discriminate.
      * exists e, m. repeat split; try assumption; reflexivity.
    + exact Hpcp_unique.
Qed.

Lemma sem_create_unreferenced_free_head__entry_closure :
  forall sg ls0 eid rest,
    EventStateDef.unUsedEventStates ls0.(EventState) = eid :: rest ->
    verification_slice_event_in_range sg ls0.(TskState) ls0.(EventState) ->
    verification_slice_cross_module_consistency sg ls0 ->
    task_event_id_unreferenced_prop ls0 eid.
Proof.
  intros sg ls0 eid rest Hfree Hevent Hcross.
  pose proof (sem_create_old_event_none__event_detach_initialize_publish
    sg ls0.(TskState) ls0.(EventState) eid rest Hfree Hevent) as Hnone.
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as [_ [_ [_ [Hwait _]]]].
  unfold verification_slice_event_wait_object_consistency in Hwait.
  destruct Hwait as [_ [_ Hclosed]].
  eapply event_wait.task_event_reference_closure_implies_unreferenced;
    eauto.
Qed.

Lemma sem_create_used_event_map_after__event_detach_initialize_publish :
  forall sg cnt eid rest before_t before_e,
    EventStateDef.inUsedEventStates before_e eid = None ->
    store_used_event_map sg before_t
        (EventStateDef.inUsedEventStates before_e) **
      used_complete_event sg before_t (event_addr sg eid) eid
        (sem_create_fresh_event cnt)
    |--
    store_used_event_map sg before_t
      (EventStateDef.inUsedEventStates
        (sem_create_event_after cnt eid rest before_e)).
Proof.
  intros sg cnt eid rest before_t before_e Hnone.
  unfold store_used_event_map, sem_create_event_after.
  simpl.
  sep_apply_l_atomic
    (store_map_equiv_store_map_missing
      (fun eid0 e =>
        used_complete_event sg before_t (event_addr sg eid0) eid0 e)
      (EventStateDef.inUsedEventStates before_e) eid Hnone).
  assert (Hother : forall eid0, eid0 <> eid ->
    EventStateDef.inUsedEventStates before_e eid0 =
      (if Z.eqb eid0 eid then Some (sem_create_fresh_event cnt)
       else EventStateDef.inUsedEventStates before_e eid0)).
  { intros eid0 Hneq.
    apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity. }
  pose proof
    (proj1 (store_map_missing_i_equiv
      (fun eid0 e =>
        used_complete_event sg before_t (event_addr sg eid0) eid0 e)
      (EventStateDef.inUsedEventStates before_e)
      (fun eid0 =>
        if Z.eqb eid0 eid then Some (sem_create_fresh_event cnt)
        else EventStateDef.inUsedEventStates before_e eid0)
      eid Hother)) as Hmissing.
  sep_apply_l_atomic Hmissing.
  apply (store_map_merge
    (fun eid0 e =>
      used_complete_event sg before_t (event_addr sg eid0) eid0 e)
    eid (sem_create_fresh_event cnt)
    (fun eid0 =>
      if Z.eqb eid0 eid then Some (sem_create_fresh_event cnt)
      else EventStateDef.inUsedEventStates before_e eid0)).
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma sem_create_full_inv_after__event_detach_initialize_publish :
  forall sg cnt eid rest before,
    valid_stable_glob_vars sg ->
    event_count_value_range_prop cnt ->
    stable_glob_vars.valid_event_id sg eid ->
    EventStateDef.unUsedEventStates before.(EventState) = eid :: rest ->
    sem_create_node_open_inv sg before rest **
      sg.(g_OSEventFreeList) # Ptr |-> free_event_head sg rest **
      sem_create_initialized_event sg
        (sem_create_state_after cnt eid rest before) cnt eid
    |-- UCOS2_verification_slice_inv sg
      (sem_create_state_after cnt eid rest before).
Proof.
  intros sg cnt eid rest before Hstable Hcnt Heid Hfree.
  unfold sem_create_node_open_inv, verification_slice_event_inv_free_head_rest.
  pureIntros.
  match goal with
  | Hevent : verification_slice_event_in_range sg before.(TskState) before.(EventState),
    Hcross : verification_slice_cross_module_consistency sg before |- _ =>
      pose proof
        (sem_create_unreferenced_free_head__entry_closure
          sg before eid rest Hfree Hevent Hcross) as Hunref;
      pose proof
        (sem_create_old_event_none__event_detach_initialize_publish
          sg before.(TskState) before.(EventState) eid rest Hfree Hevent)
        as Hnone;
      pose proof
        (sem_create_event_valid_after__event_detach_initialize_publish
          sg cnt eid rest before.(TskState) before.(EventState)
          Hcnt Heid Hfree Hevent) as Hevent_after;
      pose proof
        (sem_create_cross_consistency__event_detach_initialize_publish
          sg cnt eid rest before Hcnt Hfree Hevent Hunref Hcross)
        as Hcross_after
  end.
  unfold UCOS2_verification_slice_inv, verification_slice_event_inv,
    store_free_event_list, sem_create_initialized_event,
    sem_create_state_after.
  simpl.
  sep_apply_l_atomic
    (sem_create_used_event_map_after__event_detach_initialize_publish
      sg cnt eid rest before.(TskState) before.(EventState) Hnone).
  entailer!.
Qed.

Lemma sem_create_free_head_zero_empty__sem_create_current_all_manual :
  forall sg s head,
    valid_stable_glob_vars sg ->
    event_free_list_head_prop sg s.(EventState) head ->
    sem_create_head_open_inv sg s |--
      coq_prop (head = 0 -> s.(EventState).(unUsedEventStates) = []).
Proof.
  intros sg s head Hstable Hhead.
  unfold sem_create_head_open_inv, verification_slice_event_inv_no_free_head.
  pureIntros.
  apply derivable1s_coq_prop_r.
  intro Hz.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in H.
  destruct H as [_ [_ [Hfreeids _]]].
  destruct s.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hlist.
  - reflexivity.
  - inversion Hfreeids as [|? ? Heid _]; subst.
    unfold event_free_list_head_prop, free_event_head in Hhead.
    rewrite Hlist in Hhead. simpl in Hhead.
    unfold event_addr, event_pool_addr, event_object_size in Hhead.
    unfold valid_stable_glob_vars, valid_stable_global_addresses in Hstable.
    destruct Hstable as
      [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Haddrs _]]]]]]]]]]]]].
    unfold stable_global_addresses in Haddrs.
    inversion Haddrs as [|? ? Hbase _]; subst.
    simpl in Hbase.
    exfalso. destruct sg.(osKernelConfig).(cfgEventNames); lia.
Qed.
Lemma sem_create_head_open_rebuild__sem_create_current_all_manual :
  forall sg s head p,
    event_free_list_head_prop sg s.(EventState) head ->
    os_event_free_list_addr sg p ->
    sem_create_head_open_inv sg s ** p # Ptr |-> head |--
      UCOS2_verification_slice_inv sg s.
Proof.
  intros sg s head p Hhead Haddr.
  unfold event_free_list_head_prop in Hhead.
  unfold os_event_free_list_addr in Haddr.
  subst head p.
  unfold sem_create_head_open_inv, UCOS2_verification_slice_inv,
    verification_slice_event_inv_no_free_head, verification_slice_event_inv, store_free_event_list.
  pureIntros.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - apply _derivable1_andp_intros.
    + apply derivable1s_coq_prop_r. exact H0.
    + cancel.
Qed.
Lemma sem_create_head_open_localize__sem_create_current_all_manual :
  forall sg s eid rest,
    s.(EventState).(unUsedEventStates) = eid :: rest ->
    sem_create_head_open_inv sg s |--
      sem_create_node_open_inv sg s rest **
      sem_create_free_head_event sg eid rest.
Proof.
  intros sg s eid rest Hfree.
  unfold sem_create_head_open_inv, sem_create_node_open_inv,
    verification_slice_event_inv_no_free_head, verification_slice_event_inv_free_head_rest,
    sem_create_free_head_event.
  rewrite Hfree.
  simpl.
  pureIntros.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - apply _derivable1_andp_intros.
    + apply derivable1s_coq_prop_r. exact H0.
    + cancel.
Qed.
Lemma sem_create_free_head_valid_id__sem_create_current_all_manual :
  forall sg s eid rest,
    s.(EventState).(unUsedEventStates) = eid :: rest ->
    sem_create_head_open_inv sg s |-- coq_prop (valid_event_id sg eid).
Proof.
  intros sg s eid rest Hfree.
  unfold sem_create_head_open_inv, verification_slice_event_inv_no_free_head.
  pureIntros.
  apply derivable1s_coq_prop_r.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in H.
  destruct H as [_ [_ [Hids _]]].
  rewrite Hfree in Hids.
  inversion Hids; subst.
  exact H2.
Qed.
Lemma sem_create_node_open_valid_id__sem_create_current_all_manual :
  forall sg s eid rest,
    s.(EventState).(unUsedEventStates) = eid :: rest ->
    sem_create_node_open_inv sg s rest |-- coq_prop (valid_event_id sg eid).
Proof.
  intros sg s eid rest Hfree.
  unfold sem_create_node_open_inv, verification_slice_event_inv_free_head_rest.
  pureIntros.
  apply derivable1s_coq_prop_r.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in H.
  destruct H as [_ [_ [Hids _]]].
  rewrite Hfree in Hids.
  inversion Hids; subst.
  exact H2.
Qed.
Lemma sem_create_initialized_event_from_fields__sem_create_current_all_manual :
  forall sg s cnt eid rest type_addr ptr_addr cnt_addr grp_addr tbl_addr,
    event_core_fields_layout_prop sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    grp_addr # UChar |-> 0 ** tbl_addr # UChar |-> 0 **
    (tbl_addr + 1 * sizeof(UCHAR)) # UChar |-> 0 **
    (tbl_addr + 2 * sizeof(UCHAR)) # UChar |-> 0 **
    (tbl_addr + 3 * sizeof(UCHAR)) # UChar |-> 0 **
    (tbl_addr + 4 * sizeof(UCHAR)) # UChar |-> 0 **
    (tbl_addr + 5 * sizeof(UCHAR)) # UChar |-> 0 **
    (tbl_addr + 6 * sizeof(UCHAR)) # UChar |-> 0 **
    (tbl_addr + 7 * sizeof(UCHAR)) # UChar |-> 0 **
    type_addr # UChar |-> 3 ** ptr_addr # Ptr |-> 0 ** cnt_addr # UShort |-> cnt
    |-- sem_create_initialized_event sg (sem_create_state_after cnt eid rest s) cnt eid.
Proof.
  intros sg s cnt eid rest type_addr ptr_addr cnt_addr grp_addr tbl_addr Hcore Hwait.
  unfold event_core_fields_layout_prop in Hcore; destruct Hcore as [Htype [Hptr Hcnt]].
  unfold event_wait_fields_layout_prop in Hwait; destruct Hwait as [Hgrp Htbl].
  subst type_addr ptr_addr cnt_addr grp_addr tbl_addr.
  unfold sem_create_initialized_event, sem_create_state_after, used_complete_event,
    sem_create_fresh_event, encode_event_type, verification_slice_encode_event_ptr_value,
    encode_event_cnt_value, encode_event_wait_grp, encode_event_wait_tbl_at; simpl.
  cancel ((event_addr sg eid + OSEventType_off) # UChar |-> 3).
  cancel ((event_addr sg eid + OSEventPtr_off) # Ptr |-> 0).
  cancel ((event_addr sg eid + OSEventCnt_off) # UShort |-> cnt).
  cancel ((event_addr sg eid + OSEventGrp_off) # UChar |-> 0).
  replace (event_addr sg eid + OSEventTbl_off + 0) with (event_addr sg eid + OSEventTbl_off) by lia.
  cancel ((event_addr sg eid + OSEventTbl_off) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 1) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 2) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 3) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 4) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 5) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 6) # UChar |-> 0).
  cancel ((event_addr sg eid + OSEventTbl_off + 7) # UChar |-> 0).
Qed.
Lemma sem_create_outsidecritical_after__sem_create_current_all_manual :
  forall sg s cnt eid rest, ucos2_rules_lib.OutsideCritical sg s |--
    ucos2_rules_lib.OutsideCritical sg (sem_create_state_after cnt eid rest s).
Proof.
  intros sg s cnt eid rest.
  unfold ucos2_rules_lib.OutsideCritical, UCOS2_C_Rules.OutsideCritical,
    UCOS2_Critical_Rules.OutsideCritical.
  Intros s'. Exists s'. split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact H.
Qed.
