Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
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
Import Monad.
Import TaskStateDef.
Import EventStateDef.
Import InterruptStateDef.
Import UCOS2_C_Rules.

Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source-visible outcomes of the selected OSSemDel configuration.  The
    two ALWAYS outcomes are kept distinct so the public semantics records
    exactly when the source calls OS_Sched. *)
Inductive SemDelResult : Type :=
| SemDelNull
| SemDelWrongType
| SemDelISR
| SemDelNoPendDeleted
| SemDelNoPendWaiting
| SemDelAlwaysNoWait
| SemDelAlwaysWaiting (sched_res : SchedResult)
| SemDelInvalidOpt.

Definition sem_del_return (pevent : addr) (res : SemDelResult) : addr :=
  match res with
  | SemDelNoPendDeleted
  | SemDelAlwaysNoWait
  | SemDelAlwaysWaiting _ => 0
  | _ => pevent
  end.

Definition sem_del_error (res : SemDelResult) : Z :=
  match res with
  | SemDelNull          => encode_os_err_code OS_ERR_PEVENT_NULL
  | SemDelWrongType     => encode_os_err_code OS_ERR_EVENT_TYPE
  | SemDelISR           => encode_os_err_code OS_ERR_DEL_ISR
  | SemDelNoPendDeleted => encode_os_err_code OS_ERR_NONE
  | SemDelNoPendWaiting => encode_os_err_code OS_ERR_TASK_WAITING
  | SemDelAlwaysNoWait  => encode_os_err_code OS_ERR_NONE
  | SemDelAlwaysWaiting _ => encode_os_err_code OS_ERR_NONE
  | SemDelInvalidOpt    => encode_os_err_code OS_ERR_INVALID_OPT
  end.

(** One literal loop-body call of OS_EventTaskRdy. *)
Definition sem_del_wake_step
  (sg : StableGlobVars) (eid : EventID)
  (pre : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (post : UCOS2_Verify_State) : Prop :=
  atomic_event_task_rdy_one
    sg eid PendSem None PendAbort pre returned_prio
    canonical_waiter table_owner post.

(** Reflexive transitive closure whose only non-reflexive constructor is a
    source-literal OS_EventTaskRdy call.  This is the wake-all cardinality
    account used by the loop invariant and the public semantics. *)
Inductive sem_del_wake_prefix
  (sg : StableGlobVars) (eid : EventID)
  : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| sem_del_wake_prefix_refl :
    forall entry, sem_del_wake_prefix sg eid entry entry
| sem_del_wake_prefix_step :
    forall entry current next returned_prio
           canonical_waiter table_owner,
      sem_del_wake_prefix sg eid entry current ->
      sem_del_wake_step sg eid current returned_prio
        canonical_waiter table_owner next ->
      sem_del_wake_prefix sg eid entry next.

Definition sem_del_wake_progress
  (sg : StableGlobVars) (eid : EventID)
  (entry current : UCOS2_Verify_State)
  (e : OSEventAbstractState) : Prop :=
  sem_del_wake_prefix sg eid entry current /\
  current.(EventState).(inUsedEventStates) eid = Some e /\
  e.(eventType) = OS_EVENT_TYPE_SEM.

Definition sem_del_wake_endpoint
  (sg : StableGlobVars) (eid : EventID)
  (entry current : UCOS2_Verify_State) : Prop :=
  sem_del_wake_prefix sg eid entry current /\
  exists e sf,
    current.(EventState).(inUsedEventStates) eid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_SEM /\
    e.(semFields) = Some sf /\
    e.(waitList) = [].

Definition sem_del_loop_progress := sem_del_wake_progress.
Definition sem_del_loop_endpoint := sem_del_wake_endpoint.

(** The four concrete free-list writes remove the live map entry and push
    its EventID at the head of the free list.  The stale group/table bytes
    become don't-care fields of the free node, exactly as in [event.v]. *)
Definition sem_del_freed_event_state
  (pre : UCOS2_Verify_State) (eid : EventID)
  : UCOS2_Verify_State :=
  replace_EventS
    {| inUsedEventStates := fun other =>
         if Z.eqb other eid then None
         else pre.(EventState).(inUsedEventStates) other;
       eventLifecycle := pre.(EventState).(eventLifecycle);
       publishedQueueBytes := pre.(EventState).(publishedQueueBytes);
       unUsedEventStates := eid :: pre.(EventState).(unUsedEventStates) |}
    pre.

Definition sem_del_free_step
  (pre : UCOS2_Verify_State) (eid : EventID)
  (post : UCOS2_Verify_State) : Prop :=
  exists e sf,
    pre.(EventState).(inUsedEventStates) eid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_SEM /\
    e.(semFields) = Some sf /\
    e.(waitList) = [] /\
    post = sem_del_freed_event_state pre eid.

(** A live-to-free event transition removes exactly one map entry.  These
    lookup facts are deliberately operation-independent: they record the
    submap relation needed by event validity and cross-module preservation,
    without mentioning an OSSemDel control-flow branch. *)
Lemma sem_del_freed_lookup_some_before :
  forall pre eid other e,
    (sem_del_freed_event_state pre eid).(EventState).(inUsedEventStates)
      other = Some e ->
    pre.(EventState).(inUsedEventStates) other = Some e.
Proof.
  intros pre eid other e Hlookup.
  unfold sem_del_freed_event_state in Hlookup.
  simpl in Hlookup.
  destruct (Z.eqb other eid) eqn:Heq; [discriminate | exact Hlookup].
Qed.

Lemma sem_del_freed_lookup_other :
  forall pre eid other,
    other <> eid ->
    (sem_del_freed_event_state pre eid).(EventState).(inUsedEventStates)
      other =
    pre.(EventState).(inUsedEventStates) other.
Proof.
  intros pre eid other Hneq.
  unfold sem_del_freed_event_state.
  simpl.
  destruct (Z.eqb other eid) eqn:Heq; [|reflexivity].
  apply Z.eqb_eq in Heq. contradiction.
Qed.

Lemma sem_del_freed_event_validity :
  forall sg pre eid old,
    pre.(EventState).(inUsedEventStates) eid = Some old ->
    verification_slice_event_in_range sg pre.(TskState) pre.(EventState) ->
    verification_slice_event_in_range sg
      (sem_del_freed_event_state pre eid).(TskState)
      (sem_del_freed_event_state pre eid).(EventState).
Proof.
  intros sg pre eid old Hused Hvalid.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in *.
  destruct Hvalid as
    [Hrange [Hnodup [Hfree_range [Hpartition
     [Hfields [Hpayload [Hqueue Hwait]]]]]]].
  split.
  {
    intros other ev Hlookup.
    eapply Hrange.
    eapply sem_del_freed_lookup_some_before; eauto.
  }
  split.
  {
    simpl. constructor.
    - eapply event_slot_partition_used_not_free; eauto.
    - exact Hnodup.
  }
  split.
  {
    simpl. constructor.
    - eapply Hrange; eauto.
    - exact Hfree_range.
  }
  split.
  {
    unfold sem_del_freed_event_state. simpl.
    eapply event_slot_partition_preserved_delete; eauto.
  }
  split.
  {
    intros other ev Hlookup.
    eapply Hfields.
    eapply sem_del_freed_lookup_some_before; eauto.
  }
  split.
  {
    intros other ev Hlookup.
    eapply Hpayload.
    eapply sem_del_freed_lookup_some_before; eauto.
  }
  split.
  {
    unfold queue_binding_unique in *.
    intros eid1 eid2 e1 e2 qid Hget1 Hget2 Hqid1 Hqid2.
    eapply Hqueue; eauto using sem_del_freed_lookup_some_before.
  }
  intros other ev Hlookup.
  eapply Hwait.
  eapply sem_del_freed_lookup_some_before; eauto.
Qed.

(** The current shared event-wait invariant contains reference closure, but
    deleting a live map entry additionally needs the selected EventID to be
    absent from every TCB reference.  Keeping that premise explicit makes
    this preservation theorem sound and exposes precisely what an operation
    boundary or a strengthened shared invariant must provide. *)
Lemma sem_del_freed_event_wait_consistency :
  forall sg pre eid,
    verification_slice_event_wait_object_consistency sg pre ->
    task_event_id_unreferenced_prop pre eid ->
    verification_slice_event_wait_object_consistency sg (sem_del_freed_event_state pre eid).
Proof.
  intros sg pre eid Hconsistent Hunreferenced.
  unfold verification_slice_event_wait_object_consistency in *.
  destruct Hconsistent as [Hentry [Htotal Hclosed]].
  split; [|split].
  - intros other ev Hlookup.
    eapply Hentry.
    eapply sem_del_freed_lookup_some_before; eauto.
  - unfold task_event_reference_backlink_consistency in *.
    intros tid t other e Htask Hlookup Hreference.
    destruct (Z.eq_dec other eid) as [Heq | Hneq].
    + subst other.
      specialize (Hunreferenced tid t Htask) as [Hsingle Hmulti].
      destruct Hreference as [Hreference | Hreference]; contradiction.
    + eapply Htotal; eauto.
      eapply sem_del_freed_lookup_some_before; eauto.
  - unfold task_event_reference_closure in *.
    intros tid t Htask.
    specialize (Hclosed tid t Htask) as [Hsingle Hmulti].
    specialize (Hunreferenced tid t Htask) as [Hsingle_neq Hmulti_neq].
    split.
    + intros other Hptr.
      destruct (Z.eq_dec other eid) as [Heq | Hneq].
      * subst other. contradiction.
      * destruct (Hsingle other Hptr) as [e Hlookup].
        exists e. rewrite sem_del_freed_lookup_other; auto.
    + intros other Hin.
      destruct (Z.eq_dec other eid) as [Heq | Hneq].
      * subst other. contradiction.
      * destruct (Hmulti other Hin) as [e Hlookup].
        exists e. rewrite sem_del_freed_lookup_other; auto.
Qed.

Lemma sem_del_freed_cross_module_consistency :
  forall sg pre eid old,
    pre.(EventState).(inUsedEventStates) eid = Some old ->
    old.(eventType) = OS_EVENT_TYPE_SEM ->
    task_event_id_unreferenced_prop pre eid ->
    verification_slice_cross_module_consistency sg pre ->
    verification_slice_cross_module_consistency sg (sem_del_freed_event_state pre eid).
Proof.
  intros sg pre eid old Hused Hsem Hunreferenced Hcross.
  assert (Hlookup_back : forall mid e,
    (sem_del_freed_event_state pre eid).(EventState).(inUsedEventStates)
      mid = Some e ->
    pre.(EventState).(inUsedEventStates) mid = Some e).
  { intros. eapply sem_del_freed_lookup_some_before; eauto. }
  assert (Hmutex_forward : forall mid e m,
    pre.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    (sem_del_freed_event_state pre eid).(EventState).(inUsedEventStates)
      mid = Some e).
  {
    intros mid e m Hlookup Hmutex Hfields.
    assert (Hneq : mid <> eid).
    {
      intro Heq. subst mid.
      rewrite Hused in Hlookup. inversion Hlookup; subst e.
      rewrite Hsem in Hmutex. discriminate.
    }
    rewrite sem_del_freed_lookup_other; auto.
  }
  unfold verification_slice_cross_module_consistency in *.
  destruct Hcross as
    [Hosprio [Hpriotbl [Howner [Hwait
     [Hready_complete [Hready_order [Hceiling
      [Htask_unique [Hprotocol Hpcp_unique]]]]]]]]].
  split.
  {
    eapply osprio_cur_consistency_indep_EventState.
    - reflexivity.
    - reflexivity.
    - exact Hosprio.
  }
  split.
  {
    unfold priotbl_consistency in *.
    unfold sem_del_freed_event_state. simpl.
    intro p. specialize (Hpriotbl p).
    destruct (pre.(TskState).(prioTbl) p) eqn:Hslot;
      simpl in Hpriotbl |- *.
    - destruct Hpriotbl as [Hno_ready Hno_mutex].
      split.
      + exact Hno_ready.
      + intros [mid [e [m [Hlookup [Hmutex [Hfields Hreserve]]]]]].
        apply Hno_mutex. exists mid, e, m.
        split; [eapply Hlookup_back; eauto |].
        split; [exact Hmutex |].
        split; [exact Hfields | exact Hreserve].
    - destruct Hpriotbl as [mid [e [m [Hlookup
        [Hmutex [Hfields [Hpcp Howner_state]]]]]]].
      exists mid, e, m.
      split; [eapply Hmutex_forward; eauto |].
      split; [exact Hmutex |].
      split; [exact Hfields |].
      split; [exact Hpcp | exact Howner_state].
    - destruct Hpriotbl as [t [Htask [Htask_prio | Hmutex_case]]].
      + exists t. split; [exact Htask | left; exact Htask_prio].
      + destruct Hmutex_case as
          [mid [e [m [Hlookup [Hmutex [Hfields
           [Howner_id Hprio_source]]]]]]].
        exists t. split; [exact Htask | right].
        exists mid, e, m.
        split; [eapply Hmutex_forward; eauto |].
        split; [exact Hmutex |].
        split; [exact Hfields |].
        split; [exact Howner_id | exact Hprio_source].
  }
  split.
  {
    unfold mutex_owner_consistency in *.
    intros mid e m [Hlookup [Hmutex Hfields]].
    apply (Howner mid e m).
    split; [eapply Hlookup_back; eauto |].
    split; [exact Hmutex | exact Hfields].
  }
  split.
  { eapply sem_del_freed_event_wait_consistency; eauto. }
  split.
  {
    eapply ready_list_completeness_indep_EventState.
    - reflexivity.
    - reflexivity.
    - exact Hready_complete.
  }
  split.
  {
    eapply ready_list_order_indep_EventState.
    - reflexivity.
    - reflexivity.
    - exact Hready_order.
  }
  split.
  { exact Hceiling. }
  split.
  { exact Htask_unique. }
  split.
  {
    unfold mutex_protocol_consistency in *.
    intros mid e m Hlookup Hmutex Hfields.
    apply (Hprotocol mid e m).
    - eapply Hlookup_back; eauto.
    - exact Hmutex.
    - exact Hfields.
  }
  eapply mutex_enabled_pcp_unique_transport.
  - intros mid e m Hlookup Hmutex Hfields.
    exists e, m.
    split; [eapply Hlookup_back; eauto |].
    split; [exact Hmutex |].
    split; [exact Hfields | reflexivity].
  - exact Hpcp_unique.
Qed.

Lemma sem_del_free_step_preserves_validity_if_unreferenced :
  forall sg pre eid post,
    UCOS2_verification_slice_state_inv sg pre ->
    task_event_id_unreferenced_prop pre eid ->
    sem_del_free_step pre eid post ->
    UCOS2_verification_slice_state_inv sg post.
Proof.
  intros sg pre eid post Hvalid Hunreferenced Hfree.
  destruct Hfree as [e [sf Hfree]].
  destruct Hfree as
    [Hused [Hsem [Hsem_fields [Hempty Hpost]]]].
  subst post.
  unfold UCOS2_verification_slice_state_inv in *.
  destruct Hvalid as [Htask [Hsched [Hevent Hcross]]].
  split.
  { exact Htask. }
  split.
  { exact Hsched. }
  split.
  { eapply sem_del_freed_event_validity; eauto. }
  eapply sem_del_freed_cross_module_consistency; eauto.
Qed.

(** A selected live event whose wait list is empty has no incoming TCB
    reference under the total event/task backlink invariant.  Consequently
    the public free transition preserves the complete validity bundle without
    exposing an extra premise at the C annotation boundary. *)
Lemma sem_del_free_step_preserves_validity :
  forall sg pre eid post,
    UCOS2_verification_slice_state_inv sg pre ->
    sem_del_free_step pre eid post ->
    UCOS2_verification_slice_state_inv sg post.
Proof.
  intros sg pre eid post Hvalid Hfree.
  assert (Hunreferenced : task_event_id_unreferenced_prop pre eid).
  {
    pose proof Hfree as Hfree_shape.
    destruct Hfree_shape as
      [e [sf [Hused [Hsem [Hsem_fields [Hempty Hpost]]]]]].
    unfold UCOS2_verification_slice_state_inv in Hvalid.
    destruct Hvalid as [_ [_ [_ Hcross]]].
    unfold verification_slice_cross_module_consistency in Hcross.
    destruct Hcross as [_ [_ [_ [Hwait _]]]].
    eapply event_wait_empty_implies_unreferenced; eauto.
  }
  eapply sem_del_free_step_preserves_validity_if_unreferenced; eauto.
Qed.

Definition sem_del_sched_step
  (pre : UCOS2_Verify_State) (res : SchedResult)
  (post : UCOS2_Verify_State) : Prop :=
  atomic_sched pre res post.

Definition sem_del_tasks_waiting_prop
  (entry : UCOS2_Verify_State) (e : OSEventAbstractState)
  (tasks_waiting : Z) : Prop :=
  ((encode_event_wait_grp e.(waitList) entry.(TskState) = 0 /\
    e.(waitList) = [] /\ tasks_waiting = 0) \/
   (encode_event_wait_grp e.(waitList) entry.(TskState) <> 0 /\
    e.(waitList) <> [] /\ tasks_waiting = 1)).

(** Complete ordered semantics of the selected source. *)
Definition OSSemDel_sem
  (sg : StableGlobVars) (pevent : addr) (opt : Z)
  : program UCOS2_Verify_State SemDelResult :=
  fun entry res post =>
    (pevent = 0 /\
     res = SemDelNull /\
     post = entry) \/
    (pevent <> 0 /\
     exists eid e,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) <> OS_EVENT_TYPE_SEM /\
       res = SemDelWrongType /\
       post = entry) \/
    (pevent <> 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       entry.(IntrState).(intNesting) > 0 /\
       res = SemDelISR /\
       post = entry) \/
    (pevent <> 0 /\ opt = 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       entry.(IntrState).(intNesting) = 0 /\
       e.(waitList) = [] /\
       sem_del_free_step entry eid post /\
       res = SemDelNoPendDeleted) \/
    (pevent <> 0 /\ opt = 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       entry.(IntrState).(intNesting) = 0 /\
       e.(waitList) <> [] /\
       res = SemDelNoPendWaiting /\
       post = entry) \/
    (pevent <> 0 /\ opt = 1 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       entry.(IntrState).(intNesting) = 0 /\
       e.(waitList) = [] /\
       sem_del_free_step entry eid post /\
       res = SemDelAlwaysNoWait) \/
    (pevent <> 0 /\ opt = 1 /\
     exists eid e sf drained freed sched_res,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       entry.(IntrState).(intNesting) = 0 /\
       e.(waitList) <> [] /\
       sem_del_wake_endpoint sg eid entry drained /\
       sem_del_free_step drained eid freed /\
       sem_del_sched_step freed sched_res post /\
       res = SemDelAlwaysWaiting sched_res) \/
    (pevent <> 0 /\ opt <> 0 /\ opt <> 1 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       entry.(IntrState).(intNesting) = 0 /\
       res = SemDelInvalidOpt /\
       post = entry).

Definition sem_del_result_prop
  (sg : StableGlobVars) (pevent : addr) (opt : Z)
  (entry post : UCOS2_Verify_State)
  (ret err : Z) : Prop :=
  exists res,
    OSSemDel_sem sg pevent opt entry res post /\
    ret = sem_del_return pevent res /\
    err = sem_del_error res.

Definition sem_del_sem_result_prop := sem_del_result_prop.

Definition OSSemDel_post_token
  (post : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun observed => observed = post.

Lemma OSSemDel_post_token_injective :
  forall ls1 ls2,
    OSSemDel_post_token ls1 = OSSemDel_post_token ls2 -> ls1 = ls2.
Proof.
  intros ls1 ls2 Heq.
  assert (Hseen : OSSemDel_post_token ls2 ls1).
  { rewrite <- Heq. reflexivity. }
  exact Hseen.
Qed.

Definition OSSemDel_LastSeen
  (sg : StableGlobVars) (pevent : addr) (opt : Z)
  (entry : UCOS2_Verify_State) (res : SemDelResult)
  (post : UCOS2_Verify_State)
  : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun X =>
    OSSemDel_sem sg pevent opt entry res post /\
    X = OSSemDel_post_token post.

Definition OSSemDel_atomic_cmd
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pevent : addr) (opt : Z)
  : program (UCOS2_Verify_State -> Prop) SemDelResult :=
  fun X1 res X2 =>
    LastSeen entry X1 /\
    exists post, OSSemDel_LastSeen sg pevent opt entry res post X2.

Definition observe_sem_del_result (pevent : addr) (res : SemDelResult)
  : program (UCOS2_Verify_State -> Prop) addr :=
  fun X1 ret X2 => ret = sem_del_return pevent res /\ X2 = X1.

Lemma OSSemDel_safe_return :
  forall sg pevent opt entry res post
         (X : addr -> (UCOS2_Verify_State -> Prop) -> Prop),
    OSSemDel_sem sg pevent opt entry res post ->
    safeExec (LastSeen entry)
      (bind (OSSemDel_atomic_cmd sg entry pevent opt)
            (observe_sem_del_result pevent)) X ->
    safeExec
      (OSSemDel_LastSeen sg pevent opt entry res post)
      (@StateRelMonad.ret
         (UCOS2_Verify_State -> Prop) addr
         (sem_del_return pevent res)) X.
Proof.
  intros sg pevent opt entry res post X Hsem Hexec.
  assert (Hatomic : hs_eval
    (OSSemDel_atomic_cmd sg entry pevent opt)
    (LastSeen entry)
    (OSSemDel_LastSeen sg pevent opt entry res post) res).
  {
    unfold hs_eval, OSSemDel_atomic_cmd.
    intros X1 HX1.
    exists (OSSemDel_post_token post).
    split.
    - split; [exact HX1 |].
      exists post. unfold OSSemDel_LastSeen.
      split; [exact Hsem | reflexivity].
    - unfold OSSemDel_LastSeen.
      split; [exact Hsem | reflexivity].
  }
  pose proof (highstepbind_derive
    (OSSemDel_atomic_cmd sg entry pevent opt)
    (observe_sem_del_result pevent) (LastSeen entry) res
    (OSSemDel_LastSeen sg pevent opt entry res post)
    Hatomic X Hexec) as Hobserve.
  eapply (highstependret_derive
    (observe_sem_del_result pevent res)
    (OSSemDel_LastSeen sg pevent opt entry res post)
    (sem_del_return pevent res)
    (fun _ => OSSemDel_LastSeen sg pevent opt entry res post)).
  2: exact Hobserve.
  unfold hs_eval, observe_sem_del_result.
  intros X1 HX1. exists X1. split.
  - split; reflexivity.
  - exact HX1.
Qed.

(** Source-total ownership shapes.  The disjunction accounts for the
    high-ready cache pair being physically anchored at [entry] between one
    OS_EventTaskRdy call and the subsequent OS_Sched. *)
Definition sem_del_rep
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) : Assertion :=
  UCOS2_verification_slice_raw_rep sg post ||
  UCOS2_verification_slice_raw_ready_prio_stage sg entry post.

Definition sem_del_rep_no_event
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_rep sg post.(TskState) post.(SchedState) **
   verification_slice_event_raw_rep_no_eid sg post.(TskState) post.(EventState) eid **
   verification_slice_tick_inv sg post.(TickState) ** TT) ||
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_ready_prio_stage
     sg entry.(SchedState) post.(SchedState) post.(TskState) **
   verification_slice_event_raw_rep_no_eid sg post.(TskState) post.(EventState) eid **
   verification_slice_tick_inv sg post.(TickState) ** TT).

(** Reversible localization used while the selected live event and the
    OSEventFreeList head cell are both owned by the C body. *)
Definition sem_del_rep_no_event_no_free_head
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_rep sg post.(TskState) post.(SchedState) **
   store_used_event_map_raw_missing_i sg post.(TskState)
     post.(EventState).(inUsedEventStates) eid **
   store_free_event_nodes sg post.(EventState).(unUsedEventStates) **
   verification_slice_tick_inv sg post.(TickState) ** TT) ||
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_ready_prio_stage
     sg entry.(SchedState) post.(SchedState) post.(TskState) **
   store_used_event_map_raw_missing_i sg post.(TskState)
     post.(EventState).(inUsedEventStates) eid **
   store_free_event_nodes sg post.(EventState).(unUsedEventStates) **
   verification_slice_tick_inv sg post.(TickState) ** TT).

(** The same localization after reading OSIntNesting.  Its one concrete
    nesting byte is framed explicitly by the C annotation, so the residual
    cannot overlap that byte. *)
Definition sem_del_rep_no_event_no_free_head_no_int
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  (interrupt_inv_no_int_nesting sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_rep sg post.(TskState) post.(SchedState) **
   store_used_event_map_raw_missing_i sg post.(TskState)
     post.(EventState).(inUsedEventStates) eid **
   store_free_event_nodes sg post.(EventState).(unUsedEventStates) **
   verification_slice_tick_inv sg post.(TickState) ** TT) ||
  (interrupt_inv_no_int_nesting sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_ready_prio_stage
     sg entry.(SchedState) post.(SchedState) post.(TskState) **
   store_used_event_map_raw_missing_i sg post.(TskState)
     post.(EventState).(inUsedEventStates) eid **
   store_free_event_nodes sg post.(EventState).(unUsedEventStates) **
   verification_slice_tick_inv sg post.(TickState) ** TT).

Definition sem_del_public_event_domain_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pevent : addr) (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (tbl : list Z)
  (grp_addr tbl_addr : addr) : Prop :=
  pevent <> 0 /\
  valid_event_id sg eid /\
  pevent = event_addr sg eid /\
  event_snapshot_of_prop
    sg entry.(TskState) entry.(EventState) eid e
    etype ecnt eptr egrp tbl /\
  event_core_fields_layout_prop
    sg eid (event_addr sg eid)
    (event_addr sg eid + 4) (event_addr sg eid + 8) /\
  event_wait_fields_layout_prop sg eid grp_addr tbl_addr.

Definition sem_del_selected_event_prop
  (sg : StableGlobVars) (current : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (tbl : list Z) : Prop :=
  valid_event_id sg eid /\
  current.(EventState).(inUsedEventStates) eid = Some e /\
  event_snapshot_of_prop
    sg current.(TskState) current.(EventState) eid e
    etype ecnt eptr egrp tbl /\
  etype = encode_event_type e.(eventType) /\
  ecnt = encode_event_cnt_value e /\
  egrp = encode_event_wait_grp e.(waitList) current.(TskState).

(** Stable identity of the event selected at OSSemDel entry.  This keeps
    exactly the semantic facts needed after the wake loop: the selected
    EventID still names the original event in the entry state, and the
    source type guard established that this event is a semaphore.  It does
    not freeze mutable loop-time event bytes. *)
Definition sem_del_entry_event_identity_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) : Prop :=
  valid_event_id sg eid /\
  entry.(EventState).(inUsedEventStates) eid = Some e /\
  e.(eventType) = OS_EVENT_TYPE_SEM.

Lemma sem_del_selected_event_sem_type_from_guard :
  forall sg current eid e etype ecnt eptr egrp tbl,
    sem_del_selected_event_prop
      sg current eid e etype ecnt eptr egrp tbl ->
    unsigned_last_nbits etype 32 = 3 ->
    e.(eventType) = OS_EVENT_TYPE_SEM.
Proof.
  intros sg current eid e etype ecnt eptr egrp tbl Hselected Hguard.
  unfold sem_del_selected_event_prop in Hselected.
  destruct Hselected as [_ [_ [_ [Hencode _]]]].
  rewrite Hencode in Hguard.
  destruct e.(eventType) eqn:Htype;
    cbn [encode_event_type unsigned_last_nbits] in Hguard;
    try discriminate;
    reflexivity.
Qed.

Lemma sem_del_selected_event_to_entry_identity :
  forall sg entry eid e etype ecnt eptr egrp tbl,
    sem_del_selected_event_prop
      sg entry eid e etype ecnt eptr egrp tbl ->
    unsigned_last_nbits etype 32 = 3 ->
    sem_del_entry_event_identity_prop sg entry eid e.
Proof.
  intros sg entry eid e etype ecnt eptr egrp tbl Hselected Hguard.
  unfold sem_del_entry_event_identity_prop.
  split.
  - exact (proj1 Hselected).
  - split.
    + exact (proj1 (proj2 Hselected)).
    + eapply sem_del_selected_event_sem_type_from_guard; eauto.
Qed.

Definition sem_del_raw_event_prop := sem_del_selected_event_prop.

Definition sem_del_group_branch_prop
  (current : UCOS2_Verify_State)
  (e : OSEventAbstractState) (egrp : Z) : Prop :=
  egrp = encode_event_wait_grp e.(waitList) current.(TskState) /\
  unsigned_last_nbits egrp 32 = egrp /\
  (egrp = 0 <-> e.(waitList) = []).

Definition sem_del_conditional_validity_prop
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : Prop :=
  UCOS2_verification_slice_state_inv sg post.

Definition sem_del_restore_transition_prop
  (entry critical_entry current post : UCOS2_Verify_State)
  (eid : EventID) (kind : Z) : Prop :=
  crit_rel_no_os_state_change entry critical_entry /\
  ((kind = 0 /\ post = entry) \/
   (kind = 1 /\ sem_del_free_step current eid post)).

Definition sem_del_after_delete_context_prop
  (sg : StableGlobVars) (eid : EventID)
  (entry drained freed : UCOS2_Verify_State) : Prop :=
  sem_del_wake_endpoint sg eid entry drained /\
  sem_del_free_step drained eid freed.

Definition sem_del_sched_context_prop
  (freed : UCOS2_Verify_State) (sched_res : SchedResult)
  (post : UCOS2_Verify_State) : Prop :=
  sem_del_sched_step freed sched_res post.

Definition sem_del_interrupt_observation_prop
  (entry : UCOS2_Verify_State) (isr : Z) : Prop :=
  isr = entry.(IntrState).(intNesting).

Lemma sem_del_wake_step_preserves_event_free_list_head__loop_step_preservation :
  forall sg eid pre returned_prio canonical_waiter table_owner post head,
    sem_del_wake_step sg eid pre returned_prio canonical_waiter table_owner post ->
    event_free_list_head_prop sg pre.(EventState) head ->
    event_free_list_head_prop sg post.(EventState) head.
Proof.
  intros sg eid pre returned_prio canonical_waiter table_owner post head
    Hstep Hhead.
  unfold sem_del_wake_step, atomic_event_task_rdy_one in Hstep.
  destruct Hstep as
    (e1 & e2 & canonical_waiter_t & table_owner_t & table_owner_t' &
     _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpost).
  subst post.
  unfold event_free_list_head_prop in *.
  cbn.
  exact Hhead.
Qed.
Lemma sem_del_valid_selected_sem_fields__no_pend_and_early_returns :
  forall sg entry eid e,
    UCOS2_verification_slice_state_inv sg entry ->
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    exists sf, e.(semFields) = Some sf.
Proof.
  intros sg entry eid e Hvalid Hlookup Htype.
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [_ [_ [Hevent _]]].
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hevent.
  destruct Hevent as [_ [_ [_ [_ [_ [Hpayload _]]]]]].
  specialize (Hpayload eid e Hlookup).
  unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload.
  destruct e.(semFields) as [sf |] eqn:Hfields.
  - exists sf. reflexivity.
  - contradiction.
Qed.
Lemma sem_del_rep_int_nesting_uchar_range__no_pend_and_early_returns :
  forall sg entry post,
    sem_del_rep sg entry post |--
      sem_del_rep sg entry post &&
      coq_prop (0 <= post.(IntrState).(intNesting) <= 255).
Proof.
  intros sg entry post.
  apply _derivable1_andp_intros.
  - cancel (sem_del_rep sg entry post).
  - unfold sem_del_rep, UCOS2_verification_slice_raw_rep, UCOS2_verification_slice_raw_ready_prio_stage,
      interrupt_inv, store_int_state.
    apply derivable1_orp_elim.
    + pureIntros.
      sep_apply_l_atomic
        (valid_store_uchar
          sg.(g_OSIntNesting) post.(IntrState).(intNesting)).
      pureIntros.
      apply (derivable1s_coq_prop_r _).
      destruct H0 as [Hrange _].
      change (0 <= post.(IntrState).(intNesting) <= Byte.max_unsigned).
      exact Hrange.
    + pureIntros.
      sep_apply_l_atomic
        (valid_store_uchar
          sg.(g_OSIntNesting) post.(IntrState).(intNesting)).
      pureIntros.
      apply (derivable1s_coq_prop_r _).
      destruct H0 as [Hrange _].
      change (0 <= post.(IntrState).(intNesting) <= Byte.max_unsigned).
      exact Hrange.
Qed.
Lemma sem_del_selected_raw_snapshot__no_pend_and_early_returns :
  forall sg entry eid e etype ecnt eptr egrp tbl,
    UCOS2_verification_slice_state_inv sg entry ->
    sem_del_selected_event_prop
      sg entry eid e etype ecnt eptr egrp tbl ->
    event_raw_snapshot_of_prop
      sg entry.(TskState) entry.(EventState) eid e
      etype ecnt eptr egrp tbl.
Proof.
  intros sg entry eid e etype ecnt eptr egrp tbl
    Hvalid Hselected.
  destruct Hselected as [_ [Hlookup [Hsnapshot _]]].
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [Htask [_ [Hevent _]]].
  unfold verification_slice_task_validity in Htask.
  destruct Htask as [Htask _].
  unfold verification_slice_task_in_range in Htask.
  destruct Htask as [_ [_ [_ [_ [_ [_ Hunique]]]]]].
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hevent.
  destruct Hevent as [_ [_ [_ [_ [_ [_ [_ Hentry]]]]]]].
  specialize (Hentry eid e Hlookup).
  unfold verification_slice_event_wait_entry_consistency in Hentry.
  apply (proj1
    (event_snapshot_of_prop_stable_iff_raw
      sg entry.(TskState) entry.(EventState) eid e
      etype ecnt eptr egrp tbl (proj1 Hentry) Hunique)).
  exact Hsnapshot.
Qed.
Lemma sem_del_selected_cells_rebuild__no_pend_and_early_returns :
  forall sg tskSt evSt eid e etype ecnt eptr egrp tbl
         type_addr ptr_addr cnt_addr grp_addr tbl_addr,
    event_raw_snapshot_of_prop
      sg tskSt evSt eid e etype ecnt eptr egrp tbl ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    grp_addr # UChar |-> egrp **
    tbl_addr # UChar |-> Znth 0 tbl 0 **
    (tbl_addr + 1) # UChar |-> Znth 1 tbl 0 **
    (tbl_addr + 2) # UChar |-> Znth 2 tbl 0 **
    (tbl_addr + 3) # UChar |-> Znth 3 tbl 0 **
    (tbl_addr + 4) # UChar |-> Znth 4 tbl 0 **
    (tbl_addr + 5) # UChar |-> Znth 5 tbl 0 **
    (tbl_addr + 6) # UChar |-> Znth 6 tbl 0 **
    (tbl_addr + 7) # UChar |-> Znth 7 tbl 0 |--
      used_complete_event_raw
        sg tskSt (event_addr sg eid) eid e.
Proof.
  intros sg tskSt evSt eid e etype ecnt eptr egrp tbl
    type_addr ptr_addr cnt_addr grp_addr tbl_addr
    Hsnapshot Hcore Hwait.
  unfold event_raw_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as
    [_ [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  unfold event_core_fields_layout_prop in Hcore.
  destruct Hcore as [Htype_addr [Hptr_addr Hcnt_addr]].
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hwait as [Hgrp_addr Htbl_addr].
  assert (Htbl0 :
    Znth 0 tbl 0 = encode_event_wait_tbl_at_or e.(waitList) tskSt 0).
  { rewrite Htbl. unfold encode_event_wait_tbl_values_or.
    apply Znth0_cons. }
  assert (Htbl1 :
    Znth 1 tbl 0 = encode_event_wait_tbl_at_or e.(waitList) tskSt 1).
  { rewrite Htbl. unfold encode_event_wait_tbl_values_or.
    repeat (rewrite Znth_cons by lia). apply Znth0_cons. }
  assert (Htbl2 :
    Znth 2 tbl 0 = encode_event_wait_tbl_at_or e.(waitList) tskSt 2).
  { rewrite Htbl. unfold encode_event_wait_tbl_values_or.
    repeat (rewrite Znth_cons by lia). apply Znth0_cons. }
  assert (Htbl3 :
    Znth 3 tbl 0 = encode_event_wait_tbl_at_or e.(waitList) tskSt 3).
  { rewrite Htbl. unfold encode_event_wait_tbl_values_or.
    repeat (rewrite Znth_cons by lia). apply Znth0_cons. }
  assert (Htbl4 :
    Znth 4 tbl 0 = encode_event_wait_tbl_at_or e.(waitList) tskSt 4).
  { rewrite Htbl. unfold encode_event_wait_tbl_values_or.
    repeat (rewrite Znth_cons by lia). apply Znth0_cons. }
  assert (Htbl5 :
    Znth 5 tbl 0 = encode_event_wait_tbl_at_or e.(waitList) tskSt 5).
  { rewrite Htbl. unfold encode_event_wait_tbl_values_or.
    repeat (rewrite Znth_cons by lia). apply Znth0_cons. }
  assert (Htbl6 :
    Znth 6 tbl 0 = encode_event_wait_tbl_at_or e.(waitList) tskSt 6).
  { rewrite Htbl. unfold encode_event_wait_tbl_values_or.
    repeat (rewrite Znth_cons by lia). apply Znth0_cons. }
  assert (Htbl7 :
    Znth 7 tbl 0 = encode_event_wait_tbl_at_or e.(waitList) tskSt 7).
  { rewrite Htbl. unfold encode_event_wait_tbl_values_or.
    repeat (rewrite Znth_cons by lia). apply Znth0_cons. }
  subst type_addr. subst ptr_addr. subst cnt_addr.
  subst grp_addr. subst tbl_addr.
  subst etype. subst ecnt. subst eptr. subst egrp.
  rewrite Htbl0, Htbl1, Htbl2, Htbl3,
    Htbl4, Htbl5, Htbl6, Htbl7.
  unfold used_complete_event_raw.
  replace (event_addr sg eid + OSEventTbl_off + 0)
    with (event_addr sg eid + OSEventTbl_off) by lia.
  cancel.
Qed.
Lemma sem_del_event_residual_rebuild__no_pend_and_early_returns :
  forall sg tskSt evSt eid free_head,
    free_head = free_event_head sg evSt.(unUsedEventStates) ->
    sg.(g_OSEventFreeList) # Ptr |-> free_head **
    store_used_event_map_raw_missing_i
      sg tskSt evSt.(inUsedEventStates) eid **
    store_free_event_nodes sg evSt.(unUsedEventStates) |--
      verification_slice_event_raw_rep_no_eid sg tskSt evSt eid.
Proof.
  intros sg tskSt evSt eid free_head Hhead.
  subst free_head.
  unfold verification_slice_event_raw_rep_no_eid, store_free_event_list.
  cancel (store_free_event_nodes sg evSt.(unUsedEventStates)).
  cancel (sg.(g_OSEventFreeList) # Ptr |->
    free_event_head sg evSt.(unUsedEventStates)).
  cancel (store_used_event_map_raw_missing_i
    sg tskSt evSt.(inUsedEventStates) eid).
Qed.
Lemma sem_del_localized_rep_rebuild__no_pend_and_early_returns :
  forall sg entry eid e etype ecnt eptr egrp tbl
         int_addr free_addr free_head isr
         type_addr ptr_addr cnt_addr grp_addr tbl_addr,
    UCOS2_verification_slice_state_inv sg entry ->
    sem_del_selected_event_prop
      sg entry eid e etype ecnt eptr egrp tbl ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    os_int_nesting_addr sg int_addr ->
    os_event_free_list_addr sg free_addr ->
    sem_del_interrupt_observation_prop entry isr ->
    event_free_list_head_prop sg entry.(EventState) free_head ->
    int_addr # UChar |-> isr **
    free_addr # Ptr |-> free_head **
    sem_del_rep_no_event_no_free_head_no_int sg entry entry eid **
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    grp_addr # UChar |-> egrp **
    tbl_addr # UChar |-> Znth 0 tbl 0 **
    (tbl_addr + 1) # UChar |-> Znth 1 tbl 0 **
    (tbl_addr + 2) # UChar |-> Znth 2 tbl 0 **
    (tbl_addr + 3) # UChar |-> Znth 3 tbl 0 **
    (tbl_addr + 4) # UChar |-> Znth 4 tbl 0 **
    (tbl_addr + 5) # UChar |-> Znth 5 tbl 0 **
    (tbl_addr + 6) # UChar |-> Znth 6 tbl 0 **
    (tbl_addr + 7) # UChar |-> Znth 7 tbl 0 |--
      sem_del_rep sg entry entry.
Proof.
  intros sg entry eid e etype ecnt eptr egrp tbl
    int_addr free_addr free_head isr
    type_addr ptr_addr cnt_addr grp_addr tbl_addr
    Hvalid Hselected Hcore Hwait Hintaddr Hfreeaddr Hobs Hhead.
  pose proof
    (sem_del_selected_raw_snapshot__no_pend_and_early_returns
      sg entry eid e etype ecnt eptr egrp tbl Hvalid Hselected)
    as Hraw_snapshot.
  pose proof Hselected as Hselected_lookup.
  unfold sem_del_selected_event_prop in Hselected_lookup.
  destruct Hselected_lookup as [_ [Hlookup _]].
  sep_apply_l_atomic
    (sem_del_selected_cells_rebuild__no_pend_and_early_returns
      sg entry.(TskState) entry.(EventState) eid e
      etype ecnt eptr egrp tbl
      type_addr ptr_addr cnt_addr grp_addr tbl_addr
      Hraw_snapshot Hcore Hwait).
  unfold os_int_nesting_addr in Hintaddr.
  unfold os_event_free_list_addr in Hfreeaddr.
  unfold sem_del_interrupt_observation_prop in Hobs.
  unfold event_free_list_head_prop in Hhead.
  subst int_addr. subst free_addr. subst isr. subst free_head.
  unfold sem_del_rep_no_event_no_free_head_no_int.
  Split.
  - unfold interrupt_inv_no_int_nesting.
    pureIntros.
    sep_apply_l_atomic
      (sem_del_event_residual_rebuild__no_pend_and_early_returns
        sg entry.(TskState) entry.(EventState) eid
        (free_event_head sg entry.(EventState).(unUsedEventStates))
        eq_refl).
    sep_apply_l_atomic
      (verification_slice_event_raw_rep_merge_eid
        sg entry.(TskState) entry.(EventState) eid e Hlookup).
    unfold sem_del_rep, UCOS2_verification_slice_raw_rep, interrupt_inv,
      store_int_state.
    Left.
    split_pure_spatial.
    + cancel (verification_slice_event_raw_rep
        sg entry.(TskState) entry.(EventState)).
      cancel (sg.(g_OSIntNesting) # UChar |->
        entry.(IntrState).(intNesting)).
      cancel (sg.(g_OSLockNesting) # UChar |->
        entry.(IntrState).(lockNesting)).
      cancel (verification_slice_task_raw_rep sg entry.(TskState)).
      cancel (verification_slice_sched_raw_rep
        sg entry.(TskState) entry.(SchedState)).
      cancel (verification_slice_tick_inv sg entry.(TickState)).
      apply derivable1_truep_intros.
    + split_pures. dump_pre_spatial. assumption.
  - unfold interrupt_inv_no_int_nesting.
    pureIntros.
    sep_apply_l_atomic
      (sem_del_event_residual_rebuild__no_pend_and_early_returns
        sg entry.(TskState) entry.(EventState) eid
        (free_event_head sg entry.(EventState).(unUsedEventStates))
        eq_refl).
    sep_apply_l_atomic
      (verification_slice_event_raw_rep_merge_eid
        sg entry.(TskState) entry.(EventState) eid e Hlookup).
    unfold sem_del_rep, UCOS2_verification_slice_raw_ready_prio_stage, interrupt_inv,
      store_int_state.
    Right.
    split_pure_spatial.
    + cancel (verification_slice_event_raw_rep
        sg entry.(TskState) entry.(EventState)).
      cancel (sg.(g_OSIntNesting) # UChar |->
        entry.(IntrState).(intNesting)).
      cancel (sg.(g_OSLockNesting) # UChar |->
        entry.(IntrState).(lockNesting)).
      cancel (verification_slice_task_raw_rep sg entry.(TskState)).
      cancel (verification_slice_sched_raw_ready_prio_stage
        sg entry.(SchedState) entry.(SchedState)
        entry.(TskState)).
      cancel (verification_slice_tick_inv sg entry.(TickState)).
      apply derivable1_truep_intros.
    + split_pures. dump_pre_spatial. assumption.
Qed.
Lemma sem_del_wake_step_sem_fields_back__always_waiting_scheduler :
  forall sg eid pre returned_prio canonical_waiter table_owner post
         e_post sf,
    sem_del_wake_step sg eid pre returned_prio
      canonical_waiter table_owner post ->
    post.(EventState).(inUsedEventStates) eid = Some e_post ->
    e_post.(semFields) = Some sf ->
    exists e_pre,
      pre.(EventState).(inUsedEventStates) eid = Some e_pre /\
      e_pre.(semFields) = Some sf.
Proof.
  intros sg eid pre returned_prio canonical_waiter table_owner post
    e_post sf Hstep Hpost Hfields.
  unfold sem_del_wake_step, atomic_event_task_rdy_one in Hstep.
  destruct Hstep as
    (e1 & e2 & canonical_t & owner_t & owner_t' &
     Hpre & _ & _ & _ & _ & _ & _ & _ & _ & _ & He2 & Hstate).
  cbn in Hstate.
  subst post.
  cbn in Hpost.
  unfold update_event_field_raw in Hpost.
  cbn in Hpost.
  rewrite Z.eqb_refl in Hpost.
  inversion Hpost; subst e_post.
  subst e2.
  cbn in Hfields.
  exists e1.
  auto.
Qed.
Lemma sem_del_wake_prefix_sem_fields_back__always_waiting_scheduler :
  forall sg eid entry current,
    sem_del_wake_prefix sg eid entry current ->
    forall e_current sf,
      current.(EventState).(inUsedEventStates) eid = Some e_current ->
      e_current.(semFields) = Some sf ->
      exists e_entry,
        entry.(EventState).(inUsedEventStates) eid = Some e_entry /\
        e_entry.(semFields) = Some sf.
Proof.
  intros sg eid entry current Hprefix.
  induction Hprefix as
    [entry0
    | entry0 current0 next returned_prio canonical_waiter table_owner
      Hprefix IHHprefix Hstep].
  - intros e_current sf Hlookup Hfields.
    exists e_current.
    auto.
  - intros e_next sf Hlookup Hfields.
    destruct
      (sem_del_wake_step_sem_fields_back__always_waiting_scheduler
        sg eid current0 returned_prio canonical_waiter table_owner next
        e_next sf Hstep Hlookup Hfields)
      as (e_current & Hcurrent & Hcurrent_fields).
    exact (IHHprefix e_current sf Hcurrent Hcurrent_fields).
Qed.
Lemma sem_del_wake_endpoint_entry_sem_fields__always_waiting_scheduler :
  forall sg eid entry current e,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    sem_del_wake_endpoint sg eid entry current ->
    exists sf, e.(semFields) = Some sf.
Proof.
  intros sg eid entry current e Hentry Hendpoint.
  destruct Hendpoint as
    (Hprefix & e_current & sf & Hcurrent & _ & Hcurrent_fields & _).
  destruct
    (sem_del_wake_prefix_sem_fields_back__always_waiting_scheduler
      sg eid entry current Hprefix e_current sf Hcurrent Hcurrent_fields)
    as (e_entry & Hentry' & Hentry_fields).
  rewrite Hentry in Hentry'.
  inversion Hentry'; subst e_entry.
  exists sf.
  exact Hentry_fields.
Qed.
Lemma sem_del_rep_int_nesting_byte_range__always_waiting_scheduler :
  forall sg entry post,
    sem_del_rep sg entry post |--
      coq_prop
        (0 <= post.(IntrState).(intNesting) <= Byte.max_unsigned).
Proof.
  intros sg entry post.
  unfold sem_del_rep, UCOS2_verification_slice_raw_rep, UCOS2_verification_slice_raw_ready_prio_stage.
  Split.
  all: unfold interrupt_inv, store_int_state.
  all: Intros.
  all: prop_apply_p
    (store_uchar_range
      sg.(g_OSIntNesting) post.(IntrState).(intNesting)).
  all: Intros.
  all: dump_pre_spatial.
  all: assumption.
Qed.
Lemma sem_del_wake_step_preserves_intr__always_waiting_scheduler :
  forall sg eid pre returned_prio canonical_waiter table_owner post,
    sem_del_wake_step sg eid pre returned_prio
      canonical_waiter table_owner post ->
    post.(IntrState) = pre.(IntrState).
Proof.
  intros sg eid pre returned_prio canonical_waiter table_owner post Hstep.
  unfold sem_del_wake_step, atomic_event_task_rdy_one in Hstep.
  destruct Hstep as
    (e1 & e2 & canonical_t & owner_t & owner_t' &
     _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstate).
  cbn in Hstate.
  subst post.
  reflexivity.
Qed.
Lemma sem_del_wake_prefix_preserves_intr__always_waiting_scheduler :
  forall sg eid entry current,
    sem_del_wake_prefix sg eid entry current ->
    current.(IntrState) = entry.(IntrState).
Proof.
  intros sg eid entry current Hprefix.
  induction Hprefix as
    [entry0
    | entry0 current0 next returned_prio canonical_waiter table_owner
      Hprefix IHHprefix Hstep].
  - reflexivity.
  - rewrite
      (sem_del_wake_step_preserves_intr__always_waiting_scheduler
        sg eid current0 returned_prio canonical_waiter table_owner next Hstep).
    exact IHHprefix.
Qed.
Lemma sem_del_free_step_preserves_intr__always_waiting_scheduler :
  forall pre eid post,
    sem_del_free_step pre eid post ->
    post.(IntrState) = pre.(IntrState).
Proof.
  intros pre eid post Hfree.
  unfold sem_del_free_step in Hfree.
  destruct Hfree as (e & sf & _ & _ & _ & _ & Hpost).
  subst post.
  reflexivity.
Qed.
Lemma sem_del_sched_step_preserves_intr__always_waiting_scheduler :
  forall pre res post,
    sem_del_sched_step pre res post ->
    post.(IntrState) = pre.(IntrState).
Proof.
  intros pre res post Hsched.
  unfold sem_del_sched_step, atomic_sched in Hsched.
  repeat
    match type of Hsched with
    | context [if ?b then _ else _] => destruct b eqn:? in Hsched
    | context [match ?x with _ => _ end] => destruct x eqn:? in Hsched
    end.
  all: try (destruct Hsched as (sched2 & _ & Hpost & _);
            subst post; reflexivity).
  all: destruct Hsched as [Hpost _]; subst post; reflexivity.
Qed.
Lemma sem_del_always_waiting_preserves_intr__always_waiting_scheduler :
  forall sg eid entry drained freed sched_res post,
    sem_del_wake_endpoint sg eid entry drained ->
    sem_del_free_step drained eid freed ->
    sem_del_sched_step freed sched_res post ->
    post.(IntrState) = entry.(IntrState).
Proof.
  intros sg eid entry drained freed sched_res post
    Hendpoint Hfree Hsched.
  destruct Hendpoint as [Hprefix _].
  rewrite
    (sem_del_sched_step_preserves_intr__always_waiting_scheduler
      freed sched_res post Hsched).
  rewrite
    (sem_del_free_step_preserves_intr__always_waiting_scheduler
      drained eid freed Hfree).
  exact
    (sem_del_wake_prefix_preserves_intr__always_waiting_scheduler
      sg eid entry drained Hprefix).
Qed.
Lemma sem_del_always_waiting_sem__always_waiting_scheduler :
  forall sg pevent opt entry eid e tasks_waiting
         drained freed sched_res post,
    pevent <> 0 ->
    pevent = event_addr sg eid ->
    opt = 1 ->
    sem_del_tasks_waiting_prop entry e tasks_waiting ->
    unsigned_last_nbits tasks_waiting 32 = 1 ->
    sem_del_entry_event_identity_prop sg entry eid e ->
    entry.(IntrState).(intNesting) = 0 ->
    sem_del_wake_endpoint sg eid entry drained ->
    sem_del_free_step drained eid freed ->
    sem_del_sched_step freed sched_res post ->
    OSSemDel_sem sg pevent opt entry
      (SemDelAlwaysWaiting sched_res) post.
Proof.
  intros sg pevent opt entry eid e tasks_waiting
    drained freed sched_res post Hpevent Haddr Hopt Hwaiting Hguard
    Hidentity Hint Hendpoint Hfree Hsched.
  unfold sem_del_entry_event_identity_prop in Hidentity.
  destruct Hidentity as (Hvalid & Hlookup & Htype).
  destruct
    (sem_del_wake_endpoint_entry_sem_fields__always_waiting_scheduler
      sg eid entry drained e Hlookup Hendpoint)
    as [sf Hfields].
  unfold sem_del_tasks_waiting_prop in Hwaiting.
  destruct Hwaiting as
    [[_ [Hempty Htasks]] | [_ [Hnonempty Htasks]]].
  - subst tasks_waiting.
    cbn in Hguard.
    discriminate.
  - unfold OSSemDel_sem.
    right; right; right; right; right; right; left.
    split; [exact Hpevent |].
    split; [exact Hopt |].
    exists eid, e, sf, drained, freed, sched_res.
    split; [exact Hvalid |].
    split; [exact Haddr |].
    split; [exact Hlookup |].
    split; [exact Htype |].
    split; [exact Hfields |].
    split; [exact Hint |].
    split; [exact Hnonempty |].
    split; [exact Hendpoint |].
    split; [exact Hfree |].
    split; [exact Hsched |].
    reflexivity.
Qed.
Lemma sem_del_rep_interrupt_byte_range__always_no_wait :
  forall sg entry post,
    sem_del_rep sg entry post |--
      coq_prop
        (0 <= post.(IntrState).(intNesting) <= Byte.max_unsigned).
Proof.
  intros sg entry post.
  unfold sem_del_rep.
  apply derivable1_orp_elim.
  - unfold UCOS2_verification_slice_raw_rep, interrupt_inv, store_int_state.
    pureIntros.
    sep_apply_l_atomic
      (store_uchar_range
        sg.(g_OSIntNesting) post.(IntrState).(intNesting)).
    pureIntros.
    apply derivable1s_coq_prop_r.
    assumption.
  - unfold UCOS2_verification_slice_raw_ready_prio_stage, interrupt_inv, store_int_state.
    pureIntros.
    sep_apply_l_atomic
      (store_uchar_range
        sg.(g_OSIntNesting) post.(IntrState).(intNesting)).
    pureIntros.
    apply derivable1s_coq_prop_r.
    assumption.
Qed.
Lemma sem_del_rep_expose_interrupt_byte_range__always_no_wait :
  forall sg entry post,
    sem_del_rep sg entry post |--
      coq_prop
        (0 <= post.(IntrState).(intNesting) <= Byte.max_unsigned) &&
      sem_del_rep sg entry post.
Proof.
  intros sg entry post.
  apply _derivable1_andp_intros.
  - apply sem_del_rep_interrupt_byte_range__always_no_wait.
  - reflexivity.
Qed.
Lemma sem_del_wake_prefix_empty_eq__always_no_wait :
  forall sg eid entry current e,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(waitList) = [] ->
    sem_del_wake_prefix sg eid entry current ->
    current = entry.
Proof.
  intros sg eid entry current e Hlookup Hempty Hprefix.
  induction Hprefix as
      [entry0
      |entry0 current0 next returned_prio canonical_waiter table_owner
       Hprefix IH Hstep].
  - reflexivity.
  - specialize (IH Hlookup).
    subst current0.
    unfold sem_del_wake_step, atomic_event_task_rdy_one in Hstep.
    destruct Hstep as
      [e1 [e2 [canonical_waiter_t [table_owner_t [table_owner_t'
       [Hlookup1 [_ [Hnonempty _]]]]]]]].
    rewrite Hlookup in Hlookup1.
    inversion Hlookup1; subst e1.
    contradiction.
Qed.
Lemma sem_del_rep_int_nesting_range__invalid_option_restore :
  forall sg entry post,
    sem_del_rep sg entry post |--
      coq_prop
        (Z.le 0 post.(IntrState).(intNesting) /\
         Z.le post.(IntrState).(intNesting) Byte.max_unsigned).
Proof.
  intros sg entry post.
  unfold sem_del_rep.
  Split.
  - unfold UCOS2_verification_slice_raw_rep, interrupt_inv, interrupt_in_range,
      store_int_state.
    pureIntros.
    prop_apply_p
      (store_uchar_range (g_OSIntNesting sg)
        (post.(IntrState).(intNesting))).
    Intros_p Hrange.
    dump_pre_spatial.
    exact Hrange.
  - unfold UCOS2_verification_slice_raw_ready_prio_stage, interrupt_inv,
      interrupt_in_range, store_int_state.
    pureIntros.
    prop_apply_p
      (store_uchar_range (g_OSIntNesting sg)
        (post.(IntrState).(intNesting))).
    Intros_p Hrange.
    dump_pre_spatial.
    exact Hrange.
Qed.
Lemma sem_del_live_event_cells_merge__localization_and_critical_restore :
  forall sg current eid e etype ecnt eptr egrp tbl
         type_addr ptr_addr cnt_addr grp_addr tbl_addr,
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    sem_del_selected_event_prop
      sg current eid e etype ecnt eptr egrp tbl ->
    UCOS2_verification_slice_state_inv sg current ->
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    grp_addr # UChar |-> egrp **
    tbl_addr # UChar |-> Znth 0 tbl 0 **
    (tbl_addr + 1) # UChar |-> Znth 1 tbl 0 **
    (tbl_addr + 2) # UChar |-> Znth 2 tbl 0 **
    (tbl_addr + 3) # UChar |-> Znth 3 tbl 0 **
    (tbl_addr + 4) # UChar |-> Znth 4 tbl 0 **
    (tbl_addr + 5) # UChar |-> Znth 5 tbl 0 **
    (tbl_addr + 6) # UChar |-> Znth 6 tbl 0 **
    (tbl_addr + 7) # UChar |-> Znth 7 tbl 0 |--
    used_complete_event_raw
      sg current.(TskState) (event_addr sg eid) eid e.
Proof.
  intros sg current eid e etype ecnt eptr egrp tbl
    type_addr ptr_addr cnt_addr grp_addr tbl_addr
    Hcore Hwait Hselected Hvalid.
  assert (Hraw :
    event_raw_snapshot_of_prop
      sg current.(TskState) current.(EventState) eid e
      etype ecnt eptr egrp tbl).
  {
    assert (Hcanonical :
      event_waitList_canonical sg current.(TskState) e.(waitList)).
    {
      unfold UCOS2_verification_slice_state_inv in Hvalid.
      destruct Hvalid as [_ [_ [Hevent _]]].
      unfold verification_slice_event_in_range, verification_slice_event_in_range,
        verification_slice_event_in_range in Hevent.
      destruct Hevent as [_ [_ [_ [_ [_ [_ [_ Hentry]]]]]]].
      apply (proj1 (Hentry eid e (proj1 (proj2 Hselected)))).
    }
    assert (Hunique : task_priority_unique current.(TskState)).
    {
      unfold UCOS2_verification_slice_state_inv in Hvalid.
      destruct Hvalid as [Htask _].
      unfold verification_slice_task_validity, verification_slice_task_in_range,
        verification_slice_task_in_range in Htask.
      destruct Htask as [Htask _].
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Htask)))))).
    }
    apply (proj1 (event_snapshot_of_prop_stable_iff_raw
      sg current.(TskState) current.(EventState) eid e
      etype ecnt eptr egrp tbl Hcanonical Hunique)).
    exact (proj1 (proj2 (proj2 Hselected))).
  }
  unfold event_core_fields_layout_prop in Hcore.
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hcore as [Htype [Hptr Hcnt]].
  destruct Hwait as [Hgrp Htbl].
  unfold event_raw_snapshot_of_prop in Hraw.
  destruct Hraw as [_ [Hetype [Hecnt [Heptr [Hegrp Hvalues]]]]].
  assert (Htbl0 : Znth 0 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 0).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    rewrite Znth0_cons. reflexivity. }
  assert (Htbl1 : Znth 1 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 1).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl2 : Znth 2 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 2).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl3 : Znth 3 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 3).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl4 : Znth 4 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 4).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl5 : Znth 5 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 5).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl6 : Znth 6 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 6).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl7 : Znth 7 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 7).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  subst type_addr; subst ptr_addr; subst cnt_addr;
    subst grp_addr; subst tbl_addr.
  subst etype; subst ecnt; subst eptr; subst egrp.
  unfold used_complete_event_raw.
  rewrite Htbl0, Htbl1, Htbl2, Htbl3, Htbl4, Htbl5, Htbl6, Htbl7.
  cbn [OSEventType_off OSEventPtr_off OSEventCnt_off
    OSEventGrp_off OSEventTbl_off].
  repeat rewrite Z.add_0_r.
  cancel.
Qed.
Lemma sem_del_live_event_cells_split__localization_and_critical_restore :
  forall sg current eid e etype ecnt eptr egrp tbl
         type_addr ptr_addr cnt_addr grp_addr tbl_addr,
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    sem_del_selected_event_prop
      sg current eid e etype ecnt eptr egrp tbl ->
    UCOS2_verification_slice_state_inv sg current ->
    used_complete_event_raw
      sg current.(TskState) (event_addr sg eid) eid e |--
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    grp_addr # UChar |-> egrp **
    tbl_addr # UChar |-> Znth 0 tbl 0 **
    (tbl_addr + 1) # UChar |-> Znth 1 tbl 0 **
    (tbl_addr + 2) # UChar |-> Znth 2 tbl 0 **
    (tbl_addr + 3) # UChar |-> Znth 3 tbl 0 **
    (tbl_addr + 4) # UChar |-> Znth 4 tbl 0 **
    (tbl_addr + 5) # UChar |-> Znth 5 tbl 0 **
    (tbl_addr + 6) # UChar |-> Znth 6 tbl 0 **
    (tbl_addr + 7) # UChar |-> Znth 7 tbl 0.
Proof.
  intros sg current eid e etype ecnt eptr egrp tbl
    type_addr ptr_addr cnt_addr grp_addr tbl_addr
    Hcore Hwait Hselected Hvalid.
  assert (Hraw :
    event_raw_snapshot_of_prop
      sg current.(TskState) current.(EventState) eid e
      etype ecnt eptr egrp tbl).
  {
    assert (Hcanonical :
      event_waitList_canonical sg current.(TskState) e.(waitList)).
    {
      unfold UCOS2_verification_slice_state_inv in Hvalid.
      destruct Hvalid as [_ [_ [Hevent _]]].
      unfold verification_slice_event_in_range, verification_slice_event_in_range,
        verification_slice_event_in_range in Hevent.
      destruct Hevent as [_ [_ [_ [_ [_ [_ [_ Hentry]]]]]]].
      apply (proj1 (Hentry eid e (proj1 (proj2 Hselected)))).
    }
    assert (Hunique : task_priority_unique current.(TskState)).
    {
      unfold UCOS2_verification_slice_state_inv in Hvalid.
      destruct Hvalid as [Htask _].
      unfold verification_slice_task_validity, verification_slice_task_in_range,
        verification_slice_task_in_range in Htask.
      destruct Htask as [Htask _].
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Htask)))))).
    }
    apply (proj1 (event_snapshot_of_prop_stable_iff_raw
      sg current.(TskState) current.(EventState) eid e
      etype ecnt eptr egrp tbl Hcanonical Hunique)).
    exact (proj1 (proj2 (proj2 Hselected))).
  }
  unfold event_core_fields_layout_prop in Hcore.
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hcore as [Htype [Hptr Hcnt]].
  destruct Hwait as [Hgrp Htbl].
  unfold event_raw_snapshot_of_prop in Hraw.
  destruct Hraw as [_ [Hetype [Hecnt [Heptr [Hegrp Hvalues]]]]].
  assert (Htbl0 : Znth 0 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 0).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    rewrite Znth0_cons. reflexivity. }
  assert (Htbl1 : Znth 1 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 1).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl2 : Znth 2 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 2).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl3 : Znth 3 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 3).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl4 : Znth 4 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 4).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl5 : Znth 5 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 5).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl6 : Znth 6 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 6).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  assert (Htbl7 : Znth 7 tbl 0 =
    encode_event_wait_tbl_at_or e.(waitList) current.(TskState) 7).
  { rewrite Hvalues. unfold encode_event_wait_tbl_values_or.
    repeat rewrite Znth_cons by lia. rewrite Znth0_cons. reflexivity. }
  subst type_addr; subst ptr_addr; subst cnt_addr;
    subst grp_addr; subst tbl_addr.
  subst etype; subst ecnt; subst eptr; subst egrp.
  unfold used_complete_event_raw.
  rewrite Htbl0, Htbl1, Htbl2, Htbl3, Htbl4, Htbl5, Htbl6, Htbl7.
  cbn [OSEventType_off OSEventPtr_off OSEventCnt_off
    OSEventGrp_off OSEventTbl_off].
  repeat rewrite Z.add_0_r.
  cancel.
Qed.
Lemma sem_del_interrupt_split__localization_and_critical_restore :
  forall sg s,
    interrupt_inv sg s |--
    sg.(g_OSIntNesting) # UChar |-> s.(intNesting) **
    interrupt_inv_no_int_nesting sg s.
Proof.
  intros sg s.
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  LLM_pre_process ltac:(lia || nia).
Qed.
Lemma sem_del_residual_normal_intro__localization_and_critical_restore :
  forall sg entry post eid,
    (interrupt_inv_no_int_nesting sg post.(IntrState) **
    verification_slice_task_raw_rep sg post.(TskState) **
    verification_slice_sched_raw_rep sg post.(TskState) post.(SchedState) **
    store_used_event_map_raw_missing_i sg post.(TskState)
      post.(EventState).(inUsedEventStates) eid **
    store_free_event_nodes sg post.(EventState).(unUsedEventStates) **
    verification_slice_tick_inv sg post.(TickState) ** TT) |--
    sem_del_rep_no_event_no_free_head_no_int sg entry post eid.
Proof.
  intros sg entry post eid.
  unfold sem_del_rep_no_event_no_free_head_no_int.
  Left.
  cancel.
Qed.
Lemma sem_del_wait_grp_zero_iff_empty__localization_and_critical_restore :
  forall sg tskSt wl,
    event_waitList_canonical sg tskSt wl ->
    (encode_event_wait_grp wl tskSt = 0 <-> wl = nil).
Proof.
  intros sg tskSt wl Hcanonical.
  split.
  - intro Hgrp.
    destruct wl as [|tid rest]; [reflexivity |].
    destruct Hcanonical as [_ [_ Hrange]].
    destruct (Hrange tid ltac:(left; reflexivity))
      as [t [Hget Hprio]].
    cbn in Hgrp.
    rewrite Hget in Hgrp.
    apply Z.lor_eq_0_iff in Hgrp.
    destruct Hgrp as [Hbit _].
    rewrite Z.shiftl_1_l in Hbit.
    unfold valid_task_prio in Hprio.
    assert (Hdiv_nonneg : 0 <= t.(curPrio) / 8).
    { apply Z_div_nonneg_nonneg; lia. }
    pose proof
      (Z.pow_pos_nonneg 2 (t.(curPrio) / 8) ltac:(lia) Hdiv_nonneg).
    lia.
  - intros Hnil.
    subst wl.
    reflexivity.
Qed.
Lemma sem_del_live_event_raw_rep_merge__localization_and_critical_restore :
  forall sg tskSt evSt eid e,
    evSt.(inUsedEventStates) eid = Some e ->
    store_used_event_map_raw_missing_i
      sg tskSt evSt.(inUsedEventStates) eid **
    used_complete_event_raw sg tskSt (event_addr sg eid) eid e **
    sg.(g_OSEventFreeList) # Ptr |->
      free_event_head sg evSt.(unUsedEventStates) **
    store_free_event_nodes sg evSt.(unUsedEventStates) |--
    verification_slice_event_raw_rep sg tskSt evSt.
Proof.
  intros sg tskSt evSt eid e Hused.
  unfold verification_slice_event_raw_rep, store_used_event_map_raw,
    store_used_event_map_raw_missing_i, store_free_event_list.
  sep_apply_l_atomic
    (store_map_merge
      (fun eid0 e0 =>
         used_complete_event_raw sg tskSt (event_addr sg eid0) eid0 e0)
      eid e evSt.(inUsedEventStates) Hused).
  cancel.
Qed.
Lemma sem_del_rep_restore_live__localization_and_critical_restore :
  forall sg entry post eid e isr free_head,
    isr = post.(IntrState).(intNesting) ->
    free_head = free_event_head sg post.(EventState).(unUsedEventStates) ->
    post.(EventState).(inUsedEventStates) eid = Some e ->
    sg.(g_OSIntNesting) # UChar |-> isr **
    sg.(g_OSEventFreeList) # Ptr |-> free_head **
    sem_del_rep_no_event_no_free_head_no_int sg entry post eid **
    used_complete_event_raw
      sg post.(TskState) (event_addr sg eid) eid e |--
    sem_del_rep sg entry post.
Proof.
  intros sg entry post eid e isr free_head Hisr Hhead Hused.
  subst isr; subst free_head.
  unfold sem_del_rep_no_event_no_free_head_no_int, sem_del_rep.
  LLM_pre_process ltac:(lia || nia).
  apply derivable1_orp_elim.
  - Left.
    unfold UCOS2_verification_slice_raw_rep.
    sep_apply_l_atomic
      (sem_del_live_event_raw_rep_merge__localization_and_critical_restore
        sg post.(TskState) post.(EventState) eid e Hused).
    unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
    entailer!.
  - Right.
    unfold UCOS2_verification_slice_raw_ready_prio_stage.
    sep_apply_l_atomic
      (sem_del_live_event_raw_rep_merge__localization_and_critical_restore
        sg post.(TskState) post.(EventState) eid e Hused).
    unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
    entailer!.
Qed.
Lemma sem_del_freed_event_cells_merge__localization_and_critical_restore :
  forall sg current eid egrp tbl
         type_addr ptr_addr cnt_addr grp_addr tbl_addr free_head,
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    free_head = free_event_head sg current.(EventState).(unUsedEventStates) ->
    type_addr # UChar |-> 0 **
    ptr_addr # Ptr |-> free_head **
    cnt_addr # UShort |-> 0 **
    grp_addr # UChar |-> egrp **
    tbl_addr # UChar |-> Znth 0 tbl 0 **
    (tbl_addr + 1) # UChar |-> Znth 1 tbl 0 **
    (tbl_addr + 2) # UChar |-> Znth 2 tbl 0 **
    (tbl_addr + 3) # UChar |-> Znth 3 tbl 0 **
    (tbl_addr + 4) # UChar |-> Znth 4 tbl 0 **
    (tbl_addr + 5) # UChar |-> Znth 5 tbl 0 **
    (tbl_addr + 6) # UChar |-> Znth 6 tbl 0 **
    (tbl_addr + 7) # UChar |-> Znth 7 tbl 0 |--
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    free_event_node_rest_no_type sg eid
      (free_event_head sg current.(EventState).(unUsedEventStates)).
Proof.
  intros sg current eid egrp tbl
    type_addr ptr_addr cnt_addr grp_addr tbl_addr free_head
    Hcore Hwait Hhead.
  unfold event_core_fields_layout_prop in Hcore.
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hcore as [Htype [Hptr Hcnt]].
  destruct Hwait as [Hgrp Htbl].
  subst type_addr; subst ptr_addr; subst cnt_addr;
    subst grp_addr; subst tbl_addr; subst free_head.
  unfold free_event_node_rest_no_type.
  repeat rewrite Z.add_0_r.
  sep_apply_l_atomic
    (store_ushort_undef_store_ushort
      (event_addr sg eid + OSEventCnt_off) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventGrp_off) egrp).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off) (Znth 0 tbl 0)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 1) (Znth 1 tbl 0)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 2) (Znth 2 tbl 0)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 3) (Znth 3 tbl 0)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 4) (Znth 4 tbl 0)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 5) (Znth 5 tbl 0)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 6) (Znth 6 tbl 0)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 7) (Znth 7 tbl 0)).
  cancel.
Qed.
Lemma sem_del_freed_event_raw_rep_merge__localization_and_critical_restore :
  forall sg current eid,
    store_used_event_map_raw_missing_i
      sg current.(TskState) current.(EventState).(inUsedEventStates) eid **
    sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid **
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    free_event_node_rest_no_type sg eid
      (free_event_head sg current.(EventState).(unUsedEventStates)) **
    store_free_event_nodes sg current.(EventState).(unUsedEventStates) |--
    verification_slice_event_raw_rep sg
      (sem_del_freed_event_state current eid).(TskState)
      (sem_del_freed_event_state current eid).(EventState).
Proof.
  intros sg current eid.
  unfold verification_slice_event_raw_rep, store_used_event_map_raw,
    store_used_event_map_raw_missing_i, store_free_event_list,
    free_event_node_rest_no_type.
  unfold sem_del_freed_event_state, replace_EventS.
  cbn.
  cbn [free_event_head store_free_event_nodes encode_event_type].
  assert (Hnone :
    (fun other : EventID =>
       if Z.eqb other eid then None
       else current.(EventState).(inUsedEventStates) other) eid = None).
  {
    destruct (Z.eqb eid eid) eqn:Heq.
    - reflexivity.
    - apply Z.eqb_neq in Heq.
      contradiction.
  }
  sep_apply_l_atomic
    (proj1 (store_map_missing_i_equiv
      (fun eid0 e0 =>
         used_complete_event_raw
           sg current.(TskState) (event_addr sg eid0) eid0 e0)
      current.(EventState).(inUsedEventStates)
      (fun other =>
         if Z.eqb other eid then None
         else current.(EventState).(inUsedEventStates) other)
      eid ltac:(intros other Hneq;
        destruct (Z.eqb other eid) eqn:Heq;
        [apply Z.eqb_eq in Heq; contradiction
        |rewrite Heq; reflexivity]))).
  sep_apply_l_atomic
    (store_map_missing_equiv_store_map
      (fun eid0 e0 =>
         used_complete_event_raw
           sg current.(TskState) (event_addr sg eid0) eid0 e0)
      (fun other =>
         if Z.eqb other eid then None
         else current.(EventState).(inUsedEventStates) other)
      eid Hnone).
  cancel.
Qed.
Lemma sem_del_rep_restore_freed__localization_and_critical_restore :
  forall sg entry current eid isr,
    isr = current.(IntrState).(intNesting) ->
    sg.(g_OSIntNesting) # UChar |-> isr **
    sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid **
    sem_del_rep_no_event_no_free_head_no_int sg entry current eid **
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    free_event_node_rest_no_type sg eid
      (free_event_head sg current.(EventState).(unUsedEventStates)) |--
    sem_del_rep sg entry (sem_del_freed_event_state current eid).
Proof.
  intros sg entry current eid isr Hisr.
  subst isr.
  unfold sem_del_rep_no_event_no_free_head_no_int, sem_del_rep.
  unfold sem_del_freed_event_state, replace_EventS.
  cbn.
  LLM_pre_process ltac:(lia || nia).
  apply derivable1_orp_elim.
  - Left.
    unfold UCOS2_verification_slice_raw_rep.
    sep_apply_l_atomic
      (sem_del_freed_event_raw_rep_merge__localization_and_critical_restore
        sg current eid).
    unfold sem_del_freed_event_state, replace_EventS.
    cbn.
    unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
    entailer!.
  - Right.
    unfold UCOS2_verification_slice_raw_ready_prio_stage.
    sep_apply_l_atomic
      (sem_del_freed_event_raw_rep_merge__localization_and_critical_restore
        sg current eid).
    unfold sem_del_freed_event_state, replace_EventS.
    cbn.
    unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
    entailer!.
Qed.
Lemma sem_del_wake_prefix_intr_state__localization_and_critical_restore :
  forall sg eid entry current,
    sem_del_wake_prefix sg eid entry current ->
    current.(IntrState) = entry.(IntrState).
Proof.
  intros sg eid entry current Hprefix.
  induction Hprefix as
    [entry0
    |entry0 current0 next returned_prio
       canonical_waiter table_owner Hprefix IH Hstep].
  - reflexivity.
  - unfold sem_del_wake_step, atomic_event_task_rdy_one in Hstep.
    destruct Hstep as
      (e1 & e2 & canonical_t & table_t & table_t' &
       Hused & Hpend & Hnonempty & Hcanonical & Hcanonical_get &
       Hreturned & Hslot & Htable_get & Htable_prio & Htable_t' &
       He2 & Hnext).
    subst next.
    cbn.
    exact IH.
Qed.
