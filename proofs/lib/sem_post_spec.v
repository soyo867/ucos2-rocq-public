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
Import UCOS2_C_Rules.

Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source-visible outcomes remain distinct even though Wake and Increment
    both encode [OS_ERR_NONE]. *)
Inductive SemPostResult : Type :=
| SemPostNull
| SemPostWrongType
| SemPostWake
| SemPostIncrement
| SemPostOverflow.

Definition encode_sem_post_result (res : SemPostResult) : Z :=
  match res with
  | SemPostNull      => encode_os_err_code OS_ERR_PEVENT_NULL
  | SemPostWrongType => encode_os_err_code OS_ERR_EVENT_TYPE
  | SemPostWake      => encode_os_err_code OS_ERR_NONE
  | SemPostIncrement => encode_os_err_code OS_ERR_NONE
  | SemPostOverflow  => 51
  end.

(** The no-waiter success arm changes exactly the semaphore count. *)
Definition sem_post_event_with_count
  (e : OSEventAbstractState) (cnt : Z) : OSEventAbstractState :=
  {| eventGeneration := e.(eventGeneration);
     eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
     eventType   := e.(eventType);
     mutexFields := e.(mutexFields);
     semFields   := Some {| semCount := cnt |};
     mboxFields  := e.(mboxFields);
     queueFields := e.(queueFields);
     waitList    := e.(waitList) |}.

Definition sem_post_increment_state
  (ls : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) : UCOS2_Verify_State :=
  replace_EventS
    (update_event_field_raw
       ls.(EventState) eid
       (sem_post_event_with_count e
          (encode_event_cnt_value e + 1)))
    ls.

(** Exact cross-module step performed by OS_EventTaskRdy for a semaphore. *)
Definition sem_post_wake_step
  (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (post : UCOS2_Verify_State) : Prop :=
  atomic_event_task_rdy_one
    sg eid PendSem None PendOK entry returned_prio
    canonical_waiter table_owner post.

(** OS_Sched is a separate source step after Restore. *)
Definition sem_post_sched_step
  (entry : UCOS2_Verify_State) (res : SchedResult)
  (post : UCOS2_Verify_State) : Prop :=
  atomic_sched entry res post.

(** Ordered semantics of the selected configured source.  In particular,
    the wake arm does not increment the count and the overflow arm is an
    identity transition. *)
Definition OSSemPost_sem
  (sg : StableGlobVars) (pevent : addr)
  : program UCOS2_Verify_State SemPostResult :=
  fun ls0 res ls_post =>
    (pevent = 0 /\
     res = SemPostNull /\
     ls_post = ls0) \/
    (pevent <> 0 /\
     exists eid e,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) <> OS_EVENT_TYPE_SEM /\
       res = SemPostWrongType /\
       ls_post = ls0) \/
    (pevent <> 0 /\
     exists eid e sf returned_prio canonical_waiter table_owner
            ls_wake sched_res,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       encode_event_wait_grp e.(waitList) ls0.(TskState) <> 0 /\
       sem_post_wake_step
         sg eid ls0 returned_prio canonical_waiter table_owner ls_wake /\
       sem_post_sched_step ls_wake sched_res ls_post /\
       res = SemPostWake) \/
    (pevent <> 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       encode_event_wait_grp e.(waitList) ls0.(TskState) = 0 /\
       0 <= sf.(semCount) < 65535 /\
       res = SemPostIncrement /\
       ls_post = sem_post_increment_state ls0 eid e) \/
    (pevent <> 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       encode_event_wait_grp e.(waitList) ls0.(TskState) = 0 /\
       sf.(semCount) = 65535 /\
       res = SemPostOverflow /\
       ls_post = ls0).

Definition sem_post_result_prop
  (sg : StableGlobVars) (pevent : addr)
  (entry post : UCOS2_Verify_State) (ret : Z) : Prop :=
  exists res,
    OSSemPost_sem sg pevent entry res post /\
    ret = encode_sem_post_result res.

Definition OSSemPost_post_token
  (post : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun observed => observed = post.

Lemma OSSemPost_post_token_injective :
  forall ls1 ls2,
    OSSemPost_post_token ls1 = OSSemPost_post_token ls2 ->
    ls1 = ls2.
Proof.
  intros ls1 ls2 Heq.
  assert (Hseen : OSSemPost_post_token ls2 ls1).
  { rewrite <- Heq. reflexivity. }
  exact Hseen.
Qed.

Definition OSSemPost_LastSeen
  (sg : StableGlobVars) (pevent : addr)
  (entry : UCOS2_Verify_State) (res : SemPostResult)
  (post : UCOS2_Verify_State)
  : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun X =>
    OSSemPost_sem sg pevent entry res post /\
    X = OSSemPost_post_token post.

Definition OSSemPost_atomic_cmd
  (sg : StableGlobVars) (entry : UCOS2_Verify_State) (pevent : addr)
  : program (UCOS2_Verify_State -> Prop) SemPostResult :=
  fun X1 res X2 =>
    LastSeen entry X1 /\
    exists post, OSSemPost_LastSeen sg pevent entry res post X2.

Definition observe_sem_post_result (res : SemPostResult)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 n X2 => n = encode_sem_post_result res /\ X2 = X1.

Lemma OSSemPost_safe_return :
  forall sg pevent entry res post
         (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop),
    OSSemPost_sem sg pevent entry res post ->
    safeExec (LastSeen entry)
      (bind (OSSemPost_atomic_cmd sg entry pevent)
            observe_sem_post_result) X ->
    safeExec
      (OSSemPost_LastSeen sg pevent entry res post)
      (@StateRelMonad.ret
         (UCOS2_Verify_State -> Prop) Z
         (encode_sem_post_result res)) X.
Proof.
  intros sg pevent entry res post X Hsem Hexec.
  assert (Hatomic : hs_eval
    (OSSemPost_atomic_cmd sg entry pevent)
    (LastSeen entry)
    (OSSemPost_LastSeen sg pevent entry res post) res).
  {
    unfold hs_eval, OSSemPost_atomic_cmd.
    intros X1 HX1.
    exists (OSSemPost_post_token post).
    split.
    - split; [exact HX1 |].
      exists post. unfold OSSemPost_LastSeen.
      split; [exact Hsem | reflexivity].
    - unfold OSSemPost_LastSeen.
      split; [exact Hsem | reflexivity].
  }
  pose proof (highstepbind_derive
    (OSSemPost_atomic_cmd sg entry pevent)
    observe_sem_post_result (LastSeen entry) res
    (OSSemPost_LastSeen sg pevent entry res post)
    Hatomic X Hexec) as Hobserve.
  eapply (highstependret_derive
    (observe_sem_post_result res)
    (OSSemPost_LastSeen sg pevent entry res post)
    (encode_sem_post_result res)
    (fun _ => OSSemPost_LastSeen sg pevent entry res post)).
  2: exact Hobserve.
  unfold hs_eval, observe_sem_post_result.
  intros X1 HX1. exists X1. split.
  - split; reflexivity.
  - exact HX1.
Qed.

(** Source-total ownership at public endpoints.  Wake may temporarily use
    the raw ready-priority cache shape; all other arms use ordinary raw
    ownership. *)
Definition sem_post_rep
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) : Assertion :=
  UCOS2_verification_slice_raw_rep sg post ||
  UCOS2_verification_slice_raw_ready_prio_stage sg entry post.

(** Reversible localization of the selected event. *)
Definition sem_post_rep_no_event
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

(** Closed-world public event domain used before dereference. *)
Definition sem_post_public_event_domain_prop
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
    sg eid
    (event_addr sg eid)
    (event_addr sg eid + 4)
    (event_addr sg eid + 8) /\
  event_wait_fields_layout_prop sg eid grp_addr tbl_addr.

Definition sem_post_selected_event_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (tbl : list Z) : Prop :=
  valid_event_id sg eid /\
  entry.(EventState).(inUsedEventStates) eid = Some e /\
  event_snapshot_of_prop
    sg entry.(TskState) entry.(EventState) eid e
    etype ecnt eptr egrp tbl /\
  etype = encode_event_type e.(eventType) /\
  ecnt = encode_event_cnt_value e /\
  egrp = encode_event_wait_grp e.(waitList) entry.(TskState).

Definition sem_post_group_branch_prop
  (entry : UCOS2_Verify_State)
  (e : OSEventAbstractState) (egrp : Z) : Prop :=
  egrp = encode_event_wait_grp e.(waitList) entry.(TskState) /\
  (egrp = 0 <-> e.(waitList) = []).

Definition sem_post_increment_step_prop
  (entry post : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) : Prop :=
  post = sem_post_increment_state entry eid e.

(** The three source paths that execute Restore are tagged explicitly:
    0 = overflow identity, 1 = count increment, 2 = waiter wake stage.
    This relation intentionally describes only the abstract OS-state stage;
    the CPU_SR value/capability pairing remains owned by [interrupt.v]. *)
Definition sem_post_restore_transition_prop
  (sg : StableGlobVars)
  (entry critical_entry post : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (kind : Z) : Prop :=
  crit_rel_no_os_state_change entry critical_entry /\
  ((kind = 0 /\ post = entry) \/
   (kind = 1 /\ post = sem_post_increment_state entry eid e) \/
   (kind = 2 /\
    exists returned_prio canonical_waiter table_owner,
      sem_post_wake_step
        sg eid entry returned_prio canonical_waiter table_owner post)).

(** Stable inputs must recover the full mathematical validity bundle after
    the exact Post transition. *)
Definition sem_post_conditional_validity_prop
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : Prop :=
  UCOS2_verification_slice_state_inv sg post.

Import ListNotations.
Local Open Scope Z_scope.

Lemma sem_post_increment_validity__event_semantic_closure :
  forall sg entry eid e sf,
    UCOS2_verification_slice_state_inv sg entry ->
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    e.(semFields) = Some sf ->
    e.(waitList) = @nil TaskID ->
    0 <= encode_event_cnt_value e + 1 <= 65535 ->
    UCOS2_verification_slice_state_inv sg
      (sem_post_increment_state entry eid e).
Proof.
  intros sg entry eid e sf Hvalid Hlookup Htype Hsf
    Hwait_empty Hcount.
  destruct Hvalid as
    [Htask_valid [Hsched_valid [Hevent_valid Hcross_valid]]].
  set (e_post := sem_post_event_with_count e
    (encode_event_cnt_value e + 1)).
  assert (Hpost_lookup : forall mid,
    inUsedEventStates (EventState
      (sem_post_increment_state entry eid e)) mid =
    if Z.eqb mid eid then Some e_post
    else entry.(EventState).(inUsedEventStates) mid).
  {
    intro mid.
    unfold sem_post_increment_state, update_event_field_raw, e_post.
    reflexivity.
  }
  assert (Hevent_post : verification_slice_event_in_range sg
    (TskState (sem_post_increment_state entry eid e))
    (EventState (sem_post_increment_state entry eid e))).
  {
    unfold verification_slice_event_in_range, verification_slice_event_in_range,
      verification_slice_event_in_range in Hevent_valid |- *.
    destruct Hevent_valid as
      [Hrange [Hnodup [Hfree_range [Hpartition
        [Hfields [Hpayload [Hqueue Hwait]]]]]]].
    split.
    - intros mid evx Hget.
      rewrite Hpost_lookup in Hget.
      destruct (Z.eqb mid eid) eqn:Hmid.
      + apply Z.eqb_eq in Hmid. subst mid.
        inversion Hget; subst evx.
        exact (Hrange eid e Hlookup).
      + exact (Hrange mid evx Hget).
    - split.
      + cbn [sem_post_increment_state update_event_field_raw].
        exact Hnodup.
      + split.
        * cbn [sem_post_increment_state update_event_field_raw].
          exact Hfree_range.
        * split.
          -- unfold event_slot_partition in Hpartition |- *.
             destruct Hpartition as [Hfree Hnone].
             split.
             ++ intros mid Hin.
                rewrite Hpost_lookup.
                destruct (Z.eqb mid eid) eqn:Hmid.
                ** apply Z.eqb_eq in Hmid. subst mid.
                   specialize (Hfree eid Hin).
                   rewrite Hlookup in Hfree.
                   discriminate.
                ** exact (Hfree mid Hin).
             ++ intros mid Hvalid_mid Hnone_post.
                rewrite Hpost_lookup in Hnone_post.
                destruct (Z.eqb mid eid) eqn:Hmid.
                ** discriminate.
                ** exact (Hnone mid Hvalid_mid Hnone_post).
          -- split.
             ++ intros mid evx Hget.
                rewrite Hpost_lookup in Hget.
                destruct (Z.eqb mid eid) eqn:Hmid.
                ** apply Z.eqb_eq in Hmid. subst mid.
                   inversion Hget; subst evx.
                   pose proof (Hfields eid e Hlookup) as Hfields_old.
                   unfold event_fields_consistency in Hfields_old |- *.
                   rewrite Htype in Hfields_old.
                   unfold e_post, sem_post_event_with_count.
                   simpl.
                   rewrite Htype.
                   simpl.
                   destruct Hfields_old as
                     [Hmutex [_ [Hmbox Hqueue_none]]].
                   repeat split; try assumption; discriminate.
                ** exact (Hfields mid evx Hget).
             ++ split.
                ** intros mid evx Hget.
                   rewrite Hpost_lookup in Hget.
                   destruct (Z.eqb mid eid) eqn:Hmid.
                   --- apply Z.eqb_eq in Hmid. subst mid.
                       inversion Hget; subst evx.
                       unfold event_payload_consistency, e_post,
                         sem_post_event_with_count.
                       simpl.
                       rewrite Htype.
                       simpl.
                       unfold sem_fields_consistency.
                       split; [exact Hcount |].
                       intros Hne.
                       exfalso.
                       apply Hne.
                       exact Hwait_empty.
                   --- exact (Hpayload mid evx Hget).
                ** split.
                   --- cbn [sem_post_increment_state update_event_field_raw].
                       eapply queue_binding_unique_update_same_binding.
                       +++ exact Hlookup.
                       +++ unfold event_queue_id, e_post,
                             sem_post_event_with_count.
                           simpl. rewrite Htype. reflexivity.
                       +++ exact Hqueue.
                   --- intros mid evx Hget.
                       rewrite Hpost_lookup in Hget.
                       destruct (Z.eqb mid eid) eqn:Hmid.
                       +++ apply Z.eqb_eq in Hmid. subst mid.
                           inversion Hget; subst evx.
                           eapply verification_slice_event_wait_entry_consistency_irrelevant_fields.
                           *** unfold e_post, sem_post_event_with_count.
                               reflexivity.
                           *** unfold e_post, sem_post_event_with_count.
                               reflexivity.
                           *** exact (Hwait eid e Hlookup).
                       +++ exact (Hwait mid evx Hget).
  }
  assert (Hmutex_back : forall mid e0 m,
    inUsedEventStates (EventState
      (sem_post_increment_state entry eid e)) mid = Some e0 ->
    e0.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e0.(mutexFields) = Some m ->
    entry.(EventState).(inUsedEventStates) mid = Some e0).
  {
    intros mid e0 m Hget Htype0 Hmf0.
    rewrite Hpost_lookup in Hget.
    destruct (Z.eqb mid eid) eqn:Hmid.
    - inversion Hget; subst e0.
      unfold e_post, sem_post_event_with_count in Htype0.
      simpl in Htype0.
      rewrite Htype in Htype0.
      discriminate.
    - exact Hget.
  }
  assert (Hmutex_forward : forall mid e0 m,
    entry.(EventState).(inUsedEventStates) mid = Some e0 ->
    e0.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e0.(mutexFields) = Some m ->
    inUsedEventStates (EventState
      (sem_post_increment_state entry eid e)) mid = Some e0).
  {
    intros mid e0 m Hget Htype0 Hmf0.
    rewrite Hpost_lookup.
    destruct (Z.eqb mid eid) eqn:Hmid.
    - apply Z.eqb_eq in Hmid. subst mid.
      rewrite Hlookup in Hget.
      inversion Hget; subst e0.
      rewrite Htype in Htype0.
      discriminate.
    - exact Hget.
  }
  assert (Hcross_post : verification_slice_cross_module_consistency sg
    (sem_post_increment_state entry eid e)).
  {
    unfold sem_post_increment_state.
    unfold verification_slice_cross_module_consistency in Hcross_valid |- *.
    destruct Hcross_valid as
      [Hos [Hpt [Hmo [Hwait_cross [Hready [Horder
        [Hceil [Hunique [Hprotocol Hpcp_unique]]]]]]]]].
    split; [| split; [| split; [| split; [| split; [| split;
      [| split; [| split; [| split]]]]]]]].
    - eapply osprio_cur_consistency_indep_EventState
        with (lvs1 := entry).
      + reflexivity.
      + reflexivity.
      + exact Hos.
    - unfold priotbl_consistency in Hpt |- *.
      intro p.
      specialize (Hpt p).
      repeat rewrite replace_EventS_other_Tsk.
      repeat rewrite replace_EventS_other_Sched.
      repeat rewrite replace_EventS_EventState.
      destruct (prioTbl (TskState entry) p) as [| |tid] eqn:Hslot.
      + destruct Hpt as [Hnot_task Hnot_mutex].
        split; [exact Hnot_task |].
        intros [mid [e0 [m [Hget [Htype0 [Hmf0 Hreserve]]]]]].
        apply Hnot_mutex.
        exists mid, e0, m.
        split.
        * eapply Hmutex_back; eauto.
        * split; [exact Htype0 |].
          split; [exact Hmf0 | exact Hreserve].
      + destruct Hpt as
          [mid [e0 [m [Hget [Htype0 [Hmf0 [Hpcp Howner]]]]]]].
        exists mid, e0, m.
        split.
        * eapply Hmutex_forward; eauto.
        * split; [exact Htype0 |].
          split; [exact Hmf0 |].
          split; [exact Hpcp | exact Howner].
      + destruct Hpt as [t [Htask [Htask_prio | Hmutex_slot]]].
        * exists t. split; [exact Htask |]. left. exact Htask_prio.
        * destruct Hmutex_slot as
            [mid [e0 [m [Hget [Htype0 [Hmf0 [Howner Hsource]]]]]]].
          exists t. split; [exact Htask |]. right.
          exists mid, e0, m.
          split.
          -- eapply Hmutex_forward; eauto.
          -- split; [exact Htype0 |].
             split; [exact Hmf0 |].
             split; [exact Howner | exact Hsource].
    - unfold mutex_owner_consistency in Hmo |- *.
      intros mid e0 m [Hget [Htype0 Hmf0]].
      apply (Hmo mid e0 m).
      split.
      + eapply Hmutex_back; eauto.
      + split; [exact Htype0 | exact Hmf0].
    - unfold verification_slice_event_wait_object_consistency in Hwait_cross |- *.
      destruct Hwait_cross as [Hentries [Hrefback Hclosed]].
      split; [| split].
      + intros mid e0 Hget.
        rewrite Hpost_lookup in Hget.
        destruct (Z.eqb mid eid) eqn:Hmid.
        * apply Z.eqb_eq in Hmid. subst mid.
          inversion Hget; subst e0.
          eapply verification_slice_event_wait_entry_consistency_irrelevant_fields.
          -- unfold e_post, sem_post_event_with_count. reflexivity.
          -- unfold e_post, sem_post_event_with_count. reflexivity.
          -- exact (Hentries eid e Hlookup).
        * exact (Hentries mid e0 Hget).
      + unfold
          Ucos2Verify.lib.event_wait.task_event_reference_backlink_consistency
          in Hrefback |- *.
        intros tid0 t mid e0 Htask Hget Href.
        repeat rewrite replace_EventS_other_Tsk in Htask.
        rewrite Hpost_lookup in Hget.
        destruct (Z.eqb mid eid) eqn:Hmid.
        * apply Z.eqb_eq in Hmid. subst mid.
          inversion Hget; subst e0.
          change (List.In tid0 e.(waitList)).
          eapply Hrefback; eauto.
        * eapply Hrefback; eauto.
      + eapply Ucos2Verify.lib.event_wait.task_event_reference_closure_preserved_by_event_extension.
        * intros mid [e0 Hget].
          rewrite Hpost_lookup.
          destruct (Z.eqb mid eid).
          -- eexists. reflexivity.
          -- exists e0. exact Hget.
        * exact Hclosed.
    - eapply ready_list_completeness_indep_EventState
        with (lvs1 := entry).
      + reflexivity.
      + reflexivity.
      + exact Hready.
    - eapply ready_list_order_indep_EventState
        with (lvs1 := entry).
      + reflexivity.
      + reflexivity.
      + exact Horder.
    - unfold ceiling_priotbl_free in Hceil |- *.
      repeat rewrite replace_EventS_other_Tsk.
      exact Hceil.
    - unfold task_priority_unique_prop in Hunique |- *.
      repeat rewrite replace_EventS_other_Tsk.
      exact Hunique.
    - unfold mutex_protocol_consistency in Hprotocol |- *.
      intros mid e0 m Hget Htype0 Hmf0.
      apply (Hprotocol mid e0 m).
      + eapply Hmutex_back; eauto.
      + exact Htype0.
      + exact Hmf0.
    - eapply mutex_enabled_pcp_unique_transport
        with (lvs1 := entry).
      + intros mid e0 m Hget Htype0 Hmf0.
        exists e0, m.
        repeat split; try assumption; try reflexivity.
        eapply Hmutex_back; eauto.
      + exact Hpcp_unique.
  }
  unfold UCOS2_verification_slice_state_inv.
  split.
  - repeat rewrite replace_EventS_other_Tsk.
    exact Htask_valid.
  - split.
    + repeat rewrite replace_EventS_other_Tsk.
      repeat rewrite replace_EventS_other_Sched.
      exact Hsched_valid.
    + split; [exact Hevent_post | exact Hcross_post].
Qed.

Lemma sem_post_selected_event_validity__sem_post_complete :
  forall sg s eid e,
    UCOS2_verification_slice_state_inv sg s ->
    s.(EventState).(inUsedEventStates) eid = Some e ->
    event_waitList_canonical sg s.(TskState) e.(waitList) /\
    task_priority_unique s.(TskState) /\
    event_payload_consistency sg e.
Proof.
  intros sg s eid e [Ht [_ [He _]]] Hget.
  destruct Ht as [[_ [_ [_ [_ [_ [_ Hu]]]]]] _].
  destruct He as [_ [_ [_ [_ [_ [Hp [_ Hw]]]]]]].
  split; [exact (proj1 (Hw eid e Hget)) |].
  split; [exact Hu | exact (Hp eid e Hget)].
Qed.
Lemma encode_event_wait_grp_zero_iff_nil__sem_post_complete :
  forall sg tasks wl,
    event_waitList_canonical sg tasks wl ->
    (encode_event_wait_grp wl tasks = 0 <-> wl = []).
Proof.
  intros sg tasks wl [_ [_ Hlive]].
  destruct wl as [|tid rest].
  - simpl. tauto.
  - destruct (Hlive tid (or_introl eq_refl)) as [t [Hget Hprio]].
    cbn [encode_event_wait_grp]. rewrite Hget.
    split; [|discriminate].
    intro Hz. apply Z.lor_eq_0_l in Hz.
    apply Z.shiftl_eq_0_iff in Hz; [discriminate |].
    apply Z.div_pos; [exact (proj1 Hprio) | lia].
Qed.
Lemma sem_post_sem_count__sem_post_complete :
  forall sg e,
    event_payload_consistency sg e ->
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    exists sf, e.(semFields) = Some sf /\
      encode_event_cnt_value e = sf.(semCount) /\
      0 <= sf.(semCount) <= 65535.
Proof.
  intros sg e Hpayload Htype.
  unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload.
  destruct (semFields e) as [sf|] eqn:Hsf; [|contradiction].
  exists sf. split; [reflexivity |].
  split.
  - unfold encode_event_cnt_value. rewrite Htype, Hsf. reflexivity.
  - exact (proj1 Hpayload).
Qed.
Lemma encode_event_type_u32_eq__sem_post_complete :
  forall ty,
    unsigned_last_nbits (encode_event_type ty) 32 = encode_event_type ty.
Proof. destruct ty; reflexivity. Qed.
Lemma encode_event_type_sem_iff__sem_post_complete :
  forall ty, encode_event_type ty = 3 <-> ty = OS_EVENT_TYPE_SEM.
Proof. destruct ty; simpl; split; congruence. Qed.
Lemma unsigned_last_nbits_u32_count_eq__sem_post_complete :
  forall n, event_count_value_range_prop n -> unsigned_last_nbits n 32 = n.
Proof.
  intros n Hn. unfold event_count_value_range_prop in Hn.
  unfold unsigned_last_nbits. apply Z.mod_small. cbn. lia.
Qed.
Lemma used_complete_event_raw_snapshot_eq__sem_post_complete :
  forall sg tasks events eid e type_addr ptr_addr cnt_addr grp_addr tbl_addr
    etype ecnt eptr egrp tbl,
    event_waitList_canonical sg tasks e.(waitList) ->
    task_priority_unique tasks ->
    event_snapshot_of_prop sg tasks events eid e etype ecnt eptr egrp tbl ->
    event_core_fields_layout_prop sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    used_complete_event_raw sg tasks (event_addr sg eid) eid e =
      (type_addr # UChar |-> etype **
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
       (tbl_addr + 7) # UChar |-> Znth 7 tbl 0).
Proof.
  intros sg tasks events eid e type_addr ptr_addr cnt_addr grp_addr tbl_addr
    etype ecnt eptr egrp tbl Hcanonical Hunique
    [_ [Ht [Hc [Hp [Hg Hb]]]]] [Ha [Hd Hf]] [Hj Hk].
  subst type_addr ptr_addr cnt_addr grp_addr tbl_addr etype ecnt eptr egrp tbl.
  rewrite <- used_complete_event_stable_eq_raw by assumption.
  unfold used_complete_event, encode_event_wait_tbl_values.
  unfold Znth. simpl. repeat rewrite Z.add_0_r. reflexivity.
Qed.
Lemma sem_post_rep_split_event__sem_post_complete :
  forall sg s eid e,
    s.(EventState).(inUsedEventStates) eid = Some e ->
    UCOS2_verification_slice_raw_rep sg s |--
      used_complete_event_raw sg s.(TskState) (event_addr sg eid) eid e **
      sem_post_rep_no_event sg s s eid.
Proof.
  intros sg s eid e Hget.
  unfold UCOS2_verification_slice_raw_rep, sem_post_rep_no_event.
  sep_apply_l_atomic (verification_slice_event_raw_rep_split_eid sg (TskState s) (EventState s) eid e Hget).
  entailer!.
  Left. entailer!.
Qed.
Lemma sem_post_rep_merge_event__sem_post_complete :
  forall sg entry s eid e,
    s.(EventState).(inUsedEventStates) eid = Some e ->
    used_complete_event_raw sg s.(TskState) (event_addr sg eid) eid e **
    sem_post_rep_no_event sg entry s eid |-- sem_post_rep sg entry s.
Proof.
  intros sg entry s eid e Hget.
  unfold sem_post_rep_no_event, sem_post_rep.
  rewrite orp_sepcon_right_equiv.
  apply derivable1_orp_elim.
  - Left.
    sep_apply_l_atomic (verification_slice_event_raw_rep_merge_eid sg (TskState s) (EventState s) eid e Hget).
    unfold UCOS2_verification_slice_raw_rep. entailer!.
  - Right.
    sep_apply_l_atomic (verification_slice_event_raw_rep_merge_eid sg (TskState s) (EventState s) eid e Hget).
    unfold UCOS2_verification_slice_raw_ready_prio_stage. entailer!.
Qed.
Lemma verification_slice_event_raw_rep_no_eid_update_equiv__sem_post_complete :
  forall sg tasks events eid e,
    verification_slice_event_raw_rep_no_eid sg tasks events eid --||--
    verification_slice_event_raw_rep_no_eid sg tasks (update_event_field_raw events eid e) eid.
Proof.
  intros sg tasks events eid e.
  unfold verification_slice_event_raw_rep_no_eid, store_used_event_map_raw_missing_i.
  cbn [update_event_field_raw].
  assert (Hmap : forall a, a <> eid ->
    inUsedEventStates events a =
    (if Z.eqb a eid then Some e else inUsedEventStates events a)).
  { intros a Hne. destruct (Z.eqb a eid) eqn:Heq; [|reflexivity].
    apply Z.eqb_eq in Heq. contradiction. }
  destruct (store_map_missing_i_equiv
    (fun i ev => used_complete_event_raw sg tasks (event_addr sg i) i ev)
    _ _ eid Hmap) as [Hforward Hbackward].
  split; [sep_apply_l_atomic Hforward | sep_apply_l_atomic Hbackward]; entailer!.
Qed.
Lemma sem_post_rep_no_event_increment_equiv__sem_post_complete :
  forall sg entry eid e,
    sem_post_rep_no_event sg entry entry eid --||--
    sem_post_rep_no_event sg entry (sem_post_increment_state entry eid e) eid.
Proof.
  intros sg entry eid e.
  unfold sem_post_rep_no_event, sem_post_increment_state.
  repeat rewrite replace_EventS_other_Intr.
  repeat rewrite replace_EventS_other_Tsk.
  repeat rewrite replace_EventS_other_Sched.
  repeat rewrite replace_EventS_EventState.
  repeat rewrite replace_EventS_other_Tick.
  destruct (verification_slice_event_raw_rep_no_eid_update_equiv__sem_post_complete
    sg (TskState entry) (EventState entry) eid
    (sem_post_event_with_count e (encode_event_cnt_value e + 1))) as [Hf Hb].
  split; apply derivable1_orp_elim.
  - Left. sep_apply_l_atomic Hf. entailer!.
  - Right. sep_apply_l_atomic Hf. entailer!.
  - Left. sep_apply_l_atomic Hb. entailer!.
  - Right. sep_apply_l_atomic Hb. entailer!.
Qed.
Lemma sem_post_increment_event_snapshot__sem_post_complete :
  forall sg entry eid e etype ecnt eptr egrp tbl,
    event_snapshot_of_prop sg entry.(TskState) entry.(EventState)
      eid e etype ecnt eptr egrp tbl ->
    e.(eventType) = OS_EVENT_TYPE_SEM ->
    event_snapshot_of_prop sg
      (sem_post_increment_state entry eid e).(TskState)
      (sem_post_increment_state entry eid e).(EventState)
      eid (sem_post_event_with_count e (encode_event_cnt_value e + 1))
      etype (ecnt + 1) eptr egrp tbl.
Proof.
  intros sg entry eid e etype ecnt eptr egrp tbl
    [Hget [Ht [Hc [Hp [Hg Hb]]]]] Htype.
  unfold event_snapshot_of_prop, sem_post_increment_state.
  rewrite replace_EventS_other_Tsk, replace_EventS_EventState.
  unfold update_event_field_raw, sem_post_event_with_count. simpl.
  rewrite Z.eqb_refl. split; [reflexivity |].
  split; [exact Ht |].
  split.
  - unfold encode_event_cnt_value at 1. simpl. rewrite Htype. simpl. lia.
  - split.
    + unfold verification_slice_encode_event_ptr_value in Hp |- *. simpl. rewrite Htype in Hp |- *.
      exact Hp.
    + split; [exact Hg | exact Hb].
Qed.
