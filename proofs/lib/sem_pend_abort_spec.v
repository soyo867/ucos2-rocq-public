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

(** Source-visible outcomes of the configured public API.  The ready
    constructor retains the exact number of tasks woken, while the error
    observer remains separate from the C return value. *)
Inductive SemPendAbortResult : Type :=
| SemPendAbortNull
| SemPendAbortWrongType
| SemPendAbortNoWaiter
| SemPendAbortReady (woken : Z).

Definition sem_pend_abort_return (res : SemPendAbortResult) : Z :=
  match res with
  | SemPendAbortReady woken => woken
  | _ => 0
  end.

Definition sem_pend_abort_error (res : SemPendAbortResult) : Z :=
  match res with
  | SemPendAbortNull => encode_os_err_code OS_ERR_PEVENT_NULL
  | SemPendAbortWrongType => encode_os_err_code OS_ERR_EVENT_TYPE
  | SemPendAbortNoWaiter => encode_os_err_code OS_ERR_NONE
  | SemPendAbortReady _ => encode_os_err_code OS_ERR_PEND_ABORT
  end.

(** One literal OS_EventTaskRdy call.  The source returns the decoded
    priority, removes the canonical highest-priority waiter from the event,
    and updates the concrete priority-table owner selected at that instant.
    The three identities are deliberately not collapsed. *)
Definition sem_pend_abort_wake_step
  (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (post : UCOS2_Verify_State) : Prop :=
  atomic_event_task_rdy_one
    sg eid PendSem None PendAbort entry returned_prio
    canonical_waiter table_owner post.

(** Exact finite prefix of literal wake calls.  It is intentionally a
    relation over source states, not an executable mirror of the C loop. *)
Inductive sem_pend_abort_wake_prefix
  (sg : StableGlobVars) (eid : EventID)
  : Z -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| sem_pend_abort_wake_prefix_nil :
    forall entry,
      sem_pend_abort_wake_prefix sg eid 0 entry entry
| sem_pend_abort_wake_prefix_snoc :
    forall count entry current returned_prio
           canonical_waiter table_owner post,
      0 <= count ->
      sem_pend_abort_wake_prefix sg eid count entry current ->
      sem_pend_abort_wake_step
        sg eid current returned_prio canonical_waiter table_owner post ->
      sem_pend_abort_wake_prefix sg eid (count + 1) entry post.

(** Loop invariant semantics: [count] is both the number of literal wake
    calls already performed and the exact drop in abstract waiter
    cardinality from the selected entry event. *)
Definition sem_pend_abort_broadcast_progress
  (sg : StableGlobVars) (eid : EventID)
  (entry current : UCOS2_Verify_State)
  (entry_event current_event : OSEventAbstractState)
  (count : Z) : Prop :=
  entry.(EventState).(inUsedEventStates) eid = Some entry_event /\
  current.(EventState).(inUsedEventStates) eid = Some current_event /\
  sem_pend_abort_wake_prefix sg eid count entry current /\
  0 <= count /\
  Z.of_nat (length entry_event.(waitList)) =
    count + Z.of_nat (length current_event.(waitList)).

Definition sem_pend_abort_broadcast_endpoint
  (sg : StableGlobVars) (eid : EventID)
  (entry ready : UCOS2_Verify_State) (count : Z) : Prop :=
  exists entry_event ready_event,
    sem_pend_abort_broadcast_progress
      sg eid entry ready entry_event ready_event count /\
    entry_event.(waitList) <> [] /\
    ready_event.(waitList) = [] /\
    count = Z.of_nat (length entry_event.(waitList)).

(** OS_Sched is a distinct source step and occurs only after Restore. *)
Definition sem_pend_abort_sched_step
  (entry : UCOS2_Verify_State) (res : SchedResult)
  (post : UCOS2_Verify_State) : Prop :=
  atomic_sched entry res post.

(** Method-3 Restore consumes the capability produced at function entry and
    leaves the abstract kernel state produced inside the critical section
    unchanged.  Interrupt-enabled/disabled ownership itself is represented
    by [OutsideCritical]/[InsideCritical] in the C contract. *)
Definition sem_pend_abort_restore_transition_prop
  (entry critical_entry current post : UCOS2_Verify_State) : Prop :=
  crit_rel_no_os_state_change entry critical_entry /\
  post = current.

(** Exact pre-scheduler endpoint for the two nonempty-waiter source arms. *)
Definition sem_pend_abort_ready_result
  (sg : StableGlobVars) (eid : EventID) (opt : Z)
  (entry ready : UCOS2_Verify_State)
  (res : SemPendAbortResult) : Prop :=
  (opt = 1 /\
   exists count,
     res = SemPendAbortReady count /\
     sem_pend_abort_broadcast_endpoint sg eid entry ready count) \/
  (opt <> 1 /\
   res = SemPendAbortReady 1 /\
   exists returned_prio canonical_waiter table_owner,
     sem_pend_abort_wake_step
       sg eid entry returned_prio canonical_waiter table_owner ready).

(** Ordered semantics of the selected uC/OS-II source profile. *)
Definition OSSemPendAbort_sem
  (sg : StableGlobVars) (pevent opt : Z)
  : program UCOS2_Verify_State SemPendAbortResult :=
  fun entry res post =>
    (pevent = 0 /\
     res = SemPendAbortNull /\
     post = entry) \/
    (pevent <> 0 /\
     exists eid e,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) <> OS_EVENT_TYPE_SEM /\
       res = SemPendAbortWrongType /\
       post = entry) \/
    (pevent <> 0 /\
     exists eid e sf,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       encode_event_wait_grp e.(waitList) entry.(TskState) = 0 /\
       res = SemPendAbortNoWaiter /\
       post = entry) \/
    (pevent <> 0 /\
     exists eid e sf ready sched_res,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       entry.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_SEM /\
       e.(semFields) = Some sf /\
       encode_event_wait_grp e.(waitList) entry.(TskState) <> 0 /\
       sem_pend_abort_ready_result sg eid opt entry ready res /\
       sem_pend_abort_sched_step ready sched_res post).

Definition sem_pend_abort_result_prop
  (sg : StableGlobVars) (pevent opt : Z)
  (entry post : UCOS2_Verify_State)
  (ret err : Z) : Prop :=
  exists res,
    OSSemPendAbort_sem sg pevent opt entry res post /\
    ret = sem_pend_abort_return res /\
    err = sem_pend_abort_error res.

Definition sem_pend_abort_exact_result_prop
  (sg : StableGlobVars) (pevent opt : Z)
  (entry post : UCOS2_Verify_State)
  (res : SemPendAbortResult) : Prop :=
  OSSemPendAbort_sem sg pevent opt entry res post.

Definition OSSemPendAbort_post_token
  (post : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun observed => observed = post.

Definition OSSemPendAbort_LastSeen
  (sg : StableGlobVars) (pevent opt : Z)
  (entry : UCOS2_Verify_State) (res : SemPendAbortResult)
  (post : UCOS2_Verify_State)
  : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun X =>
    OSSemPendAbort_sem sg pevent opt entry res post /\
    X = OSSemPendAbort_post_token post.

Definition OSSemPendAbort_atomic_cmd
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pevent opt : Z)
  : program (UCOS2_Verify_State -> Prop) SemPendAbortResult :=
  fun X1 res X2 =>
    LastSeen entry X1 /\
    exists post,
      OSSemPendAbort_LastSeen sg pevent opt entry res post X2.

Definition observe_sem_pend_abort_result (res : SemPendAbortResult)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 n X2 => n = sem_pend_abort_return res /\ X2 = X1.

Lemma OSSemPendAbort_safe_return :
  forall sg pevent opt entry res post
         (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop),
    OSSemPendAbort_sem sg pevent opt entry res post ->
    safeExec (LastSeen entry)
      (bind (OSSemPendAbort_atomic_cmd sg entry pevent opt)
            observe_sem_pend_abort_result) X ->
    safeExec
      (OSSemPendAbort_LastSeen sg pevent opt entry res post)
      (@StateRelMonad.ret
         (UCOS2_Verify_State -> Prop) Z
         (sem_pend_abort_return res)) X.
Proof.
  intros sg pevent opt entry res post X Hsem Hexec.
  assert (Hatomic : hs_eval
    (OSSemPendAbort_atomic_cmd sg entry pevent opt)
    (LastSeen entry)
    (OSSemPendAbort_LastSeen sg pevent opt entry res post) res).
  {
    unfold hs_eval, OSSemPendAbort_atomic_cmd.
    intros X1 HX1.
    exists (OSSemPendAbort_post_token post).
    split.
    - split; [exact HX1 |].
      exists post. unfold OSSemPendAbort_LastSeen.
      split; [exact Hsem | reflexivity].
    - unfold OSSemPendAbort_LastSeen.
      split; [exact Hsem | reflexivity].
  }
  pose proof (highstepbind_derive
    (OSSemPendAbort_atomic_cmd sg entry pevent opt)
    observe_sem_pend_abort_result (LastSeen entry) res
    (OSSemPendAbort_LastSeen sg pevent opt entry res post)
    Hatomic X Hexec) as Hobserve.
  eapply (highstependret_derive
    (observe_sem_pend_abort_result res)
    (OSSemPendAbort_LastSeen sg pevent opt entry res post)
    (sem_pend_abort_return res)
    (fun _ => OSSemPendAbort_LastSeen
      sg pevent opt entry res post)).
  2: exact Hobserve.
  unfold hs_eval, observe_sem_pend_abort_result.
  intros X1 HX1. exists X1. split.
  - split; reflexivity.
  - exact HX1.
Qed.

(** Source-total ownership at public endpoints. *)
Definition sem_pend_abort_rep
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) : Assertion :=
  UCOS2_verification_slice_raw_rep sg post ||
  UCOS2_verification_slice_raw_ready_prio_stage sg entry post.

(** Reversible selected-event localization after at least one waiter has
    been made ready.  Unlike the source-total union below, this stage keeps
    the high-ready cache pair anchored in the function-entry scheduler
    state, exactly as OS_EventTaskRdy leaves it before OS_Sched. *)
Definition sem_pend_abort_ready_rep_no_event
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  interrupt_inv sg post.(IntrState) **
  verification_slice_task_raw_rep sg post.(TskState) **
  verification_slice_sched_raw_ready_prio_stage
    sg entry.(SchedState) post.(SchedState) post.(TskState) **
  verification_slice_event_raw_rep_no_eid sg post.(TskState) post.(EventState) eid **
  verification_slice_tick_inv sg post.(TickState) ** TT.

(** Reversible selected-event localization in either raw scheduler stage. *)
Definition sem_pend_abort_rep_no_event
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_rep sg post.(TskState) post.(SchedState) **
   verification_slice_event_raw_rep_no_eid sg post.(TskState) post.(EventState) eid **
   verification_slice_tick_inv sg post.(TickState) ** TT) ||
  sem_pend_abort_ready_rep_no_event sg entry post eid.

(** Broadcast-loop ownership indexed by the exact number of completed wake
    calls.  Before the first call the source still owns the entry raw
    scheduler representation.  Every positive prefix owns the precise
    entry-anchored ready-priority stage; this provenance is what permits the
    loop endpoint to schedule without inventing a cache relation. *)
Definition sem_pend_abort_broadcast_rep_no_event
  (sg : StableGlobVars)
  (entry current : UCOS2_Verify_State) (eid : EventID)
  (count : Z) : Assertion :=
  (coq_prop (count = 0) &&
   sem_pend_abort_rep_no_event sg entry current eid) ||
  (coq_prop (0 < count) &&
   sem_pend_abort_ready_rep_no_event sg entry current eid).

Definition sem_pend_abort_public_event_domain_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pevent : Z) (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (tbl : list Z)
  (type_addr ptr_addr cnt_addr grp_addr tbl_addr : Z) : Prop :=
  pevent <> 0 /\
  valid_event_id sg eid /\
  pevent = event_addr sg eid /\
  event_snapshot_of_prop
    sg entry.(TskState) entry.(EventState) eid e
    etype ecnt eptr egrp tbl /\
  event_core_fields_layout_prop
    sg eid type_addr ptr_addr cnt_addr /\
  event_wait_fields_layout_prop sg eid grp_addr tbl_addr.

(** Stable selected semaphore fact retained independently of later raw
    snapshots.  In particular it retains the payload/count identity. *)
Definition sem_pend_abort_selected_event_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (tbl : list Z) : Prop :=
  valid_event_id sg eid /\
  entry.(EventState).(inUsedEventStates) eid = Some e /\
  event_snapshot_of_prop
    sg entry.(TskState) entry.(EventState) eid e
    etype ecnt eptr egrp tbl /\
  event_object_layout_prop sg eid /\
  e.(eventType) = OS_EVENT_TYPE_SEM /\
  exists sf,
    e.(semFields) = Some sf /\ ecnt = sf.(semCount).

(** Source-total current event view used after one or more wake steps. *)
Definition sem_pend_abort_raw_event_prop
  (sg : StableGlobVars) (current : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt eptr egrp : Z) (tbl : list Z) : Prop :=
  valid_event_id sg eid /\
  event_raw_snapshot_of_prop
    sg current.(TskState) current.(EventState) eid e
    etype ecnt eptr egrp tbl.

Definition sem_pend_abort_group_branch_prop
  (current : UCOS2_Verify_State)
  (e : OSEventAbstractState) (egrp : Z) : Prop :=
  egrp = encode_event_wait_grp e.(waitList) current.(TskState) /\
  (egrp = 0 <-> e.(waitList) = []).

Definition sem_pend_abort_conditional_validity_prop
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : Prop :=
  UCOS2_verification_slice_state_inv sg post.

Lemma strictly_sorted_by_tail_gt__event_focus_broadcast_loop :
  forall (A : Type) (key : A -> Z) (a : A) (rest : list A),
    Ucos2Verify.lib.helpers.strictly_sorted_by key (a :: rest) ->
    forall x, In x rest -> key a < key x.
Proof.
  intros A key a rest.
  revert a.
  induction rest as [| b rest IH]; intros a Hsorted x Hin.
  - contradiction.
  - simpl in Hsorted.
    destruct Hsorted as [Hab Htail].
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst x. exact Hab.
    + pose proof (IH b Htail x Hin) as Hbx.
      lia.
Qed.
Lemma strictly_sorted_by_Z_length_bound__event_focus_broadcast_loop :
  forall (A : Type) (key : A -> Z) (xs : list A) lo hi,
    lo <= hi ->
    Ucos2Verify.lib.helpers.strictly_sorted_by key xs ->
    (forall x, In x xs -> lo <= key x < hi) ->
    Z.of_nat (List.length xs) <= hi - lo.
Proof.
  intros A key xs.
  induction xs as [| a rest IH]; intros lo hi Hbounds Hsorted Hrange.
  - simpl. lia.
  - destruct rest as [| b rest'].
    + specialize (Hrange a (or_introl eq_refl)).
      simpl. lia.
    + simpl in Hsorted.
      destruct Hsorted as [Hab Htail].
      assert (Hall : forall x, In x (b :: rest') -> key a < key x).
      {
        intros x Hin.
        assert (Hfull :
          Ucos2Verify.lib.helpers.strictly_sorted_by
            key (a :: b :: rest')).
        {
          change (key a < key b /\
            Ucos2Verify.lib.helpers.strictly_sorted_by key (b :: rest')).
          exact (conj Hab Htail).
        }
        eapply strictly_sorted_by_tail_gt__event_focus_broadcast_loop.
        - exact Hfull.
        - exact Hin.
      }
      assert (Htail_range :
        forall x, In x (b :: rest') -> key a + 1 <= key x < hi).
      {
        intros x Hin.
        specialize (Hall x Hin).
        specialize (Hrange x (or_intror Hin)).
        lia.
      }
      specialize (Hrange a (or_introl eq_refl)).
      assert (Hnext_bound : key a + 1 <= hi) by lia.
      specialize (IH (key a + 1) hi Hnext_bound Htail Htail_range).
      simpl in IH |- *.
      lia.
Qed.
Lemma event_waitList_canonical_length_bound__event_focus_broadcast_loop :
  forall sg tskSt wl,
    0 <= sg.(osLowestPrio) ->
    event_waitList_canonical sg tskSt wl ->
    Z.of_nat (List.length wl) <= sg.(osLowestPrio).
Proof.
  intros sg tskSt wl Hlowest Hcanonical.
  unfold event_waitList_canonical in Hcanonical.
  destruct Hcanonical as [_ [Hsorted Hregistered]].
  eapply strictly_sorted_by_Z_length_bound__event_focus_broadcast_loop
    with (lo := 0) (hi := sg.(osLowestPrio)) in Hsorted.
  - lia.
  - exact Hlowest.
  - intros tid Hin.
    specialize (Hregistered tid Hin).
    destruct Hregistered as [t [Hlookup Hprio]].
    unfold wait_prio_key.
    rewrite Hlookup.
    exact Hprio.
Qed.
Lemma sem_pend_abort_wake_step_preserves_canonical_unique__event_focus_broadcast_loop :
  forall sg eid before returned_prio canonical_waiter table_owner after
         before_event,
    before.(EventState).(inUsedEventStates) eid = Some before_event ->
    event_waitList_canonical
      sg before.(TskState) before_event.(waitList) ->
    task_priority_unique before.(TskState) ->
    sem_pend_abort_wake_step
      sg eid before returned_prio canonical_waiter table_owner after ->
    exists after_event,
      after.(EventState).(inUsedEventStates) eid = Some after_event /\
      event_waitList_canonical
        sg after.(TskState) after_event.(waitList) /\
      task_priority_unique after.(TskState).
Proof.
  intros sg eid before returned_prio canonical_waiter table_owner after
    before_event Hbefore_lookup Hcanonical Hunique Hwake.
  unfold sem_pend_abort_wake_step, atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (e1 & e2 & canonical_t & table_t & table_t' &
     Hevent & Hpend & Hnonempty & Hcanonical_waiter &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hafter).
  rewrite Hbefore_lookup in Hevent.
  inversion Hevent; subst e1.
  assert (Hsame : table_owner = canonical_waiter).
  {
    eapply Hunique.
    - exact Htable_get.
    - exact Hcanonical_get.
    - rewrite Htable_prio, Hreturned.
      reflexivity.
  }
  subst table_owner.
  rewrite Hcanonical_get in Htable_get.
  inversion Htable_get; subst table_t.
  subst e2.
  subst after.
  assert (Hkey_ext : forall tid,
    wait_prio_key sg before.(TskState) tid =
    wait_prio_key sg
      ({| inUsedTaskStates := fun tid0 =>
            if Z.eqb tid0 canonical_waiter
            then Some table_t'
            else before.(TskState).(inUsedTaskStates) tid0;
          unUsedTaskStates := before.(TskState).(unUsedTaskStates);
          tcbListHead := before.(TskState).(tcbListHead);
          prioTbl := before.(TskState).(prioTbl);
          taskRegNextID := before.(TskState).(taskRegNextID);
          parkedTaskStacks := before.(TskState).(parkedTaskStacks);
          taskLifecycle := before.(TskState).(taskLifecycle);
     taskCount := before.(TskState).(taskCount) |}) tid).
  {
    intro tid.
    unfold wait_prio_key.
    cbn.
    destruct (Z.eqb tid canonical_waiter) eqn:Heq.
    - apply Z.eqb_eq in Heq. subst tid.
      rewrite Hcanonical_get, Htable_t'.
      reflexivity.
    - reflexivity.
  }
  exists
    {| eventGeneration := before_event.(eventGeneration);
       eventName := before_event.(eventName);
     eventPadding1 := before_event.(eventPadding1);
     eventPadding2 := before_event.(eventPadding2);
     eventPadding3 := before_event.(eventPadding3);
     eventPadding19 := before_event.(eventPadding19);
       eventType := before_event.(eventType);
       mutexFields := before_event.(mutexFields);
       semFields := before_event.(semFields);
       mboxFields := before_event.(mboxFields);
       queueFields := before_event.(queueFields);
       waitList := Ucos2Verify.lib.helpers.remove_Z_eqb
         canonical_waiter before_event.(waitList) |}.
  split.
  - cbn. rewrite Z.eqb_refl. reflexivity.
  - split.
    + unfold event_waitList_canonical in Hcanonical |- *.
      destruct Hcanonical as [Hnodup [Hsorted Hregistered]].
      split.
      * apply Ucos2Verify.lib.helpers.remove_Z_eqb_NoDup. exact Hnodup.
      * split.
        -- eapply Ucos2Verify.lib.helpers.strictly_sorted_by_key_ext.
           ++ exact Hkey_ext.
           ++ apply Ucos2Verify.lib.helpers.remove_Z_eqb_strictly_sorted_by.
              exact Hsorted.
        -- intros tid Hin.
           pose proof (Ucos2Verify.lib.helpers.remove_Z_eqb_in
             canonical_waiter tid
             before_event.(waitList) Hin) as Hin_before.
           destruct (Hregistered tid Hin_before) as [t [Hget Hprio]].
           exists t. split; [| exact Hprio].
           cbn.
           destruct (Z.eqb tid canonical_waiter) eqn:Heq.
           ++ apply Z.eqb_eq in Heq. subst tid.
              exfalso.
              exact (Ucos2Verify.lib.helpers.remove_Z_eqb_notin canonical_waiter
                before_event.(waitList) Hin).
           ++ exact Hget.
    + unfold task_priority_unique.
      cbn.
      intros tid1 tid2 t1 t2 Hget1 Hget2 Hprio.
      destruct (Z.eqb tid1 canonical_waiter) eqn:Heq1;
        destruct (Z.eqb tid2 canonical_waiter) eqn:Heq2.
      * apply Z.eqb_eq in Heq1, Heq2. congruence.
      * apply Z.eqb_eq in Heq1. subst tid1.
        inversion Hget1; subst t1.
        assert (tid2 = canonical_waiter).
        {
          eapply Hunique.
          - exact Hget2.
          - exact Hcanonical_get.
          - rewrite Htable_t' in Hprio. cbn in Hprio.
            symmetry. exact Hprio.
        }
        subst tid2. rewrite Z.eqb_refl in Heq2. discriminate.
      * apply Z.eqb_eq in Heq2. subst tid2.
        inversion Hget2; subst t2.
        assert (tid1 = canonical_waiter).
        {
          eapply Hunique.
          - exact Hget1.
          - exact Hcanonical_get.
          - rewrite Htable_t' in Hprio. cbn in Hprio.
            exact Hprio.
        }
        subst tid1. rewrite Z.eqb_refl in Heq1. discriminate.
      * eapply Hunique; eassumption.
Qed.
Lemma encode_event_wait_grp_zero_iff_empty__event_focus_broadcast_loop :
  forall sg tskSt wl,
    event_waitList_canonical sg tskSt wl ->
    (encode_event_wait_grp wl tskSt = 0 <-> wl = []).
Proof.
  intros sg tskSt wl Hcanonical.
  split.
  - intro Hgrp.
    destruct wl as [| tid rest]; [reflexivity |].
    destruct Hcanonical as [_ [_ Hrange]].
    destruct (Hrange tid ltac:(left; reflexivity))
      as [t [Hget Hprio]].
    cbn in Hgrp. rewrite Hget in Hgrp.
    apply Z.lor_eq_0_iff in Hgrp.
    destruct Hgrp as [Hbit _].
    rewrite Z.shiftl_1_l in Hbit.
    unfold valid_task_prio in Hprio.
    assert (Hdiv_nonneg : 0 <= t.(curPrio) / 8).
    { apply Z_div_nonneg_nonneg; lia. }
    pose proof
      (Z.pow_pos_nonneg 2 (t.(curPrio) / 8) ltac:(lia) Hdiv_nonneg).
    lia.
  - intro Hempty. subst wl. reflexivity.
Qed.
Lemma sem_pend_abort_wake_prefix_preserves_canonical_unique__event_focus_broadcast_loop :
  forall sg eid count entry current entry_event current_event,
    UCOS2_verification_slice_state_inv sg entry ->
    entry.(EventState).(inUsedEventStates) eid = Some entry_event ->
    sem_pend_abort_wake_prefix sg eid count entry current ->
    current.(EventState).(inUsedEventStates) eid = Some current_event ->
    event_waitList_canonical
      sg current.(TskState) current_event.(waitList) /\
    task_priority_unique current.(TskState).
Proof.
  intros sg eid count entry current entry_event current_event
    Hvalid Hentry Hprefix.
  revert current_event.
  induction Hprefix as
    [entry0 |
     count0 entry0 current0 returned_prio canonical_waiter
       table_owner post Hcount_nonneg Hprefix IH Hstep];
    intros current_event Hcurrent.
  - rewrite Hentry in Hcurrent.
    inversion Hcurrent; subst current_event.
    destruct Hvalid as [_ [_ [_ Hcross]]].
    unfold verification_slice_cross_module_consistency in Hcross.
    destruct Hcross as
      [_ [_ [_ [Hwait_consistency
        [_ [_ [_ [Hunique _]]]]]]]].
    unfold verification_slice_event_wait_object_consistency in Hwait_consistency.
    destruct Hwait_consistency as [Hwait_entries _].
    specialize (Hwait_entries eid entry_event Hentry).
    unfold verification_slice_event_wait_entry_consistency in Hwait_entries.
    destruct Hwait_entries as [Hcanonical _].
    split; [exact Hcanonical |].
    unfold task_priority_unique_prop in Hunique.
    exact Hunique.
  - pose proof Hstep as Hstep_detail.
    unfold sem_pend_abort_wake_step,
      atomic_event_task_rdy_one in Hstep_detail.
    destruct Hstep_detail as
      (before_event & after_event0 & canonical_t & table_t & table_t' &
       Hbefore_lookup & Hpend & Hnonempty & Hcanonical_waiter &
       Hcanonical_get & Hreturned & Htable_slot &
       Htable_get & Htable_prio & Htable_t' & Hevent_after & Hpost).
    specialize (IH Hvalid Hentry before_event Hbefore_lookup).
    destruct IH as [Hcanonical Hunique].
    pose proof
      (sem_pend_abort_wake_step_preserves_canonical_unique__event_focus_broadcast_loop
        sg eid current0 returned_prio canonical_waiter table_owner post
        before_event Hbefore_lookup Hcanonical Hunique Hstep)
      as Hpreserved.
    destruct Hpreserved as
      [after_event [Hafter_lookup [Hafter_canonical Hafter_unique]]].
    rewrite Hcurrent in Hafter_lookup.
    inversion Hafter_lookup; subst after_event.
    split; assumption.
Qed.
Lemma sem_pend_abort_sched_step_preserves_event_state__event_focus_broadcast_loop :
  forall lvs1 res lvs2,
    sem_pend_abort_sched_step lvs1 res lvs2 ->
    EventState lvs1 = EventState lvs2.
Proof.
  intros lvs1 res lvs2 Hatomic.
  unfold sem_pend_abort_sched_step, atomic_sched in Hatomic.
  cbv zeta in Hatomic.
  remember (Z.eqb lvs1.(IntrState).(intNesting) 0 &&
             Z.eqb lvs1.(IntrState).(lockNesting) 0)%bool as b_outer in *.
  destruct b_outer.
  - cbv beta iota in Hatomic.
    remember (lvs1.(SchedState).(readyList)) as rl in *.
    destruct rl as [|h tl].
    + cbv beta iota in Hatomic.
      destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
    + cbv beta iota in Hatomic.
      remember (lvs1.(SchedState).(curTaskID)) as ctid in *.
      destruct ctid as [c|].
      * cbv beta iota in Hatomic.
        remember (lvs1.(TskState).(inUsedTaskStates) h) as geth in *.
        destruct geth as [headT|].
        -- cbv beta iota in Hatomic.
           remember (lvs1.(TskState).(inUsedTaskStates) c) as getc in *.
           destruct getc as [curT|].
           ++ cbv beta iota in Hatomic.
              remember (negb (is_effectively_ready curT.(stat) curT.(dly) &&
                              existsb (Z.eqb c) (h :: tl)) ||
                         negb (Z.eqb h c))%bool as b_inner in *.
              destruct b_inner.
              ** cbv beta iota in Hatomic.
                 destruct Hatomic as
                   [schedSt2 [HschedSt2_def [Hlvs2 Hres]]].
                 rewrite Hlvs2.
                 symmetry. apply replace_SchedS_other_Event.
              ** cbv beta iota in Hatomic.
                 destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
           ++ cbv beta iota in Hatomic.
              destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
        -- cbv beta iota in Hatomic.
           destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
      * cbv beta iota in Hatomic.
        destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
  - cbv beta iota in Hatomic.
    destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
Qed.
Lemma sem_pend_abort_sched_step_preserves_task_state__event_focus_broadcast_loop :
  forall lvs1 res lvs2,
    sem_pend_abort_sched_step lvs1 res lvs2 ->
    TskState lvs1 = TskState lvs2.
Proof.
  intros lvs1 res lvs2 Hatomic.
  unfold sem_pend_abort_sched_step, atomic_sched in Hatomic.
  cbv zeta in Hatomic.
  remember (Z.eqb lvs1.(IntrState).(intNesting) 0 &&
             Z.eqb lvs1.(IntrState).(lockNesting) 0)%bool as b_outer in *.
  destruct b_outer.
  - cbv beta iota in Hatomic.
    remember (lvs1.(SchedState).(readyList)) as rl in *.
    destruct rl as [|h tl].
    + cbv beta iota in Hatomic.
      destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
    + cbv beta iota in Hatomic.
      remember (lvs1.(SchedState).(curTaskID)) as ctid in *.
      destruct ctid as [c|].
      * cbv beta iota in Hatomic.
        remember (lvs1.(TskState).(inUsedTaskStates) h) as geth in *.
        destruct geth as [headT|].
        -- cbv beta iota in Hatomic.
           remember (lvs1.(TskState).(inUsedTaskStates) c) as getc in *.
           destruct getc as [curT|].
           ++ cbv beta iota in Hatomic.
              remember (negb (is_effectively_ready curT.(stat) curT.(dly) &&
                              existsb (Z.eqb c) (h :: tl)) ||
                         negb (Z.eqb h c))%bool as b_inner in *.
              destruct b_inner.
              ** cbv beta iota in Hatomic.
                 destruct Hatomic as
                   [schedSt2 [HschedSt2_def [Hlvs2 Hres]]].
                 rewrite Hlvs2.
                 symmetry. apply replace_SchedS_other_Tsk.
              ** cbv beta iota in Hatomic.
                 destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
           ++ cbv beta iota in Hatomic.
              destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
        -- cbv beta iota in Hatomic.
           destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
      * cbv beta iota in Hatomic.
        destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
  - cbv beta iota in Hatomic.
    destruct Hatomic as [Hlvs2 Hres]. subst lvs2. reflexivity.
Qed.
Lemma sem_pend_abort_wake_prefix_preserves_event_fields__event_focus_broadcast_loop :
  forall sg eid count entry current entry_event current_event,
    entry.(EventState).(inUsedEventStates) eid = Some entry_event ->
    sem_pend_abort_wake_prefix sg eid count entry current ->
    current.(EventState).(inUsedEventStates) eid = Some current_event ->
    current_event.(eventType) = entry_event.(eventType) /\
    current_event.(semFields) = entry_event.(semFields).
Proof.
  intros sg eid count entry current entry_event current_event
    Hentry Hprefix.
  revert current_event.
  induction Hprefix as
    [entry0 |
     count0 entry0 current0 returned_prio canonical_waiter
       table_owner post Hcount_nonneg Hprefix IH Hstep];
    intros current_event Hcurrent.
  - rewrite Hentry in Hcurrent.
    inversion Hcurrent; subst current_event.
    split; reflexivity.
  - pose proof Hstep as Hstep_detail.
    unfold sem_pend_abort_wake_step,
      atomic_event_task_rdy_one in Hstep_detail.
    destruct Hstep_detail as
      (before_event & after_event & canonical_t & table_t & table_t' &
       Hbefore_lookup & Hpend & Hnonempty & Hcanonical_waiter &
       Hcanonical_get & Hreturned & Htable_slot &
       Htable_get & Htable_prio & Htable_t' & Hevent_after & Hpost).
    specialize (IH Hentry before_event Hbefore_lookup).
    destruct IH as [IHtype IHsem].
    assert (Hafter_lookup :
      post.(EventState).(inUsedEventStates) eid = Some after_event).
    {
      rewrite Hpost. cbn. rewrite Z.eqb_refl. reflexivity.
    }
    rewrite Hcurrent in Hafter_lookup.
    inversion Hafter_lookup; subst current_event.
    rewrite Hevent_after. cbn.
    split; assumption.
Qed.
Lemma sem_pend_abort_wake_prefix_preserves_task_priority__event_focus_broadcast_loop :
  forall sg eid count entry current tid t,
    entry.(TskState).(inUsedTaskStates) tid = Some t ->
    sem_pend_abort_wake_prefix sg eid count entry current ->
    exists t',
      current.(TskState).(inUsedTaskStates) tid = Some t' /\
      t'.(curPrio) = t.(curPrio).
Proof.
  intros sg eid count entry current tid t Hentry Hprefix.
  induction Hprefix as
    [entry0 |
     count0 entry0 current0 returned_prio canonical_waiter
       table_owner post Hcount_nonneg Hprefix IH Hstep].
  - exists t. split; [exact Hentry | reflexivity].
  - specialize (IH Hentry).
    destruct IH as [current_t [Hcurrent_t Hprio]].
    pose proof Hstep as Hstep_detail.
    unfold sem_pend_abort_wake_step,
      atomic_event_task_rdy_one in Hstep_detail.
    destruct Hstep_detail as
      (before_event & after_event & canonical_t & table_t & table_t' &
       Hbefore_lookup & Hpend & Hnonempty & Hcanonical_waiter &
       Hcanonical_get & Hreturned & Htable_slot &
       Htable_get & Htable_prio & Htable_t' & Hevent_after & Hpost).
    rewrite Hpost. cbn.
    destruct (Z.eqb tid table_owner) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst tid.
      rewrite Htable_get in Hcurrent_t.
      inversion Hcurrent_t; subst current_t.
      exists table_t'.
      split; [reflexivity |].
      rewrite Htable_t'. cbn. exact Hprio.
    + exists current_t. split; assumption.
Qed.
Lemma encode_event_wait_grp_member_nonzero__event_focus_broadcast_loop :
  forall sg tskSt wl tid t,
    In tid wl ->
    tskSt.(inUsedTaskStates) tid = Some t ->
    valid_task_prio sg t.(curPrio) ->
    encode_event_wait_grp wl tskSt <> 0.
Proof.
  intros sg tskSt wl.
  induction wl as [|a rest IH]; intros tid t Hin Hget Hvalid.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst a. cbn. rewrite Hget.
      intro Hzero.
      apply Z.lor_eq_0_iff in Hzero.
      destruct Hzero as [Hbit _].
      rewrite Z.shiftl_1_l in Hbit.
      unfold valid_task_prio in Hvalid.
      assert (Hdiv_nonneg : 0 <= t.(curPrio) / 8).
      { apply Z_div_nonneg_nonneg; lia. }
      pose proof
        (Z.pow_pos_nonneg 2 (t.(curPrio) / 8) ltac:(lia) Hdiv_nonneg).
      lia.
    + cbn.
      destruct (tskSt.(inUsedTaskStates) a) as [a_t |] eqn:Ha.
      * intro Hzero.
        apply Z.lor_eq_0_iff in Hzero.
        destruct Hzero as [_ Hrest].
        eapply (IH tid t); eassumption.
      * eapply (IH tid t); eassumption.
Qed.
Lemma sem_pend_abort_wake_prefix_zero_eq__event_focus_broadcast_loop :
  forall sg eid count entry current,
    sem_pend_abort_wake_prefix sg eid count entry current ->
    count = 0 ->
    current = entry.
Proof.
  intros sg eid count entry current Hprefix Hzero.
  inversion Hprefix; subst; [reflexivity | lia].
Qed.
Lemma sem_pend_abort_positive_prefix_entry_head_task__event_focus_broadcast_loop :
  forall sg eid count entry current entry_event,
    entry.(EventState).(inUsedEventStates) eid = Some entry_event ->
    entry_event.(waitList) <> @nil TaskID ->
    sem_pend_abort_wake_prefix sg eid count entry current ->
    0 < count ->
    exists t,
      entry.(TskState).(inUsedTaskStates)
        (List.hd 0 entry_event.(waitList)) = Some t.
Proof.
  intros sg eid count entry current entry_event
    Hentry Hentry_nonempty Hprefix.
  induction Hprefix as
    [entry0 |
     count0 entry0 current0 returned_prio canonical_waiter
       table_owner post Hcount_nonneg Hprefix IH Hstep];
    intro Hpositive.
  - lia.
  - destruct (Z.eq_dec count0 0) as [Hcount_zero | Hcount_nonzero].
    + assert (Hcurrent_eq : current0 = entry0).
      {
        eapply sem_pend_abort_wake_prefix_zero_eq__event_focus_broadcast_loop;
          eassumption.
      }
      subst current0.
      pose proof Hstep as Hstep_detail.
      unfold sem_pend_abort_wake_step,
        atomic_event_task_rdy_one in Hstep_detail.
      destruct Hstep_detail as
        (before_event & after_event & canonical_t & table_t & table_t' &
         Hbefore_lookup & Hpend & Hnonempty & Hcanonical_waiter &
         Hcanonical_get & Hreturned & Htable_slot &
         Htable_get & Htable_prio & Htable_t' & Hevent_after & Hpost).
      rewrite Hentry in Hbefore_lookup.
      inversion Hbefore_lookup; subst before_event.
      rewrite Hcanonical_waiter in Hcanonical_get.
      exists canonical_t. exact Hcanonical_get.
    + apply IH; [exact Hentry | lia].
Qed.
Lemma sem_pend_abort_positive_prefix_current_event_sem__event_focus_broadcast_loop :
  forall sg eid count entry current current_event,
    sem_pend_abort_wake_prefix sg eid count entry current ->
    current.(EventState).(inUsedEventStates) eid = Some current_event ->
    0 < count ->
    current_event.(eventType) = OS_EVENT_TYPE_SEM.
Proof.
  intros sg eid count entry current current_event Hprefix Hcurrent Hpositive.
  destruct Hprefix as
    [entry0 |
     count0 entry0 current0 returned_prio canonical_waiter
       table_owner post Hcount_nonneg Hprefix Hstep].
  - lia.
  - pose proof Hstep as Hstep_detail.
    unfold sem_pend_abort_wake_step,
      atomic_event_task_rdy_one in Hstep_detail.
    destruct Hstep_detail as
      (before_event & after_event & canonical_t & table_t & table_t' &
       Hbefore_lookup & Hpend & Hnonempty & Hcanonical_waiter &
       Hcanonical_get & Hreturned & Htable_slot &
       Htable_get & Htable_prio & Htable_t' & Hevent_after & Hpost).
    assert (Hafter_lookup :
      post.(EventState).(inUsedEventStates) eid = Some after_event).
    {
      rewrite Hpost. cbn. rewrite Z.eqb_refl. reflexivity.
    }
    rewrite Hcurrent in Hafter_lookup.
    inversion Hafter_lookup; subst current_event.
    rewrite Hevent_after. cbn.
    destruct before_event.(eventType); cbn in Hpend;
      try discriminate; reflexivity.
Qed.
Lemma shiftl_bit_byte__single_wake_restore_and_early_returns : forall i,
  0 <= i < 8 -> 0 <= Z.shiftl 1 i < 2 ^ 8.
Proof.
  intros i Hi. rewrite Z.shiftl_1_l.
  assert (Hi_cases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
          i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Hi_cases]; [subst i; cbn; lia|].
  destruct Hi_cases as [Heq|Heq]; subst i; cbn; lia.
Qed.
Lemma lor_byte__single_wake_restore_and_early_returns : forall a b,
  0 <= a < 2 ^ 8 -> 0 <= b < 2 ^ 8 ->
  0 <= Z.lor a b < 2 ^ 8.
Proof.
  intros a b Ha Hb.
  pose proof (unsigned_Lastnbits_range (Z.lor a b) 8 ltac:(lia)) as Hr.
  rewrite unsigned_last_nbits_lor_distr_missing in Hr; lia.
Qed.
Lemma encode_event_wait_grp_byte__single_wake_restore_and_early_returns :
  forall sg wl tskSt,
    valid_stable_glob_vars sg ->
    (forall tid,
      In tid wl ->
      exists t,
        inUsedTaskStates tskSt tid = Some t /\
        valid_task_prio sg (curPrio t)) ->
    0 <= encode_event_wait_grp wl tskSt < 2 ^ 8.
Proof.
  intros sg wl.
  induction wl as [|tid rest IH]; intros tskSt Hstable Hrange.
  - cbn. lia.
  - destruct (Hrange tid ltac:(left; reflexivity))
      as [t [Hget Hprio]].
    cbn. rewrite Hget.
    apply lor_byte__single_wake_restore_and_early_returns.
    + apply shiftl_bit_byte__single_wake_restore_and_early_returns.
      unfold valid_task_prio in Hprio.
      unfold valid_stable_glob_vars in Hstable.
      split.
      * apply Z_div_nonneg_nonneg; lia.
      * apply Zdiv_lt_upper_bound; lia.
    + apply IH; [exact Hstable |].
      intros tid0 Hin. apply Hrange. right. exact Hin.
Qed.
