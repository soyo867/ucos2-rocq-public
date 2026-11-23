Require Import Coq.ZArith.ZArith.
From AUXLib Require Import int_auto ListLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import IntLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.mutex_func_sem.
Require Import Ucos2Verify.lib.mutex_rdyatprio_spec.

Import Monad.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(* Exact public observation of the source-ordered OSMutexPost semantics. *)
Definition mutex_post_result_prop
  (sg : StableGlobVars) (pevent : Z)
  (ls0 ls_post : UCOS2_Verify_State) (ret : Z) : Prop :=
  exists err,
    OSMutexPost_sem sg pevent ls0 err ls_post /\
    ret = encode_os_err_code err.

(* [RTrans_Abs] is deliberately permissive, so the generic [LastSeen] token
   does not identify the state selected by the source-exact Post semantics.
   Keep the chosen post state in an operation-labelled singleton token. *)
Definition OSMutexPost_post_token
  (ls_post : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun observed => observed = ls_post.

Lemma OSMutexPost_post_token_injective :
  forall ls1 ls2,
    OSMutexPost_post_token ls1 = OSMutexPost_post_token ls2 ->
    ls1 = ls2.
Proof.
  intros ls1 ls2 Heq.
  assert (Hseen : OSMutexPost_post_token ls2 ls1).
  {
    rewrite <- Heq.
    unfold OSMutexPost_post_token.
    reflexivity.
  }
  exact Hseen.
Qed.

Definition OSMutexPost_LastSeen
  (sg : StableGlobVars) (pevent : Z)
  (ls0 : UCOS2_Verify_State) (err : OSErrCode)
  (ls_post : UCOS2_Verify_State)
  : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun X =>
    OSMutexPost_sem sg pevent ls0 err ls_post /\
    X = OSMutexPost_post_token ls_post.

(* Precise L5 lift of Post.  This leaves the ambient critical STS unchanged
   and refines only this operation's continuation endpoint. *)
Definition OSMutexPost_atomic_cmd
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State) (pevent : Z)
  : program (UCOS2_Verify_State -> Prop) OSErrCode :=
  fun X1 err X2 =>
    LastSeen ls0 X1 /\
    exists ls_post,
      OSMutexPost_LastSeen sg pevent ls0 err ls_post X2.

Lemma OSMutexPost_safe_return :
  forall sg pevent ls0 err ls_post
         (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop),
    OSMutexPost_sem sg pevent ls0 err ls_post ->
    safeExec (LastSeen ls0)
      (bind (OSMutexPost_atomic_cmd sg ls0 pevent)
            observe_os_err_code) X ->
    safeExec
      (OSMutexPost_LastSeen sg pevent ls0 err ls_post)
      (@StateRelMonad.ret
         (UCOS2_Verify_State -> Prop) Z
         (encode_os_err_code err)) X.
Proof.
  intros sg pevent ls0 err ls_post X Hsem Hexec.
  assert (Hatomic : hs_eval
    (OSMutexPost_atomic_cmd sg ls0 pevent)
    (LastSeen ls0)
    (OSMutexPost_LastSeen sg pevent ls0 err ls_post) err).
  {
    unfold hs_eval, OSMutexPost_atomic_cmd.
    intros X1 HX1.
    exists (OSMutexPost_post_token ls_post).
    split.
    - split.
      + exact HX1.
      + exists ls_post.
        unfold OSMutexPost_LastSeen.
        split; [exact Hsem | reflexivity].
    - unfold OSMutexPost_LastSeen.
      split; [exact Hsem | reflexivity].
  }
  pose proof (highstepbind_derive
    (OSMutexPost_atomic_cmd sg ls0 pevent)
    observe_os_err_code (LastSeen ls0) err
    (OSMutexPost_LastSeen sg pevent ls0 err ls_post)
    Hatomic X Hexec) as Hobserve.
  eapply (highstependret_derive
    (observe_os_err_code err)
    (OSMutexPost_LastSeen sg pevent ls0 err ls_post)
    (encode_os_err_code err)
    (fun _ => OSMutexPost_LastSeen
       sg pevent ls0 err ls_post)).
  2: exact Hobserve.
  unfold hs_eval, observe_os_err_code.
  intros X1 HX1.
  exists X1.
  split.
  - split; reflexivity.
  - exact HX1.
Qed.

(* Post-specific source-total view of the literal current-TCB relocation.
   Unlike the older ready-domain specialization, this relation does not use
   ready-list membership as an execution guard: the source clears and then
   reinserts the current TCB's ready bit even from a represented
   blocked-before-schedule entry.  Stable closure therefore needs an
   explicit call-boundary protocol or a larger source-exact transient; it
   cannot be obtained by silently filtering this raw relation. *)
Definition OSMutexPost_RdyAtPrio_sem
  (sg : StableGlobVars) (ptcb : Z) (prio : Priority)
  : program UCOS2_Verify_State unit :=
  fun lvs1 (_ : unit) lvs2 =>
    exists tid old_t,
      ptcb = verification_slice_tcb_addr sg tid /\
      atomic_task_set_curPrio_current_literal_exec
        sg tid old_t prio lvs1 tt lvs2.

Definition OSMutexPost_RdyAtPrio_guarantee
  (sg : StableGlobVars) (ptcb : Z) (prio : Priority)
  (ls0 ls_post : UCOS2_Verify_State) : Prop :=
  OSMutexPost_RdyAtPrio_sem sg ptcb prio ls0 tt ls_post.

Definition OSMutexPost_RdyAtPrio_post_token
  (ls_post : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun observed => observed = ls_post.

Definition OSMutexPost_RdyAtPrio_LastSeen
  (sg : StableGlobVars) (ptcb : Z) (prio : Priority)
  (ls0 ls_post : UCOS2_Verify_State)
  : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun X =>
    OSMutexPost_RdyAtPrio_guarantee
      sg ptcb prio ls0 ls_post /\
    X = OSMutexPost_RdyAtPrio_post_token ls_post.

Definition OSMutexPost_RdyAtPrio_atomic_cmd
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (ptcb : Z) (prio : Priority)
  : program (UCOS2_Verify_State -> Prop) unit :=
  fun X1 (_ : unit) X2 =>
    LastSeen ls0 X1 /\
    exists ls_post,
      OSMutexPost_RdyAtPrio_LastSeen
        sg ptcb prio ls0 ls_post X2.

(* Exact relational views for source-level calls and state updates. *)
Definition mutex_post_current_ready_step_prop
  (sg : StableGlobVars) (ptcb : Z) (prio : Z)
  (ls0 ls_post : UCOS2_Verify_State) : Prop :=
  OSMutexPost_RdyAtPrio_sem sg ptcb prio ls0 tt ls_post.

Definition mutex_post_sched_step_prop
  (ls0 ls_post : UCOS2_Verify_State) : Prop :=
  exists sched_res, atomic_sched ls0 sched_res ls_post.

Definition mutex_post_release_step_prop
  (sg : StableGlobVars) (eid : EventID)
  (ls0 ls_post : UCOS2_Verify_State) : Prop :=
  OSMutexPost_empty_release_sem sg eid ls0 ls_post.

Definition mutex_post_empty_count_commit_step_prop
  (eid : EventID) (ls_reserved ls_available : UCOS2_Verify_State) : Prop :=
  OSMutexPost_empty_count_commit_sem eid ls_reserved ls_available.

Definition mutex_post_empty_owner_commit_step_prop
  (eid : EventID) (ls_available ls_post : UCOS2_Verify_State) : Prop :=
  OSMutexPost_empty_owner_commit_sem eid ls_available ls_post.

Definition mutex_post_checked_entry_prop
  (ls0 : UCOS2_Verify_State) (pevent : Z) : Prop :=
  ls0.(IntrState).(intNesting) <= 0 /\ pevent <> 0.

(* L5 public-domain view for the source-ordered type test.  This deliberately
   packages, rather than redefines, the generic event representation:
   [event_snapshot_of_prop]/[event_slot_unused_prop] and all type-only
   split/merge ownership remain in [event.v].  The live-only owner/PCP/task
   facts are therefore unavailable until the concrete type read selects the
   mutex branch. *)
Definition mutex_post_public_event_domain_prop
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (pevent : Z) (eid : EventID) (e : OSEventAbstractState)
  (etype ecnt owner_ptr egrp : Z) (etbl : list Z)
  (pcp_idx prio_tbl_pcp tcbcur tcbprio : Z)
  (prio_tbl : list Z) (cur_tid : TaskID)
  (cur_t : TaskAbstractState)
  (wait_grp_addr wait_tbl_addr prio_addr : Z) : Prop :=
  pevent = event_addr sg eid /\
  ((0 <= etype <= 255 /\
    event_snapshot_of_prop
      sg ls0.(TskState) ls0.(EventState) eid e
      etype ecnt owner_ptr egrp etbl /\
    event_wait_fields_layout_prop sg eid wait_grp_addr wait_tbl_addr /\
    (etype <> 4 \/
     (etype = 4 /\
      UCOS2_isr_or_task_call_boundary_prop ls0 /\
      tcbcur <> 0 /\
      pcp_idx = decode_PCP_from_cnt ecnt /\
      prio_tbl_list_rel sg ls0.(TskState) prio_tbl /\
      Znth pcp_idx prio_tbl 0 = prio_tbl_pcp /\
      verification_slice_sched_tcb_cur_snapshot_prop sg ls0.(SchedState) tcbcur /\
      task_prio_snapshot_of_prop
        sg ls0.(TskState) cur_tid cur_t tcbcur tcbprio /\
      task_prio_field_layout_prop tcbcur prio_addr))) \/
   event_slot_unused_prop ls0.(EventState) eid).

(* The public contract above is total.  Only the successful concrete mutex
   type comparison may expose the facts whose meaning presupposes a live
   mutex event. *)
Lemma mutex_post_public_event_domain_select_mutex :
  forall sg ls0 pevent eid e etype ecnt owner_ptr egrp etbl
         pcp_idx prio_tbl_pcp tcbcur tcbprio prio_tbl cur_tid cur_t
         wait_grp_addr wait_tbl_addr prio_addr,
    unsigned_last_nbits
      (event_slot_type_value ls0.(EventState) eid) 32 = 4 ->
    mutex_post_public_event_domain_prop
      sg ls0 pevent eid e etype ecnt owner_ptr egrp etbl
      pcp_idx prio_tbl_pcp tcbcur tcbprio prio_tbl cur_tid cur_t
      wait_grp_addr wait_tbl_addr prio_addr ->
    etype = 4 /\
    UCOS2_isr_or_task_call_boundary_prop ls0 /\
    tcbcur <> 0 /\
    pcp_idx = decode_PCP_from_cnt ecnt /\
    prio_tbl_list_rel sg ls0.(TskState) prio_tbl /\
    Znth pcp_idx prio_tbl 0 = prio_tbl_pcp /\
    verification_slice_sched_tcb_cur_snapshot_prop sg ls0.(SchedState) tcbcur /\
    task_prio_snapshot_of_prop
      sg ls0.(TskState) cur_tid cur_t tcbcur tcbprio /\
    task_prio_field_layout_prop tcbcur prio_addr /\
    event_snapshot_of_prop
      sg ls0.(TskState) ls0.(EventState) eid e
      etype ecnt owner_ptr egrp etbl /\
    event_wait_fields_layout_prop sg eid wait_grp_addr wait_tbl_addr.
Proof.
  intros sg ls0 pevent eid e etype ecnt owner_ptr egrp etbl
         pcp_idx prio_tbl_pcp tcbcur tcbprio prio_tbl cur_tid cur_t
         wait_grp_addr wait_tbl_addr prio_addr Htype Hdomain.
  unfold mutex_post_public_event_domain_prop in Hdomain.
  destruct Hdomain as [_ Hdomain].
  destruct Hdomain as
      [[Hrange [Hsnapshot [Hwait [Hnot_mutex | Hmutex]]]] | Hfree].
  - unfold event_snapshot_of_prop in Hsnapshot.
    destruct Hsnapshot as
        [Hused [Hetype [Hecnt [Hptr [Hgrp Htbl]]]]].
    subst etype.
    unfold event_slot_type_value in Htype.
    rewrite Hused in Htype.
    destruct (eventType e); cbn in Htype, Hnot_mutex; congruence.
  - destruct Hmutex as
        [Hetype [Hscenario [Htcb [Hpcp [Hprio_tbl [Hlookup
         [Hsched [Htask Hprio_layout]]]]]]]].
    split; [exact Hetype |].
    split; [exact Hscenario |].
    split; [exact Htcb |].
    split; [exact Hpcp |].
    split; [exact Hprio_tbl |].
    split; [exact Hlookup |].
    split; [exact Hsched |].
    split; [exact Htask |].
    split; [exact Hprio_layout |].
    split; [exact Hsnapshot | exact Hwait].
  - unfold event_slot_unused_prop in Hfree.
    unfold event_slot_type_value in Htype.
    rewrite Hfree in Htype.
    cbn in Htype.
    discriminate.
Qed.

(* The stable entry facts for the optional current-owner disinherit call.
   Relocation legality is a preservation classifier, not an execution guard
   of the total public Post semantics. *)
Definition mutex_post_owner_entry_context_prop
  (sg : StableGlobVars) (pevent : Z) (eid : EventID)
  (ls0 ls_entry : UCOS2_Verify_State)
  (pcp owner_orig ptcb current_prio : Z) : Prop :=
  valid_stable_glob_vars sg /\
  ls_entry = ls0 /\
  mutex_post_checked_entry_prop ls0 pevent /\
  UCOS2_isr_or_task_call_boundary_prop ls0 /\
  exists e m cur_tid cur_t,
    pevent = event_addr sg eid /\
    ls0.(EventState).(inUsedEventStates) eid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some cur_tid /\
    m.(mfPCP) = pcp /\
    m.(mfOwnerOrigPrio) = Some owner_orig /\
    ls0.(SchedState).(curTaskID) = Some cur_tid /\
    ls0.(TskState).(inUsedTaskStates) cur_tid = Some cur_t /\
    ptcb = verification_slice_tcb_addr sg cur_tid /\
    cur_t.(curPrio) = current_prio.

(* Exact checkpoint after the optional disinherit source branch. *)
Definition mutex_post_owner_disinherit_stage_prop
  (sg : StableGlobVars) (pevent : Z)
  (ls0 : UCOS2_Verify_State) (pcp owner_orig : Z)
  (ls_d : UCOS2_Verify_State) : Prop :=
  mutex_post_checked_entry_prop ls0 pevent /\
  UCOS2_isr_or_task_call_boundary_prop ls0 /\
  exists eid e m cur_tid,
    pevent = event_addr sg eid /\
    ls0.(EventState).(inUsedEventStates) eid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    m.(mfOwner) = Some cur_tid /\
    m.(mfPCP) = pcp /\
    m.(mfOwnerOrigPrio) = Some owner_orig /\
    ls0.(SchedState).(curTaskID) = Some cur_tid /\
    OSMutexPost_disinherit_sem sg m cur_tid ls0 ls_d.

Lemma mutex_post_owner_disinherit_stage_task_call_boundary :
  forall sg pevent ls0 pcp owner_orig ls_d,
    mutex_post_owner_disinherit_stage_prop
      sg pevent ls0 pcp owner_orig ls_d ->
    sched_task_call_boundary ls0.(TskState) ls0.(SchedState).
Proof.
  intros sg pevent ls0 pcp owner_orig ls_d Hstage.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage.
  destruct Hstage as [Hchecked [Hscenario _]].
  unfold mutex_post_checked_entry_prop in Hchecked.
  destruct Hchecked as [Hnonisr _].
  eapply UCOS2_isr_or_task_call_boundary_non_isr; eassumption.
Qed.

(* Exact source-order PCP reservation between disinherit and release.  The
   canonical transition lives with the Post function semantics; this
   case-local name is only the annotation-facing view. *)
Definition mutex_post_reservation_stage_prop
  (sg : StableGlobVars) (eid : EventID)
  (ls_d ls_reserved : UCOS2_Verify_State) : Prop :=
  OSMutexPost_reservation_sem sg eid ls_d ls_reserved.

(* OS_EventTaskRdy stops here; neither subsequent caller write is included. *)
Definition mutex_post_wake_step_prop
  (sg : StableGlobVars) (eid : EventID)
  (ls_reserved : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (ls_wake : UCOS2_Verify_State) : Prop :=
  OSMutexPost_wake_sem
    sg eid ls_reserved returned_prio
    canonical_waiter table_owner ls_wake.

(* The two count operations form one exact logical checkpoint. *)
Definition mutex_post_count_commit_step_prop
  (eid : EventID) (returned_prio : Priority)
  (ls_wake ls_cnt : UCOS2_Verify_State) : Prop :=
  OSMutexPost_count_commit_sem eid returned_prio ls_wake ls_cnt.

(* The owner pointer changes only after the literal second prioTbl read. *)
Definition mutex_post_owner_commit_step_prop
  (eid : EventID) (returned_prio : Priority) (table_owner : TaskID)
  (ls_cnt ls_h : UCOS2_Verify_State) : Prop :=
  OSMutexPost_owner_commit_sem
    eid returned_prio table_owner ls_cnt ls_h.

(* Full source-order handover observation.  The event-selected
   [canonical_waiter] and the [table_owner] read through
   OSTCBPrioTbl[returned_prio] remain distinct in the raw transition.  C
   annotations carry [returned_prio] unchanged to the second priority-table
   read; identity equality is a conditional stable closure fact, never a raw
   helper premise. *)
Definition mutex_post_handover_step_prop
  (sg : StableGlobVars) (eid : EventID)
  (ls_d : UCOS2_Verify_State) (returned_prio : Priority)
  (canonical_waiter table_owner : TaskID)
  (ls_h : UCOS2_Verify_State) : Prop :=
  OSMutexPost_handover_sem
    sg eid ls_d returned_prio canonical_waiter table_owner ls_h.

(* Post executes for every source-defined input, including states where an
   internal priority relocation cannot re-establish the stable L1--L4
   validity bundle.  Keep all concrete ownership in the source-total raw
   representation.  The second disjunct records the exact transient cache
   shape left by RdyAtPrio/EventTaskRdy until OS_Sched refreshes it. *)
Definition mutex_post_rep
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) : Assertion :=
  UCOS2_verification_slice_raw_rep sg post ||
  UCOS2_verification_slice_raw_ready_prio_stage sg entry post.

(* Reversible localization of the selected mutex event.  [TT] is not a
   footprint shortcut: it preserves the explicit legacy residual exported
   by [UCOS2_verification_slice_raw_rep], whose full-invariant source ends in a separating pure
   proposition. *)
Definition mutex_post_rep_no_event
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_rep sg post.(TskState) post.(SchedState) **
   verification_slice_event_raw_rep_no_eid
     sg post.(TskState) post.(EventState) eid **
   verification_slice_tick_inv sg post.(TickState) **
   TT) ||
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep sg post.(TskState) **
   verification_slice_sched_raw_ready_prio_stage
     sg entry.(SchedState) post.(SchedState) post.(TskState) **
   verification_slice_event_raw_rep_no_eid
     sg post.(TskState) post.(EventState) eid **
   verification_slice_tick_inv sg post.(TickState) **
   TT).

(* Residual after localizing both the selected event and the priority table. *)
Definition mutex_post_rep_no_priotbl_no_event
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep_no_priotbl sg post.(TskState) **
   verification_slice_sched_raw_rep sg post.(TskState) post.(SchedState) **
   verification_slice_event_raw_rep_no_eid
     sg post.(TskState) post.(EventState) eid **
   verification_slice_tick_inv sg post.(TickState) **
   TT) ||
  (interrupt_inv sg post.(IntrState) **
   verification_slice_task_raw_rep_no_priotbl sg post.(TskState) **
   verification_slice_sched_raw_ready_prio_stage
     sg entry.(SchedState) post.(SchedState) post.(TskState) **
   verification_slice_event_raw_rep_no_eid
     sg post.(TskState) post.(EventState) eid **
   verification_slice_tick_inv sg post.(TickState) **
   TT).

(* EventTaskRdy has already changed the abstract task/event/scheduler state,
   but the selected event's count/owner cells are committed by the following
   source statements.  These predicates own precisely the unaffected
   residual; the C contract keeps the selected event cells explicit. *)
Definition mutex_post_handover_residual
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  interrupt_inv sg post.(IntrState) **
  verification_slice_task_raw_rep sg post.(TskState) **
  verification_slice_sched_raw_ready_prio_stage
    sg entry.(SchedState) post.(SchedState) post.(TskState) **
  verification_slice_event_raw_rep_no_eid
    sg post.(TskState) post.(EventState) eid **
  verification_slice_tick_inv sg post.(TickState) **
  TT.

Definition mutex_post_handover_residual_no_priotbl
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  interrupt_inv sg post.(IntrState) **
  verification_slice_task_raw_rep_no_priotbl sg post.(TskState) **
  verification_slice_sched_raw_ready_prio_stage
    sg entry.(SchedState) post.(SchedState) post.(TskState) **
  verification_slice_event_raw_rep_no_eid
    sg post.(TskState) post.(EventState) eid **
  verification_slice_tick_inv sg post.(TickState) **
  TT.

(* Relocation legality is a preservation classifier, never a public
   execution precondition.  When it holds, the exact source result must
   recover the inherited L1--L4 mathematical validity bundle. *)
Definition mutex_post_conditional_validity_prop
  (sg : StableGlobVars) (pevent : Z)
  (entry post : UCOS2_Verify_State) : Prop :=
  OSMutexPost_relocations_legal sg pevent entry ->
  UCOS2_verification_slice_state_inv sg post.

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Psatz.
Require Import Coq.Bool.Bool.
Lemma mutex_post_ready_stage_absorb_truep__disinherit_reservation :
  forall sg entry post,
    TT ** UCOS2_verification_slice_raw_ready_prio_stage sg entry post
    |-- UCOS2_verification_slice_raw_ready_prio_stage sg entry post.
Proof.
  intros.
  unfold UCOS2_verification_slice_raw_ready_prio_stage.
  sep_apply_l_atomic debug_truep_merge__relocation_semantics.
  entailer!.
Qed.
Lemma mutex_post_ready_stage_absorb_three_truep__disinherit_reservation :
  forall sg entry post,
    TT ** (TT ** (TT ** UCOS2_verification_slice_raw_ready_prio_stage sg entry post))
    |-- UCOS2_verification_slice_raw_ready_prio_stage sg entry post.
Proof.
  intros.
  unfold UCOS2_verification_slice_raw_ready_prio_stage.
  repeat
    sep_apply_l_atomic debug_truep_merge__relocation_semantics.
  entailer!.
Qed.
Lemma mutex_post_entail_add_truep__disinherit_reservation :
  forall P Q : Assertion,
    P |-- Q ->
    P |-- TT ** Q.
Proof.
  intros P Q H.
  unfold derivable1, sepcon, truep in *.
  intros m HP.
  destruct (unit_join m) as [u [Hu Hjoin]].
  exists u, m.
  split.
  - apply join_comm.
    exact Hjoin.
  - split.
    + exact I.
    + apply H.
      exact HP.
Qed.
Lemma verification_slice_prioTbl_to_addrs_rel__disinherit_reservation :
  forall sg st,
    prio_tbl_list_rel sg st
      (verification_slice_prioTbl_to_addrs sg st.(TaskStateDef.prioTbl)).
Proof.
  intros sg st.
  unfold prio_tbl_list_rel. split.
  - unfold verification_slice_prioTbl_to_addrs, OS_PRIO_TBL_SIZE, Zlength.
    vm_compute. reflexivity.
  - intros p Hp.
    unfold verification_slice_prioTbl_to_addrs, OS_PRIO_TBL_SIZE in *.
    rewrite verification_slice_prioTbl_to_addrs_rec_seq__relocation_semantics.
    rewrite app_nil_r.
    unfold Znth.
    assert (Hnat : (Z.to_nat p < 64)%nat) by lia.
    assert (Hdefault :
      nth (Z.to_nat p)
        (map
          (fun k : nat =>
            verification_slice_prio_tbl_entry_to_addr sg
              (TaskStateDef.prioTbl st (Z.of_nat k)))
          (seq 0 64))
        0 =
      nth (Z.to_nat p)
        (map
          (fun k : nat =>
            verification_slice_prio_tbl_entry_to_addr sg
              (TaskStateDef.prioTbl st (Z.of_nat k)))
          (seq 0 64))
        (verification_slice_prio_tbl_entry_to_addr sg
          (TaskStateDef.prioTbl st (Z.of_nat 0)))).
    {
      apply nth_indep.
      rewrite length_map, length_seq.
      exact Hnat.
    }
    rewrite Hdefault.
    change
      (nth (Z.to_nat p)
        (map
          (fun k : nat =>
            verification_slice_prio_tbl_entry_to_addr sg
              (TaskStateDef.prioTbl st (Z.of_nat k)))
          (seq 0 64))
        ((fun k : nat =>
          verification_slice_prio_tbl_entry_to_addr sg
            (TaskStateDef.prioTbl st (Z.of_nat k))) 0%nat) =
       verification_slice_prio_tbl_entry_to_addr sg (TaskStateDef.prioTbl st p)).
    rewrite map_nth.
    rewrite seq_nth by exact Hnat.
    simpl Nat.add.
    rewrite Z2Nat.id by lia.
    reflexivity.
Qed.
Lemma prio_tbl_list_rel_update_reserved__disinherit_reservation :
  forall sg st st2 p l,
    0 <= p < OS_PRIO_TBL_SIZE ->
    prioTbl st2 =
      (fun q => if Z.eqb q p then PTReserved else prioTbl st q) ->
    prio_tbl_list_rel sg st l ->
    prio_tbl_list_rel sg st2 (replace_Znth p 1 l).
Proof.
  intros sg st st2 p l Hp Htbl Hrel.
  unfold prio_tbl_list_rel in Hrel |- *.
  destruct Hrel as [Hlen Hnth].
  split.
  - rewrite Zlength_replace_Znth.
    exact Hlen.
  - intros q Hq.
    rewrite Htbl.
    destruct (Z.eq_dec q p) as [-> | Hne].
    + rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_eq_gen by
        (rewrite Hlen; exact Hp).
      rewrite Z.eqb_refl.
      reflexivity.
    + rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_neq_gen.
      2: exact Hne.
      2: rewrite Hlen; exact Hq.
      2: rewrite Hlen; exact Hp.
      rewrite Hnth by exact Hq.
      rewrite (proj2 (Z.eqb_neq q p) Hne).
      reflexivity.
Qed.
Lemma encode_ready_tbl_at_or_task_ext__disinherit_reservation :
  forall rl t1 t2 y,
    inUsedTaskStates t1 = inUsedTaskStates t2 ->
    encode_ready_tbl_at_or rl t1 y =
      encode_ready_tbl_at_or rl t2 y.
Proof.
  induction rl as [| tid rest IH]; intros t1 t2 y Hmap.
  - reflexivity.
  - simpl.
    rewrite Hmap.
    rewrite (IH t1 t2 y Hmap).
    reflexivity.
Qed.
Lemma encode_event_wait_tbl_at_or_task_ext__disinherit_reservation :
  forall wl t1 t2 y,
    inUsedTaskStates t1 = inUsedTaskStates t2 ->
    encode_event_wait_tbl_at_or wl t1 y =
      encode_event_wait_tbl_at_or wl t2 y.
Proof.
  induction wl as [| tid rest IH]; intros t1 t2 y Hmap.
  - reflexivity.
  - simpl.
    rewrite Hmap.
    rewrite (IH t1 t2 y Hmap).
    reflexivity.
Qed.
Lemma mutex_post_rep_reservation_merge__disinherit_reservation :
  forall sg entry post reserved eid,
    inUsedTaskStates post.(TskState) =
      inUsedTaskStates reserved ->
    verification_slice_task_raw_rep_no_priotbl sg post.(TskState) =
      verification_slice_task_raw_rep_no_priotbl sg reserved ->
    verification_slice_store_prio_tbl sg reserved.(prioTbl) **
      mutex_post_rep_no_priotbl_no_event sg entry post eid
    |-- mutex_post_rep_no_event
          sg entry (replace_TskS reserved post) eid.
Proof.
  intros sg entry post reserved eid Hmap Htask_no_eq.
  assert (Hused_event_raw_eq :
    forall base eid' ev,
      used_complete_event_raw
        sg post.(TskState) base eid' ev =
      used_complete_event_raw
        sg reserved base eid' ev).
  {
    intros base eid' ev.
    unfold used_complete_event_raw.
    assert (Hpoint :
      forall tid, In tid (waitList ev) ->
        inUsedTaskStates post.(TskState) tid =
          inUsedTaskStates reserved tid).
    {
      intros tid Hin.
      rewrite Hmap.
      reflexivity.
    }
    rewrite
      (debug_event_grp_ext_in__relocation_semantics
        (waitList ev) post.(TskState) reserved Hpoint).
    rewrite
      (encode_event_wait_tbl_at_or_task_ext__disinherit_reservation
        (waitList ev) post.(TskState) reserved 0 Hmap).
    rewrite
      (encode_event_wait_tbl_at_or_task_ext__disinherit_reservation
        (waitList ev) post.(TskState) reserved 1 Hmap).
    rewrite
      (encode_event_wait_tbl_at_or_task_ext__disinherit_reservation
        (waitList ev) post.(TskState) reserved 2 Hmap).
    rewrite
      (encode_event_wait_tbl_at_or_task_ext__disinherit_reservation
        (waitList ev) post.(TskState) reserved 3 Hmap).
    rewrite
      (encode_event_wait_tbl_at_or_task_ext__disinherit_reservation
        (waitList ev) post.(TskState) reserved 4 Hmap).
    rewrite
      (encode_event_wait_tbl_at_or_task_ext__disinherit_reservation
        (waitList ev) post.(TskState) reserved 5 Hmap).
    rewrite
      (encode_event_wait_tbl_at_or_task_ext__disinherit_reservation
        (waitList ev) post.(TskState) reserved 6 Hmap).
    rewrite
      (encode_event_wait_tbl_at_or_task_ext__disinherit_reservation
        (waitList ev) post.(TskState) reserved 7 Hmap).
    reflexivity.
  }
  assert (Hevent_no_eq :
    verification_slice_event_raw_rep_no_eid
      sg post.(TskState) post.(EventState) eid =
    verification_slice_event_raw_rep_no_eid
      sg reserved post.(EventState) eid).
  {
    unfold verification_slice_event_raw_rep_no_eid,
      store_used_event_map_raw_missing_i.
    assert (Hfun :
      (fun eid' ev =>
        used_complete_event_raw
          sg post.(TskState) (event_addr sg eid') eid' ev) =
      (fun eid' ev =>
        used_complete_event_raw
          sg reserved (event_addr sg eid') eid' ev)).
    {
      apply functional_extensionality.
      intro eid'.
      apply functional_extensionality.
      intro ev.
      apply Hused_event_raw_eq.
    }
    rewrite Hfun.
    reflexivity.
  }
  assert (Hsched_raw_eq :
    forall sched,
      verification_slice_sched_raw_rep sg post.(TskState) sched =
      verification_slice_sched_raw_rep sg reserved sched).
  {
    intro sched.
    unfold verification_slice_sched_raw_rep.
    rewrite
      (encode_ready_grp_ext
        (readyList sched) post.(TskState) reserved Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 0 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 1 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 2 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 3 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 4 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 5 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 6 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 7 Hmap).
    reflexivity.
  }
  assert (Hsched_stage_eq :
    forall pre sched,
      verification_slice_sched_raw_ready_prio_stage
        sg pre sched post.(TskState) =
      verification_slice_sched_raw_ready_prio_stage
        sg pre sched reserved).
  {
    intros pre sched.
    unfold verification_slice_sched_raw_ready_prio_stage.
    rewrite
      (encode_ready_grp_ext
        (readyList sched) post.(TskState) reserved Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 0 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 1 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 2 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 3 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 4 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 5 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 6 Hmap).
    rewrite
      (encode_ready_tbl_at_or_task_ext__disinherit_reservation
        (readyList sched) post.(TskState) reserved 7 Hmap).
    reflexivity.
  }
  unfold mutex_post_rep_no_priotbl_no_event,
    mutex_post_rep_no_event.
  rewrite Htask_no_eq.
  rewrite (Hsched_raw_eq post.(SchedState)).
  rewrite
    (Hsched_stage_eq entry.(SchedState) post.(SchedState)).
  rewrite Hevent_no_eq.
  Split.
  - Left.
    sep_apply_l_atomic (verification_slice_task_raw_rep_merge_priotbl sg reserved).
    entailer!.
    unfold replace_TskS.
    cbn.
    cancel.
  - Right.
    sep_apply_l_atomic (verification_slice_task_raw_rep_merge_priotbl sg reserved).
    entailer!.
    unfold replace_TskS.
    cbn.
    cancel.
Qed.
Lemma post_wake_returned_prio_range__handover_commit :
  forall sg pevent entry pcp owner_orig ls_d eid ls_r
         retval canonical_waiter table_owner ls_wake,
    valid_stable_glob_vars sg ->
    UCOS2_verification_slice_state_inv sg entry ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig ls_d ->
    mutex_post_reservation_stage_prop sg eid ls_d ls_r ->
    mutex_post_wake_step_prop
      sg eid ls_r retval canonical_waiter table_owner ls_wake ->
    0 <= retval < 64.
Proof.
  intros sg pevent entry pcp owner_orig ls_d eid ls_r
    retval canonical_waiter table_owner ls_wake
    Hstable Hvalid Hdisinherit Hreservation Hwake.
  unfold mutex_post_wake_step_prop, OSMutexPost_wake_sem,
    atomic_event_task_rdy, atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (e1 & e2 & canonical_t & table_t & table_t' &
     Hevent & Hpend & Hnonempty & Hcanonical &
     Hcanonical_get & Hretval & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hls_wake).
  unfold mutex_post_reservation_stage_prop,
    OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (er & mr & owner & tsk_reserved &
     Her & Hertype & Hermutex & Howner & Htsk_reserved & Hls_r).
  subst tsk_reserved ls_r.
  cbn in Htable_slot.
  destruct
    (negb (Z.eqb (mfPCP mr) (osPrioMutexCeilDis sg)) &&
     Z.eqb retval (mfPCP mr))%bool eqn:Hreserved.
  - discriminate.
  - unfold mutex_post_owner_disinherit_stage_prop in Hdisinherit.
    destruct Hdisinherit as
      (_ & _ & eid0 & e0 & m0 & cur_tid &
       _ & _ & _ & _ & _ & _ & _ & _ & Hdisinherit).
    unfold OSMutexPost_disinherit_sem in Hdisinherit.
    destruct Hdisinherit as (cur_t & Hcur_t & Hbranch).
    destruct Hbranch as
      [[Hdisabled Hsame] |
       [[Henabled [Hnot_pcp Hsame]] |
        [Henabled [Hat_pcp [orig [Horig Hexec]]]]]].
    + subst ls_d.
      unfold UCOS2_verification_slice_state_inv in Hvalid.
      destruct Hvalid as [[Htask _] _].
      unfold verification_slice_task_in_range in Htask.
      destruct Htask as [_ [_ [_ [_ [Hprio _]]]]].
      specialize (Hprio retval table_owner Htable_slot).
      unfold valid_task_prio in Hprio.
      unfold valid_stable_glob_vars in Hstable.
      lia.
    + subst ls_d.
      unfold UCOS2_verification_slice_state_inv in Hvalid.
      destruct Hvalid as [[Htask _] _].
      unfold verification_slice_task_in_range in Htask.
      destruct Htask as [_ [_ [_ [_ [Hprio _]]]]].
      specialize (Hprio retval table_owner Htable_slot).
      unfold valid_task_prio in Hprio.
      unfold valid_stable_glob_vars in Hstable.
      lia.
    + unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
      destruct Hexec as
        (t' & Hcur & Hcur_prio & Hlookup & Horig_lo & Horig_hi &
         Ht' & Hls_d).
      cbv zeta in Hls_d.
      subst ls_d.
      cbn in Htable_slot.
      destruct (Z.eqb retval orig) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst retval.
        unfold valid_stable_glob_vars in Hstable.
        lia.
      * unfold UCOS2_verification_slice_state_inv in Hvalid.
        destruct Hvalid as [[Htask _] _].
        unfold verification_slice_task_in_range in Htask.
        destruct Htask as [_ [_ [_ [_ [Hprio _]]]]].
        specialize (Hprio retval table_owner Htable_slot).
        unfold valid_task_prio in Hprio.
        unfold valid_stable_glob_vars in Hstable.
        lia.
Qed.
Lemma mutex_post_owner_commit_snapshot__handover_commit :
  forall sg eid ls_d ls_r returned_prio canonical_waiter table_owner
         ls_wake ls_cnt e_cnt cnt ptr grp tbl,
    mutex_post_reservation_stage_prop sg eid ls_d ls_r ->
    mutex_post_wake_step_prop
      sg eid ls_r returned_prio canonical_waiter table_owner ls_wake ->
    mutex_post_count_commit_step_prop eid returned_prio ls_wake ls_cnt ->
    event_raw_snapshot_of_prop
      sg (TskState ls_cnt) (EventState ls_cnt) eid e_cnt
      4 cnt ptr grp tbl ->
    exists e_owner,
      let ls_owner :=
        replace_EventS
          (update_event_field_raw (EventState ls_cnt) eid e_owner)
          ls_cnt in
      mutex_post_owner_commit_step_prop
        eid returned_prio table_owner ls_cnt ls_owner /\
      event_raw_snapshot_of_prop
        sg (TskState ls_owner) (EventState ls_owner) eid e_owner
        4 cnt (verification_slice_tcb_addr sg table_owner) grp tbl.
Proof.
  intros sg eid ls_d ls_r returned_prio canonical_waiter table_owner
    ls_wake ls_cnt e_cnt cnt ptr grp tbl Hreservation Hwake Hcount Hsnap.
  unfold event_raw_snapshot_of_prop in Hsnap.
  destruct Hsnap as [Hget_cnt [Htype_cnt [Hcnt [Hptr [Hgrp Htbl]]]]].
  pose proof Hcount as Hcount_detail.
  unfold mutex_post_count_commit_step_prop,
    OSMutexPost_count_commit_sem in Hcount_detail.
  destruct Hcount_detail as
    (e1 & e2 & m1 & m2 & Hget1 & Htype1 & Hfields1 &
     Hm2 & He2 & Hls_cnt).
  assert (He_cnt_e2 : e_cnt = e2).
  {
    rewrite Hls_cnt in Hget_cnt.
    cbn in Hget_cnt.
    rewrite Z.eqb_refl in Hget_cnt.
    inversion Hget_cnt.
    reflexivity.
  }
  subst e_cnt.
  pose proof Hwake as Hwake_detail.
  unfold mutex_post_wake_step_prop, OSMutexPost_wake_sem,
    atomic_event_task_rdy, atomic_event_task_rdy_one in Hwake_detail.
  destruct Hwake_detail as
    (ew1 & ew2 & canonical_t & table_t & table_t' &
     Hget_wake & Hpend & Hnonempty & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & Hew2 & Hls_wake).
  unfold mutex_post_reservation_stage_prop,
    OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (er & mr & owner & tsk_reserved &
     Hget_reserved & Htype_reserved & Hfields_reserved &
     Howner_reserved & Htsk_reserved & Hls_r).
  assert (Her_ew1 : er = ew1).
  {
    rewrite Hls_r in Hget_wake.
    cbn in Hget_wake.
    rewrite Hget_reserved in Hget_wake.
    inversion Hget_wake.
    reflexivity.
  }
  subst er.
  assert (He1_ew2 : e1 = ew2).
  {
    rewrite Hls_wake in Hget1.
    cbn in Hget1.
    rewrite Z.eqb_refl in Hget1.
    inversion Hget1.
    reflexivity.
  }
  assert (Hm1_mr : m1 = mr).
  {
    rewrite He1_ew2, Hew2 in Hfields1.
    cbn in Hfields1.
    rewrite Hfields_reserved in Hfields1.
    inversion Hfields1.
    reflexivity.
  }
  assert (Howner_m2 : mfOwner m2 = Some owner).
  {
    rewrite Hm2, Hm1_mr.
    cbn.
    exact Howner_reserved.
  }
  assert (Htable_cnt :
    prioTbl (TskState ls_cnt) returned_prio = PTTask table_owner).
  {
    rewrite Hls_cnt, Hls_wake.
    cbn.
    exact Htable_slot.
  }
  set (m_owner :=
    {| mfPCP := mfPCP m2;
       mfOwner := Some table_owner;
       mfOwnerOrigPrio := mfOwnerOrigPrio m2 |}).
  set (e_owner :=
    {| eventGeneration := e2.(eventGeneration);
       eventName := e2.(eventName);
     eventPadding1 := e2.(eventPadding1);
     eventPadding2 := e2.(eventPadding2);
     eventPadding3 := e2.(eventPadding3);
     eventPadding19 := e2.(eventPadding19);
       eventType := eventType e2;
       mutexFields := Some m_owner;
       semFields := semFields e2;
       mboxFields := mboxFields e2;
       queueFields := queueFields e2;
       waitList := waitList e2 |}).
  exists e_owner.
  cbn zeta.
  split.
  - unfold mutex_post_owner_commit_step_prop,
      OSMutexPost_owner_commit_sem.
    split; [exact Htable_cnt|].
    exists e2, e_owner, m2, m_owner.
    repeat split; try reflexivity; try exact Hget_cnt.
    + rewrite He2.
      cbn.
      exact Htype1.
    + rewrite He2.
      cbn.
      reflexivity.
    + exact Htable_cnt.
  - unfold event_raw_snapshot_of_prop.
    repeat split.
    + cbn. rewrite Z.eqb_refl. reflexivity.
    + unfold e_owner. cbn.
      exact Htype_cnt.
    + unfold e_owner, m_owner. cbn.
      unfold encode_event_cnt_value in Hcnt |- *.
      cbn.
      rewrite He2 in Hcnt.
      cbn in Hcnt.
      rewrite Htype1, Howner_m2 in Hcnt.
      rewrite He2.
      cbn.
      rewrite Htype1.
      exact Hcnt.
    + unfold e_owner, m_owner, verification_slice_encode_event_ptr_value.
      cbn.
      rewrite He2.
      cbn.
      rewrite Htype1.
      reflexivity.
    + unfold e_owner. cbn.
      exact Hgrp.
    + unfold e_owner. cbn.
      exact Htbl.
Qed.
Lemma verification_slice_event_raw_rep_no_eid_update__handover_commit :
  forall sg tskSt evSt eid e,
    verification_slice_event_raw_rep_no_eid sg tskSt evSt eid |--
      verification_slice_event_raw_rep_no_eid
        sg tskSt (update_event_field_raw evSt eid e) eid.
Proof.
  intros sg tskSt evSt eid e.
  unfold verification_slice_event_raw_rep_no_eid, store_used_event_map_raw_missing_i.
  assert (Hother :
    forall eid0, eid0 <> eid ->
      inUsedEventStates evSt eid0 =
      inUsedEventStates (update_event_field_raw evSt eid e) eid0).
  {
    intros eid0 Hneq.
    simpl.
    apply Z.eqb_neq in Hneq.
    rewrite Hneq.
    reflexivity.
  }
  pose proof
    (proj1 (store_map_missing_i_equiv
      (fun eid0 e0 =>
         used_complete_event_raw sg tskSt (event_addr sg eid0) eid0 e0)
      (inUsedEventStates evSt)
      (inUsedEventStates (update_event_field_raw evSt eid e))
      eid Hother)) as Hmissing.
  sep_apply_l_atomic Hmissing.
  entailer!.
Qed.
Lemma mutex_replace_low_byte__handover_commit :
  forall pcp old new,
    0 <= pcp <= 255 ->
    0 <= old <= 255 ->
    0 <= new <= 255 ->
    Z.lor (Z.land (pcp * 256 + old) 65280) new =
      pcp * 256 + new.
Proof.
  intros pcp old new Hpcp Hold Hnew.
  set (x := pcp * 256 + old).
  assert (Hx : 0 <= x <= 65535) by (unfold x; nia).
  assert (Hlow : Z.land x 255 = old).
  {
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    replace (2 ^ 8) with 256 by reflexivity.
    unfold x.
    rewrite Z.add_comm, Z.mod_add by lia.
    apply Z.mod_small.
    lia.
  }
  assert (Hhigh : Z.land x 65280 = x - old).
  {
    replace 65280 with (Z.land (Z.lnot 255) 65535) by reflexivity.
    rewrite Z.land_assoc.
    rewrite <- Z.sub_land_same_l.
    rewrite Hlow.
    replace 65535 with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia.
    apply Z.mod_small.
    lia.
  }
  rewrite Hhigh.
  assert (Hdisjoint : Z.land (x - old) new = 0).
  {
    assert (Hnew_mask : Z.land new 255 = new).
    {
      replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia.
      apply Z.mod_small.
      lia.
    }
    unfold x.
    replace (pcp * 256 + old - old) with (pcp * 256) by lia.
    rewrite <- Hnew_mask.
    rewrite (Z.land_comm new 255).
    rewrite Z.land_assoc.
    assert (Hpcp_mask : Z.land (pcp * 256) 255 = 0).
    {
      replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      apply Z.mod_mul.
      lia.
    }
    rewrite Hpcp_mask.
    reflexivity.
  }
  pose proof (Z.add_lor_land (x - old) new) as Hsum.
  rewrite Hdisjoint in Hsum.
  unfold x in *.
  lia.
Qed.
Lemma mutex_post_disinherit_event_state__handover_commit :
  forall sg m cur_tid entry ls_d,
    OSMutexPost_disinherit_sem sg m cur_tid entry ls_d ->
    EventState ls_d = EventState entry.
Proof.
  intros sg m cur_tid entry ls_d Hdisinherit.
  unfold OSMutexPost_disinherit_sem in Hdisinherit.
  destruct Hdisinherit as (cur_t & Hlookup & Hbranch).
  destruct Hbranch as
    [[Hdisabled Hsame] |
     [[Henabled [Hnot_pcp Hsame]] |
      [Henabled [Hat_pcp [orig [Horig Hexec]]]]]].
  - subst ls_d. reflexivity.
  - subst ls_d. reflexivity.
  - unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
    destruct Hexec as
      (t' & Hcur & Hcur_prio & Hget & Hlo & Hhi & Ht' & Hls_d).
    cbv zeta in Hls_d.
    subst ls_d.
    reflexivity.
Qed.
Lemma mutex_post_count_commit_snapshot__handover_commit :
  forall sg pevent entry pcp ecnt_in owner_ptr
         egrp_in evtL_in ls_d eid ls_r e
         retval canonical_waiter table_owner ls_wake e_wake
         cnt_out ptr_out egrp_out evtL_out,
    valid_stable_glob_vars sg ->
    pevent = event_addr sg eid ->
    valid_mutex_pcp sg pcp ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp (decode_OwnerPrio_from_cnt ecnt_in) ls_d ->
    mutex_post_reservation_stage_prop sg eid ls_d ls_r ->
    event_raw_snapshot_of_prop
      sg (TskState ls_r) (EventState ls_r) eid e
      4 ecnt_in owner_ptr egrp_in evtL_in ->
    mutex_post_wake_step_prop
      sg eid ls_r retval canonical_waiter table_owner ls_wake ->
    event_raw_snapshot_of_prop
      sg (TskState ls_wake) (EventState ls_wake) eid e_wake
      4 cnt_out ptr_out egrp_out evtL_out ->
    0 <= retval < 64 ->
    exists e_cnt,
      let ls_cnt :=
        replace_EventS
          (update_event_field_raw (EventState ls_wake) eid e_cnt)
          ls_wake in
      mutex_post_count_commit_step_prop eid retval ls_wake ls_cnt /\
      event_raw_snapshot_of_prop
        sg (TskState ls_cnt) (EventState ls_cnt) eid e_cnt
        4
        (Z.lor (Z.land ecnt_in 65280)
          (unsigned_last_nbits retval 16))
        owner_ptr egrp_out evtL_out.
Proof.
  intros sg pevent entry pcp ecnt_in owner_ptr
    egrp_in evtL_in ls_d eid ls_r e
    retval canonical_waiter table_owner ls_wake e_wake
    cnt_out ptr_out egrp_out evtL_out
    Hstable Hpevent_eid Hpcp Hdisinherit Hreservation Hsnap_r
    Hwake Hsnap_wake Hretval_range.
  unfold event_raw_snapshot_of_prop in Hsnap_r, Hsnap_wake.
  destruct Hsnap_r as
    [Hget_r [Htype_r [Hcnt_r [Hptr_r [Hgrp_r Htbl_r]]]]].
  destruct Hsnap_wake as
    [Hget_wake [Htype_wake [Hcnt_wake
      [Hptr_wake [Hgrp_wake Htbl_wake]]]]].
  pose proof Hdisinherit as Hdisinherit_stage.
  unfold mutex_post_owner_disinherit_stage_prop in Hdisinherit_stage.
  destruct Hdisinherit_stage as [Hchecked [Hboundary Hstage]].
  destruct Hstage as
    (eid0 & e0 & m0 & cur_tid &
      Hpevent & Hentry_get & Hentry_type & Hentry_fields &
      Hentry_owner & Hentry_pcp & Hentry_orig &
      Hcurrent & Hdisinherit_sem).
  assert (Heid0 : eid0 = eid).
  {
    apply event_addr_injective with (sg := sg).
    rewrite <- Hpevent.
    exact Hpevent_eid.
  }
  subst eid0.
  assert (Hdis_event : EventState ls_d = EventState entry).
  {
    eapply mutex_post_disinherit_event_state__handover_commit.
    exact Hdisinherit_sem.
  }
  unfold mutex_post_reservation_stage_prop,
    OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (er & mr & owner & tsk_reserved &
      Hget_reserved & Hreserved_type & Hreserved_fields &
      Hreserved_owner & Htsk_reserved & Hls_r).
  assert (Hevent_r : EventState ls_r = EventState ls_d).
  {
    rewrite Hls_r.
    reflexivity.
  }
  assert (Her_e0 : er = e0).
  {
    rewrite Hdis_event in Hget_reserved.
    rewrite Hentry_get in Hget_reserved.
    inversion Hget_reserved.
    reflexivity.
  }
  subst er.
  rewrite Hentry_fields in Hreserved_fields.
  inversion Hreserved_fields.
  subst mr.
  assert (He_e0 : e = e0).
  {
    rewrite Hevent_r, Hdis_event, Hentry_get in Hget_r.
    inversion Hget_r.
    reflexivity.
  }
  subst e.
  unfold mutex_post_wake_step_prop, OSMutexPost_wake_sem,
    atomic_event_task_rdy, atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (e1 & e2 & canonical_t & table_t & table_t' &
      Hwake_get & Hpend & Hnonempty & Hcanonical &
      Hcanonical_get & Hreturned & Htable_slot &
      Htable_get & Htable_prio & Htable_t' & He2 & Hls_wake).
  assert (He1_e0 : e1 = e0).
  {
    rewrite Hevent_r, Hdis_event, Hentry_get in Hwake_get.
    inversion Hwake_get.
    reflexivity.
  }
  subst e1.
  cbv zeta in Hls_wake.
  assert (He_wake_e2 : e_wake = e2).
  {
    rewrite Hls_wake in Hget_wake.
    cbn in Hget_wake.
    rewrite Z.eqb_refl in Hget_wake.
    inversion Hget_wake.
    reflexivity.
  }
  assert (Hwake_type :
    eventType e_wake = OS_EVENT_TYPE_MUTEX).
  {
    rewrite He_wake_e2, He2.
    exact Hentry_type.
  }
  assert (Hwake_fields : mutexFields e_wake = Some m0).
  {
    rewrite He_wake_e2, He2.
    exact Hentry_fields.
  }
  set (m_cnt :=
    {| mfPCP := mfPCP m0;
       mfOwner := mfOwner m0;
       mfOwnerOrigPrio := Some retval |}).
  set (e_cnt :=
    {| eventGeneration := e_wake.(eventGeneration);
       eventName := e_wake.(eventName);
     eventPadding1 := e_wake.(eventPadding1);
     eventPadding2 := e_wake.(eventPadding2);
     eventPadding3 := e_wake.(eventPadding3);
     eventPadding19 := e_wake.(eventPadding19);
       eventType := eventType e_wake;
       mutexFields := Some m_cnt;
       semFields := semFields e_wake;
       mboxFields := mboxFields e_wake;
       queueFields := queueFields e_wake;
       waitList := waitList e_wake |}).
  exists e_cnt.
  cbn zeta.
  split.
  - unfold mutex_post_count_commit_step_prop,
      OSMutexPost_count_commit_sem.
    exists e_wake, e_cnt, m0, m_cnt.
    repeat split; try reflexivity; assumption.
  - unfold event_raw_snapshot_of_prop.
    repeat split.
    + cbn.
      rewrite Z.eqb_refl.
      reflexivity.
    + unfold e_cnt.
      cbn.
      rewrite Hwake_type.
      reflexivity.
    + assert (Hpcp_byte : 0 <= pcp <= 255).
      {
        unfold valid_mutex_pcp in Hpcp.
        unfold valid_stable_glob_vars in Hstable.
        destruct Hpcp as [Hdisabled | Henabled].
        - lia.
        - lia.
      }
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
      assert (Hretval_byte : 0 <= retval <= 255) by lia.
      assert (Hcnt_input :
        ecnt_in =
          pcp * 256 + decode_OwnerPrio_from_cnt ecnt_in).
      {
        unfold encode_event_cnt_value in Hcnt_r.
        rewrite Hentry_type, Hentry_fields, Hentry_owner,
          Hentry_orig, Hentry_pcp in Hcnt_r.
        exact Hcnt_r.
      }
      rewrite unsigned_last_nbits_eq by (cbn; lia).
      unfold e_cnt, m_cnt, encode_event_cnt_value.
      cbn.
      rewrite Hwake_type, Hentry_owner, Hentry_pcp.
      rewrite Hcnt_input.
      apply mutex_replace_low_byte__handover_commit;
        assumption.
    + unfold e_cnt, m_cnt.
      cbn.
      unfold verification_slice_encode_event_ptr_value in Hptr_r.
      rewrite Hentry_type, Hentry_fields, Hentry_owner in Hptr_r.
      unfold verification_slice_encode_event_ptr_value.
      cbn.
      rewrite Hwake_type, Hentry_owner.
      exact Hptr_r.
    + unfold e_cnt.
      cbn.
      exact Hgrp_wake.
    + unfold e_cnt.
      cbn.
      exact Htbl_wake.
Qed.
Lemma verification_slice_prioTbl_to_addrs_rec_seq__handover_commit :
  forall sg f n acc,
    verification_slice_prioTbl_to_addrs_rec sg f n acc =
      List.app
        (map (fun k => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)))
          (seq 0 n))
        acc.
Proof.
  intros sg f n. induction n as [|n IH]; intro acc.
  - reflexivity.
  - simpl verification_slice_prioTbl_to_addrs_rec.
    rewrite IH, seq_S, map_app. simpl.
    rewrite <- app_assoc. reflexivity.
Qed.
Lemma verification_slice_prioTbl_to_addrs_rel__handover_commit :
  forall sg st,
    prio_tbl_list_rel sg st
      (verification_slice_prioTbl_to_addrs sg st.(TaskStateDef.prioTbl)).
Proof.
  intros sg st.
  unfold prio_tbl_list_rel. split.
  - unfold verification_slice_prioTbl_to_addrs, OS_PRIO_TBL_SIZE, Zlength.
    vm_compute. reflexivity.
  - intros p Hp.
    unfold verification_slice_prioTbl_to_addrs, OS_PRIO_TBL_SIZE in *.
    rewrite verification_slice_prioTbl_to_addrs_rec_seq__handover_commit.
    rewrite app_nil_r.
    unfold Znth.
    assert (Hnat : (Z.to_nat p < 64)%nat) by lia.
    assert (Hdefault :
      nth (Z.to_nat p)
        (map
        (fun k : nat =>
          verification_slice_prio_tbl_entry_to_addr sg
            (TaskStateDef.prioTbl st (Z.of_nat k)))
        (seq 0 64))
        0 =
      nth (Z.to_nat p)
        (map
        (fun k : nat =>
          verification_slice_prio_tbl_entry_to_addr sg
            (TaskStateDef.prioTbl st (Z.of_nat k)))
        (seq 0 64))
        (verification_slice_prio_tbl_entry_to_addr sg
          (TaskStateDef.prioTbl st (Z.of_nat 0)))).
    { apply nth_indep.
      rewrite length_map, length_seq. exact Hnat. }
    rewrite Hdefault.
    change
      (nth (Z.to_nat p)
        (map
          (fun k : nat =>
            verification_slice_prio_tbl_entry_to_addr sg
              (TaskStateDef.prioTbl st (Z.of_nat k)))
          (seq 0 64))
        ((fun k : nat =>
          verification_slice_prio_tbl_entry_to_addr sg
            (TaskStateDef.prioTbl st (Z.of_nat k))) 0%nat) =
       verification_slice_prio_tbl_entry_to_addr sg (TaskStateDef.prioTbl st p)).
    rewrite map_nth.
    rewrite seq_nth by exact Hnat.
    simpl Nat.add.
    rewrite Z2Nat.id by lia.
    reflexivity.
Qed.
Lemma mutex_post_disinherit_crit_rel__handover_commit :
  forall sg m cur_tid entry ls_d,
    OSMutexPost_disinherit_sem sg m cur_tid entry ls_d ->
    crit_rel_task_event_sched entry ls_d.
Proof.
  intros sg m cur_tid entry ls_d Hdisinherit.
  unfold OSMutexPost_disinherit_sem in Hdisinherit.
  destruct Hdisinherit as (cur_t & Hlookup & Hbranch).
  destruct Hbranch as
    [[Hdisabled Hsame] |
     [[Henabled [Hnot_pcp Hsame]] |
      [Henabled [Hat_pcp [orig [Horig Hexec]]]]]].
  - subst ls_d. unfold crit_rel_task_event_sched.
    destruct entry; reflexivity.
  - subst ls_d. unfold crit_rel_task_event_sched.
    destruct entry; reflexivity.
  - unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
    destruct Hexec as
      (t' & Hcur & Hcur_prio & Hget & Hlo & Hhi & Ht' & Hls_d).
    cbv zeta in Hls_d.
    subst ls_d.
    unfold crit_rel_task_event_sched.
    destruct entry; reflexivity.
Qed.
Lemma mutex_post_handover_crit_rel__handover_commit :
  forall sg pevent entry pcp owner_orig ls_d eid ls_r
         returned_prio canonical_waiter table_owner
         ls_wake ls_cnt ls_h,
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig ls_d ->
    mutex_post_reservation_stage_prop sg eid ls_d ls_r ->
    mutex_post_wake_step_prop
      sg eid ls_r returned_prio canonical_waiter table_owner ls_wake ->
    mutex_post_count_commit_step_prop eid returned_prio ls_wake ls_cnt ->
    mutex_post_owner_commit_step_prop
      eid returned_prio table_owner ls_cnt ls_h ->
    crit_rel_task_event_sched entry ls_h.
Proof.
  intros sg pevent entry pcp owner_orig ls_d eid ls_r
    returned_prio canonical_waiter table_owner ls_wake ls_cnt ls_h
    Hstage Hreservation Hwake Hcount Howner.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage.
  destruct Hstage as
    (_ & _ & eid0 & e0 & m0 & cur_tid &
     _ & _ & _ & _ & _ & _ & _ & _ & Hdisinherit).
  pose proof
    (mutex_post_disinherit_crit_rel__handover_commit
      sg m0 cur_tid entry ls_d Hdisinherit) as Hdisinherit_frame.
  unfold mutex_post_reservation_stage_prop,
    OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (er & mr & owner & tsk_reserved &
     Hgetr & Htyper & Hfieldsr & Hownerr & Htsk_reserved & Hls_r).
  unfold mutex_post_wake_step_prop, OSMutexPost_wake_sem,
    atomic_event_task_rdy, atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (ew1 & ew2 & canonical_t & table_t & table_t' &
     Hgetw & Hpend & Hnonempty & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & Hew2 & Hls_wake).
  unfold mutex_post_count_commit_step_prop,
    OSMutexPost_count_commit_sem in Hcount.
  destruct Hcount as
    (ec1 & ec2 & mc1 & mc2 & Hgetc & Htypec & Hfieldsc &
     Hmc2 & Hec2 & Hls_cnt).
  unfold mutex_post_owner_commit_step_prop,
    OSMutexPost_owner_commit_sem in Howner.
  destruct Howner as
    [Htable_cnt
      (eh1 & eh2 & mh1 & mh2 & Hgeth & Htypeh & Hfieldsh &
       Hmh2 & Heh2 & Hls_h & Htable_h)].
  unfold crit_rel_task_event_sched in Hdisinherit_frame |- *.
  rewrite Hls_h, Hls_cnt, Hls_wake, Hls_r.
  rewrite Hdisinherit_frame.
  destruct entry; reflexivity.
Qed.
Lemma mutex_post_disinherit_frames_waiter__handover_commit :
  forall sg pevent entry pcp owner_orig ls_d eid e tid,
    UCOS2_verification_slice_state_inv sg entry ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig ls_d ->
    inUsedEventStates (EventState entry) eid = Some e ->
    In tid (waitList e) ->
    EventState ls_d = EventState entry /\
    inUsedTaskStates (TskState ls_d) tid =
      inUsedTaskStates (TskState entry) tid.
Proof.
  intros sg pevent entry pcp owner_orig ls_d eid e tid
    Hvalid Hstage Hevent Hin.
  pose proof Hstage as Hstage0.
  destruct Hvalid as [_ [Hsched [Hevent_valid _]]].
  pose proof
    (mutex_post_owner_disinherit_stage_task_call_boundary
      sg pevent entry pcp owner_orig ls_d Hstage0) as Hboundary.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage.
  destruct Hstage as
    (_ & _ & eid0 & e0 & m & cur_tid &
     _ & _ & _ & _ & _ & _ & _ & Hcurrent & Hdisinherit).
  unfold OSMutexPost_disinherit_sem in Hdisinherit.
  destruct Hdisinherit as [cur_t [Hcur Hbranches]].
  destruct Hbranches as
    [[Hdisabled Hsame] |
     [[Henabled [Hnot_pcp Hsame]] |
      [Henabled [Hat_pcp [orig [Horig Hexec]]]]]].
  - subst ls_d. split; reflexivity.
  - subst ls_d. split; reflexivity.
  - unfold sched_task_call_boundary, sched_current_ready_at in Hboundary.
    destruct Hboundary as
      [_ [boundary_tid [boundary_t
        [Hboundary_get [Hboundary_current
          [Hboundary_prio [Hboundary_ready Hboundary_effective]]]]]]].
    rewrite Hcurrent in Hboundary_current.
    inversion Hboundary_current; subst boundary_tid.
    rewrite Hcur in Hboundary_get.
    inversion Hboundary_get; subst boundary_t.
    assert (Hnot_wait : ~ In cur_tid (waitList e)).
    {
      eapply debug_ready_tid_not_event_wait__relocation_semantics.
      - exact Hsched.
      - exact Hevent_valid.
      - exact Hcur.
      - exact Hboundary_ready.
      - exact Hevent.
    }
    assert (Hneq : tid <> cur_tid).
    {
      intro Heq.
      subst tid.
      contradiction.
    }
    unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
    destruct Hexec as
      (t' & Hcur' & Hcur_prio & Hget & Hlo & Hhi & Ht' & Hls_d).
    cbv zeta in Hls_d.
    rewrite Hls_d.
    split; [reflexivity |].
    cbn.
    rewrite (proj2 (Z.eqb_neq tid cur_tid) Hneq).
    reflexivity.
Qed.
Lemma mutex_post_reservation_frames_event_tasks__handover_commit :
  forall sg eid ls_d ls_r,
    mutex_post_reservation_stage_prop sg eid ls_d ls_r ->
    EventState ls_r = EventState ls_d /\
    inUsedTaskStates (TskState ls_r) =
      inUsedTaskStates (TskState ls_d).
Proof.
  intros sg eid ls_d ls_r Hreservation.
  unfold mutex_post_reservation_stage_prop,
    OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (e & m & owner & tsk_reserved &
     Hget & Htype & Hfields & Howner & Htsk_reserved & Hls_r).
  subst tsk_reserved ls_r.
  split; reflexivity.
Qed.
Lemma encode_event_wait_grp_byte__handover_commit :
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
    cbn.
    rewrite Hget.
    apply debug_lor_byte__relocation_semantics.
    + apply debug_shiftl_bit_byte__relocation_semantics.
      unfold valid_task_prio in Hprio.
      unfold valid_stable_glob_vars in Hstable.
      split.
      * apply Z_div_nonneg_nonneg; lia.
      * apply Zdiv_lt_upper_bound; lia.
    + apply IH; [exact Hstable |].
      intros tid0 Hin.
      apply Hrange.
      right.
      exact Hin.
Qed.
Lemma mutex_post_zero_group_empty_waitlist__handover_commit :
  forall sg pevent entry pcp owner_orig ls_d eid ls_r e
         etype cnt ptr grp tbl,
    valid_stable_glob_vars sg ->
    UCOS2_verification_slice_state_inv sg entry ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig ls_d ->
    mutex_post_reservation_stage_prop sg eid ls_d ls_r ->
    event_raw_snapshot_of_prop
      sg (TskState ls_r) (EventState ls_r) eid e
      etype cnt ptr grp tbl ->
    unsigned_last_nbits grp 32 = 0 ->
    waitList e = nil.
Proof.
  intros sg pevent entry pcp owner_orig ls_d eid ls_r e
    etype cnt ptr grp tbl
    Hstable Hvalid Hstage Hreservation Hsnapshot Hgrp_zero.
  pose proof Hvalid as Hvalid0.
  pose proof Hstage as Hstage0.
  unfold event_raw_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as
    [Hget_r [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  unfold mutex_post_owner_disinherit_stage_prop in Hstage0.
  destruct Hstage0 as
    (_ & _ & eid0 & e0 & m & cur_tid &
     _ & _ & _ & _ & _ & _ & _ & _ & Hdisinherit).
  pose proof
    (mutex_post_disinherit_event_state__handover_commit
      sg m cur_tid entry ls_d Hdisinherit) as Hevent_d.
  pose proof
    (mutex_post_reservation_frames_event_tasks__handover_commit
      sg eid ls_d ls_r Hreservation) as [Hevent_r Htasks_r].
  assert (Hget_entry :
    inUsedEventStates (EventState entry) eid = Some e).
  {
    rewrite Hevent_r in Hget_r.
    rewrite Hevent_d in Hget_r.
    exact Hget_r.
  }
  destruct Hvalid as [_ [_ [Hevent_valid _]]].
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hevent_valid.
  destruct Hevent_valid as
    [_ [_ [_ [_ [_ [_ [_ Hentry]]]]]]].
  specialize (Hentry eid e Hget_entry).
  unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency in Hentry.
  destruct Hentry as [Hcanonical _].
  unfold Ucos2Verify.lib.event_wait.event_waitList_canonical in Hcanonical.
  destruct Hcanonical as [_ [_ Hwait_range_entry]].
  assert (Hwait_range_r :
    forall tid,
      In tid (waitList e) ->
      exists t,
        inUsedTaskStates (TskState ls_r) tid = Some t /\
        valid_task_prio sg (curPrio t)).
  {
    intros tid Hin.
    destruct (Hwait_range_entry tid Hin) as [t [Hget_t Hprio_t]].
    pose proof
      (mutex_post_disinherit_frames_waiter__handover_commit
        sg pevent entry pcp owner_orig ls_d eid e tid
        Hvalid0 Hstage Hget_entry Hin) as [_ Htask_d].
    exists t.
    split; [|exact Hprio_t].
    rewrite Htasks_r.
    rewrite Htask_d.
    exact Hget_t.
  }
  pose proof
    (encode_event_wait_grp_byte__handover_commit
      sg (waitList e) (TskState ls_r)
      Hstable Hwait_range_r) as Henc_range.
  rewrite Hgrp in Hgrp_zero.
  rewrite unsigned_last_nbits_eq in Hgrp_zero by lia.
  destruct (waitList e) as [|tid rest] eqn:Hwait; [reflexivity |].
  destruct (Hwait_range_r tid ltac:(left; reflexivity))
    as [t [Hget_t Hprio_t]].
  cbn in Hgrp_zero.
  rewrite Hget_t in Hgrp_zero.
  apply Z.lor_eq_0_iff in Hgrp_zero.
  destruct Hgrp_zero as [Hbit_zero _].
  rewrite Z.shiftl_1_l in Hbit_zero.
  unfold valid_task_prio in Hprio_t.
  assert (Hdiv_nonneg : 0 <= curPrio t / 8).
  {
    apply Z_div_nonneg_nonneg.
    all: lia.
  }
  pose proof
    (Z.pow_pos_nonneg 2 (curPrio t / 8)
      ltac:(lia) Hdiv_nonneg) as Hbit_pos.
  lia.
Qed.
Lemma mutex_post_empty_cnt_encoding__handover_commit :
  forall pcp orig,
    0 <= pcp <= 255 ->
    0 <= orig <= 255 ->
    Z.lor
      (unsigned_last_nbits (pcp * 256 + orig) 16) 255 =
      pcp * 256 + 255.
Proof.
  intros pcp orig Hpcp Horig.
  rewrite unsigned_last_nbits_eq by (cbn; nia).
  assert (Hlow : Z.land (pcp * 256 + orig) 255 = orig).
  {
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    replace (2 ^ 8) with 256 by reflexivity.
    rewrite Z.add_comm, Z.mod_add by lia.
    apply Z.mod_small.
    lia.
  }
  pose proof (Z.add_lor_land (pcp * 256 + orig) 255) as Hsum.
  rewrite Hlow in Hsum.
  lia.
Qed.
Lemma verification_slice_event_raw_rep_merge_eid_two_updates__handover_commit :
  forall sg tskSt evSt eid e1 e2,
    used_complete_event_raw
      sg tskSt (event_addr sg eid) eid e2 **
    verification_slice_event_raw_rep_no_eid sg tskSt evSt eid |--
      verification_slice_event_raw_rep sg tskSt
        (update_event_field_raw
          (update_event_field_raw evSt eid e1) eid e2).
Proof.
  intros sg tskSt evSt eid e1 e2.
  sep_apply_l_atomic
    (verification_slice_event_raw_rep_no_eid_update__handover_commit
      sg tskSt evSt eid e1).
  sep_apply_l_atomic
    (verification_slice_event_raw_rep_no_eid_update__handover_commit
      sg tskSt (update_event_field_raw evSt eid e1) eid e2).
  assert (Hget :
    inUsedEventStates
      (update_event_field_raw
        (update_event_field_raw evSt eid e1) eid e2) eid =
    Some e2).
  {
    cbn.
    rewrite Z.eqb_refl.
    reflexivity.
  }
  sep_apply_l_atomic
    (verification_slice_event_raw_rep_merge_eid
      sg tskSt
      (update_event_field_raw
        (update_event_field_raw evSt eid e1) eid e2)
      eid e2 Hget).
  entailer!.
Qed.
Lemma mutex_post_empty_release_snapshot__handover_commit :
  forall sg pevent entry pcp owner_orig ls_d eid ls_reserved
         e cnt ptr grp tbl,
    valid_stable_glob_vars sg ->
    valid_mutex_pcp sg pcp ->
    0 <= owner_orig <= 255 ->
    pevent = event_addr sg eid ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig ls_d ->
    mutex_post_reservation_stage_prop sg eid ls_d ls_reserved ->
    event_raw_snapshot_of_prop
      sg (TskState ls_reserved) (EventState ls_reserved) eid e
      4 cnt ptr grp tbl ->
    waitList e = nil ->
    exists (e_available e_r : OSEventAbstractState)
           (ls_available ls_r : UCOS2_Verify_State),
      mutex_post_empty_count_commit_step_prop
        eid ls_reserved ls_available /\
      mutex_post_empty_owner_commit_step_prop
        eid ls_available ls_r /\
      mutex_post_release_step_prop sg eid ls_d ls_r /\
      crit_rel_task_event_sched entry ls_r /\
      ls_available =
        replace_EventS
          (update_event_field_raw
            (EventState ls_reserved) eid e_available)
          ls_reserved /\
      ls_r =
        replace_EventS
          (update_event_field_raw
            (EventState ls_available) eid e_r)
          ls_available /\
      event_raw_snapshot_of_prop
        sg (TskState ls_r) (EventState ls_r) eid e_r
        4
        (Z.lor (unsigned_last_nbits cnt 16) 255)
        0 grp tbl.
Proof.
  intros sg pevent entry pcp owner_orig ls_d eid ls_reserved
    e cnt ptr grp tbl
    Hstable Hpcp Horig_byte Hpevent_eid Hstage Hreservation
    Hsnapshot Hwait.
  pose proof Hreservation as Hreservation0.
  pose proof Hsnapshot as Hsnapshot0.
  unfold event_raw_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as
    [Hget_snapshot [Htype_snapshot [Hcnt_snapshot
      [Hptr_snapshot [Hgrp_snapshot Htbl_snapshot]]]]].
  unfold mutex_post_owner_disinherit_stage_prop in Hstage.
  destruct Hstage as
    (_ & _ & eid0 & e0 & m0 & cur_tid &
     Hpevent0 & Hget_entry & Htype0 & Hfields0 & Howner0 &
     Hpcp0 & Horig0 & Hcurrent & Hdisinherit).
  assert (Heid0 : eid0 = eid).
  {
    apply event_addr_injective with (sg := sg).
    transitivity pevent.
    - symmetry; exact Hpevent0.
    - exact Hpevent_eid.
  }
  subst eid0.
  pose proof
    (mutex_post_disinherit_event_state__handover_commit
      sg m0 cur_tid entry ls_d Hdisinherit) as Hevent_d.
  pose proof
    (mutex_post_disinherit_crit_rel__handover_commit
      sg m0 cur_tid entry ls_d Hdisinherit) as Hdisinherit_frame.
  unfold mutex_post_reservation_stage_prop,
    OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (er & mr & owner & tsk_reserved &
     Hget_reserved & Htype_reserved & Hfields_reserved &
     Howner_reserved & Htsk_reserved & Hls_reserved).
  assert (Her : er = e0).
  {
    rewrite Hevent_d, Hget_entry in Hget_reserved.
    inversion Hget_reserved.
    reflexivity.
  }
  subst er.
  rewrite Hfields0 in Hfields_reserved.
  inversion Hfields_reserved.
  subst mr.
  assert (He : e = e0).
  {
    rewrite Hls_reserved in Hget_snapshot.
    cbn in Hget_snapshot.
    rewrite Hevent_d, Hget_entry in Hget_snapshot.
    inversion Hget_snapshot.
    reflexivity.
  }
  subst e.
  set (m_available :=
    {| mfPCP := mfPCP m0;
       mfOwner := mfOwner m0;
       mfOwnerOrigPrio := Some 255 |}).
  set (e_available :=
    {| eventGeneration := e0.(eventGeneration);
       eventName := e0.(eventName);
     eventPadding1 := e0.(eventPadding1);
     eventPadding2 := e0.(eventPadding2);
     eventPadding3 := e0.(eventPadding3);
     eventPadding19 := e0.(eventPadding19);
       eventType := eventType e0;
       mutexFields := Some m_available;
       semFields := semFields e0;
       mboxFields := mboxFields e0;
       queueFields := queueFields e0;
       waitList := waitList e0 |}).
  set (ls_available :=
    replace_EventS
      (update_event_field_raw
        (EventState ls_reserved) eid e_available)
      ls_reserved).
  set (m_r :=
    {| mfPCP := mfPCP m_available;
       mfOwner := None;
       mfOwnerOrigPrio := None |}).
  set (e_r :=
    {| eventGeneration := e_available.(eventGeneration);
       eventName := e_available.(eventName);
     eventPadding1 := e_available.(eventPadding1);
     eventPadding2 := e_available.(eventPadding2);
     eventPadding3 := e_available.(eventPadding3);
     eventPadding19 := e_available.(eventPadding19);
       eventType := eventType e_available;
       mutexFields := Some m_r;
       semFields := semFields e_available;
       mboxFields := mboxFields e_available;
       queueFields := queueFields e_available;
       waitList := waitList e_available |}).
  set (ls_r :=
    replace_EventS
      (update_event_field_raw (EventState ls_available) eid e_r)
      ls_available).
  exists e_available, e_r, ls_available, ls_r.
  assert (Hcount :
    mutex_post_empty_count_commit_step_prop
      eid ls_reserved ls_available).
  {
    unfold mutex_post_empty_count_commit_step_prop,
      OSMutexPost_empty_count_commit_sem.
    exists e0, e_available, m0, m_available, cur_tid.
    repeat split; try assumption;
      unfold m_available, e_available, ls_available;
      reflexivity.
  }
  assert (Howner :
    mutex_post_empty_owner_commit_step_prop
      eid ls_available ls_r).
  {
    assert (Hget_available :
      inUsedEventStates (EventState ls_available) eid =
        Some e_available).
    {
      unfold ls_available.
      cbn.
      rewrite Z.eqb_refl.
      reflexivity.
    }
    unfold mutex_post_empty_owner_commit_step_prop,
      OSMutexPost_empty_owner_commit_sem.
    exists e_available, e_r, m_available, m_r.
    repeat split; try assumption;
      unfold m_r, e_r, m_available, e_available, ls_r;
      reflexivity.
  }
  split.
  {
    exact Hcount.
  }
  split.
  {
    exact Howner.
  }
  split.
  {
    unfold mutex_post_release_step_prop,
      OSMutexPost_empty_release_sem.
    exists ls_reserved, ls_available.
    repeat split; assumption.
  }
  split.
  {
    unfold crit_rel_task_event_sched in Hdisinherit_frame |- *.
    unfold ls_r, ls_available.
    rewrite Hls_reserved, Hdisinherit_frame.
    destruct entry; reflexivity.
  }
  split.
  {
    unfold ls_available.
    reflexivity.
  }
  split.
  {
    unfold ls_r.
    reflexivity.
  }
  unfold event_raw_snapshot_of_prop.
  split.
    {
      unfold ls_r.
      cbn.
      rewrite Z.eqb_refl.
      reflexivity.
    }
    split.
    {
      unfold e_r, e_available.
      cbn.
      rewrite Htype0.
      reflexivity.
    }
    split.
    {
      assert (Hpcp_byte : 0 <= pcp <= 255).
      {
        unfold valid_mutex_pcp in Hpcp.
        unfold valid_stable_glob_vars in Hstable.
        destruct Hpcp as [Hdisabled | Henabled]; lia.
      }
      assert (Hcnt_input :
        cnt = pcp * 256 + owner_orig).
      {
        unfold encode_event_cnt_value in Hcnt_snapshot.
        rewrite Htype0, Hfields0, Howner0, Horig0, Hpcp0
          in Hcnt_snapshot.
        exact Hcnt_snapshot.
      }
      rewrite Hcnt_input.
      unfold e_r, e_available, m_r, m_available,
        encode_event_cnt_value.
      cbn.
      rewrite Htype0, Hpcp0.
      apply mutex_post_empty_cnt_encoding__handover_commit;
        assumption.
    }
    split.
    {
      unfold e_r, e_available, m_r, m_available,
        verification_slice_encode_event_ptr_value.
      cbn.
      rewrite Htype0.
      reflexivity.
    }
    split.
    {
      rewrite Hwait in Hgrp_snapshot.
      cbn in Hgrp_snapshot.
      unfold e_r, e_available.
      cbn.
      rewrite Hwait.
      cbn.
      exact Hgrp_snapshot.
    }
    {
      unfold encode_event_wait_tbl_values_or in Htbl_snapshot.
      rewrite Hwait in Htbl_snapshot.
      cbn in Htbl_snapshot.
      unfold e_r, e_available.
      cbn.
      unfold encode_event_wait_tbl_values_or.
      rewrite Hwait.
      cbn.
      exact Htbl_snapshot.
    }
Qed.
Lemma mutex_post_disinherit_event_state__return_semantics :
  forall sg m cur_tid entry post,
    OSMutexPost_disinherit_sem sg m cur_tid entry post ->
    post.(EventState) = entry.(EventState).
Proof.
  intros sg m cur_tid entry post Hstep.
  unfold OSMutexPost_disinherit_sem in Hstep.
  destruct Hstep as
    [cur_t [Hcur
      [[Hdisabled Heq] |
       [[Henabled [Hnot_pcp Heq]] |
        [Henabled [Hat_pcp [orig [Horig Hexec]]]]]]]].
  - subst post. reflexivity.
  - subst post. reflexivity.
  - unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
    destruct Hexec as
      [new_t [Hcurrent [Hcurrent_prio [Hlookup
       [Hlo [Hhi [Hnew_t Hpost]]]]]]].
    cbv zeta in Hpost.
    subst post.
    reflexivity.
Qed.
Lemma mutex_post_reservation_event_state__return_semantics :
  forall sg eid before after,
    OSMutexPost_reservation_sem sg eid before after ->
    after.(EventState) = before.(EventState).
Proof.
  intros sg eid before after Hstep.
  unfold OSMutexPost_reservation_sem in Hstep.
  destruct Hstep as
    [e [m [owner [tsk_reserved
      [Hlookup [Htype [Hfields [Howner [Htsk Hafter]]]]]]]]].
  subst after.
  reflexivity.
Qed.
Lemma mutex_post_stage_event_id_eq__return_semantics :
  forall sg pevent eid1 eid2,
    pevent = event_addr sg eid1 ->
    pevent = event_addr sg eid2 ->
    eid1 = eid2.
Proof.
  intros sg pevent eid1 eid2 H1 H2.
  apply event_addr_injective with (sg := sg).
  transitivity pevent.
  - symmetry; exact H1.
  - exact H2.
Qed.
Lemma mutex_post_empty_entry_waitlist__return_semantics :
  forall sg eid e m cur_tid entry disinherited released,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    OSMutexPost_disinherit_sem
      sg m cur_tid entry disinherited ->
    OSMutexPost_empty_release_sem
      sg eid disinherited released ->
    e.(waitList) = nil.
Proof.
  intros sg eid e m cur_tid entry disinherited released
    Hentry Hdisinherit Hrelease.
  pose proof
    (mutex_post_disinherit_event_state__return_semantics
       sg m cur_tid entry disinherited Hdisinherit)
    as Hdisinherit_event.
  unfold OSMutexPost_empty_release_sem in Hrelease.
  destruct Hrelease as
    [reserved [available
      [Hreservation [Hcount Howner_commit]]]].
  pose proof
    (mutex_post_reservation_event_state__return_semantics
       sg eid disinherited reserved Hreservation)
    as Hreservation_event.
  unfold OSMutexPost_empty_count_commit_sem in Hcount.
  destruct Hcount as
    [e1 [e2 [m1 [m2 [owner
      [Hreserved [Htype [Hfields [Hwait
       [Howner [Hm2 [He2 Havailable]]]]]]]]]]]].
  rewrite Hreservation_event, Hdisinherit_event, Hentry in Hreserved.
  inversion Hreserved.
  exact Hwait.
Qed.
Lemma mutex_post_handover_entry_waitlist__return_semantics :
  forall sg eid e m cur_tid entry disinherited post
         returned_prio canonical_waiter table_owner,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    OSMutexPost_disinherit_sem
      sg m cur_tid entry disinherited ->
    OSMutexPost_handover_sem
      sg eid disinherited returned_prio
      canonical_waiter table_owner post ->
    e.(waitList) <> nil.
Proof.
  intros sg eid e m cur_tid entry disinherited post
    returned_prio canonical_waiter table_owner
    Hentry Hdisinherit Hhandover.
  pose proof
    (mutex_post_disinherit_event_state__return_semantics
       sg m cur_tid entry disinherited Hdisinherit)
    as Hdisinherit_event.
  unfold OSMutexPost_handover_sem in Hhandover.
  destruct Hhandover as
    [reserved [wake [counted
      [Hreservation [Hwake [Hcount Howner_commit]]]]]].
  pose proof
    (mutex_post_reservation_event_state__return_semantics
       sg eid disinherited reserved Hreservation)
    as Hreservation_event.
  unfold OSMutexPost_wake_sem, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    [e1 [e2 [canonical_t [table_t [table_t'
      [Hreserved [Hpend [Hwait [Hcanonical
       [Hcanonical_get [Hreturned [Htable_slot
        [Htable_get [Htable_prio [Htable_t' Hpost]]]]]]]]]]]]]]].
  rewrite Hreservation_event, Hdisinherit_event, Hentry in Hreserved.
  inversion Hreserved.
  exact Hwait.
Qed.
Lemma mutex_post_empty_sem_from_stages__return_semantics :
  forall sg pevent eid entry disinherited released pcp owner_orig,
    pevent = event_addr sg eid ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig disinherited ->
    mutex_post_release_step_prop
      sg eid disinherited released ->
    OSMutexPost_sem sg pevent entry OS_ERR_NONE released.
Proof.
  intros sg pevent eid entry disinherited released pcp owner_orig
    Hpevent Hstage Hrelease.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage.
  destruct Hstage as
    [Hchecked [Hscenario
      [stage_eid [e [m [cur_tid
        [Hstage_pevent [Hentry [Htype [Hfields
         [Howner [Hpcp [Horig [Hcurrent Hdisinherit]]]]]]]]]]]]]].
  assert (Heid : stage_eid = eid).
  {
    eapply mutex_post_stage_event_id_eq__return_semantics;
      eassumption.
  }
  subst stage_eid.
  unfold mutex_post_checked_entry_prop in Hchecked.
  destruct Hchecked as [Hnonisr Hnonnull].
  unfold mutex_post_release_step_prop in Hrelease.
  assert (Hwait : e.(waitList) = nil).
  {
    eapply mutex_post_empty_entry_waitlist__return_semantics;
      eassumption.
  }
  unfold OSMutexPost_sem.
  right; right; right; right; right; right; left.
  repeat split; try assumption.
  exists eid, e, m, cur_tid, disinherited, released.
  repeat split; try assumption.
Qed.
Lemma mutex_post_handover_sem_from_stages__return_semantics :
  forall sg pevent eid entry disinherited handover scheduled
         pcp owner_orig returned_prio canonical_waiter table_owner err,
    pevent = event_addr sg eid ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig disinherited ->
    mutex_post_handover_step_prop
      sg eid disinherited returned_prio
      canonical_waiter table_owner handover ->
    mutex_post_sched_step_prop handover scheduled ->
    ((pcp <> sg.(osPrioMutexCeilDis) /\
      returned_prio <= pcp /\
      err = OS_ERR_PCP_LOWER) \/
     ((pcp = sg.(osPrioMutexCeilDis) \/
       returned_prio > pcp) /\
      err = OS_ERR_NONE)) ->
    OSMutexPost_sem sg pevent entry err scheduled.
Proof.
  intros sg pevent eid entry disinherited handover scheduled
    pcp owner_orig returned_prio canonical_waiter table_owner err
    Hpevent Hstage Hhandover Hsched Hresult.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage.
  destruct Hstage as
    [Hchecked [Hscenario
      [stage_eid [e [m [cur_tid
        [Hstage_pevent [Hentry [Htype [Hfields
         [Howner [Hm_pcp [Horig [Hcurrent Hdisinherit]]]]]]]]]]]]]].
  assert (Heid : stage_eid = eid).
  {
    eapply mutex_post_stage_event_id_eq__return_semantics;
      eassumption.
  }
  subst stage_eid.
  unfold mutex_post_checked_entry_prop in Hchecked.
  destruct Hchecked as [Hnonisr Hnonnull].
  unfold mutex_post_handover_step_prop in Hhandover.
  assert (Hwait : e.(waitList) <> nil).
  {
    eapply mutex_post_handover_entry_waitlist__return_semantics;
      eassumption.
  }
  unfold mutex_post_sched_step_prop in Hsched.
  destruct Hsched as [sched_result Hsched].
  unfold OSMutexPost_sem.
  right; right; right; right; right; right; right.
  split; [exact Hnonisr |].
  split; [exact Hnonnull |].
  exists eid, e, m, cur_tid, disinherited, handover, scheduled,
    sched_result, returned_prio, canonical_waiter, table_owner.
  repeat split; try assumption.
  rewrite Hm_pcp.
  exact Hresult.
Qed.
Lemma mutex_post_disinherit_validity__return_semantics :
  forall sg pevent entry pcp owner_orig disinherited,
    valid_stable_glob_vars sg ->
    UCOS2_verification_slice_state_inv sg entry ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig disinherited ->
    OSMutexPost_relocations_legal sg pevent entry ->
    UCOS2_verification_slice_state_inv sg disinherited.
Proof.
  intros sg pevent entry pcp owner_orig disinherited
    Hstable Hvalid Hstage Hrelocations.
  pose proof Hstage as Hstage0.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage.
  destruct Hstage as
    [Hchecked [Hcall
      [eid [e [m [cur_tid
        [Hpevent [Hevent [Htype [Hfields
          [Howner [Hpcp [Horig [Hcurrent Hdisinherit]]]]]]]]]]]]]].
  pose proof Hdisinherit as Hdisinherit0.
  unfold OSMutexPost_disinherit_sem in Hdisinherit.
  destruct Hdisinherit as
    [cur_t [Hcur_get
      [[Hdisabled Hsame] |
       [[Henabled [Hnot_at_pcp Hsame]] |
        [Henabled [Hat_pcp
          [orig [Howner_orig Hexec]]]]]]]].
  - subst disinherited. exact Hvalid.
  - subst disinherited. exact Hvalid.
  - destruct Hvalid as
      [Htask [Hsched [Hevent_valid Hcross]]].
    assert (Hboundary :
      sched_task_call_boundary
        entry.(TskState) entry.(SchedState)).
    {
      eapply mutex_post_owner_disinherit_stage_task_call_boundary.
      exact Hstage0.
    }
    unfold sched_task_call_boundary in Hboundary.
    destruct Hboundary as
      [Hrunning [boundary_tid [boundary_t Hready]]].
    unfold sched_current_ready_at in Hready.
    destruct Hready as
      [Hboundary_get [Hboundary_current
        [Hboundary_prio [Hready_member Heffective]]]].
    rewrite Hcurrent in Hboundary_current.
    inversion Hboundary_current; subst boundary_tid.
    rewrite Hcur_get in Hboundary_get.
    inversion Hboundary_get; subst boundary_t.
    assert (Hlegal :
      task_priority_relocation_legal sg entry cur_tid orig).
    {
      unfold OSMutexPost_relocations_legal in Hrelocations.
      specialize
        (Hrelocations eid e m cur_tid disinherited
          Hpevent Hevent Htype Hfields Howner Hcurrent
          Hdisinherit0).
      unfold OSMutexPost_disinherit_relocation_legal
        in Hrelocations.
      eapply Hrelocations;
        eassumption.
    }
    assert (Hready_exec :
      atomic_task_set_curPrio_ready_literal_exec
        sg cur_tid cur_t orig entry tt disinherited).
    {
      unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
      destruct Hexec as
        [new_t [Hexec_current [Hexec_prio [Hexec_get
          [Hlo [Hhi [Hnew_t Hpost]]]]]]].
      unfold atomic_task_set_curPrio_ready_literal_exec.
      exists new_t.
      repeat split; try assumption.
    }
    assert (Hdomain :
      ready_task_relocation_domain
        sg entry.(TskState) entry.(SchedState)
        cur_tid cur_t orig).
    {
      unfold ready_task_relocation_domain.
      unfold atomic_task_set_curPrio_ready_literal_exec in Hready_exec.
      destruct Hready_exec as
        [new_t [Hexec_member [Hexec_current [Hexec_prio
          [Hexec_get [Hlo [Hhi [Hnew_t Hpost]]]]]]]].
      repeat split; try assumption.
    }
    assert (Howner_domain :
      ready_owner_relocation_domain
        sg entry.(TskState) entry.(SchedState)
        cur_tid cur_t orig).
    {
      eapply ready_task_relocation_domain_refines_ready_owner_domain.
      exact Hdomain.
    }
    assert (Howner_exec :
      atomic_task_set_curPrio_ready_owner_exec
        sg cur_tid cur_t orig entry tt disinherited).
    {
      eapply current_ready_literal_exec_refines_ready_owner_exec.
      exact Hready_exec.
    }
    pose proof
      (debug_ready_post_properties__relocation_semantics
        sg entry disinherited cur_tid cur_t orig
        Hstable Htask Hsched Hevent_valid Hcross
        Howner_domain Hlegal Howner_exec)
      as [Htask_post [Hsched_post Hevent_post]].
    assert (Hsafe :
      mutex_ready_relocation_safe
        sg entry.(EventState) eid cur_tid
        cur_t.(curPrio) orig).
    {
      unfold mutex_ready_relocation_safe.
      destruct (Z.eq_dec cur_t.(curPrio) orig)
        as [Heq | Hneq].
      - left. exact Heq.
      - right. split; [exact Hneq |].
        split.
        + unfold mutex_target_restore_reason.
          exists e, m.
          repeat split; try assumption.
          symmetry. exact Hat_pcp.
        + unfold task_priority_relocation_legal in Hlegal.
          destruct Hlegal as
            [legal_t [Hlegal_get
              [Hlegal_slot [Hrestore_safe Hold_alias]]]].
          exact Hrestore_safe.
    }
    assert (Hcross_post :
      Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
        sg disinherited).
    {
      eapply debug_ready_cross_preserved__relocation_semantics.
      - exact Hstable.
      - exact Hsched.
      - exact Hevent_valid.
      - exact Htask_post.
      - exact Hsched_post.
      - exact Hcross.
      - exact Howner_domain.
      - exact Hlegal.
      - exact Hsafe.
      - exact Howner_exec.
    }
    exact (conj Htask_post
      (conj Hsched_post (conj Hevent_post Hcross_post))).
Qed.
Lemma update_event_field_raw_same__return_semantics :
  forall evSt eid e1 e2,
    update_event_field_raw
      (update_event_field_raw evSt eid e1) eid e2 =
    update_event_field_raw evSt eid e2.
Proof.
  intros [used unused queue_bytes] eid e1 e2.
  unfold update_event_field_raw.
  cbn.
  f_equal.
  apply functional_extensionality.
  intro eid'.
  destruct (Z.eqb eid' eid); reflexivity.
Qed.
Lemma update_event_field_raw_existing__return_semantics :
  forall evSt eid e,
    evSt.(inUsedEventStates) eid = Some e ->
    update_event_field_raw evSt eid e = evSt.
Proof.
  intros [used unused queue_bytes] eid e Hlookup.
  unfold update_event_field_raw in *.
  cbn in *.
  f_equal.
  apply functional_extensionality.
  intro eid'.
  destruct (Z.eqb eid' eid) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst eid'.
    symmetry. exact Hlookup.
  - reflexivity.
Qed.
Lemma mutex_post_empty_release_refines_atomic__return_semantics :
  forall sg eid before after,
    OSMutexPost_empty_release_sem sg eid before after ->
    atomic_mutex_release sg eid before tt after.
Proof.
  intros sg eid before after Hrelease.
  unfold OSMutexPost_empty_release_sem in Hrelease.
  destruct Hrelease as
    [reserved [available
      [Hreservation [Hcount Howner_commit]]]].
  unfold OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    [e [m [owner [tsk_reserved
      [Hevent [Htype [Hfields [Howner [Htsk Hreserved]]]]]]]]].
  unfold OSMutexPost_empty_count_commit_sem in Hcount.
  destruct Hcount as
    [e_count [e_available [m_count [m_available [owner_count
      [Hcount_event [Hcount_type [Hcount_fields [Hwait
       [Hcount_owner [Hm_available [He_available Havailable]]]]]]]]]]]].
  unfold OSMutexPost_empty_owner_commit_sem in Howner_commit.
  destruct Howner_commit as
    [e_owner [e_final [m_owner [m_final
      [Howner_event [Howner_type [Howner_fields [Howner_wait
       [Howner_orig [Hm_final [He_final Hafter]]]]]]]]]]].
  subst reserved.
  cbn in Hcount_event.
  rewrite Hevent in Hcount_event.
  inversion Hcount_event; subst e_count.
  rewrite Htype in Hcount_type.
  rewrite Hfields in Hcount_fields.
  inversion Hcount_fields; subst m_count.
  rewrite Howner in Hcount_owner.
  inversion Hcount_owner; subst owner_count.
  subst m_available.
  subst e_available.
  subst available.
  cbn in Howner_event.
  unfold update_event_field_raw in Howner_event.
  cbn in Howner_event.
  rewrite Z.eqb_refl in Howner_event.
  inversion Howner_event; subst e_owner.
  cbn in Howner_fields.
  inversion Howner_fields; subst m_owner.
  subst tsk_reserved.
  subst m_final.
  subst e_final.
  unfold replace_EventS, replace_TskS in Hafter.
  cbn in Hafter.
  rewrite update_event_field_raw_same__return_semantics in Hafter.
  unfold atomic_mutex_release.
  exists e.
  eexists.
  exists m.
  eexists.
  exists owner.
  eexists.
  exists
    {| inUsedTaskStates := (TskState before).(inUsedTaskStates);
       unUsedTaskStates := (TskState before).(unUsedTaskStates);
       tcbListHead := (TskState before).(tcbListHead);
       prioTbl := fun p =>
         if (negb (Z.eqb (mfPCP m) (osPrioMutexCeilDis sg)) &&
             Z.eqb p (mfPCP m))%bool
         then PTReserved
       else (TskState before).(prioTbl) p;
       taskRegNextID := (TskState before).(taskRegNextID);
       parkedTaskStacks := (TskState before).(parkedTaskStacks);
       taskLifecycle := (TskState before).(taskLifecycle);
     taskCount := (TskState before).(taskCount) |}.
  repeat split; try assumption; try reflexivity.
Qed.
Lemma mutex_post_disinherit_owner_restored__return_semantics :
  forall sg pevent entry pcp owner_orig disinherited,
    UCOS2_verification_slice_state_inv sg entry ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig disinherited ->
    exists eid e m owner owner_t,
      pevent = event_addr sg eid /\
      disinherited.(EventState).(inUsedEventStates) eid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e.(mutexFields) = Some m /\
      m.(mfOwner) = Some owner /\
      m.(mfPCP) = pcp /\
      m.(mfOwnerOrigPrio) = Some owner_orig /\
      disinherited.(TskState).(inUsedTaskStates) owner = Some owner_t /\
      owner_t.(curPrio) = owner_orig.
Proof.
  intros sg pevent entry pcp owner_orig disinherited
    Hvalid Hstage.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage.
  destruct Hstage as
    [Hchecked [Hboundary
      [eid [e [m [owner
        [Hpevent [Hevent [Htype [Hfields [Howner
          [Hpcp [Horig [Hcurrent Hdisinherit]]]]]]]]]]]]]].
  destruct Hvalid as
    [Htask [Hsched [Hevent_valid Hcross]]].
  pose proof Hcross as Hcross0.
  unfold Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
    in Hcross0.
  destruct Hcross0 as
    [Hosprio [Hprio [Howner_consistency Hcross_rest]]].
  unfold Ucos2Verify.lib.cross_module_invariants.mutex_owner_consistency
    in Howner_consistency.
  specialize
    (Howner_consistency eid e m
      (conj Hevent (conj Htype Hfields))).
  rewrite Howner in Howner_consistency.
  destruct Howner_consistency as
    [entry_owner_t [entry_orig
      [Hentry_owner [Hentry_orig [Hentry_prio Hentry_notin]]]]].
  rewrite Horig in Hentry_orig.
  inversion Hentry_orig; subst entry_orig.
  unfold OSMutexPost_disinherit_sem in Hdisinherit.
  destruct Hdisinherit as
    [cur_t [Hcur
      [[Hdisabled Hsame] |
       [[Henabled [Hnot_pcp Hsame]] |
        [Henabled [Hat_pcp
          [restored_prio [Hrestored Hexec]]]]]]]].
  - subst disinherited.
    exists eid, e, m, owner, entry_owner_t.
    repeat split; try assumption.
    destruct Hentry_prio as
      [Hentry_prio | [Hentry_enabled Hentry_prio]];
      [assumption | contradiction].
  - subst disinherited.
    exists eid, e, m, owner, entry_owner_t.
    repeat split; try assumption.
    destruct Hentry_prio as
      [Hentry_prio | [Hentry_enabled Hentry_prio]];
      [assumption |].
    exfalso.
    apply Hnot_pcp.
    rewrite Hcur in Hentry_owner.
    inversion Hentry_owner; subst entry_owner_t.
    exact Hentry_prio.
  - rewrite Horig in Hrestored.
    inversion Hrestored; subst restored_prio.
    unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
    destruct Hexec as
      [owner_t' [Hexec_current [Hexec_prio [Hexec_get
        [Hlo [Hhi [Howner_t' Hpost]]]]]]].
    cbv zeta in Hpost.
    subst disinherited.
    assert (Howner_eq : owner = owner).
    { reflexivity. }
    exists eid, e, m, owner, owner_t'.
    repeat split; try assumption; try reflexivity.
    + cbn. rewrite Z.eqb_refl. reflexivity.
    + subst owner_t'. reflexivity.
Qed.
Lemma atomic_mutex_release_preserves_validity__return_semantics :
  forall sg mid before after e m owner owner_t orig,
    UCOS2_verification_slice_state_inv sg before ->
    before.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some owner ->
    before.(TskState).(inUsedTaskStates) owner = Some owner_t ->
    m.(mfOwnerOrigPrio) = Some orig ->
    owner_t.(curPrio) = orig ->
    atomic_mutex_release sg mid before tt after ->
    UCOS2_verification_slice_state_inv sg after.
Proof.
  intros sg mid before after e m owner owner_t orig
    Hvalid Hevent Htype Hfields Howner Howner_t Horig Howner_prio
    Hrelease.
  unfold atomic_mutex_release in Hrelease.
  destruct Hrelease as
    [e1 [e2 [m1 [m2 [owner1 [evSt2 [tskSt2
      [Hevent1 [Htype1 [Hfields1 [Hwait1 [Howner1
       [Hm2 [He2 [HevSt2 [HtskSt2 Hafter]]]]]]]]]]]]]]]].
  rewrite Hevent in Hevent1.
  inversion Hevent1; subst e1.
  rewrite Hfields in Hfields1.
  inversion Hfields1; subst m1.
  rewrite Howner in Howner1.
  inversion Howner1; subst owner1.
  subst m2.
  subst e2.
  subst evSt2.
  subst tskSt2.
  subst after.
  destruct Hvalid as
    [Htask [Hsched [Hevent_valid Hcross]]].
  pose proof Hcross as Hcross_for_protocol.
  unfold Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
    in Hcross_for_protocol.
  destruct Hcross_for_protocol as
    [Hosprio [Hpriotbl [Hmutex_owner [Hwait_cross
      [Hready_complete [Hready_order [Hceil [Htask_unique
        [Hprotocol Hpcp_unique]]]]]]]]].
  assert (Hselected_protocol :
    valid_mutex_pcp sg m.(mfPCP) /\
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None => True
     | Some _, Some op =>
         valid_task_prio sg op /\
         (m.(mfPCP) <> sg.(osPrioMutexCeilDis) -> op <> m.(mfPCP))
     | _, _ => False
     end) /\
    (m.(mfPCP) = sg.(osPrioMutexCeilDis) \/
     (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
      ((TskState before).(prioTbl) m.(mfPCP) = PTReserved \/
       exists owner0,
         m.(mfOwner) = Some owner0 /\
         (TskState before).(prioTbl) m.(mfPCP) = PTTask owner0)))).
  {
    eapply Hprotocol; eassumption.
  }
  destruct Htask as [Htask_range Htask_fields].
  unfold verification_slice_task_in_range in Htask_range.
  destruct Htask_range as
    [Hids [Hfree_nodup [Hfree_range [Hfree_unused
      [Htable_live [Hregistered Hunique]]]]]].
  assert (Htask_post :
    verification_slice_task_validity sg
      {|
        inUsedTaskStates := inUsedTaskStates (TskState before);
        unUsedTaskStates := unUsedTaskStates (TskState before);
        tcbListHead := tcbListHead (TskState before);
        prioTbl := fun p : Priority =>
          if
           (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
            (p =? mfPCP m))%bool
          then PTReserved
          else prioTbl (TskState before) p;
        taskRegNextID := taskRegNextID (TskState before);
        parkedTaskStacks := parkedTaskStacks (TskState before);
        taskLifecycle := taskLifecycle (TskState before);
     taskCount := taskCount (TskState before)
      |}).
  {
    unfold verification_slice_task_validity, verification_slice_task_in_range,
      verification_slice_task_in_range.
    split.
    - split.
      + exact Hids.
      + split.
        * exact Hfree_nodup.
        * split.
          -- exact Hfree_range.
          -- split.
             ++ exact Hfree_unused.
             ++ split.
                ** intros p tid Hlookup.
        cbn in Hlookup.
        destruct
          (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
           (p =? mfPCP m))%bool eqn:Hcond.
                   --- discriminate.
                   --- eapply Htable_live. exact Hlookup.
                ** split.
                   --- unfold task_current_prio_registered.
                       intros tid t Hlookup.
                       cbn in Hlookup |- *.
                       pose proof (Hregistered tid t Hlookup) as Hentry_slot.
                       destruct
                         (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
                          (curPrio t =? mfPCP m))%bool eqn:Hcond.
                       +++ apply andb_true_iff in Hcond.
                           destruct Hcond as [Henabled_b Hprio_b].
                           apply negb_true_iff in Henabled_b.
                           apply Z.eqb_neq in Henabled_b.
                           apply Z.eqb_eq in Hprio_b.
                           rewrite Hprio_b in Hentry_slot.
                           destruct Hselected_protocol as
                             [Hvalid_pcp [Howner_fields Hslot]].
                           rewrite Howner, Horig in Howner_fields.
                           destruct Howner_fields as
                             [Horig_valid Horig_ne_pcp].
                           specialize (Horig_ne_pcp Henabled_b).
                           destruct Hslot as
                             [Hdisabled | [Henabled [Hreserved | Howned]]].
                           *** contradiction.
                           *** rewrite Hreserved in Hentry_slot.
                               discriminate.
                           *** destruct Howned as
                                 [owner0 [Howner0 Howned_slot]].
                               rewrite Howner in Howner0.
                               inversion Howner0; subst owner0.
                               rewrite Howned_slot in Hentry_slot.
                               inversion Hentry_slot; subst tid.
                               rewrite Howner_t in Hlookup.
                               inversion Hlookup; subst t.
                               rewrite Howner_prio in Hprio_b.
                               contradiction.
                       +++ exact Hentry_slot.
                   --- exact Hunique.
    - intros tid t Hlookup.
      cbn in Hlookup.
      eapply Htask_fields.
      exact Hlookup.
  }
  assert (Hsched_post :
    verification_slice_sched_in_range sg
      {|
        inUsedTaskStates := inUsedTaskStates (TskState before);
        unUsedTaskStates := unUsedTaskStates (TskState before);
        tcbListHead := tcbListHead (TskState before);
        prioTbl := fun p : Priority =>
          if
           (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
            (p =? mfPCP m))%bool
          then PTReserved
          else prioTbl (TskState before) p;
        taskRegNextID := taskRegNextID (TskState before);
        parkedTaskStacks := parkedTaskStacks (TskState before);
        taskLifecycle := taskLifecycle (TskState before);
     taskCount := taskCount (TskState before)
      |}
      (SchedState before)).
  {
    rewrite <-
      (verification_slice_sched_in_range_ext sg
        (TskState before)
        {|
          inUsedTaskStates := inUsedTaskStates (TskState before);
          unUsedTaskStates := unUsedTaskStates (TskState before);
          tcbListHead := tcbListHead (TskState before);
          prioTbl := fun p : Priority =>
            if
             (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
              (p =? mfPCP m))%bool
            then PTReserved
            else prioTbl (TskState before) p;
          taskRegNextID := taskRegNextID (TskState before);
          parkedTaskStacks := parkedTaskStacks (TskState before);
          taskLifecycle := taskLifecycle (TskState before);
     taskCount := taskCount (TskState before)
        |}
        (SchedState before)).
    - exact Hsched.
    - reflexivity.
  }
  assert (Hevent_post :
    verification_slice_event_in_range sg
      {|
        inUsedTaskStates := inUsedTaskStates (TskState before);
        unUsedTaskStates := unUsedTaskStates (TskState before);
        tcbListHead := tcbListHead (TskState before);
        prioTbl := fun p : Priority =>
          if
           (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
            (p =? mfPCP m))%bool
          then PTReserved
          else prioTbl (TskState before) p;
        taskRegNextID := taskRegNextID (TskState before);
        parkedTaskStacks := parkedTaskStacks (TskState before);
        taskLifecycle := taskLifecycle (TskState before);
     taskCount := taskCount (TskState before)
      |}
      (update_event_field_raw (EventState before) mid
       {|
         eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType := eventType e;
         mutexFields :=
           Some
             {|
               mfPCP := mfPCP m;
               mfOwner := None;
               mfOwnerOrigPrio := None
             |};
         semFields := semFields e;
         mboxFields := mboxFields e;
         queueFields := queueFields e;
         waitList := waitList e
       |})).
  {
    unfold verification_slice_event_in_range, verification_slice_event_in_range.
    rewrite Hwait1.
    eapply verification_slice_event_in_range_preserved_by_mutex_owner_clear.
    - exact Hevent.
    - exact Htype.
    - exact Hfields.
    - exact Hevent_valid.
  }
  assert (Hcross_post :
    Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency sg
      {|
        IntrState := IntrState before;
        TskState :=
          {|
            inUsedTaskStates := inUsedTaskStates (TskState before);
            unUsedTaskStates := unUsedTaskStates (TskState before);
            tcbListHead := tcbListHead (TskState before);
            prioTbl := fun p : Priority =>
              if
               (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
                (p =? mfPCP m))%bool
              then PTReserved
              else prioTbl (TskState before) p;
            taskRegNextID := taskRegNextID (TskState before);
            parkedTaskStacks := parkedTaskStacks (TskState before);
            taskLifecycle := taskLifecycle (TskState before);
     taskCount := taskCount (TskState before)
          |};
        SchedState := SchedState before;
        EventState :=
          update_event_field_raw (EventState before) mid
            {|
              eventGeneration := e.(eventGeneration);
              eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
              eventType := eventType e;
              mutexFields :=
                Some
                  {|
                    mfPCP := mfPCP m;
                    mfOwner := None;
                    mfOwnerOrigPrio := None
                  |};
              semFields := semFields e;
              mboxFields := mboxFields e;
              queueFields := queueFields e;
              waitList := waitList e
            |};
        TickState := TickState before;
        FlagState := before.(FlagState);
        MemoryState := before.(MemoryState);
        TimerState := before.(TimerState);
        StatsState := before.(StatsState);
        ControlState := before.(ControlState);
        NameState := before.(NameState)
      |}).
  {
    eapply
      Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency_preserved_by_release.
    - exact Hevent.
    - exact Htype.
    - exact Hfields.
    - exact Howner.
    - exact Howner_t.
    - exact Horig.
    - exact Howner_prio.
    - reflexivity.
    - exact Hcross.
  }
  unfold UCOS2_verification_slice_state_inv.
  exact
    (conj Htask_post
      (conj Hsched_post (conj Hevent_post Hcross_post))).
Qed.
Lemma mutex_post_empty_release_validity__return_semantics :
  forall sg pevent eid entry disinherited released pcp owner_orig,
    pevent = event_addr sg eid ->
    UCOS2_verification_slice_state_inv sg entry ->
    UCOS2_verification_slice_state_inv sg disinherited ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig disinherited ->
    mutex_post_release_step_prop
      sg eid disinherited released ->
    UCOS2_verification_slice_state_inv sg released.
Proof.
  intros sg pevent eid entry disinherited released pcp owner_orig
    Hpevent Hentry_valid Hdisinherited_valid Hstage Hrelease.
  pose proof
    (mutex_post_disinherit_owner_restored__return_semantics
       sg pevent entry pcp owner_orig disinherited
       Hentry_valid Hstage)
    as [stage_eid [e [m [owner [owner_t
      [Hstage_pevent [Hevent [Htype [Hfields
       [Howner [Hpcp [Horig [Howner_t Howner_prio]]]]]]]]]]]]].
  assert (Heid : stage_eid = eid).
  {
    apply event_addr_injective with (sg := sg).
    transitivity pevent.
    - symmetry; exact Hstage_pevent.
    - exact Hpevent.
  }
  subst stage_eid.
  unfold mutex_post_release_step_prop in Hrelease.
  pose proof
    (mutex_post_empty_release_refines_atomic__return_semantics
       sg eid disinherited released Hrelease)
    as Hatomic.
  eapply atomic_mutex_release_preserves_validity__return_semantics.
  - exact Hdisinherited_valid.
  - exact Hevent.
  - exact Htype.
  - exact Hfields.
  - exact Howner.
  - exact Howner_t.
  - exact Horig.
  - exact Howner_prio.
  - exact Hatomic.
Qed.
Lemma mutex_post_reservation_task_validity__return_semantics :
  forall sg mid before reserved e m owner owner_t orig,
    UCOS2_verification_slice_state_inv sg before ->
    before.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some owner ->
    before.(TskState).(inUsedTaskStates) owner = Some owner_t ->
    m.(mfOwnerOrigPrio) = Some orig ->
    owner_t.(curPrio) = orig ->
    OSMutexPost_reservation_sem sg mid before reserved ->
    verification_slice_task_validity sg reserved.(TskState).
Proof.
  intros sg mid before reserved e m owner owner_t orig
    Hvalid Hevent Htype Hfields Howner Howner_t Horig Howner_prio
    Hreservation.
  unfold OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (e1 & m1 & owner1 & tsk_reserved &
     Hevent1 & Htype1 & Hfields1 & Howner1 &
     Htsk_reserved & Hreserved).
  rewrite Hevent in Hevent1.
  inversion Hevent1; subst e1.
  rewrite Hfields in Hfields1.
  inversion Hfields1; subst m1.
  rewrite Howner in Howner1.
  inversion Howner1; subst owner1.
  subst tsk_reserved.
  subst reserved.
  destruct Hvalid as
    [Htask [Hsched [Hevent_valid Hcross]]].
  pose proof Hcross as Hcross_for_protocol.
  unfold Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
    in Hcross_for_protocol.
  destruct Hcross_for_protocol as
    [Hosprio [Hpriotbl [Hmutex_owner [Hwait_cross
      [Hready_complete [Hready_order [Hceil [Htask_unique
        [Hprotocol Hpcp_unique]]]]]]]]].
  assert (Hselected_protocol :
    valid_mutex_pcp sg m.(mfPCP) /\
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None => True
     | Some _, Some op =>
         valid_task_prio sg op /\
         (m.(mfPCP) <> sg.(osPrioMutexCeilDis) ->
          op <> m.(mfPCP))
     | _, _ => False
     end) /\
    (m.(mfPCP) = sg.(osPrioMutexCeilDis) \/
     (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
      ((TskState before).(prioTbl) m.(mfPCP) = PTReserved \/
       exists owner0,
         m.(mfOwner) = Some owner0 /\
         (TskState before).(prioTbl) m.(mfPCP) =
           PTTask owner0)))).
  {
    eapply Hprotocol; eassumption.
  }
  destruct Htask as [Htask_range Htask_fields].
  unfold verification_slice_task_in_range in Htask_range.
  destruct Htask_range as
    [Hids [Hfree_nodup [Hfree_range [Hfree_unused
      [Htable_live [Hregistered Hunique]]]]]].
  split.
  - unfold verification_slice_task_in_range, verification_slice_task_in_range.
    cbn.
    split.
    + exact Hids.
    + split; [exact Hfree_nodup |].
      split; [exact Hfree_range |].
      split; [exact Hfree_unused |].
      split.
      * intros p tid Hlookup.
        destruct
          (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
           (p =? mfPCP m))%bool eqn:Hcond.
        -- discriminate.
        -- eapply Htable_live. exact Hlookup.
      * split.
        -- unfold task_current_prio_registered.
           intros tid t Hlookup.
           cbn in Hlookup |- *.
           pose proof (Hregistered tid t Hlookup) as Hentry_slot.
           destruct
             (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
              (curPrio t =? mfPCP m))%bool eqn:Hcond.
           ++ apply andb_true_iff in Hcond.
              destruct Hcond as [Henabled_b Hprio_b].
              apply negb_true_iff in Henabled_b.
              apply Z.eqb_neq in Henabled_b.
              apply Z.eqb_eq in Hprio_b.
              rewrite Hprio_b in Hentry_slot.
              destruct Hselected_protocol as
                [Hvalid_pcp [Howner_fields Hslot]].
              rewrite Howner, Horig in Howner_fields.
              destruct Howner_fields as
                [Horig_valid Horig_ne_pcp].
              specialize (Horig_ne_pcp Henabled_b).
              destruct Hslot as
                [Hdisabled | [Henabled [Hreserved_slot | Howned]]].
              ** contradiction.
              ** rewrite Hreserved_slot in Hentry_slot.
                 discriminate.
              ** destruct Howned as
                   [owner0 [Howner0 Howned_slot]].
                 rewrite Howner in Howner0.
                 inversion Howner0; subst owner0.
                 rewrite Howned_slot in Hentry_slot.
                 inversion Hentry_slot; subst tid.
                 rewrite Howner_t in Hlookup.
                 inversion Hlookup; subst t.
                 rewrite Howner_prio in Hprio_b.
                 contradiction.
           ++ exact Hentry_slot.
        -- exact Hunique.
  - intros tid t Hlookup.
    cbn in Hlookup.
    eapply Htask_fields.
    exact Hlookup.
Qed.
Lemma task_validity_preserved_by_same_priority_update__return_semantics :
  forall sg st tid t t',
    st.(inUsedTaskStates) tid = Some t ->
    t'.(curPrio) = t.(curPrio) ->
    verification_slice_task_validity sg st ->
    verification_slice_task_validity sg
      (glob_task_set_usedtask st tid t').
Proof.
  intros sg st tid t t' Hlookup Hprio Hvalid.
  destruct Hvalid as [Hrange Hderived].
  unfold verification_slice_task_in_range in Hrange.
  destruct Hrange as
    [Hids [Hfree_nodup [Hfree_range [Hfree_unused
      [Htable_live [Hregistered Hunique]]]]]].
  split.
  - unfold verification_slice_task_in_range,
      glob_task_set_usedtask.
    cbn.
    split.
    + intros tid0 t0 Hlookup0.
      destruct (Z.eqb tid0 tid) eqn:Heq.
      * apply Z.eqb_eq in Heq. subst tid0.
        inversion Hlookup0; subst t0.
        eapply Hids. exact Hlookup.
      * eapply Hids. exact Hlookup0.
    + split; [exact Hfree_nodup |].
      split; [exact Hfree_range |].
      split.
      * intros tid0 Hin.
        destruct (Z.eqb tid0 tid) eqn:Heq.
        -- apply Z.eqb_eq in Heq. subst tid0.
           pose proof (Hfree_unused tid Hin) as Hnone.
           rewrite Hlookup in Hnone. discriminate.
        -- exact (Hfree_unused tid0 Hin).
      * split.
        -- intros p tid0 Htable.
           destruct (Htable_live p tid0 Htable)
             as [Hvalid_p [t0 Hlookup0]].
           split; [exact Hvalid_p |].
           destruct (Z.eqb tid0 tid) eqn:Heq.
           ++ apply Z.eqb_eq in Heq. subst tid0.
              rewrite Hlookup in Hlookup0.
              inversion Hlookup0; subst t0.
              exists t'. reflexivity.
           ++ exists t0. exact Hlookup0.
        -- split.
           ++ eapply
                glob_task_set_usedtask_preserves_current_prio_registered.
              ** exact Hlookup.
              ** exact Hprio.
              ** exact Hregistered.
           ++ unfold task_priority_unique.
              cbn.
              intros tid1 tid2 t1 t2 Hlookup1 Hlookup2 Heq_prio.
              destruct (Z.eqb tid1 tid) eqn:Heq1;
                destruct (Z.eqb tid2 tid) eqn:Heq2.
              ** apply Z.eqb_eq in Heq1, Heq2. congruence.
              ** apply Z.eqb_eq in Heq1. subst tid1.
                 inversion Hlookup1; subst t1.
                 assert (tid2 = tid).
                 {
                   eapply Hunique.
                   - exact Hlookup2.
                   - exact Hlookup.
                   - rewrite <- Hprio. symmetry. exact Heq_prio.
                 }
                 subst tid2. rewrite Z.eqb_refl in Heq2. discriminate.
              ** apply Z.eqb_eq in Heq2. subst tid2.
                 inversion Hlookup2; subst t2.
                 assert (tid1 = tid).
                 {
                   eapply Hunique.
                   - exact Hlookup1.
                   - exact Hlookup.
                   - rewrite <- Hprio. exact Heq_prio.
                 }
                 subst tid1. rewrite Z.eqb_refl in Heq1. discriminate.
              ** eapply Hunique; eassumption.
  - intros tid0 t0 Hlookup0.
    unfold glob_task_set_usedtask in Hlookup0.
    cbn in Hlookup0.
    destruct (Z.eqb tid0 tid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst tid0.
      inversion Hlookup0; subst t0.
      pose proof (Hderived tid t Hlookup) as [Hvalid_p Hfields].
      split.
      * rewrite Hprio. exact Hvalid_p.
      * unfold valid_derived_fields in *.
        rewrite Hprio.
        exact Hfields.
    + exact (Hderived tid0 t0 Hlookup0).
Qed.
Lemma atomic_event_task_rdy_same_identity_preserves_validity__return_semantics :
  forall sg mid pend_stat before returned_prio tid after,
    UCOS2_verification_slice_state_inv sg before ->
    atomic_event_task_rdy
      sg mid pend_stat before returned_prio tid tid after ->
    UCOS2_verification_slice_state_inv sg after.
Proof.
  intros sg mid pend_stat before returned_prio tid after
    Hvalid Hwake.
  unfold atomic_event_task_rdy, atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (e1 & e2 & canonical_t & table_t & table_t' &
     Hevent & Hpend_type & Hwait_nonempty & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hafter).
  rewrite Hcanonical_get in Htable_get.
  inversion Htable_get; subst table_t.
  assert (Hin_wait : In tid e1.(waitList)).
  {
    destruct e1.(waitList) as [|head tail] eqn:Hwait.
    - exfalso. apply Hwait_nonempty. reflexivity.
    - cbn in Hcanonical. subst tid. left. reflexivity.
  }
  destruct Hvalid as [Htask [Hsched [Hevent_valid Hcross]]].
  assert (Hwait_pend :
    (task_non_suspension_bits canonical_t.(stat)) = task_pend_mask PendMutex).
  {
    pose proof Hcross as Hcross_wait.
    unfold Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      in Hcross_wait.
    destruct Hcross_wait as
      [_ [_ [_ [Hwait_consistency _]]]].
    unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_object_consistency
      in Hwait_consistency.
    destruct Hwait_consistency as [Hwait_entry _].
    specialize (Hwait_entry mid e1 Hevent).
    unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency
      in Hwait_entry.
    destruct Hwait_entry as [_ Hwait_match].
    rewrite Hpend_type in Hwait_match.
    specialize (Hwait_match tid Hin_wait).
    destruct Hwait_match as
      [wait_t [Hwait_get [_ [_ Hwait_pend]]]].
    rewrite Hcanonical_get in Hwait_get.
    inversion Hwait_get; subst wait_t.
    exact Hwait_pend.
  }
  assert (Hnot_ready :
    ~ In tid before.(SchedState).(readyList)).
  {
    intro Hin_ready.
    destruct Hsched as [Hready_sound _].
    specialize (Hready_sound tid Hin_ready).
    destruct Hready_sound as [ready_t [Hready_get Hready]].
    rewrite Hcanonical_get in Hready_get.
    inversion Hready_get; subst ready_t.
    unfold is_effectively_ready in Hready.
    rewrite Hwait_pend in Hready.
    discriminate.
  }
  assert (Hunique_before :
    task_priority_unique before.(TskState)).
  {
    pose proof Htask as Htask_copy.
    unfold verification_slice_task_validity, verification_slice_task_in_range,
      verification_slice_task_in_range in Htask_copy.
    destruct Htask_copy as
      [[_ [_ [_ [_ [_ [_ Hunique_before]]]]]] _].
    exact Hunique_before.
  }
  assert (HTsk_after :
    after.(TskState) =
      glob_task_set_usedtask before.(TskState) tid table_t').
  {
    rewrite Hafter.
    reflexivity.
  }
  set (ready_after :=
    if (task_is_suspended table_t'.(stat))
    then before.(SchedState).(readyList)
    else Ucos2Verify.lib.helpers.insert_sorted_by
      (fun task_id =>
         match before.(TskState).(inUsedTaskStates) task_id with
         | Some task => task.(curPrio)
         | None => sg.(osLowestPrio) + 1
         end)
      tid
      (Ucos2Verify.lib.helpers.remove_Z_eqb
         tid before.(SchedState).(readyList))).
  assert (HSched_after :
    after.(SchedState) =
      {|
        readyList := ready_after;
        curTaskID := before.(SchedState).(curTaskID);
        curSchedPrio := before.(SchedState).(curSchedPrio);
        highRdyTid :=
          match ready_after with
          | cons head _ => Some head
          | nil => None
          end;
        highRdyPrio :=
          match ready_after with
          | cons head _ =>
              match
                before.(TskState).(inUsedTaskStates) head
              with
              | Some head_t => Some head_t.(curPrio)
              | None => None
              end
          | nil => None
          end;
        ctxSwCtr := before.(SchedState).(ctxSwCtr);
        isRunning := before.(SchedState).(isRunning)
      |}).
  {
    rewrite Hafter.
    unfold ready_after.
    reflexivity.
  }
  assert (HEv_after :
    after.(EventState) =
      update_event_field_raw before.(EventState) mid e2).
  {
    rewrite Hafter.
    reflexivity.
  }
  assert (Htask_after :
    verification_slice_task_validity sg after.(TskState)).
  {
    rewrite HTsk_after.
    eapply
      task_validity_preserved_by_same_priority_update__return_semantics.
    - exact Hcanonical_get.
    - rewrite Htable_t'. reflexivity.
    - exact Htask.
  }
  assert (Hsched_after :
    verification_slice_sched_in_range sg after.(TskState) after.(SchedState)).
  {
    rewrite HTsk_after, HSched_after.
    eapply verification_slice_sched_in_range_preserved_by_make_ready
      with
        (cur_tid := tid)
        (t := canonical_t)
        (t' := table_t')
        (ready_after := ready_after).
    - exact Hcanonical_get.
    - rewrite Htable_t'. reflexivity.
    - reflexivity.
    - unfold ready_after.
      assert (Hcleared : task_non_suspension_bits table_t'.(stat) = 0).
      {
        rewrite Htable_t'.
        change (task_non_suspension_bits
          (task_clear_pending_status canonical_t.(stat) PendMutex) = 0).
        apply task_clear_pending_status_same_kind.
        exact Hwait_pend.
      }
      assert (Hdelay : table_t'.(dly) = 0).
      { rewrite Htable_t'. reflexivity. }
      unfold is_effectively_ready.
      rewrite Hcleared, Hdelay.
      destruct (task_is_suspended table_t'.(stat));
        reflexivity.
    - reflexivity.
    - exact Hnot_ready.
    - exact Hunique_before.
    - exact Hsched.
  }
  assert (Hevent_after :
    verification_slice_event_in_range
      sg after.(TskState) after.(EventState)).
  {
    unfold verification_slice_event_in_range, verification_slice_event_in_range.
    rewrite HTsk_after, HEv_after.
    eapply verification_slice_event_in_range_preserved_by_eventTaskRemove
      with
        (cur_tid := tid)
        (e1 := e1)
        (t := canonical_t)
        (t' := table_t').
    - exact Hcanonical_get.
    - rewrite Htable_t'. reflexivity.
    - reflexivity.
    - exact Hevent.
    - exact Hin_wait.
    - exact He2.
    - reflexivity.
    - exact Hevent_valid.
  }
  set (removed_t :=
    {|
      taskID := canonical_t.(taskID);
     taskGeneration := canonical_t.(taskGeneration);
     tcbStkPtr := canonical_t.(tcbStkPtr);
     tcbExtPtr := canonical_t.(tcbExtPtr);
     tcbStkBottom := canonical_t.(tcbStkBottom);
     tcbStkSize := canonical_t.(tcbStkSize);
     tcbOpt := canonical_t.(tcbOpt);
     tcbPublicId := canonical_t.(tcbPublicId);
     tcbFlagNode := canonical_t.(tcbFlagNode);
     tcbFlagsRdy := canonical_t.(tcbFlagsRdy);
     tcbTaskName := canonical_t.(tcbTaskName);
     tcbReg0 := canonical_t.(tcbReg0);
     tcbCtxSwCtr := canonical_t.(tcbCtxSwCtr);
     tcbCyclesTot := canonical_t.(tcbCyclesTot);
     tcbCyclesStart := canonical_t.(tcbCyclesStart);
     tcbStkBase := canonical_t.(tcbStkBase);
     tcbStkUsed := canonical_t.(tcbStkUsed);
     tcbPadding42 := canonical_t.(tcbPadding42);
     tcbPadding43 := canonical_t.(tcbPadding43);
     tcbEventMultiPtr := canonical_t.(tcbEventMultiPtr);
      curPrio := canonical_t.(curPrio);
      stat := canonical_t.(stat);
      statPend := canonical_t.(statPend);
      dly := canonical_t.(dly);
      eventPtr := None;
      eventMultiWaitEvents := canonical_t.(eventMultiWaitEvents);
      eventMultiRdy := canonical_t.(eventMultiRdy);
      msg := canonical_t.(msg);
      nextTCB := canonical_t.(nextTCB);
      prevTCB := canonical_t.(prevTCB);
      delReq := canonical_t.(delReq)
    |}).
  set (removed :=
    {|
      IntrState := before.(IntrState);
      TskState :=
        glob_task_set_usedtask before.(TskState) tid removed_t;
      SchedState := before.(SchedState);
      EventState :=
        update_event_field_raw before.(EventState) mid e2;
      TickState := before.(TickState);
      FlagState := before.(FlagState);
      MemoryState := before.(MemoryState);
      TimerState := before.(TimerState);
      StatsState := before.(StatsState);
      ControlState := before.(ControlState);
      NameState := before.(NameState)
    |}).
  assert (Hremove :
    atomic_event_task_remove tid mid before tt removed).
  {
    unfold atomic_event_task_remove.
    exists e1, e2, canonical_t, removed_t.
    split; [exact Hevent |].
    split; [exact Hin_wait |].
    split; [exact Hcanonical_get |].
    split; [exact He2 |].
    split.
    - unfold removed_t. reflexivity.
    - unfold removed, glob_task_set_usedtask.
      reflexivity.
  }
  assert (Hcross_removed :
    Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      sg removed).
  {
    eapply verification_slice_cross_module_consistency_preserved_by_event_task_remove.
    - exact Hremove.
    - exact Hsched.
    - exact Hcross.
  }
  assert (HEvent_frame :
    after.(EventState) = removed.(EventState)).
  {
    rewrite HEv_after.
    unfold removed.
    reflexivity.
  }
  assert (HTable_frame :
    after.(TskState).(prioTbl) =
      removed.(TskState).(prioTbl)).
  {
    rewrite HTsk_after.
    unfold removed, glob_task_set_usedtask.
    reflexivity.
  }
  assert (HUsed_after :
    forall task_id,
      after.(TskState).(inUsedTaskStates) task_id =
      if Z.eqb task_id tid
      then Some table_t'
      else removed.(TskState).(inUsedTaskStates) task_id).
  {
    intro task_id.
    rewrite HTsk_after.
    unfold removed, glob_task_set_usedtask.
    cbn.
    destruct (Z.eqb task_id tid); reflexivity.
  }
  assert (HRemoved_get :
    removed.(TskState).(inUsedTaskStates) tid = Some removed_t).
  {
    unfold removed, glob_task_set_usedtask.
    cbn.
    rewrite Z.eqb_refl.
    reflexivity.
  }
  assert (Hcompletion_prio :
    table_t'.(curPrio) = removed_t.(curPrio)).
  {
    rewrite Htable_t'.
    unfold removed_t.
    reflexivity.
  }
  assert (HCurrent_frame :
    after.(SchedState).(curTaskID) =
      removed.(SchedState).(curTaskID)).
  {
    rewrite HSched_after.
    unfold removed.
    reflexivity.
  }
  assert (HCurrent_prio_frame :
    after.(SchedState).(curSchedPrio) =
      removed.(SchedState).(curSchedPrio)).
  {
    rewrite HSched_after.
    unfold removed.
    reflexivity.
  }
  assert (Hcross_after :
    Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      sg after).
  {
    unfold Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      in Hcross_removed |- *.
    destruct Hcross_removed as
      [Hosprio [Hpriotbl [Howner [Hwait
       [Hready_complete [Hready_order [Hceil [Htask_unique
        [Hprotocol Hpcp_unique]]]]]]]]].
    pose proof Htask_after as Htask_after_parts.
    unfold verification_slice_task_validity, verification_slice_task_in_range,
      verification_slice_task_in_range in Htask_after_parts.
    destruct Htask_after_parts as
      [[Hids_after [Hfree_nodup_after [Hfree_range_after
        [Hfree_unused_after [Htable_live_after
          [Hregistered_after Hunique_after]]]]]]
       Hderived_after].
    pose proof Hsched_after as Hsched_after_parts.
    destruct Hsched_after_parts as
      [Hready_sound_after [Hsorted_after
       [Hcomplete_after [Hnodup_after Hsched_rest]]]].
    split.
    - eapply
        Ucos2Verify.lib.cross_module_invariants.osprio_cur_consistency_preserved_by_handover
        with
          (lvs1 := removed)
          (new_owner := tid)
          (new_owner_t' := table_t')
          (new_owner_t := removed_t).
      + rewrite HUsed_after, Z.eqb_refl. reflexivity.
      + exact Hcompletion_prio.
      + exact HUsed_after.
      + exact HCurrent_frame.
      + exact HCurrent_prio_frame.
      + exact HRemoved_get.
      + exact Hosprio.
    - split.
      + unfold Ucos2Verify.lib.cross_module_invariants.priotbl_consistency
          in Hpriotbl |- *.
        intro p.
        rewrite HTable_frame.
        specialize (Hpriotbl p).
        destruct (removed.(TskState).(prioTbl) p)
          as [| |slot_tid] eqn:Hslot.
        * destruct Hpriotbl as [Hno_ready Hno_mutex].
          split.
          -- intros
               [ready_tid [Hin_ready
                [ready_t [Hready_get Hready_prio]]]].
             pose proof
               (Hregistered_after
                  ready_tid ready_t Hready_get)
               as Hregistered_slot.
             rewrite Hready_prio, HTable_frame, Hslot
               in Hregistered_slot.
             discriminate.
          -- intro Hmutex_claim.
             apply Hno_mutex.
             rewrite <- HEvent_frame.
             exact Hmutex_claim.
        * destruct Hpriotbl as
            [claim_eid [claim_e [claim_m
             [Hclaim_get [Hclaim_type [Hclaim_fields
              [Hclaim_pcp Hclaim_owner]]]]]]].
          exists claim_eid, claim_e, claim_m.
          rewrite HEvent_frame.
          repeat split; try assumption.
          destruct claim_m.(mfOwner) as [claim_tid |]
            eqn:Hclaim_owner_eq.
          -- destruct Hclaim_owner as
               [claim_t [claim_op
                [Hclaim_task [Hclaim_orig Hclaim_prio]]]].
             destruct (Z.eqb claim_tid tid) eqn:Hclaim_tid.
             ++ apply Z.eqb_eq in Hclaim_tid. subst claim_tid.
                rewrite HRemoved_get in Hclaim_task.
                inversion Hclaim_task; subst claim_t.
                exists table_t', claim_op.
                repeat split; try assumption.
                ** rewrite HUsed_after, Z.eqb_refl.
                   reflexivity.
                ** rewrite Hcompletion_prio.
                   exact Hclaim_prio.
             ++ exists claim_t, claim_op.
                repeat split; try assumption.
                rewrite HUsed_after, Hclaim_tid.
                exact Hclaim_task.
          -- exact I.
        * destruct Hpriotbl as
            [slot_t [Hslot_task Hslot_source]].
          destruct (Z.eqb slot_tid tid) eqn:Hslot_tid.
          -- apply Z.eqb_eq in Hslot_tid. subst slot_tid.
             rewrite HRemoved_get in Hslot_task.
             inversion Hslot_task; subst slot_t.
             exists table_t'.
             split.
             ++ rewrite HUsed_after, Z.eqb_refl.
                reflexivity.
             ++ destruct Hslot_source as
                  [Hslot_prio | Hslot_mutex].
                ** left. rewrite Hcompletion_prio.
                   exact Hslot_prio.
                ** right. rewrite HEvent_frame.
                   exact Hslot_mutex.
          -- exists slot_t.
             split.
             ++ rewrite HUsed_after, Hslot_tid.
                exact Hslot_task.
             ++ destruct Hslot_source as
                  [Hslot_prio | Hslot_mutex].
                ** left. exact Hslot_prio.
                ** right. rewrite HEvent_frame.
                   exact Hslot_mutex.
      + split.
        * unfold
            Ucos2Verify.lib.cross_module_invariants.mutex_owner_consistency
            in Howner |- *.
          intros claim_eid claim_e claim_m Hclaim.
          destruct Hclaim as
            [Hclaim_get [Hclaim_type Hclaim_fields]].
          rewrite HEvent_frame in Hclaim_get.
          specialize
            (Howner claim_eid claim_e claim_m
              (conj Hclaim_get
                (conj Hclaim_type Hclaim_fields))).
          destruct claim_m.(mfOwner) as [claim_tid |]
            eqn:Hclaim_owner_eq.
          -- destruct Howner as
               [claim_t [claim_op
                [Hclaim_task [Hclaim_orig
                  [Hclaim_prio Hclaim_notin]]]]].
             destruct (Z.eqb claim_tid tid) eqn:Hclaim_tid.
             ++ apply Z.eqb_eq in Hclaim_tid. subst claim_tid.
                rewrite HRemoved_get in Hclaim_task.
                inversion Hclaim_task; subst claim_t.
                exists table_t', claim_op.
                repeat split; try assumption.
                ** rewrite HUsed_after, Z.eqb_refl.
                   reflexivity.
                ** rewrite Hcompletion_prio.
                   exact Hclaim_prio.
             ++ exists claim_t, claim_op.
                repeat split; try assumption.
                rewrite HUsed_after, Hclaim_tid.
                exact Hclaim_task.
          -- exact I.
        * split.
          -- unfold
               Ucos2Verify.lib.event_wait.verification_slice_event_wait_object_consistency
               in Hwait |- *.
             destruct Hwait as
               [Hwait_entry [Hwait_refback Hwait_closed]].
             assert (Htarget_not_waiting :
               forall event_id event,
                 removed.(EventState).(inUsedEventStates)
                   event_id = Some event ->
                 ~ In tid event.(waitList)).
             {
               intros event_id event Hevent_lookup Hin_target.
               specialize
                 (Hwait_entry event_id event Hevent_lookup).
               unfold
                 Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency
                 in Hwait_entry.
               destruct Hwait_entry as [_ Hwait_match].
               destruct
                 (Ucos2Verify.lib.event_wait.event_type_to_pend_type
                    event.(eventType))
                 as [event_pend |] eqn:Hevent_pend.
               - specialize (Hwait_match tid Hin_target).
                 destruct Hwait_match as
                   [target_t [Htarget_get
                    [Htarget_event [_ _]]]].
                 rewrite HRemoved_get in Htarget_get.
                 inversion Htarget_get; subst target_t.
                 unfold removed_t in Htarget_event.
                 discriminate.
               - rewrite Hwait_match in Hin_target.
                 contradiction.
             }
             split; [|split].
             ++ intros event_id event Hevent_lookup.
                rewrite HEvent_frame in Hevent_lookup.
                pose proof
                  (Hwait_entry event_id event Hevent_lookup)
                  as Hentry.
                pose proof
                  (Htarget_not_waiting
                     event_id event Hevent_lookup)
                  as Htarget_absent.
                unfold
                  Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency
                  in Hentry |- *.
                destruct Hentry as
                  [[Hwait_nodup [Hwait_sorted Hwait_tasks]]
                   Hwait_match].
                split.
                ** unfold
                     Ucos2Verify.lib.event_wait.event_waitList_canonical.
                   split; [exact Hwait_nodup |].
                   split.
                   --- eapply
                         strictly_sorted_by_key_ext_in__relocation_semantics.
                       +++ intros task_id Hin_task.
                           assert (Hneq : task_id <> tid).
                           {
                             intro Heq. subst task_id.
                             exact (Htarget_absent Hin_task).
                           }
                           unfold Ucos2Verify.lib.event_wait.wait_prio_key.
                           rewrite HUsed_after.
                           apply Z.eqb_neq in Hneq.
                           rewrite Hneq.
                           reflexivity.
                       +++ exact Hwait_sorted.
                   --- intros task_id Hin_task.
                       assert (Hneq : task_id <> tid).
                       {
                         intro Heq. subst task_id.
                         exact (Htarget_absent Hin_task).
                       }
                       destruct
                         (Hwait_tasks task_id Hin_task)
                         as [task [Htask_get Hvalid_prio]].
                       exists task.
                       split; [|exact Hvalid_prio].
                       rewrite HUsed_after.
                       apply Z.eqb_neq in Hneq.
                       rewrite Hneq.
                       exact Htask_get.
                ** destruct
                     (Ucos2Verify.lib.event_wait.event_type_to_pend_type
                        event.(eventType))
                     as [event_pend |] eqn:Hevent_pend.
                   --- intros task_id Hin_task.
                       assert (Hneq : task_id <> tid).
                       {
                         intro Heq. subst task_id.
                         exact (Htarget_absent Hin_task).
                       }
                       specialize (Hwait_match task_id Hin_task).
                       destruct Hwait_match as
                         [task [Htask_get
                          [Htask_event
                           [Htask_multi Htask_pend]]]].
                       exists task.
                       repeat split; try assumption.
                       rewrite HUsed_after.
                       apply Z.eqb_neq in Hneq.
                       rewrite Hneq.
                       exact Htask_get.
                   --- exact Hwait_match.
             ++ unfold
                  Ucos2Verify.lib.event_wait.task_event_reference_backlink_consistency
                  in Hwait_refback |- *.
                intros task_id task event_id event
                  Htask_get Hevent_lookup Href.
                rewrite HUsed_after in Htask_get.
                destruct (Z.eqb task_id tid) eqn:Htask_id.
                ** apply Z.eqb_eq in Htask_id. subst task_id.
                   inversion Htask_get; subst task.
                   rewrite Htable_t' in Href. cbn in Href.
                   destruct Href as [Hnone | Hmulti_ref]; [discriminate|].
                   eapply Hwait_refback.
                   --- exact HRemoved_get.
                   --- rewrite <- HEvent_frame. exact Hevent_lookup.
                   --- right. unfold removed_t. cbn. exact Hmulti_ref.
                ** eapply Hwait_refback.
                   --- exact Htask_get.
                   --- rewrite <- HEvent_frame. exact Hevent_lookup.
                   --- exact Href.
             ++ unfold
                  Ucos2Verify.lib.event_wait.task_event_reference_closure
                  in Hwait_closed |- *.
                intros task_id task Htask_get.
                rewrite HUsed_after in Htask_get.
                destruct (Z.eqb task_id tid) eqn:Htask_id.
                ** apply Z.eqb_eq in Htask_id. subst task_id.
                   inversion Htask_get; subst task.
                   specialize (Hwait_closed tid removed_t HRemoved_get)
                     as [Hsingle Hmulti].
                   split.
                   --- intros event_id Hptr.
                       rewrite Htable_t' in Hptr. cbn in Hptr. discriminate.
                   --- intros event_id Hin.
                       rewrite HEvent_frame. apply Hmulti.
                       rewrite Htable_t' in Hin. unfold removed_t. cbn in *.
                       exact Hin.
                ** rewrite HEvent_frame. exact (Hwait_closed task_id task Htask_get).
          -- split.
             ++ unfold
                  Ucos2Verify.lib.cross_module_invariants.ready_list_completeness.
                exact Hcomplete_after.
             ++ split.
                ** unfold
                     Ucos2Verify.lib.cross_module_invariants.ready_list_order.
                   split; assumption.
                ** split.
                   --- unfold
                         Ucos2Verify.lib.cross_module_invariants.ceiling_priotbl_free
                         in Hceil |- *.
                       rewrite HTable_frame.
                       exact Hceil.
                   --- split.
                       +++ unfold
                             Ucos2Verify.lib.cross_module_invariants.task_priority_unique_prop.
                           exact Hunique_after.
                       +++ split.
                           *** unfold
                                 Ucos2Verify.lib.cross_module_invariants.mutex_protocol_consistency
                                 in Hprotocol |- *.
                               intros event_id event mutex
                                 Hevent_lookup Hevent_type
                                 Hevent_fields.
                               rewrite HEvent_frame
                                 in Hevent_lookup.
                               specialize
                                 (Hprotocol event_id event mutex
                                   Hevent_lookup Hevent_type
                                   Hevent_fields).
                               rewrite HTable_frame.
                               exact Hprotocol.
                           *** unfold
                                 Ucos2Verify.lib.cross_module_invariants.mutex_enabled_pcp_unique
                                 in Hpcp_unique |- *.
                               intros event_id1 event1 mutex1
                                 event_id2 event2 mutex2
                                 Hevent1 Htype1 Hfields1
                                 Hevent2 Htype2 Hfields2
                                 Hpcp Henabled.
                               rewrite HEvent_frame in Hevent1, Hevent2.
                               eapply Hpcp_unique; eassumption.
  }
  exact
    (conj Htask_after
      (conj Hsched_after (conj Hevent_after Hcross_after))).
Qed.
Lemma mutex_post_disinherit_event_frame__return_semantics :
  forall sg m cur_tid entry post,
    OSMutexPost_disinherit_sem sg m cur_tid entry post ->
    post.(EventState) = entry.(EventState).
Proof.
  intros sg m cur_tid entry post Hstep.
  unfold OSMutexPost_disinherit_sem in Hstep.
  destruct Hstep as
    [cur_t [Hcur
      [[Hdisabled Heq] |
       [[Henabled [Hnot_pcp Heq]] |
        [Henabled [Hat_pcp [orig [Horig Hexec]]]]]]]].
  - subst post. reflexivity.
  - subst post. reflexivity.
  - unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
    destruct Hexec as
      [new_t [Hcurrent [Hcurrent_prio [Hlookup
       [Hlo [Hhi [Hnew_t Hpost]]]]]]].
    cbv zeta in Hpost.
    subst post.
    reflexivity.
Qed.
Lemma mutex_post_disinherit_owner_not_pending__return_semantics :
  forall sg pevent entry pcp owner_orig disinherited,
    UCOS2_verification_slice_state_inv sg entry ->
    UCOS2_verification_slice_state_inv sg disinherited ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig disinherited ->
    exists eid e m owner owner_t,
      pevent = event_addr sg eid /\
      disinherited.(EventState).(inUsedEventStates) eid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e.(mutexFields) = Some m /\
      m.(mfOwner) = Some owner /\
      m.(mfPCP) = pcp /\
      m.(mfOwnerOrigPrio) = Some owner_orig /\
      disinherited.(TskState).(inUsedTaskStates) owner = Some owner_t /\
      owner_t.(curPrio) = owner_orig /\
      (task_non_suspension_bits owner_t.(stat)) = 0.
Proof.
  intros sg pevent entry pcp owner_orig disinherited
    Hentry_valid Hdisinherited_valid Hstage.
  pose proof Hstage as Hstage_copy.
  pose proof
    (mutex_post_disinherit_owner_restored__return_semantics
       sg pevent entry pcp owner_orig disinherited
       Hentry_valid Hstage)
    as Howner_restored.
  destruct Howner_restored as
    (eid & e & m & owner & owner_t &
     Hpevent & Hevent & Htype & Hfields & Howner &
     Hpcp & Horig & Howner_t & Howner_prio).
  unfold mutex_post_owner_disinherit_stage_prop in Hstage_copy.
  destruct Hstage_copy as
    [Hchecked [Hboundary
      [eid0 [e0 [m0 [cur_tid
       [Hpevent0 [Hevent0 [Htype0 [Hfields0
        [Howner0 [Hpcp0 [Horig0 [Hcurrent Hdisinherit]]]]]]]]]]]]]].
  assert (Heid : eid0 = eid).
  {
    apply event_addr_injective with (sg := sg).
    transitivity pevent.
    - symmetry; exact Hpevent0.
    - exact Hpevent.
  }
  subst eid0.
  pose proof
    (mutex_post_disinherit_event_frame__return_semantics
       sg m0 cur_tid entry disinherited Hdisinherit)
    as Hevent_frame.
  rewrite Hevent_frame in Hevent.
  rewrite Hevent in Hevent0.
  inversion Hevent0; subst e0.
  rewrite Hfields in Hfields0.
  inversion Hfields0; subst m0.
  rewrite Howner in Howner0.
  inversion Howner0; subst cur_tid.
  assert (Hcall :
    sched_task_call_boundary entry.(TskState) entry.(SchedState)).
  {
    eapply mutex_post_owner_disinherit_stage_task_call_boundary.
    exact Hstage.
  }
  unfold sched_task_call_boundary in Hcall.
  destruct Hcall as
    [Hrunning [boundary_tid [boundary_t Hready]]].
  unfold sched_current_ready_at in Hready.
  destruct Hready as
    [Hboundary_get [Hboundary_current
     [Hboundary_prio [Hin_ready Heffective]]]].
  rewrite Hcurrent in Hboundary_current.
  inversion Hboundary_current; subst boundary_tid.
  assert (Hentry_pend :
    (task_non_suspension_bits boundary_t.(stat)) = 0).
  {
    unfold is_effectively_ready in Heffective.
    destruct (task_non_suspension_bits boundary_t.(stat)); try discriminate.
    reflexivity.
  }
  assert (Hpend_none : (task_non_suspension_bits owner_t.(stat)) = 0).
  {
    unfold OSMutexPost_disinherit_sem in Hdisinherit.
    destruct Hdisinherit as
      [cur_t [Hcur
        [[Hdisabled Heq] |
         [[Henabled [Hnot_pcp Heq]] |
          [Henabled [Hat_pcp [orig [Horig_step Hexec]]]]]]]].
    - subst disinherited.
      rewrite Howner_t in Hboundary_get.
      inversion Hboundary_get; subst owner_t.
      exact Hentry_pend.
    - subst disinherited.
      rewrite Howner_t in Hboundary_get.
      inversion Hboundary_get; subst owner_t.
      exact Hentry_pend.
    - rewrite Hcur in Hboundary_get.
      inversion Hboundary_get; subst boundary_t.
      unfold atomic_task_set_curPrio_current_literal_exec in Hexec.
      destruct Hexec as
        [new_t [Hexec_current [Hexec_prio [Hexec_get
         [Hlo [Hhi [Hnew_t Hpost]]]]]]].
      cbv zeta in Hpost.
      subst disinherited.
      cbn in Howner_t.
      rewrite Z.eqb_refl in Howner_t.
      inversion Howner_t; subst owner_t.
      subst new_t.
      exact Hentry_pend.
  }
  exists eid, e, m, owner, owner_t.
  repeat split; try assumption.
  rewrite Hevent_frame.
  exact Hevent.
Qed.
Lemma mutex_post_reservation_preserves_validity__return_semantics :
  forall sg mid before reserved e m owner owner_t orig,
    UCOS2_verification_slice_state_inv sg before ->
    before.(EventState).(inUsedEventStates) mid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some owner ->
    before.(TskState).(inUsedTaskStates) owner = Some owner_t ->
    m.(mfOwnerOrigPrio) = Some orig ->
    owner_t.(curPrio) = orig ->
    (task_non_suspension_bits owner_t.(stat)) = 0 ->
    OSMutexPost_reservation_sem sg mid before reserved ->
    UCOS2_verification_slice_state_inv sg reserved.
Proof.
  intros sg mid before reserved e m owner owner_t orig
    Hvalid Hevent Htype Hfields Howner Howner_t Horig Howner_prio
    Howner_pend Hreservation.
  pose proof Hvalid as Hvalid_copy.
  pose proof Hreservation as Hreservation_copy.
  assert (Htask_reserved :
    verification_slice_task_validity sg reserved.(TskState)).
  {
    eapply mutex_post_reservation_task_validity__return_semantics;
      eassumption.
  }
  destruct Hvalid as [Htask [Hsched [Hevent_valid Hcross]]].
  unfold OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (e1 & m1 & owner1 & tsk_reserved &
     Hevent1 & Htype1 & Hfields1 & Howner1 &
     Htsk_reserved & Hreserved).
  rewrite Hevent in Hevent1.
  inversion Hevent1; subst e1.
  rewrite Hfields in Hfields1.
  inversion Hfields1; subst m1.
  rewrite Howner in Howner1.
  inversion Howner1; subst owner1.
  subst reserved.
  assert (Hsched_reserved :
    verification_slice_sched_in_range sg
      (replace_TskS tsk_reserved before).(TskState)
      (replace_TskS tsk_reserved before).(SchedState)).
  {
    rewrite replace_TskS_TskState, replace_TskS_other_Sched,
      Htsk_reserved.
    cbn.
    exact Hsched.
  }
  assert (Hevent_reserved :
    verification_slice_event_in_range sg
      (replace_TskS tsk_reserved before).(TskState)
      (replace_TskS tsk_reserved before).(EventState)).
  {
    unfold verification_slice_event_in_range in *.
    rewrite replace_TskS_TskState, replace_TskS_other_Event,
      Htsk_reserved.
    cbn.
    exact Hevent_valid.
  }
  set (e_clear :=
    {| eventGeneration := e.(eventGeneration);
       eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
       eventType := e.(eventType);
       mutexFields :=
         Some {| mfPCP := m.(mfPCP);
                 mfOwner := None;
                 mfOwnerOrigPrio := None |};
       semFields := e.(semFields);
       mboxFields := e.(mboxFields);
       queueFields := e.(queueFields);
       waitList := e.(waitList) |}).
  set (m_clear :=
    {| mfPCP := m.(mfPCP);
       mfOwner := None;
       mfOwnerOrigPrio := None |}).
  set (cleared :=
    replace_TskS tsk_reserved
      (replace_EventS
        (Ucos2Verify.lib.cross_module_invariants.owner_release_update
          before.(EventState) mid e m.(mfPCP))
        before)).
  assert (Hcross_cleared :
    Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      sg cleared).
  {
    unfold cleared.
    rewrite Htsk_reserved.
    eapply
      Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency_preserved_by_release.
    - exact Hevent.
    - exact Htype.
    - exact Hfields.
    - exact Howner.
    - exact Howner_t.
    - exact Horig.
    - exact Howner_prio.
    - reflexivity.
    - exact Hcross.
  }
  assert (Hclear_event :
    cleared.(EventState).(inUsedEventStates) mid = Some e_clear).
  {
    unfold cleared, e_clear,
      Ucos2Verify.lib.cross_module_invariants.owner_release_update,
      update_event_field_raw.
    cbn.
    rewrite Z.eqb_refl.
    reflexivity.
  }
  assert (Hclear_fields : e_clear.(mutexFields) = Some m_clear).
  {
    unfold e_clear, m_clear.
    reflexivity.
  }
  assert (Hclear_task :
    cleared.(TskState).(inUsedTaskStates) owner = Some owner_t).
  {
    unfold cleared.
    rewrite replace_TskS_TskState, Htsk_reserved.
    cbn.
    exact Howner_t.
  }
  assert (Horig_valid : valid_task_prio sg orig).
  {
    destruct Htask as [Htask_range Htask_fields].
    pose proof (Htask_fields owner owner_t Howner_t)
      as [Hvalid_prio Hderived].
    rewrite Howner_prio in Hvalid_prio.
    exact Hvalid_prio.
  }
  assert (Hregistered_cleared :
    task_current_prio_registered cleared.(TskState)).
  {
    pose proof Htask_reserved as Htask_parts.
    unfold verification_slice_task_validity, verification_slice_task_in_range,
      verification_slice_task_in_range in Htask_parts.
    destruct Htask_parts as
      [[Hids [Hfree_nodup [Hfree_range [Hfree_unused
        [Htable_live [Hregistered Hunique]]]]]] Hderived].
    unfold cleared.
    rewrite replace_TskS_TskState.
    exact Hregistered.
  }
  set (acquired :=
    replace_EventS
      (Ucos2Verify.lib.cross_module_invariants.owner_acquire_update
        cleared.(EventState) mid e_clear m_clear owner orig)
      cleared).
  assert (Hcross_acquired :
    Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      sg acquired).
  {
    unfold acquired.
    eapply
      Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency_preserved_by_acquire.
    - exact Hclear_event.
    - unfold e_clear. exact Htype.
    - exact Hclear_fields.
    - unfold m_clear. reflexivity.
    - exact Hclear_task.
    - exact Howner_prio.
    - exact Howner_pend.
    - exact Horig_valid.
    - exact Hregistered_cleared.
    - exact Hcross_cleared.
  }
  assert (Hm_restore :
    {| mfPCP := m.(mfPCP);
       mfOwner := Some owner;
       mfOwnerOrigPrio := Some orig |} = m).
  {
    destruct m as [pcp old_owner old_orig].
    cbn in Howner, Horig |- *.
    subst old_owner old_orig.
    reflexivity.
  }
  assert (He_restore :
    {| eventGeneration := e.(eventGeneration);
       eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
       eventType := e.(eventType);
       mutexFields :=
         Some {| mfPCP := m.(mfPCP);
                 mfOwner := Some owner;
                 mfOwnerOrigPrio := Some orig |};
       semFields := e.(semFields);
       mboxFields := e.(mboxFields);
       queueFields := e.(queueFields);
       waitList := e.(waitList) |} = e).
  {
    rewrite Hm_restore.
    destruct e as
      [etype mutex_fields sem_fields mbox_fields queue_fields wait_list].
    cbn in Hfields |- *.
    subst mutex_fields.
    reflexivity.
  }
  assert (Hacquired_eq :
    acquired = replace_TskS tsk_reserved before).
  {
    unfold acquired, cleared,
      Ucos2Verify.lib.cross_module_invariants.owner_acquire_update,
      Ucos2Verify.lib.cross_module_invariants.owner_release_update,
      e_clear, m_clear.
    cbn.
    rewrite He_restore.
    rewrite update_event_field_raw_same__return_semantics.
    rewrite update_event_field_raw_existing__return_semantics;
      [reflexivity | exact Hevent].
  }
  rewrite Hacquired_eq in Hcross_acquired.
  exact
    (conj Htask_reserved
      (conj Hsched_reserved
        (conj Hevent_reserved Hcross_acquired))).
Qed.
Lemma verification_slice_event_in_range_preserved_by_owner_replace__return_semantics :
  forall sg tskSt evSt mid e1 m1 tid origPrio,
    valid_stable_glob_vars sg ->
    evSt.(inUsedEventStates) mid = Some e1 ->
    e1.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e1.(mutexFields) = Some m1 ->
    valid_task_prio sg origPrio ->
    verification_slice_event_in_range sg tskSt evSt ->
    verification_slice_event_in_range sg tskSt
      (Ucos2Verify.lib.cross_module_invariants.owner_acquire_update
         evSt mid e1 m1 tid origPrio).
Proof.
  intros sg tskSt evSt mid e1 m1 tid origPrio
    Hstable Hget Htype Hfields Hprio Hin.
  unfold verification_slice_event_in_range in *.
  destruct Hin as
    [Hids [Hfree_nodup [Hfree_range [Hpartition
      [Hfield_consistency [Hpayload
        [Hqueue_unique Hwait_entry]]]]]]].
  unfold Ucos2Verify.lib.cross_module_invariants.owner_acquire_update,
    update_event_field_raw.
  cbn.
  split.
  - intros eid e Hget'.
    destruct (Z.eqb eid mid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid.
      inversion Hget'; subst.
      exact (Hids mid e1 Hget).
    + exact (Hids eid e Hget').
  - split; [exact Hfree_nodup |].
    split; [exact Hfree_range |].
    split.
    + eapply event_slot_partition_preserved_some_to_some;
        eassumption.
    + split.
      * intros eid e Hget'.
        destruct (Z.eqb eid mid) eqn:Heq.
        -- apply Z.eqb_eq in Heq. subst eid.
           inversion Hget'; subst.
           unfold event_fields_consistency.
           rewrite Htype.
           assert (Hselected :
             event_fields_consistency e1).
           {
             exact (Hfield_consistency mid e1 Hget).
           }
           unfold event_fields_consistency in Hselected.
           rewrite Htype in Hselected.
           destruct Hselected as
             [Hmutex [Hsem [Hmbox Hqueue]]].
           repeat split;
             [discriminate | exact Hsem | exact Hmbox |
              exact Hqueue].
        -- exact (Hfield_consistency eid e Hget').
      * split.
        -- intros eid e Hget'.
           destruct (Z.eqb eid mid) eqn:Heq.
           ++ apply Z.eqb_eq in Heq. subst eid.
              inversion Hget'; subst.
              unfold event_payload_consistency.
              rewrite Htype.
              cbn.
              split.
              ** unfold mutex_fields_consistency.
                 cbn.
                 destruct Hprio as [Hprio_lo Hprio_hi].
                 split; [exact Hprio_lo |].
                 split; [exact Hprio_hi |].
                 eapply valid_task_prio_ne_ceil.
                 --- exact Hstable.
                 --- split; assumption.
              ** intro Hnone. discriminate.
           ++ exact (Hpayload eid e Hget').
        -- split.
           ++ eapply queue_binding_unique_update_same_binding.
              ** exact Hget.
              ** unfold event_queue_id.
                 rewrite Htype.
                 reflexivity.
              ** exact Hqueue_unique.
           ++ intros eid e Hget'.
              destruct (Z.eqb eid mid) eqn:Heq.
              ** apply Z.eqb_eq in Heq. subst eid.
                 inversion Hget'; subst.
                 eapply
                   (Ucos2Verify.lib.cross_module_invariants.verification_slice_event_wait_entry_consistency_irrelevant_fields
                      sg tskSt mid e1).
                 --- reflexivity.
                 --- reflexivity.
                 --- exact (Hwait_entry mid e1 Hget).
              ** exact (Hwait_entry eid e Hget').
Qed.
Lemma mutex_post_reservation_wake_reapply_eq__return_semantics :
  forall sg eid before reserved wake returned_prio
         canonical_waiter table_owner e m,
    before.(EventState).(inUsedEventStates) eid = Some e ->
    e.(mutexFields) = Some m ->
    OSMutexPost_reservation_sem sg eid before reserved ->
    OSMutexPost_wake_sem
      sg eid reserved returned_prio
      canonical_waiter table_owner wake ->
    {|
      inUsedTaskStates := wake.(TskState).(inUsedTaskStates);
      unUsedTaskStates := wake.(TskState).(unUsedTaskStates);
      tcbListHead := wake.(TskState).(tcbListHead);
      prioTbl := fun p =>
        if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
            Z.eqb p m.(mfPCP))%bool
        then PTReserved
        else wake.(TskState).(prioTbl) p;
      taskRegNextID := wake.(TskState).(taskRegNextID);
      parkedTaskStacks := wake.(TskState).(parkedTaskStacks);
      taskLifecycle := wake.(TskState).(taskLifecycle);
     taskCount := wake.(TskState).(taskCount)
    |} = wake.(TskState).
Proof.
  intros sg eid before reserved wake returned_prio
    canonical_waiter table_owner e m
    Hevent Hfields Hreservation Hwake.
  unfold OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (e1 & m1 & owner & tsk_reserved &
     Hevent1 & Htype1 & Hfields1 & Howner &
     Htsk_reserved & Hreserved).
  rewrite Hevent in Hevent1.
  inversion Hevent1; subst e1.
  rewrite Hfields in Hfields1.
  inversion Hfields1; subst m1.
  unfold OSMutexPost_wake_sem, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (wake_e1 & wake_e2 & canonical_t & table_t & table_t' &
     Hwake_event & Hpend & Hwait & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & Hwake_e2 &
     Hwake_post).
  subst reserved.
  subst tsk_reserved.
  subst wake.
  cbn.
  f_equal.
  apply functional_extensionality.
  intro p.
  destruct
    (negb (mfPCP m =? osPrioMutexCeilDis sg) &&
     (p =? mfPCP m))%bool;
    reflexivity.
Qed.
Lemma mutex_post_commits_refine_owner_replace__return_semantics :
  forall eid returned_prio table_owner wake counted final,
    OSMutexPost_count_commit_sem
      eid returned_prio wake counted ->
    OSMutexPost_owner_commit_sem
      eid returned_prio table_owner counted final ->
    exists e m,
      wake.(EventState).(inUsedEventStates) eid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e.(mutexFields) = Some m /\
      wake.(TskState).(prioTbl) returned_prio =
        PTTask table_owner /\
      final =
        replace_EventS
          (Ucos2Verify.lib.cross_module_invariants.owner_acquire_update
            wake.(EventState) eid e m table_owner returned_prio)
          wake.
Proof.
  intros eid returned_prio table_owner wake counted final
    Hcount Howner_commit.
  unfold OSMutexPost_count_commit_sem in Hcount.
  destruct Hcount as
    (e1 & e2 & m1 & m2 &
     Hevent1 & Htype1 & Hfields1 & Hm2 & He2 & Hcounted).
  unfold OSMutexPost_owner_commit_sem in Howner_commit.
  destruct Howner_commit as
    [Htable_counted
      [e3 [e4 [m3 [m4
       [Hevent3 [Htype3 [Hfields3 [Hm4 [He4
        [Hfinal Htable_final]]]]]]]]]]].
  subst m2.
  subst e2.
  subst counted.
  cbn in Hevent3, Htable_counted.
  unfold update_event_field_raw in Hevent3.
  cbn in Hevent3.
  rewrite Z.eqb_refl in Hevent3.
  inversion Hevent3; subst e3.
  cbn in Hfields3.
  inversion Hfields3; subst m3.
  subst m4.
  subst e4.
  exists e1, m1.
  repeat split; try assumption.
  unfold Ucos2Verify.lib.cross_module_invariants.owner_acquire_update.
  cbn in Hfinal.
  rewrite update_event_field_raw_same__return_semantics in Hfinal.
  exact Hfinal.
Qed.
Lemma mutex_post_reservation_wake_mutex_fields__return_semantics :
  forall sg eid before reserved wake returned_prio
         canonical_waiter table_owner e m wake_e wake_m,
    before.(EventState).(inUsedEventStates) eid = Some e ->
    e.(mutexFields) = Some m ->
    OSMutexPost_reservation_sem sg eid before reserved ->
    OSMutexPost_wake_sem
      sg eid reserved returned_prio
      canonical_waiter table_owner wake ->
    wake.(EventState).(inUsedEventStates) eid = Some wake_e ->
    wake_e.(mutexFields) = Some wake_m ->
    wake_m = m.
Proof.
  intros sg eid before reserved wake returned_prio
    canonical_waiter table_owner e m wake_e wake_m
    Hevent Hfields Hreservation Hwake Hwake_event Hwake_fields.
  unfold OSMutexPost_reservation_sem in Hreservation.
  destruct Hreservation as
    (e1 & m1 & owner & tsk_reserved &
     Hevent1 & Htype1 & Hfields1 & Howner &
     Htsk_reserved & Hreserved).
  rewrite Hevent in Hevent1.
  inversion Hevent1; subst e1.
  rewrite Hfields in Hfields1.
  inversion Hfields1; subst m1.
  unfold OSMutexPost_wake_sem, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (e2 & e3 & canonical_t & table_t & table_t' &
     Hevent2 & Hpend & Hwait & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & He3 & Hpost).
  subst reserved.
  cbn in Hevent2.
  rewrite Hevent in Hevent2.
  inversion Hevent2; subst e2.
  subst wake.
  cbn in Hwake_event.
  unfold update_event_field_raw in Hwake_event.
  cbn in Hwake_event.
  rewrite Z.eqb_refl in Hwake_event.
  inversion Hwake_event; subst wake_e.
  subst e3.
  cbn in Hwake_fields.
  rewrite Hfields in Hwake_fields.
  inversion Hwake_fields.
  reflexivity.
Qed.
Lemma mutex_post_handover_commits_preserve_validity__return_semantics :
  forall sg eid before reserved wake counted final returned_prio
         canonical_waiter table_owner e m old_owner,
    valid_stable_glob_vars sg ->
    UCOS2_verification_slice_state_inv sg reserved ->
    UCOS2_verification_slice_state_inv sg wake ->
    before.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some old_owner ->
    OSMutexPost_reservation_sem sg eid before reserved ->
    OSMutexPost_wake_sem
      sg eid reserved returned_prio
      canonical_waiter table_owner wake ->
    OSMutexPost_count_commit_sem
      eid returned_prio wake counted ->
    OSMutexPost_owner_commit_sem
      eid returned_prio table_owner counted final ->
    UCOS2_verification_slice_state_inv sg final.
Proof.
  intros sg eid before reserved wake counted final returned_prio
    canonical_waiter table_owner e m old_owner
    Hstable Hvalid_reserved Hvalid_wake Hevent Htype Hfields Howner
    Hreservation Hwake Hcount Howner_commit.
  pose proof Hvalid_wake as Hvalid_wake_copy.
  destruct Hvalid_wake as
    [Htask [Hsched [Hevent_valid Hcross]]].
  pose proof
    (mutex_post_commits_refine_owner_replace__return_semantics
       eid returned_prio table_owner wake counted final
       Hcount Howner_commit)
    as Hcommits.
  destruct Hcommits as
    (wake_e & wake_m & Hwake_event & Hwake_type &
     Hwake_fields & Htable_final & Hfinal).
  assert (Hwake_m : wake_m = m).
  {
    exact
      (mutex_post_reservation_wake_mutex_fields__return_semantics
         sg eid before reserved wake returned_prio
         canonical_waiter table_owner e m wake_e wake_m
         Hevent Hfields Hreservation Hwake
         Hwake_event Hwake_fields).
  }
  subst wake_m.
  assert (Htable_task :
    exists table_t',
      wake.(TskState).(inUsedTaskStates) table_owner =
        Some table_t' /\
      table_t'.(curPrio) = returned_prio /\
      (task_non_suspension_bits table_t'.(stat)) = 0).
  {
    unfold OSMutexPost_wake_sem, atomic_event_task_rdy,
      atomic_event_task_rdy_one in Hwake.
    destruct Hwake as
      (wake_e1 & wake_e2 & canonical_t & table_t & table_t' &
       Hwake_e1 & Hpend & Hwait & Hcanonical &
       Hcanonical_get & Hreturned & Htable_slot &
       Htable_get & Htable_prio & Htable_t' & Hwake_e2 &
       Hwake_post).
    destruct Hvalid_reserved as [[Htask_range _] [_ [_ Hcross_reserved]]].
    destruct Htask_range as [_ [_ [_ [_ [_ [_ Hunique_reserved]]]]]].
    assert (Hidentity : table_owner = canonical_waiter).
    {
      eapply Hunique_reserved.
      - exact Htable_get.
      - exact Hcanonical_get.
      - rewrite Htable_prio, Hreturned. reflexivity.
    }
    assert (Hin_wait : In table_owner wake_e1.(waitList)).
    {
      rewrite Hidentity.
      destruct wake_e1.(waitList) as [|head tail] eqn:Hwait_list.
      - exfalso. apply Hwait. reflexivity.
      - cbn in Hcanonical. subst canonical_waiter. left. reflexivity.
    }
    unfold Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      in Hcross_reserved.
    destruct Hcross_reserved as [_ [_ [_ [Hwait_consistency _]]]].
    unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_object_consistency
      in Hwait_consistency.
    destruct Hwait_consistency as [Hwait_entry _].
    specialize (Hwait_entry eid wake_e1 Hwake_e1).
    unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency
      in Hwait_entry.
    destruct Hwait_entry as [_ Hwait_match].
    rewrite Hpend in Hwait_match.
    destruct (Hwait_match table_owner Hin_wait) as
      [wait_t [Hwait_get [_ [_ Hwait_mask]]]].
    rewrite Htable_get in Hwait_get.
    inversion Hwait_get; subst wait_t.
    exists table_t'.
    split.
    - rewrite Hwake_post.
      cbn.
      rewrite Z.eqb_refl.
      reflexivity.
    - split.
      + rewrite Htable_t'.
        cbn.
        exact Htable_prio.
      + rewrite Htable_t'.
        change (task_non_suspension_bits
          (task_clear_pending_status table_t.(stat) PendMutex) = 0).
        apply task_clear_pending_status_same_kind.
        exact Hwait_mask.
  }
  destruct Htable_task as
    [new_owner_t [Hnew_owner_get
      [Hnew_owner_prio Hnew_owner_pend]]].
  assert (Hreturned_valid : valid_task_prio sg returned_prio).
  {
    destruct Htask as [Htask_range Htask_fields].
    pose proof
      (Htask_fields table_owner new_owner_t Hnew_owner_get)
      as [Hvalid_prio Hderived].
    rewrite Hnew_owner_prio in Hvalid_prio.
    exact Hvalid_prio.
  }
  assert (Hregistered :
    task_current_prio_registered wake.(TskState)).
  {
    pose proof Htask as Htask_parts.
    unfold verification_slice_task_validity, verification_slice_task_in_range,
      verification_slice_task_in_range in Htask_parts.
    destruct Htask_parts as
      [[Hids [Hfree_nodup [Hfree_range [Hfree_unused
        [Htable_live [Hregistered Hunique]]]]]] Hderived].
    exact Hregistered.
  }
  assert (Htask_final :
    verification_slice_task_validity sg final.(TskState)).
  {
    rewrite Hfinal, replace_EventS_other_Tsk.
    exact Htask.
  }
  assert (Hsched_final :
    verification_slice_sched_in_range sg final.(TskState) final.(SchedState)).
  {
    rewrite Hfinal, replace_EventS_other_Tsk,
      replace_EventS_other_Sched.
    exact Hsched.
  }
  assert (Hevent_final :
    verification_slice_event_in_range
      sg final.(TskState) final.(EventState)).
  {
    unfold verification_slice_event_in_range in *.
    rewrite Hfinal, replace_EventS_other_Tsk,
      replace_EventS_EventState.
    eapply verification_slice_event_in_range_preserved_by_owner_replace__return_semantics.
    - exact Hstable.
    - exact Hwake_event.
    - exact Hwake_type.
    - exact Hwake_fields.
    - exact Hreturned_valid.
    - exact Hevent_valid.
  }
  pose proof Hcross as Hcross_owner.
  unfold Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
    in Hcross_owner.
  destruct Hcross_owner as
    [Hosprio [Hpriotbl [Hmutex_owner Hcross_rest]]].
  unfold Ucos2Verify.lib.cross_module_invariants.mutex_owner_consistency
    in Hmutex_owner.
  specialize
    (Hmutex_owner eid wake_e m
      (conj Hwake_event (conj Hwake_type Hwake_fields))).
  rewrite Howner in Hmutex_owner.
  destruct Hmutex_owner as
    [old_owner_t [old_orig
      [Hold_owner_get [Hold_orig
        [Hold_owner_prio Hold_owner_notin]]]]].
  set (tsk_released :=
    {|
      inUsedTaskStates := wake.(TskState).(inUsedTaskStates);
      unUsedTaskStates := wake.(TskState).(unUsedTaskStates);
      tcbListHead := wake.(TskState).(tcbListHead);
      prioTbl := fun p =>
        if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
            Z.eqb p m.(mfPCP))%bool
        then PTReserved
        else wake.(TskState).(prioTbl) p;
      taskRegNextID := wake.(TskState).(taskRegNextID);
      parkedTaskStacks := wake.(TskState).(parkedTaskStacks);
      taskLifecycle := wake.(TskState).(taskLifecycle);
     taskCount := wake.(TskState).(taskCount)
    |}).
  assert (Htsk_released : tsk_released = wake.(TskState)).
  {
    unfold tsk_released.
    exact
      (mutex_post_reservation_wake_reapply_eq__return_semantics
         sg eid before reserved wake returned_prio
         canonical_waiter table_owner e m
         Hevent Hfields Hreservation Hwake).
  }
  assert (Hold_owner_prio_exact :
    old_owner_t.(curPrio) = old_orig).
  {
    destruct Hold_owner_prio as
      [Hrestored | [Henabled Hboosted]].
    - exact Hrestored.
    - exfalso.
      pose proof
        (Hregistered old_owner old_owner_t Hold_owner_get)
        as Hregistered_old.
      rewrite Hboosted in Hregistered_old.
      pose proof
        (f_equal
          (fun st => st.(prioTbl) m.(mfPCP))
          Htsk_released)
        as Hreserved_slot.
      unfold tsk_released in Hreserved_slot.
      cbn in Hreserved_slot.
      apply Z.eqb_neq in Henabled.
      rewrite Henabled, Z.eqb_refl in Hreserved_slot.
      cbn in Hreserved_slot.
      rewrite Hregistered_old in Hreserved_slot.
      discriminate.
  }
  set (cleared :=
    replace_EventS
      (Ucos2Verify.lib.cross_module_invariants.owner_release_update
        wake.(EventState) eid wake_e m.(mfPCP))
      wake).
  assert (Hcross_cleared :
    Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      sg cleared).
  {
    pose proof
      (Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency_preserved_by_release
        sg wake eid wake_e m old_owner old_owner_t
        old_orig m.(mfPCP)
        Hwake_event Hwake_type Hwake_fields Howner
        Hold_owner_get Hold_orig Hold_owner_prio_exact eq_refl Hcross)
      as Hreleased.
    change
      (Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency sg
        (replace_TskS tsk_released
          (replace_EventS
            (Ucos2Verify.lib.cross_module_invariants.owner_release_update
              wake.(EventState) eid wake_e m.(mfPCP))
            wake)))
      in Hreleased.
    rewrite Htsk_released in Hreleased.
    unfold cleared.
    destruct wake.
    exact Hreleased.
  }
  set (m_clear :=
    {| mfPCP := m.(mfPCP);
       mfOwner := None;
       mfOwnerOrigPrio := None |}).
  set (e_clear :=
    {| eventGeneration := wake_e.(eventGeneration);
       eventName := wake_e.(eventName);
     eventPadding1 := wake_e.(eventPadding1);
     eventPadding2 := wake_e.(eventPadding2);
     eventPadding3 := wake_e.(eventPadding3);
     eventPadding19 := wake_e.(eventPadding19);
       eventType := wake_e.(eventType);
       mutexFields := Some m_clear;
       semFields := wake_e.(semFields);
       mboxFields := wake_e.(mboxFields);
       queueFields := wake_e.(queueFields);
       waitList := wake_e.(waitList) |}).
  assert (Hclear_event :
    cleared.(EventState).(inUsedEventStates) eid =
      Some e_clear).
  {
    unfold cleared, e_clear, m_clear,
      Ucos2Verify.lib.cross_module_invariants.owner_release_update,
      update_event_field_raw.
    cbn.
    rewrite Z.eqb_refl.
    reflexivity.
  }
  assert (Hclear_task :
    cleared.(TskState).(inUsedTaskStates) table_owner =
      Some new_owner_t).
  {
    unfold cleared.
    rewrite replace_EventS_other_Tsk.
    exact Hnew_owner_get.
  }
  assert (Hregistered_cleared :
    task_current_prio_registered cleared.(TskState)).
  {
    unfold cleared.
    rewrite replace_EventS_other_Tsk.
    exact Hregistered.
  }
  set (acquired :=
    replace_EventS
      (Ucos2Verify.lib.cross_module_invariants.owner_acquire_update
        cleared.(EventState) eid e_clear m_clear
        table_owner returned_prio)
      cleared).
  assert (Hcross_acquired :
    Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      sg acquired).
  {
    unfold acquired.
    eapply
      Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency_preserved_by_acquire.
    - exact Hclear_event.
    - unfold e_clear. exact Hwake_type.
    - unfold e_clear. reflexivity.
    - unfold m_clear. reflexivity.
    - exact Hclear_task.
    - exact Hnew_owner_prio.
    - exact Hnew_owner_pend.
    - exact Hreturned_valid.
    - exact Hregistered_cleared.
    - exact Hcross_cleared.
  }
  assert (Hacquired :
    acquired =
      replace_EventS
        (Ucos2Verify.lib.cross_module_invariants.owner_acquire_update
          wake.(EventState) eid wake_e m
          table_owner returned_prio)
        wake).
  {
    unfold acquired, cleared,
      Ucos2Verify.lib.cross_module_invariants.owner_acquire_update,
      Ucos2Verify.lib.cross_module_invariants.owner_release_update,
      e_clear, m_clear.
    cbn.
    rewrite update_event_field_raw_same__return_semantics.
    reflexivity.
  }
  rewrite <- Hfinal in Hacquired.
  rewrite Hacquired in Hcross_acquired.
  exact
    (conj Htask_final
      (conj Hsched_final
        (conj Hevent_final Hcross_acquired))).
Qed.
Lemma mutex_post_handover_validity__return_semantics :
  forall sg pevent eid entry disinherited handover
         pcp owner_orig returned_prio
         canonical_waiter table_owner,
    valid_stable_glob_vars sg ->
    UCOS2_verification_slice_state_inv sg entry ->
    pevent = event_addr sg eid ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig disinherited ->
    mutex_post_handover_step_prop
      sg eid disinherited returned_prio
      canonical_waiter table_owner handover ->
    OSMutexPost_relocations_legal sg pevent entry ->
    UCOS2_verification_slice_state_inv sg handover.
Proof.
  intros sg pevent eid entry disinherited handover
    pcp owner_orig returned_prio canonical_waiter table_owner
    Hstable Hentry_valid Hpevent Hstage Hhandover Hrelocations.
  pose proof Hstage as Hstage_copy.
  unfold mutex_post_owner_disinherit_stage_prop in Hstage_copy.
  destruct Hstage_copy as
    [Hchecked [Hboundary
      [stage_eid [stage_e [stage_m [stage_owner
       [Hstage_pevent [Hstage_event [Hstage_type
        [Hstage_fields [Hstage_owner [Hstage_pcp
         [Hstage_orig [Hstage_current Hdisinherit]]]]]]]]]]]]]].
  assert (Heid : stage_eid = eid).
  {
    eapply mutex_post_stage_event_id_eq__return_semantics;
      eassumption.
  }
  subst stage_eid.
  pose proof
    (mutex_post_disinherit_validity__return_semantics
       sg pevent entry pcp owner_orig disinherited
       Hstable Hentry_valid Hstage Hrelocations)
    as Hdisinherited_valid.
  pose proof
    (mutex_post_disinherit_owner_not_pending__return_semantics
       sg pevent entry pcp owner_orig disinherited
       Hentry_valid Hdisinherited_valid Hstage)
    as Howner_info.
  destruct Howner_info as
    (owner_eid & owner_e & owner_m & old_owner & old_owner_t &
     Howner_pevent & Howner_event & Howner_type & Howner_fields &
     Howner_owner & Howner_pcp & Howner_orig &
     Hold_owner_get & Hold_owner_prio & Hold_owner_pend).
  assert (Howner_eid : owner_eid = eid).
  {
    eapply mutex_post_stage_event_id_eq__return_semantics;
      eassumption.
  }
  subst owner_eid.
  unfold mutex_post_handover_step_prop,
    OSMutexPost_handover_sem in Hhandover.
  destruct Hhandover as
    [reserved [wake [counted
      [Hreservation [Hwake [Hcount Howner_commit]]]]]].
  assert (Hreserved_valid :
    UCOS2_verification_slice_state_inv sg reserved).
  {
    eapply mutex_post_reservation_preserves_validity__return_semantics.
    - exact Hdisinherited_valid.
    - exact Howner_event.
    - exact Howner_type.
    - exact Howner_fields.
    - exact Howner_owner.
    - exact Hold_owner_get.
    - exact Howner_orig.
    - exact Hold_owner_prio.
    - exact Hold_owner_pend.
    - exact Hreservation.
  }
  assert (Hidentity : table_owner = canonical_waiter).
  {
    exact
      (OSMutexPost_handover_identity_closure
         sg pevent entry eid stage_e stage_m stage_owner
         disinherited reserved wake returned_prio
         canonical_waiter table_owner
         Hentry_valid Hpevent Hstage_event Hstage_type
         Hstage_fields Hstage_owner Hstage_current Hrelocations
         Hdisinherit Hreservation Hwake).
  }
  subst table_owner.
  assert (Hwake_valid : UCOS2_verification_slice_state_inv sg wake).
  {
    eapply
      atomic_event_task_rdy_same_identity_preserves_validity__return_semantics.
    - exact Hreserved_valid.
    - exact Hwake.
  }
  eapply mutex_post_handover_commits_preserve_validity__return_semantics.
  - exact Hstable.
  - exact Hreserved_valid.
  - exact Hwake_valid.
  - exact Howner_event.
  - exact Howner_type.
  - exact Howner_fields.
  - exact Howner_owner.
  - exact Hreservation.
  - exact Hwake.
  - exact Hcount.
  - exact Howner_commit.
Qed.
Lemma atomic_sched_preserves_validity__return_semantics :
  forall sg before result after,
    UCOS2_verification_slice_state_inv sg before ->
    atomic_sched before result after ->
    UCOS2_verification_slice_state_inv sg after.
Proof.
  intros sg before result after Hvalid Hsched_step.
  destruct Hvalid as [Htask [Hsched [Hevent Hcross]]].
  pose proof
    (atomic_sched_preserves_neutral_fields
       before result after Hsched_step)
    as [Htask_eq [Hevent_eq [Hintr_eq Htick_eq]]].
  assert (Htask_after :
    verification_slice_task_validity sg after.(TskState)).
  {
    rewrite <- Htask_eq.
    exact Htask.
  }
  assert (Hsched_after :
    verification_slice_sched_in_range sg after.(TskState) after.(SchedState)).
  {
    rewrite <- Htask_eq.
    eapply atomic_sched_preserves_sched_in_range.
    - exact Hsched_step.
    - exact Hsched.
  }
  assert (Hevent_after :
    verification_slice_event_in_range
      sg after.(TskState) after.(EventState)).
  {
    rewrite <- Htask_eq, <- Hevent_eq.
    exact Hevent.
  }
  assert (Hcross_after :
    Ucos2Verify.lib.cross_module_invariants.verification_slice_cross_module_consistency
      sg after).
  {
    eapply verification_slice_cross_module_consistency_preserved_by_sched;
      eassumption.
  }
  exact
    (conj Htask_after
      (conj Hsched_after (conj Hevent_after Hcross_after))).
Qed.
Lemma mutex_post_handover_sched_validity__return_semantics :
  forall sg pevent eid entry disinherited handover scheduled
         pcp owner_orig returned_prio
         canonical_waiter table_owner,
    valid_stable_glob_vars sg ->
    UCOS2_verification_slice_state_inv sg entry ->
    pevent = event_addr sg eid ->
    mutex_post_owner_disinherit_stage_prop
      sg pevent entry pcp owner_orig disinherited ->
    mutex_post_handover_step_prop
      sg eid disinherited returned_prio
      canonical_waiter table_owner handover ->
    mutex_post_sched_step_prop handover scheduled ->
    OSMutexPost_relocations_legal sg pevent entry ->
    UCOS2_verification_slice_state_inv sg scheduled.
Proof.
  intros sg pevent eid entry disinherited handover scheduled
    pcp owner_orig returned_prio canonical_waiter table_owner
    Hstable Hentry_valid Hpevent Hstage Hhandover
    Hsched Hrelocations.
  pose proof
    (mutex_post_handover_validity__return_semantics
       sg pevent eid entry disinherited handover
       pcp owner_orig returned_prio canonical_waiter table_owner
       Hstable Hentry_valid Hpevent Hstage Hhandover Hrelocations)
    as Hhandover_valid.
  unfold mutex_post_sched_step_prop in Hsched.
  destruct Hsched as [sched_result Hsched].
  eapply atomic_sched_preserves_validity__return_semantics;
    eassumption.
Qed.
