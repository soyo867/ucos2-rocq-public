Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto ListLib.
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
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.array_abstraction.

Import ListNotations.
Import Monad.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Inductive MutexDelOpt : Type :=
| MutexDelNoPend
| MutexDelAlways
| MutexDelInvalid.

(** Exact decoding relation between the source option byte and the abstract
    option consumed by [OSMutexDel_full_sem].  Keeping this relation opaque
    to symbolic execution avoids duplicating the three-way case split at
    every later assertion boundary while preserving the public C contract. *)
Definition mutex_del_option_decode_prop
  (opt_in : Z) (opt : MutexDelOpt) : Prop :=
  (opt_in = 0 /\ opt = MutexDelNoPend) \/
  (opt_in = 1 /\ opt = MutexDelAlways) \/
  (opt_in <> 0 /\ opt_in <> 1 /\ opt = MutexDelInvalid).

Definition mutex_del_observe_ptr
  (pevent : addr) (ret : OSErrCode * option addr)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun X1 p X2 =>
    p = match snd ret with Some a => a | None => 0 end /\
    X2 = X1.

Definition mutex_del_observe_unit (_ : unit)
  : program (UCOS2_Verify_State -> Prop) unit :=
  fun X1 _ X2 => X2 = X1.

(** Exact source checkpoint after owner restoration and before the PCP-table
    write.  It clears only the mutex owner fields; the final free is a later
    stage. *)
Definition mutex_del_no_pend_prepare
  (mid : EventID) : program UCOS2_Verify_State unit :=
  fun ls1 (_ : unit) ls2 =>
    exists e1 m1 evSt2,
      ls1.(EventState).(inUsedEventStates) mid = Some e1 /\
      e1.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e1.(mutexFields) = Some m1 /\
      e1.(waitList) = [] /\
      evSt2 =
        update_event_field_raw
          ls1.(EventState) mid
          {| eventGeneration := e1.(eventGeneration);
             eventName := e1.(eventName);
     eventPadding1 := e1.(eventPadding1);
     eventPadding2 := e1.(eventPadding2);
     eventPadding3 := e1.(eventPadding3);
     eventPadding19 := e1.(eventPadding19);
             eventType := e1.(eventType);
             mutexFields := Some
               {| mfPCP := m1.(mfPCP);
                  mfOwner := None;
                  mfOwnerOrigPrio := None |};
             semFields := e1.(semFields);
             mboxFields := e1.(mboxFields);
             queueFields := e1.(queueFields);
             waitList := [] |} /\
      ls2 = replace_EventS evSt2 ls1.

(** Source-total owner restoration used by both successful Delete branches.

    The source guards are represented in their exact order.  When an enabled
    mutex has an owner at its PCP, [atomic_task_set_curPrio] classifies the
    owner as ready, waiting, or dormant.  Its ready arm changes
    [curSchedPrio] only for the current task; its waiting and dormant arms keep
    the scheduler state unchanged.  Thus this relation adds neither a
    current-task nor a ready-owner precondition to the public Delete API. *)
Definition mutex_del_owner_restore_total
  (sg : StableGlobVars) (e : OSEventAbstractState)
  : program UCOS2_Verify_State unit :=
  fun ls1 (_ : unit) ls2 =>
    exists m,
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e.(mutexFields) = Some m /\
      (match m.(mfOwner), m.(mfOwnerOrigPrio) with
       | None, None | Some _, Some _ => True
       | _, _ => False
       end) /\
      if Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)
      then ls2 = ls1
      else
        match m.(mfOwner), m.(mfOwnerOrigPrio) with
        | None, None => ls2 = ls1
        | Some owner_tid, Some owner_orig =>
            exists owner_t,
              ls1.(TskState).(inUsedTaskStates) owner_tid = Some owner_t /\
              if Z.eqb owner_t.(curPrio) m.(mfPCP)
              then atomic_task_set_curPrio
                     sg owner_tid owner_orig ls1 tt ls2
              else ls2 = ls1
        | _, _ => False
        end.

(** Exact aggregate relation exposed by the internal owner-priority call.
    [owner_tid] is an explicit caller witness, so the call boundary does not
    depend on injectivity of a concrete address encoding. *)
Definition mutex_del_owner_ready_call_sem
  (sg : StableGlobVars) (owner_tid : TaskID)
  (ptcb : addr) (prio : Priority)
  : program UCOS2_Verify_State unit :=
  fun ls1 (_ : unit) ls2 =>
    ptcb = verification_slice_tcb_addr sg owner_tid /\
    atomic_task_set_curPrio sg owner_tid prio ls1 tt ls2.

Definition mutex_del_owner_ready_call_prop
  (sg : StableGlobVars) (owner_tid : TaskID)
  (ptcb : addr) (prio : Priority)
  (ls1 ls2 : UCOS2_Verify_State) : Prop :=
  mutex_del_owner_ready_call_sem
    sg owner_tid ptcb prio ls1 tt ls2.

(** Derived footprint exposed by the owner-priority helper call.  It says that
    the selected mutex object is untouched and that every task used to encode
    its concrete wait bitmap has the same abstract lookup after the call.  The
    raw priority transformer remains source-total; this is a theorem-side
    effect, not an extra execution guard. *)
Definition mutex_del_selected_event_noninterference_prop
  (eid : EventID) (ls1 ls2 : UCOS2_Verify_State) : Prop :=
  forall e,
    ls1.(EventState).(inUsedEventStates) eid = Some e ->
    ls2.(EventState).(inUsedEventStates) eid = Some e /\
    forall tid,
      In tid e.(waitList) ->
      ls2.(TskState).(inUsedTaskStates) tid =
      ls1.(TskState).(inUsedTaskStates) tid.

(** Stable representation facts selected at the owner dereference.  This is
    a disjoint total classification of the abstract mutex owner shape, not a
    public readiness/current-task guard. *)
Definition mutex_del_owner_snapshot_prop
  (sg : StableGlobVars) (ls : UCOS2_Verify_State)
  (e : OSEventAbstractState) (owner_ptr : addr)
  (owner_tid : TaskID) (owner_t : TaskAbstractState)
  (owner_prio prio_addr : Z) : Prop :=
  sg.(osPrioMutexCeilDis) = 255 /\
  exists m,
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    match m.(mfOwner), m.(mfOwnerOrigPrio) with
    | None, None => owner_ptr = 0
    | Some tid, Some _ =>
        owner_tid = tid /\
        ls.(TskState).(inUsedTaskStates) tid = Some owner_t /\
        owner_ptr <> 0 /\
        owner_ptr = verification_slice_tcb_addr sg tid /\
        owner_prio = owner_t.(curPrio) /\
        task_prio_snapshot_of_prop
          sg ls.(TskState) tid owner_t owner_ptr owner_prio /\
        task_prio_field_layout_prop owner_ptr prio_addr
    | _, _ => False
    end.

(** Source-value lineage used at both guarded owner calls. *)
Definition mutex_del_owner_value_lineage_prop
  (e : OSEventAbstractState) (ecnt pcp owner_orig : Z) : Prop :=
  exists m,
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    pcp = decode_PCP_from_cnt ecnt /\
    owner_orig = decode_OwnerPrio_from_cnt ecnt /\
    m.(mfPCP) = pcp /\
    match m.(mfOwner), m.(mfOwnerOrigPrio) with
    | None, None => True
    | Some _, Some p => p = owner_orig
    | _, _ => False
    end.

(** Immutable facts established before the option dispatch.  They are kept
    as a single source-level trace fact so later call boundaries cannot lose
    the event identity, public discriminator, or the exact C boolean derived
    from [OSEventGrp]. *)
Definition mutex_del_tasks_waiting_prop
  (e : OSEventAbstractState) (tasks_waiting : Z) : Prop :=
  (tasks_waiting = 0 /\ e.(waitList) = []) \/
  (tasks_waiting = 1 /\ e.(waitList) <> []).

(** Entry-state owner consistency retained across event deletion.  The
    post-state cross-module invariant cannot recover the deleted event's
    owner/original-priority relation, so the selected immutable slice is
    transported from the entry invariant.  This is not an execution guard:
    it is exactly the [mutex_owner_consistency] fact already established by
    the public entry [UCOS2_verification_slice_inv]. *)
Definition mutex_del_owner_entry_consistency_prop
  (sg : StableGlobVars) (e : OSEventAbstractState)
  (entry : UCOS2_Verify_State) : Prop :=
  exists m,
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    e.(mutexFields) = Some m /\
    match m.(mfOwner) with
    | None => True
    | Some tid =>
        exists t op,
          entry.(TskState).(inUsedTaskStates) tid = Some t /\
          m.(mfOwnerOrigPrio) = Some op /\
          (t.(curPrio) = op \/
           (m.(mfPCP) <> sg.(osPrioMutexCeilDis) /\
            t.(curPrio) = m.(mfPCP)))
    end.

Lemma mutex_del_owner_entry_consistency_from_cross :
  forall sg entry eid e,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    (exists m, e.(mutexFields) = Some m) ->
    mutex_owner_consistency sg entry ->
    mutex_del_owner_entry_consistency_prop sg e entry.
Proof.
  intros sg entry eid e Hlookup Htype [m Hfields] Howners.
  exists m. split; [exact Htype|]. split; [exact Hfields|].
  specialize (Howners eid e m (conj Hlookup (conj Htype Hfields))).
  destruct m.(mfOwner) as [tid|] eqn:Howner; simpl in *.
  - destruct Howners as
      (t & op & Htask & Horig & Hprio & Hnot_waiting).
    exists t, op. repeat split; assumption.
  - exact I.
Qed.

Definition mutex_del_source_entry_prop
  (sg : StableGlobVars) (e : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID)
  (pevent : addr) (tasks_waiting : Z) : Prop :=
  pevent = event_addr sg eid /\
  valid_event_id sg eid /\
  entry.(EventState).(inUsedEventStates) eid = Some e /\
  e.(eventType) = OS_EVENT_TYPE_MUTEX /\
  (exists m, e.(mutexFields) = Some m) /\
  entry.(IntrState).(intNesting) <= 0 /\
  mutex_del_tasks_waiting_prop e tasks_waiting /\
  mutex_del_owner_entry_consistency_prop sg e entry.

(** Closed, pure classification of the source-level function inputs.  Keeping
    the entry disjunction inside one proposition gives every later branch a
    unique function-pre state, while the fields below are exactly the facts
    that the original Require exposed directly. *)
Definition mutex_del_input_classification_prop
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (pevent : addr)
  (etype ecnt eptr egrp : Z) (etbl : list Z)
  (type_addr ptr_addr cnt_addr grp_addr tbl_addr : addr)
  (owner_tid : TaskID) (owner_t : TaskAbstractState)
  (owner_prio : Z) (owner_prio_addr : addr)
  (owner_orig pcp_idx : Z) : Prop :=
  pevent = 0 \/
  (pevent <> 0 /\
   pevent = event_addr sg eid /\
   valid_event_id sg eid /\
   0 <= etype /\ etype <= 255 /\
   event_snapshot_of_prop
     sg entry.(TskState) entry.(EventState) eid e
     etype ecnt eptr egrp etbl /\
   event_core_fields_layout_prop
     sg eid type_addr ptr_addr cnt_addr /\
   event_wait_fields_layout_prop sg eid grp_addr tbl_addr /\
   (etype <> 4 \/
    (mutex_del_owner_snapshot_prop
       sg entry e eptr owner_tid owner_t owner_prio owner_prio_addr /\
     mutex_del_owner_value_lineage_prop
       e ecnt pcp_idx owner_orig))).

(** Concrete address provenance for the cache refresh implemented in the
    target C file.  It is carried by the source lineage so both successful
    branches reach the same verified helper without inventing aliases. *)
Definition mutex_del_refresh_layout_prop
  (sg : StableGlobVars) (rdy_grp rdy_tbl prio_high tcb_high prio_tbl : addr)
  : Prop :=
  rdy_grp = sg.(g_OSRdyGrp) /\
  rdy_tbl = sg.(g_OSRdyTbl) /\
  prio_high = sg.(g_OSPrioHighRdy) /\
  tcb_high = sg.(g_OSTCBHighRdy) /\
  prio_tbl = sg.(g_OSTCBPrioTbl).

Definition mutex_del_refresh_context_prop
  (sg : StableGlobVars) (rdy_grp rdy_tbl prio_high tcb_high prio_tbl : addr)
  : Prop :=
  valid_stable_glob_vars sg /\
  mutex_del_refresh_layout_prop
    sg rdy_grp rdy_tbl prio_high tcb_high prio_tbl.

(** Function-entry values needed by every post-dispatch return.  This is a
    source-level trace fact, not a proof-only shortcut: it records the
    unchanged parameter aliases together with the mutex discriminator and
    concrete selected-event snapshot that were established before entering
    the critical section. *)
Definition mutex_del_return_lineage_prop
  (sg : StableGlobVars) (e : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID)
  (pe pd pevent perr pevent_pre perr_pre : addr)
  (etype isr opt_in : Z) (opt : MutexDelOpt)
  (ecnt eptr egrp : Z) (etbl : list Z) : Prop :=
  pe = pevent_pre /\
  pevent = pevent_pre /\
  pd = perr_pre /\
  perr = perr_pre /\
  pevent_pre <> 0 /\
  etype = 4 /\
  isr = entry.(IntrState).(intNesting) /\
  isr <= 0 /\
  mutex_del_option_decode_prop opt_in opt /\
  event_snapshot_of_prop
    sg entry.(TskState) entry.(EventState) eid e
    etype ecnt eptr egrp etbl /\
  mutex_del_owner_value_lineage_prop
    e ecnt (decode_PCP_from_cnt ecnt)
    (decode_OwnerPrio_from_cnt ecnt).

Definition mutex_del_success_mode_prop
  (opt : MutexDelOpt) (tasks_waiting : Z) : Prop :=
  match opt with
  | MutexDelNoPend => tasks_waiting = 0
  | MutexDelAlways => tasks_waiting = 0 \/ tasks_waiting = 1
  | MutexDelInvalid => False
  end.

Definition mutex_del_no_pend_mode_prop
  (opt : MutexDelOpt) (tasks_waiting : Z) : Prop :=
  opt = MutexDelNoPend /\ tasks_waiting = 0.

(** Branch-local selector for the ALWAYS arm.  Unlike the generic success
    mode proposition, this records the control-flow choice needed to justify
    the wake-stage arm of [mutex_del_mode_wake_prop]. *)
Definition mutex_del_always_mode_prop
  (opt : MutexDelOpt) (tasks_waiting : Z) : Prop :=
  opt = MutexDelAlways /\
  (tasks_waiting = 0 \/ tasks_waiting = 1).

Definition mutex_del_error_mode_prop
  (opt : MutexDelOpt) (tasks_waiting err : Z) : Prop :=
  (opt = MutexDelNoPend /\
   tasks_waiting = 1 /\ err = 73) \/
  (opt = MutexDelInvalid /\ err = 7).

(** Event residual after exposing both the selected live record and the
    OSEventFreeList head cell.  Keeping the head outside is required by the
    literal delete sequence [pevent->OSEventPtr = OSEventFreeList] followed
    by [OSEventFreeList = pevent]. *)
Definition mutex_del_event_inv_no_eid_no_free_head
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState)
  (st : Glob_EventAbstractState) (eid : EventID) : Assertion :=
  coq_prop (verification_slice_event_in_range sg tskSt st) &&
  store_used_event_map_missing_i sg tskSt st.(inUsedEventStates) eid **
  store_free_event_nodes sg st.(unUsedEventStates).

(** Reversible selected-event residual used from the public discriminator
    read until the delete commit.  The selected OS_EVENT record and the
    OSEventFreeList head cell are owned by the caller; this predicate owns
    every other component of the public invariant exactly once. *)
Definition mutex_del_event_focus_inv
  (sg : StableGlobVars) (ls : UCOS2_Verify_State)
  (eid : EventID) : Assertion :=
  interrupt_inv sg ls.(IntrState) **
  verification_slice_task_inv sg ls.(TskState) **
  verification_slice_sched_inv sg ls.(TskState) ls.(SchedState) **
  mutex_del_event_inv_no_eid_no_free_head
    sg ls.(TskState) ls.(EventState) eid **
  verification_slice_tick_inv sg ls.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg ls).

(** The same selected-event residual with the interrupt component exposed.
    This is used only around the concrete OSIntNesting read: it preserves all
    task/scheduler/event/tick/cross-module ownership while [interrupt_inv] is
    reversibly localized to its byte cell. *)
Definition mutex_del_event_focus_no_interrupt_inv
  (sg : StableGlobVars) (ls : UCOS2_Verify_State)
  (eid : EventID) : Assertion :=
  verification_slice_task_inv sg ls.(TskState) **
  verification_slice_sched_inv sg ls.(TskState) ls.(SchedState) **
  mutex_del_event_inv_no_eid_no_free_head
    sg ls.(TskState) ls.(EventState) eid **
  verification_slice_tick_inv sg ls.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg ls).

Lemma mutex_del_event_focus_open_interrupt :
  forall sg ls eid,
    mutex_del_event_focus_inv sg ls eid |--
      interrupt_inv sg ls.(IntrState) **
      mutex_del_event_focus_no_interrupt_inv sg ls eid.
Proof.
  intros sg ls eid.
  unfold mutex_del_event_focus_inv,
    mutex_del_event_focus_no_interrupt_inv.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma mutex_del_event_focus_close_interrupt :
  forall sg ls eid,
    interrupt_inv sg ls.(IntrState) **
    mutex_del_event_focus_no_interrupt_inv sg ls eid |--
      mutex_del_event_focus_inv sg ls eid.
Proof.
  intros sg ls eid.
  unfold mutex_del_event_focus_inv,
    mutex_del_event_focus_no_interrupt_inv.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma mutex_del_event_focus_split :
  forall sg ls eid e base type_addr ptr_addr cnt_addr grp_addr tbl_addr
         free_addr etype ecnt eptr egrp etbl free_head,
    event_snapshot_of_prop sg ls.(TskState) ls.(EventState) eid e
      etype ecnt eptr egrp etbl ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    os_event_free_list_addr sg free_addr ->
    event_free_list_head_prop sg ls.(EventState) free_head ->
    base = event_addr sg eid ->
    UCOS2_verification_slice_inv sg ls |--
      type_addr # UChar |-> etype **
      ptr_addr # Ptr |-> eptr **
      cnt_addr # UShort |-> ecnt **
      grp_addr # UChar |-> egrp **
      used_event_wait_table_storage ls.(TskState) base e **
      free_addr # Ptr |-> free_head **
      mutex_del_event_focus_inv sg ls eid.
Proof.
  intros sg ls eid e base type_addr ptr_addr cnt_addr grp_addr tbl_addr
    free_addr etype ecnt eptr egrp etbl free_head
    Hsnapshot Hcore Hwait Hfreeaddr Hfreehead Hbase.
  pose proof Hsnapshot as Hsnapshot0.
  unfold event_snapshot_of_prop in Hsnapshot0.
  destruct Hsnapshot0 as
    [Hused [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  unfold event_core_fields_layout_prop in Hcore.
  destruct Hcore as [Htype_addr [Hptr_addr Hcnt_addr]].
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hwait as [Hgrp_addr Htbl_addr].
  unfold os_event_free_list_addr in Hfreeaddr.
  unfold event_free_list_head_prop in Hfreehead.
  subst base type_addr ptr_addr cnt_addr grp_addr tbl_addr.
  subst free_addr free_head etype ecnt eptr egrp etbl.
  unfold UCOS2_verification_slice_inv, mutex_del_event_focus_inv.
  unfold verification_slice_event_inv.
  pureIntros.
  sepcon_lift
    (store_used_event_map sg ls.(TskState)
      ls.(EventState).(inUsedEventStates)).
  unfold store_used_event_map.
  sep_apply_l_atomic
    (store_map_split
       (fun eid0 e0 =>
          used_complete_event
            sg ls.(TskState) (event_addr sg eid0) eid0 e0)
       eid e ls.(EventState).(inUsedEventStates) Hused).
  unfold used_complete_event, used_event_wait_table_storage.
  unfold mutex_del_event_inv_no_eid_no_free_head,
    store_used_event_map_missing_i, store_free_event_list.
  cancel.
  andp_cancel.
  unfold used_complete_event.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma mutex_del_selected_event_cells_fold :
  forall sg tskSt base eid e etype ecnt eptr egrp,
    etype = encode_event_type e.(eventType) ->
    ecnt = encode_event_cnt_value e ->
    eptr = verification_slice_encode_event_ptr_value sg e ->
    egrp = encode_event_wait_grp e.(waitList) tskSt ->
    (base + OSEventType_off) # UChar |-> etype **
    (base + OSEventPtr_off) # Ptr |-> eptr **
    (base + OSEventCnt_off) # UShort |-> ecnt **
    (base + OSEventGrp_off) # UChar |-> egrp **
    used_event_wait_table_storage tskSt base e |--
      used_complete_event sg tskSt base eid e.
Proof.
  intros sg tskSt base eid e etype ecnt eptr egrp
    Htype Hcnt Hptr Hgrp.
  subst etype ecnt eptr egrp.
  unfold used_complete_event, used_event_wait_table_storage.
  sepcon_assoc_change.
  cancel.
Qed.

Lemma mutex_del_event_focus_merge :
  forall sg ls eid e base type_addr ptr_addr cnt_addr grp_addr tbl_addr
         free_addr etype ecnt eptr egrp etbl free_head,
    event_snapshot_of_prop sg ls.(TskState) ls.(EventState) eid e
      etype ecnt eptr egrp etbl ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    os_event_free_list_addr sg free_addr ->
    event_free_list_head_prop sg ls.(EventState) free_head ->
    base = event_addr sg eid ->
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    grp_addr # UChar |-> egrp **
    used_event_wait_table_storage ls.(TskState) base e **
    free_addr # Ptr |-> free_head **
    mutex_del_event_focus_inv sg ls eid |--
      UCOS2_verification_slice_inv sg ls.
Proof.
  intros sg ls eid e base type_addr ptr_addr cnt_addr grp_addr tbl_addr
    free_addr etype ecnt eptr egrp etbl free_head
    Hsnapshot Hcore Hwait Hfreeaddr Hfreehead Hbase.
  pose proof Hsnapshot as Hsnapshot0.
  unfold event_snapshot_of_prop in Hsnapshot0.
  destruct Hsnapshot0 as
    [Hused [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  unfold event_core_fields_layout_prop in Hcore.
  destruct Hcore as [Htype_addr [Hptr_addr Hcnt_addr]].
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hwait as [Hgrp_addr Htbl_addr].
  unfold os_event_free_list_addr in Hfreeaddr.
  unfold event_free_list_head_prop in Hfreehead.
  subst base type_addr ptr_addr cnt_addr grp_addr tbl_addr.
  pose proof Htype as Htype0.
  pose proof Hcnt as Hcnt0.
  pose proof Hptr as Hptr0.
  pose proof Hgrp as Hgrp0.
  subst free_addr free_head etype ecnt eptr egrp etbl.
  sep_apply_l_atomic
    (mutex_del_selected_event_cells_fold
       sg ls.(TskState) (event_addr sg eid) eid e
       (encode_event_type e.(eventType))
       (encode_event_cnt_value e)
       (verification_slice_encode_event_ptr_value sg e)
       (encode_event_wait_grp e.(waitList) ls.(TskState))
       eq_refl eq_refl eq_refl eq_refl).
  unfold mutex_del_event_focus_inv, UCOS2_verification_slice_inv.
  unfold mutex_del_event_inv_no_eid_no_free_head.
  pureIntros.
  unfold store_used_event_map_missing_i.
  sep_apply_l_atomic
    (store_map_merge
       (fun eid0 e0 =>
          used_complete_event
            sg ls.(TskState) (event_addr sg eid0) eid0 e0)
       eid e ls.(EventState).(inUsedEventStates) Hused).
  unfold verification_slice_event_inv, store_used_event_map, store_free_event_list.
  cancel.
  andp_cancel.
  sepcon_assoc_change.
  cancel.
Qed.

(** Owner-priority localization inside the selected-event residual.  The
    selected event cells remain a caller frame across OSMutex_RdyAtPrio, so
    neither the live event record nor its wait-table storage is duplicated in
    the helper contract. *)
Definition mutex_del_event_owner_open_inv
  (sg : StableGlobVars) (ls : UCOS2_Verify_State)
  (eid : EventID) (owner_tid : TaskID)
  (owner_t : TaskAbstractState) : Assertion :=
  interrupt_inv sg ls.(IntrState) **
  used_task_no_prio sg (verification_slice_tcb_addr sg owner_tid) owner_tid owner_t **
  verification_slice_task_inv_no_tid sg ls.(TskState) owner_tid **
  verification_slice_sched_inv sg ls.(TskState) ls.(SchedState) **
  mutex_del_event_inv_no_eid_no_free_head
    sg ls.(TskState) ls.(EventState) eid **
  verification_slice_tick_inv sg ls.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg ls).

(** Reversible residual after focusing the owner's priority byte out of the
    full invariant.  No spatial component is duplicated or discarded. *)
Definition mutex_del_open_inv
  (sg : StableGlobVars) (ls : UCOS2_Verify_State)
  (owner_tid : TaskID) (owner_t : TaskAbstractState) : Assertion :=
  interrupt_inv sg ls.(IntrState) **
  used_task_no_prio sg (verification_slice_tcb_addr sg owner_tid) owner_tid owner_t **
  verification_slice_task_inv_no_tid sg ls.(TskState) owner_tid **
  verification_slice_sched_inv sg ls.(TskState) ls.(SchedState) **
  verification_slice_event_inv sg ls.(TskState) ls.(EventState) **
  verification_slice_tick_inv sg ls.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg ls).

Lemma mutex_del_open_inv_split :
  forall sg ls owner_tid owner_t owner_ptr owner_prio prio_addr,
    task_prio_snapshot_of_prop
      sg ls.(TskState) owner_tid owner_t owner_ptr owner_prio ->
    task_prio_field_layout_prop owner_ptr prio_addr ->
    UCOS2_verification_slice_inv sg ls |--
      prio_addr # UChar |-> owner_prio **
      mutex_del_open_inv sg ls owner_tid owner_t.
Proof.
  intros sg ls owner_tid owner_t owner_ptr owner_prio prio_addr
    Hsnapshot Hlayout.
  unfold task_prio_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as [Htask [Hptr Hprio]].
  unfold task_prio_field_layout_prop in Hlayout.
  subst owner_ptr owner_prio prio_addr.
  unfold UCOS2_verification_slice_inv, mutex_del_open_inv.
  sep_apply_l_atomic
    (verification_slice_task_inv_split_prio__focus_and_pure
       sg ls.(TskState) owner_tid owner_t Htask).
  cancel.
  andp_cancel.
Qed.

Lemma mutex_del_task_open_merge :
  forall sg st owner_tid owner_t owner_ptr owner_prio prio_addr,
    task_prio_snapshot_of_prop
      sg st owner_tid owner_t owner_ptr owner_prio ->
    task_prio_field_layout_prop owner_ptr prio_addr ->
    prio_addr # UChar |-> owner_prio **
    used_task_no_prio sg (verification_slice_tcb_addr sg owner_tid) owner_tid owner_t **
    verification_slice_task_inv_no_tid sg st owner_tid |--
      verification_slice_task_inv sg st.
Proof.
  intros sg st owner_tid owner_t owner_ptr owner_prio prio_addr
    Hsnapshot Hlayout.
  pose proof Hsnapshot as Hsnapshot0.
  unfold task_prio_snapshot_of_prop in Hsnapshot0.
  destruct Hsnapshot0 as [Htask [Hptr Hprio]].
  subst owner_ptr owner_prio.
  pose proof Hlayout as Hlayout0.
  unfold task_prio_field_layout_prop in Hlayout0.
  subst prio_addr.
  assert (Hrebuild :
    (verification_slice_tcb_addr sg owner_tid + verification_slice_OSTCBPrio_off)
      # UChar |-> curPrio owner_t **
    used_task_no_prio sg (verification_slice_tcb_addr sg owner_tid) owner_tid owner_t |--
      verification_slice_used_complete_task sg
        (verification_slice_tcb_addr sg owner_tid) owner_tid owner_t).
  { unfold verification_slice_used_complete_task, used_task_no_prio; entailer!. }
  sep_apply_l_atomic Hrebuild.
  unfold verification_slice_task_inv, verification_slice_task_inv_no_tid,
    verification_slice_store_used_task_map, verification_slice_store_used_task_map_missing_i.
  cancel.
  pureIntros.
  sep_apply_l_atomic
    (store_map_merge
       (fun tid0 t0 =>
          verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t0)
       owner_tid owner_t (inUsedTaskStates st) Htask).
  cancel.
  andp_cancel.
Qed.

Lemma mutex_del_open_inv_merge :
  forall sg ls owner_tid owner_t owner_ptr owner_prio prio_addr,
    task_prio_snapshot_of_prop
      sg ls.(TskState) owner_tid owner_t owner_ptr owner_prio ->
    task_prio_field_layout_prop owner_ptr prio_addr ->
    prio_addr # UChar |-> owner_prio **
    mutex_del_open_inv sg ls owner_tid owner_t |--
      UCOS2_verification_slice_inv sg ls.
Proof.
  intros sg ls owner_tid owner_t owner_ptr owner_prio prio_addr
    Hsnapshot Hlayout.
  unfold mutex_del_open_inv, UCOS2_verification_slice_inv.
  sep_apply_l_atomic
    (mutex_del_task_open_merge
       sg ls.(TskState) owner_tid owner_t
       owner_ptr owner_prio prio_addr Hsnapshot Hlayout).
  cancel.
  andp_cancel.
Qed.

(** The C dereference guard rules out the no-owner arm of the total owner
    snapshot.  Keep that guard explicit across the reversible localization so
    that both the generated split and merge witnesses have the exact premises
    needed to select the owner task. *)
Lemma mutex_del_owner_snapshot_nonnull_components :
  forall sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr,
    owner_ptr <> 0 ->
    mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    task_prio_snapshot_of_prop
      sg ls.(TskState) owner_tid owner_t owner_ptr owner_prio /\
    task_prio_field_layout_prop owner_ptr prio_addr.
Proof.
  intros sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
    Hnonnull Howner.
  unfold mutex_del_owner_snapshot_prop in Howner.
  destruct Howner as [_ [m [_ [_ Hshape]]]].
  destruct m.(mfOwner) as [tid|] eqn:Htid;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hshape.
  - destruct Hshape as
      [Howner_tid [_ [_ [Hptr [_ [Hsnapshot Hlayout]]]]]].
    subst owner_tid.
    exact (conj Hsnapshot Hlayout).
  - contradiction.
  - contradiction.
  - subst owner_ptr. contradiction.
Qed.

Lemma mutex_del_owner_open_split :
  forall sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr,
    owner_ptr <> 0 ->
    mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    UCOS2_verification_slice_inv sg ls |--
      prio_addr # UChar |-> owner_prio **
      mutex_del_open_inv sg ls owner_tid owner_t **
      coq_prop (mutex_del_owner_snapshot_prop
        sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr).
Proof.
  intros sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
    Hnonnull Howner.
  pose proof
    (mutex_del_owner_snapshot_nonnull_components
       sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
       Hnonnull Howner) as [Hsnapshot Hlayout].
  sep_apply_l_atomic
    (mutex_del_open_inv_split
       sg ls owner_tid owner_t owner_ptr owner_prio prio_addr
       Hsnapshot Hlayout).
  cancel.
  andp_cancel.
  apply derivable1_truep_intros.
Qed.

Lemma mutex_del_owner_open_merge :
  forall sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr,
    owner_ptr <> 0 ->
    mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    prio_addr # UChar |-> owner_prio **
    mutex_del_open_inv sg ls owner_tid owner_t **
    coq_prop (mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr) |--
      UCOS2_verification_slice_inv sg ls **
      coq_prop (mutex_del_owner_snapshot_prop
        sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr).
Proof.
  intros sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
    Hnonnull Howner.
  pose proof
    (mutex_del_owner_snapshot_nonnull_components
       sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
       Hnonnull Howner) as [Hsnapshot Hlayout].
  sep_apply_l_atomic
    (mutex_del_open_inv_merge
       sg ls owner_tid owner_t owner_ptr owner_prio prio_addr
       Hsnapshot Hlayout).
  cancel.
Qed.

Lemma mutex_del_event_owner_open_split :
  forall sg ls eid e owner_ptr owner_tid owner_t owner_prio prio_addr,
    owner_ptr <> 0 ->
    mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    mutex_del_event_focus_inv sg ls eid |--
      prio_addr # UChar |-> owner_prio **
      mutex_del_event_owner_open_inv
        sg ls eid owner_tid owner_t **
      coq_prop (mutex_del_owner_snapshot_prop
        sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr).
Proof.
  intros sg ls eid e owner_ptr owner_tid owner_t owner_prio prio_addr
    Hnonnull Howner.
  pose proof
    (mutex_del_owner_snapshot_nonnull_components
       sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
       Hnonnull Howner) as [Hsnapshot Hlayout].
  unfold task_prio_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as [Htask [Hptr Hprio]].
  unfold task_prio_field_layout_prop in Hlayout.
  subst owner_ptr owner_prio prio_addr.
  unfold mutex_del_event_focus_inv,
    mutex_del_event_owner_open_inv.
  sep_apply_l_atomic
    (verification_slice_task_inv_split_prio__focus_and_pure
       sg ls.(TskState) owner_tid owner_t Htask).
  cancel.
  andp_cancel.
  apply derivable1_truep_intros.
Qed.

Lemma mutex_del_event_owner_open_merge :
  forall sg ls eid e owner_ptr owner_tid owner_t owner_prio prio_addr,
    owner_ptr <> 0 ->
    mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    prio_addr # UChar |-> owner_prio **
    mutex_del_event_owner_open_inv sg ls eid owner_tid owner_t **
    coq_prop (mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr) |--
      mutex_del_event_focus_inv sg ls eid **
      coq_prop (mutex_del_owner_snapshot_prop
        sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr).
Proof.
  intros sg ls eid e owner_ptr owner_tid owner_t owner_prio prio_addr
    Hnonnull Howner.
  pose proof
    (mutex_del_owner_snapshot_nonnull_components
       sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
       Hnonnull Howner) as [Hsnapshot Hlayout].
  unfold mutex_del_event_owner_open_inv,
    mutex_del_event_focus_inv.
  sep_apply_l_atomic
    (mutex_del_task_open_merge
       sg ls.(TskState) owner_tid owner_t
       owner_ptr owner_prio prio_addr Hsnapshot Hlayout).
  cancel.
  andp_cancel.
Qed.

Definition mutex_del_rdyatprio_stage_prop
  (sg : StableGlobVars) (e : OSEventAbstractState)
  (ls1 ls_owner : UCOS2_Verify_State) : Prop :=
  mutex_del_owner_restore_total sg e ls1 tt ls_owner.

Definition mutex_del_owner_stage_prop := mutex_del_rdyatprio_stage_prop.

(** Owner restoration never allocates or frees an event.  The waiting-owner
    arm can update one live event's wait-list ordering, but the free-event
    list itself is unchanged in all three source-total relocation arms. *)
Lemma mutex_del_atomic_task_set_curPrio_preserves_unused_events :
  forall sg tid prio pre post,
    atomic_task_set_curPrio sg tid prio pre tt post ->
    post.(EventState).(unUsedEventStates) =
    pre.(EventState).(unUsedEventStates).
Proof.
  intros sg tid prio pre post Hstep.
  unfold atomic_task_set_curPrio in Hstep.
  destruct Hstep as [Hready | [Hwaiting | Hdormant]].
  - unfold atomic_task_set_curPrio_ready in Hready.
    destruct Hready as [t [oldPrio [t'
      [_ [_ [_ [_ [_ [_ [_ [_ Hpost]]]]]]]]]]].
    cbv zeta in Hpost. subst post. reflexivity.
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
       evSt2 & pty & Hnot_ready & Htask & Hold & Hne & Hlo & Hhi &
       Hpt & Hpend & Hevent & Hmulti & Hget & Htype & Hin & Ht' &
       Htsk & Hwait' & Hev & Hpost).
    rewrite Hpost, Hev. unfold update_event_field_raw. reflexivity.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask & Hold & Hne &
       Hlo & Hhi & Hpt & Hevent & Hmulti & Hnot_effective & Ht' &
       Htsk & Hpost).
    rewrite Hpost. reflexivity.
Qed.

Lemma mutex_del_rdyatprio_stage_preserves_unused_events :
  forall sg e pre post,
    mutex_del_rdyatprio_stage_prop sg e pre post ->
    post.(EventState).(unUsedEventStates) =
    pre.(EventState).(unUsedEventStates).
Proof.
  intros sg e pre post Hstage.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as (m & _ & _ & _ & Hexec).
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - subst post. reflexivity.
  - destruct m.(mfOwner) as [owner_tid|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [owner_orig|] eqn:Horig;
      simpl in Hexec.
    + destruct Hexec as (owner_t & _ & Hexec).
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Hprio.
      * eapply mutex_del_atomic_task_set_curPrio_preserves_unused_events.
        exact Hexec.
      * subst post. reflexivity.
    + contradiction.
    + contradiction.
    + subst post. reflexivity.
Qed.

(** Exact selected-event residual after an owner relocation or one or more
    OS_EventTaskRdy calls.  The post task/event states remain invariant
    closed, but the scheduler representation deliberately uses the current
    source-total raw stage: ready/current cells denote [post], while the two
    high-ready cache cells are still anchored in [anchor]. *)
Definition mutex_del_event_ready_focus_inv
  (sg : StableGlobVars) (anchor post : UCOS2_Verify_State)
  (eid : EventID) : Assertion :=
  interrupt_inv sg post.(IntrState) **
  verification_slice_task_inv sg post.(TskState) **
  verification_slice_sched_raw_ready_prio_stage
    sg anchor.(SchedState) post.(SchedState) post.(TskState) **
  mutex_del_event_inv_no_eid_no_free_head
    sg post.(TskState) post.(EventState) eid **
  verification_slice_tick_inv sg post.(TickState) **
  coq_prop
    (verification_slice_sched_in_range sg post.(TskState) post.(SchedState) /\
     verification_slice_cross_module_consistency sg post).

(** Existential owner-stage package used at the C branch join.  The endpoint
    is chosen by the source branch (identity, or the exact owner helper
    result); callers cannot instantiate an unrelated public [With] state. *)
Definition mutex_del_owner_stage_focus
  (sg : StableGlobVars) (e : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  EX owner_post : UCOS2_Verify_State,
    Ucos2Verify.lib.ucos2_rules_lib.InsideCritical sg owner_post **
    mutex_del_event_ready_focus_inv sg entry owner_post eid **
    coq_prop
      (mutex_del_rdyatprio_stage_prop sg e entry owner_post).

(** Selected-event residual with exactly one priority-table cell removed.
    It is the only representation used while the literal
    [OSTCBPrioTbl[pcp] = 0] store is pending. *)
Definition mutex_del_event_missing_priotbl_focus
  (sg : StableGlobVars) (anchor post : UCOS2_Verify_State)
  (eid : EventID) (pcp : Priority) : Assertion :=
  interrupt_inv sg post.(IntrState) **
  verification_slice_task_inv_missing_priotbl sg post.(TskState) pcp **
  verification_slice_sched_raw_ready_prio_stage
    sg anchor.(SchedState) post.(SchedState) post.(TskState) **
  mutex_del_event_inv_no_eid_no_free_head
    sg post.(TskState) post.(EventState) eid **
  verification_slice_tick_inv sg post.(TickState) **
  coq_prop
    (verification_slice_sched_in_range sg post.(TskState) post.(SchedState) /\
     verification_slice_cross_module_consistency sg post).

Lemma mutex_del_prioTbl_to_addrs_rec_Zlength :
  forall sg table n acc,
    Zlength (verification_slice_prioTbl_to_addrs_rec sg table n acc) =
    Z.of_nat n + Zlength acc.
Proof.
  intros sg table n.
  induction n as [|n IH]; intros acc.
  - change (Zlength acc = Z.of_nat 0 + Zlength acc). lia.
  - change
      (Zlength
         (verification_slice_prioTbl_to_addrs_rec sg table n
            (verification_slice_prio_tbl_entry_to_addr sg (table (Z.of_nat n)) :: acc)) =
       Z.of_nat (S n) + Zlength acc).
    rewrite IH, Zlength_cons, Nat2Z.inj_succ. lia.
Qed.

Lemma mutex_del_prioTbl_to_addrs_Zlength :
  forall sg table,
    Zlength (verification_slice_prioTbl_to_addrs sg table) = OS_PRIO_TBL_SIZE.
Proof.
  intros sg table.
  unfold verification_slice_prioTbl_to_addrs, OS_PRIO_TBL_SIZE.
  rewrite mutex_del_prioTbl_to_addrs_rec_Zlength.
  cbn. lia.
Qed.

Lemma mutex_del_store_prio_tbl_split_exists :
  forall sg table pcp,
    priotbl_index_in_range pcp ->
    verification_slice_store_prio_tbl sg table |--
      EX old_cell : addr,
        priotbl_element_store sg.(g_OSTCBPrioTbl) pcp old_cell **
        verification_slice_store_prio_tbl_missing_i sg table pcp.
Proof.
  intros sg table pcp Hrange.
  unfold verification_slice_store_prio_tbl, verification_slice_store_prio_tbl_missing_i.
  pose proof
    (mutex_del_prioTbl_to_addrs_Zlength sg table) as Hlen.
  sep_apply_l_atomic
    (verification_slice_store_priotbl_list_split
       sg (verification_slice_prioTbl_to_addrs sg table) pcp Hrange Hlen).
  Exists (Znth pcp (verification_slice_prioTbl_to_addrs sg table) 0).
  cancel.
Qed.

Lemma mutex_del_event_focus_split_priotbl :
  forall sg anchor post eid pcp,
    priotbl_index_in_range pcp ->
    mutex_del_event_ready_focus_inv sg anchor post eid |--
      EX old_cell : addr,
        priotbl_element_store sg.(g_OSTCBPrioTbl) pcp old_cell **
        mutex_del_event_missing_priotbl_focus sg anchor post eid pcp.
Proof.
  intros sg anchor post eid pcp Hrange.
  unfold mutex_del_event_ready_focus_inv,
    mutex_del_event_missing_priotbl_focus.
  unfold verification_slice_task_inv.
  pureIntros.
  sep_apply_l_atomic
    (mutex_del_store_prio_tbl_split_exists
       sg post.(TskState).(prioTbl) pcp Hrange).
  Intros old_cell.
  Exists old_cell.
  unfold verification_slice_task_inv_missing_priotbl.
  cancel.
  andp_cancel.
  sepcon_assoc_change.
  cancel.
Qed.

(** Concrete representation after the conditional PCP-table store.  In the
    disabled arm the full focused invariant is unchanged.  In the enabled
    arm the old mathematical state remains the transition source, while its
    table cell is held separately with the literal null value. *)
Definition mutex_del_pcp_release_focus
  (sg : StableGlobVars) (anchor post : UCOS2_Verify_State)
  (eid : EventID) (pcp : Priority) : Assertion :=
  if Z.eqb pcp sg.(osPrioMutexCeilDis)
  then mutex_del_event_ready_focus_inv sg anchor post eid
  else
    priotbl_element_store sg.(g_OSTCBPrioTbl) pcp 0 **
    mutex_del_event_missing_priotbl_focus sg anchor post eid pcp.

Definition mutex_del_owner_release_stage_focus
  (sg : StableGlobVars) (e : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID)
  (pcp : Priority) : Assertion :=
  EX owner_post : UCOS2_Verify_State,
    Ucos2Verify.lib.ucos2_rules_lib.InsideCritical sg owner_post **
    mutex_del_pcp_release_focus sg entry owner_post eid pcp **
    coq_prop
      (mutex_del_rdyatprio_stage_prop sg e entry owner_post).

Definition mutex_del_no_pend_pcp_release_residual
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (base : addr)
  (ecnt eptr egrp : Z) (pcp : Priority) (free_head : addr) : Assertion :=
  EX owner_post : UCOS2_Verify_State,
  EX current_event : OSEventAbstractState,
  EX current_tbl : list Z,
    Ucos2Verify.lib.ucos2_rules_lib.InsideCritical sg owner_post **
    mutex_del_pcp_release_focus sg entry owner_post eid pcp **
    (base + OSEventType_off) # UChar |->
      encode_event_type current_event.(eventType) **
    (base + OSEventPtr_off) # Ptr |-> eptr **
    used_event_wait_table_storage
      owner_post.(TskState) base current_event **
    coq_prop
      (mutex_del_rdyatprio_stage_prop
         sg initial_event entry owner_post /\
       pcp = decode_PCP_from_cnt ecnt /\
       event_free_list_head_prop
         sg owner_post.(EventState) free_head /\
       event_snapshot_of_prop
         sg owner_post.(TskState) owner_post.(EventState) eid current_event
         (encode_event_type current_event.(eventType))
         ecnt eptr egrp current_tbl).

(** The raw wake relation deliberately exposes the waiter selected from the
    event bitmap and the task selected from [OSTCBPrioTbl] separately.  At a
    stable Delete loop checkpoint, task-priority uniqueness proves that the
    two observations name the same live task. *)
Lemma mutex_del_atomic_event_task_rdy_identity :
  forall sg eid pre post returned_prio canonical_waiter table_owner,
    verification_slice_task_validity sg pre.(TskState) ->
    atomic_event_task_rdy
      sg eid PendAbort pre returned_prio
      canonical_waiter table_owner post ->
    canonical_waiter = table_owner.
Proof.
  intros sg eid pre post returned_prio canonical_waiter table_owner
    Htask Hwake.
  destruct Htask as [Hvalid _].
  unfold verification_slice_task_in_range in Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ Hunique]]]]]].
  unfold atomic_event_task_rdy, atomic_event_task_rdy_one in Hwake.
  destruct Hwake as
    (e1 & e2 & canonical_t & table_t & table_t' &
     Hevent & Hpend & Hnonempty & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hpost).
  eapply Hunique.
  - exact Hcanonical_get.
  - exact Htable_get.
  - rewrite Htable_prio, Hreturned. reflexivity.
Qed.

(** One source-literal successful loop iteration.  The identities remain
    existential, but the canonical waiter/table-owner equality is retained
    in the history instead of being discarded at the external-call edge. *)
Definition mutex_del_wake_step
  (sg : StableGlobVars) (eid : EventID)
  (pre post : UCOS2_Verify_State) : Prop :=
  exists returned_prio canonical_waiter table_owner,
    canonical_waiter = table_owner /\
    atomic_event_task_rdy
      sg eid PendAbort pre returned_prio
      canonical_waiter table_owner post.

Lemma mutex_del_wake_step_intro :
  forall sg eid pre post returned_prio canonical_waiter table_owner,
    verification_slice_task_validity sg pre.(TskState) ->
    atomic_event_task_rdy
      sg eid PendAbort pre returned_prio
      canonical_waiter table_owner post ->
    mutex_del_wake_step sg eid pre post.
Proof.
  intros sg eid pre post returned_prio canonical_waiter table_owner
    Htask Hwake.
  exists returned_prio, canonical_waiter, table_owner.
  split.
  - eapply mutex_del_atomic_event_task_rdy_identity; eassumption.
  - exact Hwake.
Qed.

(** OS_EventTaskRdy changes one live event and task/scheduler state, never the
    event free list.  This fact is carried through the loop RTC so the later
    literal [OSEventPtr = OSEventFreeList] write retains its exact value
    lineage. *)
Lemma mutex_del_wake_step_preserves_unused_events :
  forall sg eid pre post,
    mutex_del_wake_step sg eid pre post ->
    post.(EventState).(unUsedEventStates) =
    pre.(EventState).(unUsedEventStates).
Proof.
  intros sg eid pre post Hstep.
  unfold mutex_del_wake_step, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hstep.
  repeat match type of Hstep with
         | ex _ => destruct Hstep as [? Hstep]
         | _ /\ _ => destruct Hstep as [_ Hstep]
         end.
  cbv zeta in Hstep. subst post.
  unfold update_event_field_raw. reflexivity.
Qed.

Inductive mutex_del_wake_steps
  (sg : StableGlobVars) (eid : EventID)
  : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| mutex_del_wake_steps_refl :
    forall s, mutex_del_wake_steps sg eid s s
| mutex_del_wake_steps_snoc :
    forall s0 s1 s2,
      mutex_del_wake_steps sg eid s0 s1 ->
      mutex_del_wake_step sg eid s1 s2 ->
      mutex_del_wake_steps sg eid s0 s2.

Lemma mutex_del_wake_steps_preserves_unused_events :
  forall sg eid pre post,
    mutex_del_wake_steps sg eid pre post ->
    post.(EventState).(unUsedEventStates) =
    pre.(EventState).(unUsedEventStates).
Proof.
  intros sg eid pre post Hsteps.
  induction Hsteps as [s | s0 s1 s2 Hprefix IH Hlast].
  - reflexivity.
  - rewrite (mutex_del_wake_step_preserves_unused_events
               sg eid s1 s2 Hlast).
    exact IH.
Qed.

Lemma mutex_del_owner_wake_free_head_transport :
  forall sg e eid entry owner_post current free_head,
    event_free_list_head_prop sg entry.(EventState) free_head ->
    mutex_del_rdyatprio_stage_prop sg e entry owner_post ->
    mutex_del_wake_steps sg eid owner_post current ->
    event_free_list_head_prop sg current.(EventState) free_head.
Proof.
  intros sg e eid entry owner_post current free_head
    Hhead Howner Hwakes.
  unfold event_free_list_head_prop in Hhead |- *.
  rewrite (mutex_del_wake_steps_preserves_unused_events
             sg eid owner_post current Hwakes).
  rewrite (mutex_del_rdyatprio_stage_preserves_unused_events
             sg e entry owner_post Howner).
  exact Hhead.
Qed.

Definition mutex_del_abort_loop_stage_prop
  (sg : StableGlobVars) (eid : EventID)
  (ls_owner ls_ready : UCOS2_Verify_State) : Prop :=
  mutex_del_wake_steps sg eid ls_owner ls_ready.

(** Case-local loop residuals.  The selected count and group cells stay
    outside so the literal C guards can read them.  Every other selected
    event cell and the exact owner/RTC endpoints are existentially packaged;
    no public arbitrary state can be substituted at a later join. *)
Definition mutex_del_abort_loop_residual
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (base : addr)
  (ecnt eptr egrp : Z) (free_head : addr) : Assertion :=
  EX owner_post current : UCOS2_Verify_State,
  EX current_event : OSEventAbstractState,
  EX current_tbl : list Z,
    Ucos2Verify.lib.ucos2_rules_lib.InsideCritical sg current **
    mutex_del_event_ready_focus_inv sg entry current eid **
    (base + OSEventType_off) # UChar |->
      encode_event_type current_event.(eventType) **
    (base + OSEventPtr_off) # Ptr |-> eptr **
    used_event_wait_table_storage current.(TskState) base current_event **
    coq_prop
      (mutex_del_rdyatprio_stage_prop
         sg initial_event entry owner_post /\
       mutex_del_wake_steps sg eid owner_post current /\
       event_free_list_head_prop
         sg current.(EventState) free_head /\
       event_snapshot_of_prop
         sg current.(TskState) current.(EventState) eid current_event
         (encode_event_type current_event.(eventType))
         ecnt eptr egrp current_tbl).

Definition mutex_del_abort_loop_missing_priotbl_residual
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (base : addr)
  (ecnt eptr egrp : Z) (pcp : Priority) (free_head : addr) : Assertion :=
  EX owner_post current : UCOS2_Verify_State,
  EX current_event : OSEventAbstractState,
  EX current_tbl : list Z,
    Ucos2Verify.lib.ucos2_rules_lib.InsideCritical sg current **
    mutex_del_event_missing_priotbl_focus
      sg entry current eid pcp **
    (base + OSEventType_off) # UChar |->
      encode_event_type current_event.(eventType) **
    (base + OSEventPtr_off) # Ptr |-> eptr **
    used_event_wait_table_storage current.(TskState) base current_event **
    coq_prop
      (mutex_del_rdyatprio_stage_prop
         sg initial_event entry owner_post /\
       mutex_del_wake_steps sg eid owner_post current /\
       event_free_list_head_prop
         sg current.(EventState) free_head /\
       event_snapshot_of_prop
         sg current.(TskState) current.(EventState) eid current_event
         (encode_event_type current_event.(eventType))
         ecnt eptr egrp current_tbl).

Definition mutex_del_abort_loop_pcp_release_residual
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (base : addr)
  (ecnt eptr egrp : Z) (pcp : Priority) (free_head : addr) : Assertion :=
  coq_prop (pcp = decode_PCP_from_cnt ecnt) &&
  (if Z.eqb pcp sg.(osPrioMutexCeilDis)
   then mutex_del_abort_loop_residual
          sg initial_event entry eid base ecnt eptr egrp free_head
   else
     priotbl_element_store sg.(g_OSTCBPrioTbl) pcp 0 **
     mutex_del_abort_loop_missing_priotbl_residual
       sg initial_event entry eid base ecnt eptr egrp pcp free_head).

Definition mutex_del_no_pend_prepare_stage_prop
  (eid : EventID) (ls_owner ls_prepare : UCOS2_Verify_State) : Prop :=
  mutex_del_no_pend_prepare eid ls_owner tt ls_prepare.

Definition mutex_del_free_stage_prop
  (sg : StableGlobVars) (eid : EventID)
  (ls_prepare ls_free : UCOS2_Verify_State) : Prop :=
  atomic_event_free_with_priotbl_free
    sg eid ls_prepare tt ls_free.

Definition mutex_del_sched_stage_prop
  (ls_free ls_sched : UCOS2_Verify_State) : Prop :=
  exists sched_result,
    atomic_sched ls_free sched_result ls_sched.

Definition mutex_del_optional_sched_stage_prop
  (tasks_waiting : bool)
  (ls_free ls_out : UCOS2_Verify_State) : Prop :=
  if tasks_waiting
  then mutex_del_sched_stage_prop ls_free ls_out
  else ls_out = ls_free.

(** Source-exact carrier for the delete transient.  Full representation is
    retained when no derived scheduler cache is pending.  Otherwise raw task,
    event, and scheduler ownership is paired with the complete pure validity
    bundle, while [UCOS2_verification_slice_raw_ready_prio_stage] records that the concrete
    high-ready cache pair still denotes [entry].  Successful public
    [OSMutexDel_full] exits expose this exact disjunction; unchanged/error
    exits continue to expose [UCOS2_verification_slice_inv]. *)
Definition mutex_del_transition_rep
  (sg : StableGlobVars) (entry post : UCOS2_Verify_State) : Assertion :=
  UCOS2_verification_slice_inv sg post ||
  ((UCOS2_verification_slice_raw_rep sg post ||
    UCOS2_verification_slice_raw_ready_prio_stage sg entry post) &&
   coq_prop (UCOS2_verification_slice_state_inv sg post)).

(** Exact closure condition for the only concrete cache cells that the
    raw-ready stage leaves anchored at function entry.  It holds when the
    relocation did not change the abstract high-ready choice, or after an
    enabled scheduler-selection step has installed that choice.  Merely
    calling [OS_Sched] is deliberately not enough: under scheduler locking
    [atomic_sched] may be the identity. *)
Definition mutex_del_high_ready_cache_closed_prop
  (entry post : UCOS2_Verify_State) : Prop :=
  entry.(SchedState).(highRdyPrio) =
    post.(SchedState).(highRdyPrio) /\
  entry.(SchedState).(highRdyTid) =
    post.(SchedState).(highRdyTid).

(** The source uses a bounded eight-bit scan rather than relying on the
    scheduler-lock-gated [OS_Sched]. *)
Definition mutex_del_first_set8 (bits : Z) : Z :=
  if negb (Z.eqb (Z.land bits 1) 0) then 0 else
  if negb (Z.eqb (Z.land bits 2) 0) then 1 else
  if negb (Z.eqb (Z.land bits 4) 0) then 2 else
  if negb (Z.eqb (Z.land bits 8) 0) then 3 else
  if negb (Z.eqb (Z.land bits 16) 0) then 4 else
  if negb (Z.eqb (Z.land bits 32) 0) then 5 else
  if negb (Z.eqb (Z.land bits 64) 0) then 6 else 7.

Definition mutex_del_refresh_grp_value
  (post : UCOS2_Verify_State) : Z :=
  encode_ready_grp post.(SchedState).(readyList) post.(TskState).

Definition mutex_del_refresh_ready_tbl_values
  (post : UCOS2_Verify_State) : list Z :=
  [encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) 0;
   encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) 1;
   encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) 2;
   encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) 3;
   encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) 4;
   encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) 5;
   encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) 6;
   encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) 7].

Definition mutex_del_refresh_prio_tbl_values
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : list addr :=
  verification_slice_prioTbl_to_addrs sg post.(TskState).(prioTbl).

(** Pure snapshot used to verify the literal bounded scan.  The final two
    equalities are mathematical consequences of the ordered ready-list,
    scheduler validity, and priority-table consistency; they are exposed as
    proof obligations at the transition-to-refresh boundary, not assumed by
    the public API. *)
Definition mutex_del_refresh_snapshot_prop
  (sg : StableGlobVars) (post : UCOS2_Verify_State)
  (rdy_grp : Z) (rdy_tbl : list Z) (prio_tbl : list addr) : Prop :=
  rdy_grp =
    encode_ready_grp post.(SchedState).(readyList) post.(TskState) /\
  rdy_tbl = mutex_del_refresh_ready_tbl_values post /\
  prio_tbl = verification_slice_prioTbl_to_addrs sg post.(TskState).(prioTbl) /\
  match post.(SchedState).(readyList) with
  | [] =>
      rdy_grp = 0 /\
      post.(SchedState).(highRdyPrio) = None /\
      post.(SchedState).(highRdyTid) = None
  | head :: _ =>
      exists head_t,
        post.(TskState).(inUsedTaskStates) head = Some head_t /\
        0 <= head_t.(curPrio) < 64 /\
        rdy_grp <> 0 /\
        mutex_del_first_set8 rdy_grp = head_t.(curPrio) / 8 /\
        Znth (mutex_del_first_set8 rdy_grp) rdy_tbl 0 <> 0 /\
        mutex_del_first_set8
          (Znth (mutex_del_first_set8 rdy_grp) rdy_tbl 0) =
          head_t.(curPrio) mod 8 /\
        Znth head_t.(curPrio) prio_tbl 0 = verification_slice_tcb_addr sg head /\
        post.(SchedState).(highRdyPrio) = Some head_t.(curPrio) /\
        post.(SchedState).(highRdyTid) = Some head
  end.

Definition mutex_del_refresh_choice_prop
  (sg : StableGlobVars) (post : UCOS2_Verify_State)
  (high_prio high_tcb : Z) : Prop :=
  high_prio =
    match post.(SchedState).(highRdyPrio) with
    | Some p => p
    | None => 0xFF
    end /\
  high_tcb =
    match post.(SchedState).(highRdyTid) with
    | Some tid => verification_slice_tcb_addr sg tid
    | None => 0
    end.

(** Every scheduler cell except the ready bitmap/table and high-ready pair.
    This explicitly frames OSPrioCur, OSTCBCur, the switch counter, and the
    running flag across the refresh body. *)
Definition mutex_del_sched_refresh_rest
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSPrioCur) # UChar |->
    (match post.(SchedState).(curSchedPrio) with
     | Some p => p | None => 0xFF
     end) **
  sg.(g_OSTCBCur) # Ptr |->
    (match post.(SchedState).(curTaskID) with
     | Some tid => verification_slice_tcb_addr sg tid | None => 0
     end) **
  sg.(g_OSCtxSwCtr) # UInt |-> post.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |->
    (if post.(SchedState).(isRunning) then 1 else 0).

Definition mutex_del_refresh_residual
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg post.(IntrState) **
  verification_slice_task_raw_rep_no_priotbl sg post.(TskState) **
  mutex_del_sched_refresh_rest sg post **
  verification_slice_event_raw_rep sg post.(TskState) post.(EventState) **
  verification_slice_tick_inv sg post.(TickState) **
  TT.

(** Exact spatial heap after the bounded C body has overwritten the two
    cache cells.  Keeping the pure validity bundle outside this definition
    makes the spatial-to-raw regrouping independent of sepcon syntax. *)
Definition mutex_del_refresh_spatial
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |->
    encode_ready_grp post.(SchedState).(readyList) post.(TskState) **
  Ucos2Verify.lib.array_abstraction.store_osrdytbl
    sg (mutex_del_refresh_ready_tbl_values post) **
  sg.(g_OSPrioHighRdy) # UChar |->
    (match post.(SchedState).(highRdyPrio) with
     | Some p => p | None => 0xFF
     end) **
  sg.(g_OSTCBHighRdy) # Ptr |->
    (match post.(SchedState).(highRdyTid) with
     | Some tid => verification_slice_tcb_addr sg tid | None => 0
     end) **
  verification_slice_store_priotbl_list
    sg (verification_slice_prioTbl_to_addrs sg post.(TskState).(prioTbl)) **
  mutex_del_refresh_residual sg post.

(** No abstract module field changes: [post] already contains the normalized
    high-ready choice; only its physical representation was stale. *)
Definition mutex_del_refresh_closed_inv
  (sg : StableGlobVars) (post : UCOS2_Verify_State) : Assertion :=
  UCOS2_verification_slice_raw_rep sg post &&
  coq_prop (UCOS2_verification_slice_state_inv sg post).

Lemma mutex_del_task_raw_rep_close :
  forall sg st,
    verification_slice_task_validity sg st ->
    verification_slice_task_raw_rep sg st |-- verification_slice_task_inv sg st.
Proof.
  intros sg st Hvalid.
  unfold verification_slice_task_inv.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact Hvalid.
  - unfold verification_slice_task_raw_rep. reflexivity.
Qed.

Lemma mutex_del_sched_raw_rep_close :
  forall sg tskSt schedSt,
    verification_slice_task_validity sg tskSt ->
    verification_slice_sched_in_range sg tskSt schedSt ->
    verification_slice_sched_raw_rep sg tskSt schedSt |--
      verification_slice_sched_inv sg tskSt schedSt.
Proof.
  intros sg tskSt schedSt Htask Hsched.
  unfold verification_slice_sched_inv.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact Hsched.
  - assert (Heq : forall y,
      encode_ready_tbl_at schedSt.(readyList) tskSt y =
      encode_ready_tbl_at_or schedSt.(readyList) tskSt y).
    {
      intro y.
      apply (sched_stable_tbl_eq_or sg tskSt schedSt y);
        assumption.
    }
    unfold verification_slice_sched_raw_rep, verification_slice_store_sched_state.
    rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
      <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
    reflexivity.
Qed.

Lemma verification_slice_mutex_del_sched_raw_ready_prio_stage_close :
  forall sg entry post tskSt,
    verification_slice_task_validity sg tskSt ->
    verification_slice_sched_in_range sg tskSt post ->
    entry.(highRdyPrio) = post.(highRdyPrio) ->
    entry.(highRdyTid) = post.(highRdyTid) ->
    verification_slice_sched_raw_ready_prio_stage sg entry post tskSt |--
      verification_slice_sched_inv sg tskSt post.
Proof.
  intros sg entry post tskSt Htask Hsched Hprio Htid.
  unfold verification_slice_sched_inv.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact Hsched.
  - assert (Heq : forall y,
      encode_ready_tbl_at post.(readyList) tskSt y =
      encode_ready_tbl_at_or post.(readyList) tskSt y).
    {
      intro y.
      apply (sched_stable_tbl_eq_or sg tskSt post y);
        assumption.
    }
    unfold verification_slice_sched_raw_ready_prio_stage, verification_slice_store_sched_state.
    rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
      <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
    rewrite Hprio, Htid.
    reflexivity.
Qed.

Lemma mutex_del_event_raw_rep_close :
  forall sg tskSt eventSt,
    verification_slice_task_validity sg tskSt ->
    verification_slice_event_in_range sg tskSt eventSt ->
    verification_slice_event_raw_rep sg tskSt eventSt |--
      verification_slice_event_inv sg tskSt eventSt.
Proof.
  intros sg tskSt eventSt Htask Hevent.
  unfold verification_slice_event_inv.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact Hevent.
  - unfold verification_slice_event_raw_rep, store_used_event_map,
      store_used_event_map_raw, store_map.
    Intros l.
    Exists l.
    assert (Hmap :
      map
        (fun eid =>
           match eventSt.(inUsedEventStates) eid with
           | Some e =>
               used_complete_event sg tskSt (event_addr sg eid) eid e
           | None => emp
           end) l =
      map
        (fun eid =>
           match eventSt.(inUsedEventStates) eid with
           | Some e =>
               used_complete_event_raw sg tskSt
                 (event_addr sg eid) eid e
           | None => emp
           end) l).
    {
      apply map_ext_in.
      intros eid Hin.
      destruct (eventSt.(inUsedEventStates) eid) as [e|]
        eqn:Hlookup; [|reflexivity].
      apply used_complete_event_stable_eq_raw.
      - unfold verification_slice_event_in_range, verification_slice_event_in_range,
          verification_slice_event_in_range in Hevent.
        destruct Hevent as [_ [_ [_ [_ [_ [_ [_ Hentry]]]]]]].
        specialize (Hentry eid e Hlookup).
        unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency
          in Hentry.
        exact (proj1 Hentry).
      - unfold verification_slice_task_validity, verification_slice_task_in_range,
          verification_slice_task_in_range in Htask.
        destruct Htask as [Htask _].
        destruct Htask as [_ [_ [_ [_ [_ [_ Hunique]]]]]].
        exact Hunique.
    }
    rewrite Hmap.
    entailer!.
Qed.

Lemma mutex_del_raw_validity_close :
  forall sg post,
    UCOS2_verification_slice_state_inv sg post ->
    UCOS2_verification_slice_raw_rep sg post |-- UCOS2_verification_slice_inv sg post.
Proof.
  intros sg post Hvalid.
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [Htask [Hsched [Hevent Hcross]]].
  unfold UCOS2_verification_slice_raw_rep, UCOS2_verification_slice_inv.
  sep_apply_l_atomic
    (mutex_del_task_raw_rep_close sg post.(TskState) Htask).
  sep_apply_l_atomic
    (mutex_del_sched_raw_rep_close
       sg post.(TskState) post.(SchedState) Htask Hsched).
  sep_apply_l_atomic
    (mutex_del_event_raw_rep_close
       sg post.(TskState) post.(EventState) Htask Hevent).
  entailer!.
Qed.

Lemma mutex_del_refresh_closed_full :
  forall sg post,
    mutex_del_refresh_closed_inv sg post |--
      UCOS2_verification_slice_inv sg post.
Proof.
  intros sg post.
  intros h Hclosed.
  unfold mutex_del_refresh_closed_inv, andp, coq_prop in Hclosed.
  destruct Hclosed as [Hraw Hvalid].
  exact (mutex_del_raw_validity_close sg post Hvalid h Hraw).
Qed.

Lemma mutex_del_raw_ready_validity_close :
  forall sg entry post,
    UCOS2_verification_slice_state_inv sg post ->
    mutex_del_high_ready_cache_closed_prop entry post ->
    UCOS2_verification_slice_raw_ready_prio_stage sg entry post |--
      UCOS2_verification_slice_inv sg post.
Proof.
  intros sg entry post Hvalid Hcache.
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [Htask [Hsched [Hevent Hcross]]].
  unfold mutex_del_high_ready_cache_closed_prop in Hcache.
  destruct Hcache as [Hprio Htid].
  unfold UCOS2_verification_slice_raw_ready_prio_stage, UCOS2_verification_slice_inv.
  sep_apply_l_atomic
    (mutex_del_task_raw_rep_close sg post.(TskState) Htask).
  sep_apply_l_atomic
    (verification_slice_mutex_del_sched_raw_ready_prio_stage_close
       sg entry.(SchedState) post.(SchedState) post.(TskState)
       Htask Hsched Hprio Htid).
  sep_apply_l_atomic
    (mutex_del_event_raw_rep_close
       sg post.(TskState) post.(EventState) Htask Hevent).
  entailer!.
Qed.

(** Conditional recovery of the historical full public invariant.  This is
    intentionally conditional on the exact high-ready cache closure; it does
    not hide that condition in the function precondition or pretend that a
    scheduler call performed a selection while scheduler locking was active. *)
Lemma mutex_del_transition_rep_full_if_cache_closed :
  forall sg entry post,
    mutex_del_high_ready_cache_closed_prop entry post ->
    mutex_del_transition_rep sg entry post |--
      UCOS2_verification_slice_inv sg post.
Proof.
  intros sg entry post Hcache.
  intros h Hrep.
  unfold mutex_del_transition_rep, orp, andp, coq_prop in Hrep.
  destruct Hrep as [Hfull | [[Hraw | Hready] Hvalid]].
  - exact Hfull.
  - exact (mutex_del_raw_validity_close sg post Hvalid h Hraw).
  - exact
      (mutex_del_raw_ready_validity_close
         sg entry post Hvalid Hcache h Hready).
Qed.

(** A scheduler call started from a valid full state preserves the already
    selected high-ready pair.  Identity branches are immediate; the switch
    branch writes the same ready-list head guaranteed by scheduler validity. *)
Lemma mutex_del_sched_stage_cache_closed :
  forall sg pre post,
    UCOS2_verification_slice_state_inv sg pre ->
    mutex_del_sched_stage_prop pre post ->
    mutex_del_high_ready_cache_closed_prop pre post.
Proof.
  intros sg pre post Hvalid Hstage.
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [_ [Hsched _]].
  unfold verification_slice_sched_in_range in Hsched.
  destruct Hsched as
    [_ [_ [_ [_ [_ [Hhigh _]]]]]].
  unfold mutex_del_sched_stage_prop in Hstage.
  destruct Hstage as [res Hatomic].
  unfold atomic_sched in Hatomic.
  cbn beta in Hatomic.
  destruct
    ((Z.eqb pre.(IntrState).(intNesting) 0 &&
      Z.eqb pre.(IntrState).(lockNesting) 0)%bool)
    eqn:Hgate.
  - destruct pre.(SchedState).(readyList) as [|head tail]
      eqn:Hready.
    + destruct Hatomic as [Hpost _]. subst post.
      unfold mutex_del_high_ready_cache_closed_prop.
      split; reflexivity.
    + destruct pre.(SchedState).(curTaskID) as [cur|]
        eqn:Hcur.
      * destruct
          (pre.(TskState).(inUsedTaskStates) head)
          as [headT|] eqn:Hhead.
        -- destruct
             (pre.(TskState).(inUsedTaskStates) cur)
             as [curT|] eqn:HcurT.
           ++ cbn in Hatomic.
              match type of Hatomic with
              | context [if ?b then _ else _] =>
                  destruct b eqn:Hswitch
              end.
              ** cbn in Hatomic.
                 destruct Hatomic as
                   [schedSt2 [HschedSt2 [Hpost _]]].
                 subst schedSt2. subst post.
                 unfold sched_high_ready_consistency in Hhigh.
                 rewrite Hready in Hhigh.
                 cbn in Hhigh.
                 destruct Hhigh as [Htid [t [Ht Hprio]]].
                 rewrite Hhead in Ht. inversion Ht. subst t.
                 unfold mutex_del_high_ready_cache_closed_prop.
                 cbn. split; assumption.
              ** cbn in Hatomic.
                 destruct Hatomic as [Hpost _]. subst post.
                 unfold sched_high_ready_consistency in Hhigh.
                 rewrite Hready in Hhigh; cbn in Hhigh.
                 destruct Hhigh as [Htid [t [Ht Hprio]]].
                 rewrite Hhead in Ht; inversion Ht; subst t.
                 unfold mutex_del_high_ready_cache_closed_prop.
                 cbn; split; assumption.
           ++ cbn in Hatomic.
              destruct Hatomic as [Hpost _]. subst post.
              unfold mutex_del_high_ready_cache_closed_prop.
              split; reflexivity.
        -- cbn in Hatomic.
           destruct Hatomic as [Hpost _]. subst post.
           unfold mutex_del_high_ready_cache_closed_prop.
           split; reflexivity.
      * cbn in Hatomic.
        destruct Hatomic as [Hpost _]. subst post.
        unfold mutex_del_high_ready_cache_closed_prop.
        split; reflexivity.
  - cbn in Hatomic.
    destruct Hatomic as [Hpost _]. subst post.
    unfold mutex_del_high_ready_cache_closed_prop.
    split; reflexivity.
Qed.

(** [OS_CPU_SR_Restore] must preserve which representation family its caller
    supplies.  The tag prevents an unchanged/error path that starts with the
    full invariant from being weakened merely because successful deletion may
    temporarily carry the raw-ready cache stage. *)
Definition mutex_del_restore_rep
  (raw_stage : bool) (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) : Assertion :=
  if raw_stage
  then mutex_del_transition_rep sg entry post
  else UCOS2_verification_slice_inv sg post.

(** Explicit critical-section edges.  They package only the canonical STS
    facts already exposed by the architecture calls. *)
Definition mutex_del_enter_critical_call_prop
  (sg : StableGlobVars) (ls0 ls1 : UCOS2_Verify_State) : Prop :=
  RTrans_C sg ls0 sg ls1 /\
  crit_rel_no_os_state_change ls0 ls1.

Definition mutex_del_exit_critical_call_prop
  (sg : StableGlobVars) (ls1 ls2 : UCOS2_Verify_State) : Prop :=
  GTrans_C sg ls1 sg ls2 /\
  crit_rel_intr_only ls1 ls2.

(** Exit edge when the exact [InsideCritical] token is still anchored at the
    last pre-write logical state, while the concrete representation already
    describes [logical_post].  The C-level critical STS consumes the exact
    anchor; the intr-only relation states precisely what Restore changes
    relative to the already materialized logical post.  No inside-to-inside
    token retagging is assumed. *)
Definition mutex_del_exit_critical_anchored_call_prop
  (sg : StableGlobVars)
  (critical_anchor logical_post exited : UCOS2_Verify_State) : Prop :=
  GTrans_C sg critical_anchor sg exited /\
  crit_rel_intr_only logical_post exited.

(** The original Restore contract is the equal-anchor specialization of the
    anchor-aware contract.  This proved compatibility keeps unchanged/error
    callers on their existing interface while successful delete callers use
    the exact pre-free token anchor. *)
Lemma mutex_del_exit_critical_call_anchored_compat :
  forall sg logical_post exited,
    mutex_del_exit_critical_call_prop sg logical_post exited ->
    mutex_del_exit_critical_anchored_call_prop
      sg logical_post logical_post exited.
Proof.
  intros sg logical_post exited Hexit.
  exact Hexit.
Qed.

Definition mutex_del_mode_wake_prop
  (opt : MutexDelOpt) (sg : StableGlobVars) (eid : EventID)
  (owner_post current : UCOS2_Verify_State) : Prop :=
  match opt with
  | MutexDelNoPend => current = owner_post
  | MutexDelAlways => mutex_del_wake_steps sg eid owner_post current
  | MutexDelInvalid => False
  end.

(** Exact successful commit with the last pre-free critical-token anchor
    exposed.  [prepare] is the abstract selected-event owner-clear checkpoint;
    its cells are still caller-owned until the literal free writes have all
    executed. *)
Definition mutex_del_success_commit_anchor_prop
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (opt : MutexDelOpt)
  (critical_anchor commit : UCOS2_Verify_State) : Prop :=
  exists owner_post prepare,
    mutex_del_rdyatprio_stage_prop
      sg initial_event entry owner_post /\
    mutex_del_mode_wake_prop
      opt sg eid owner_post critical_anchor /\
    mutex_del_no_pend_prepare_stage_prop
      eid critical_anchor prepare /\
    mutex_del_free_stage_prop sg eid prepare commit.

(** Exact successful commit, up to but excluding the critical-section exit.
    The existential anchor is retained by annotation invariants whenever the
    spatial [InsideCritical] token is still live. *)
Definition mutex_del_success_commit_prop
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (opt : MutexDelOpt)
  (commit : UCOS2_Verify_State) : Prop :=
  exists critical_anchor,
    mutex_del_success_commit_anchor_prop
      sg initial_event entry eid opt critical_anchor commit.

(** Full source-level semantics for the repaired function.  The successful
    NO_PEND path now has the same source-ordered owner stage as ALWAYS, before
    PCP release and event free. *)
Definition OSMutexDel_full_sem
  (sg : StableGlobVars) (pevent : addr) (opt : MutexDelOpt)
  : program UCOS2_Verify_State (OSErrCode * option addr) :=
  fun ls0 ret ls2 =>
    let err := fst ret in
    let oret := snd ret in
    (pevent = 0 /\
     err = OS_ERR_PEVENT_NULL /\ oret = Some pevent /\ ls2 = ls0) \/
    (pevent <> 0 /\
     exists eid,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = None /\
       err = OS_ERR_EVENT_TYPE /\ oret = Some pevent /\ ls2 = ls0) \/
    (pevent <> 0 /\
     exists eid e,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) <> OS_EVENT_TYPE_MUTEX /\
       err = OS_ERR_EVENT_TYPE /\ oret = Some pevent /\ ls2 = ls0) \/
    (pevent <> 0 /\
     exists eid e m,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\
       ls0.(IntrState).(intNesting) > 0 /\
       err = OS_ERR_DEL_ISR /\ oret = Some pevent /\ ls2 = ls0) \/
    (pevent <> 0 /\ ls0.(IntrState).(intNesting) <= 0 /\
     opt = MutexDelNoPend /\
     exists eid e m exited,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\ e.(waitList) <> [] /\
       mutex_del_exit_critical_call_prop sg ls0 exited /\
       err = OS_ERR_TASK_WAITING /\ oret = Some pevent /\ ls2 = exited) \/
    (pevent <> 0 /\ ls0.(IntrState).(intNesting) <= 0 /\
     opt = MutexDelInvalid /\
     exists eid e m exited,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\
       mutex_del_exit_critical_call_prop sg ls0 exited /\
       err = OS_ERR_INVALID_OPT /\ oret = Some pevent /\ ls2 = exited) \/
    (pevent <> 0 /\ ls0.(IntrState).(intNesting) <= 0 /\
     opt = MutexDelNoPend /\
     exists eid e m critical_anchor commit exited,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\ e.(waitList) = [] /\
       mutex_del_success_commit_anchor_prop
         sg e ls0 eid MutexDelNoPend critical_anchor commit /\
       mutex_del_exit_critical_anchored_call_prop
         sg critical_anchor commit exited /\
       err = OS_ERR_NONE /\ oret = None /\ ls2 = exited) \/
    (pevent <> 0 /\ ls0.(IntrState).(intNesting) <= 0 /\
     opt = MutexDelAlways /\
     exists eid e m critical_anchor commit exited,
       pevent = event_addr sg eid /\
       ls0.(EventState).(inUsedEventStates) eid = Some e /\
       e.(eventType) = OS_EVENT_TYPE_MUTEX /\
       e.(mutexFields) = Some m /\
       mutex_del_success_commit_anchor_prop
         sg e ls0 eid MutexDelAlways critical_anchor commit /\
       mutex_del_exit_critical_anchored_call_prop
         sg critical_anchor commit exited /\
       err = OS_ERR_NONE /\ oret = None /\
       ((e.(waitList) = [] /\ ls2 = exited) \/
        (e.(waitList) <> [] /\
       mutex_del_sched_stage_prop exited ls2))).

(** L5/public functional postcondition for the ALWAYS-delete waiter effects.
    The source clears only the Mutex bit, then resets delay and event link.
    Entry wait consistency and its preservation through owner restoration
    and the wake loop prove that no other non-suspension bits remain.
    Ready-list insertion still depends on the preserved suspension flag;
    this derived effect does not strengthen the raw wake relation. *)
Definition mutex_del_waiters_aborted_effective_prop
  (e : OSEventAbstractState) (tskSt : Glob_TaskAbstractState)
  (schedSt : SchedAbstractState) : Prop :=
  forall tid,
    In tid e.(waitList) ->
    exists t,
      tskSt.(inUsedTaskStates) tid = Some t /\
      (task_non_suspension_bits (t.(stat))) = 0 /\
      t.(statPend) = PendAbort /\
      t.(dly) = 0 /\
      t.(eventPtr) = None /\
      ((task_is_suspended (t.(stat))) = false ->
       In tid schedSt.(readyList)).

(** Operation-owned successful state refinement used by the public post.
    This is deliberately narrower than a generic "all other events unchanged"
    frame: a waiting owner restoration may update that owner's distinct wait
    event.  Every admitted change is nevertheless tied to the exact source
    stages of this deletion, its critical exit, and (for ALWAYS/nonempty) the
    scheduler stage. *)
Definition mutex_del_success_post_refinement_prop
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (opt : MutexDelOpt)
  (post : UCOS2_Verify_State) : Prop :=
  match opt with
  | MutexDelNoPend =>
      exists critical_anchor commit,
        mutex_del_success_commit_anchor_prop
          sg initial_event entry eid MutexDelNoPend
          critical_anchor commit /\
        mutex_del_exit_critical_anchored_call_prop
          sg critical_anchor commit post
  | MutexDelAlways =>
      exists critical_anchor commit exited,
        mutex_del_success_commit_anchor_prop
          sg initial_event entry eid MutexDelAlways
          critical_anchor commit /\
        mutex_del_exit_critical_anchored_call_prop
          sg critical_anchor commit exited /\
        ((initial_event.(waitList) = [] /\ post = exited) \/
         (initial_event.(waitList) <> [] /\
          mutex_del_sched_stage_prop exited post))
  | MutexDelInvalid => False
  end.

Definition mutex_del_result_prop
  (sg : StableGlobVars) (pevent : addr) (opt : MutexDelOpt)
  (ls0 ls_post : UCOS2_Verify_State) (ret : Z) : Prop :=
  exists err oret,
    OSMutexDel_full_sem sg pevent opt ls0 (err, oret) ls_post /\
    ret = match oret with Some p => p | None => 0 end.

Definition mutex_del_success_commit_inv
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (opt : MutexDelOpt)
  (pevent : addr) (tasks_waiting : Z) X : Assertion :=
  EX critical_anchor commit : UCOS2_Verify_State,
    Ucos2Verify.lib.ucos2_rules_lib.InsideCritical
      sg critical_anchor **
    mutex_del_transition_rep sg entry commit **
    coq_prop
      (mutex_del_success_commit_anchor_prop
         sg initial_event entry eid opt critical_anchor commit /\
       mutex_del_source_entry_prop
         sg initial_event entry eid pevent tasks_waiting /\
       mutex_del_success_mode_prop opt tasks_waiting /\
       safeExec
         (LastSeen entry)
         (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
               (mutex_del_observe_ptr pevent)) X).

(** The executable refresh changes no abstract field.  It only closes the
    concrete high-ready cache pair for the already-computed [commit]. *)
Definition mutex_del_success_refreshed_commit_inv
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (opt : MutexDelOpt)
  (pevent : addr) (tasks_waiting : Z) X : Assertion :=
  EX critical_anchor commit : UCOS2_Verify_State,
    Ucos2Verify.lib.ucos2_rules_lib.InsideCritical
      sg critical_anchor **
    UCOS2_verification_slice_inv sg commit **
    coq_prop
      (mutex_del_success_commit_anchor_prop
         sg initial_event entry eid opt critical_anchor commit /\
       mutex_del_source_entry_prop
         sg initial_event entry eid pevent tasks_waiting /\
       mutex_del_success_mode_prop opt tasks_waiting /\
       safeExec
         (LastSeen entry)
         (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
               (mutex_del_observe_ptr pevent)) X).

Definition mutex_del_success_exit_inv
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (opt : MutexDelOpt)
  (pevent : addr) (tasks_waiting : Z) X : Assertion :=
  EX critical_anchor commit exited : UCOS2_Verify_State,
    Ucos2Verify.lib.ucos2_rules_lib.OutsideCritical sg exited **
    UCOS2_verification_slice_inv sg exited **
    coq_prop
      (mutex_del_success_commit_anchor_prop
         sg initial_event entry eid opt critical_anchor commit /\
       mutex_del_source_entry_prop
         sg initial_event entry eid pevent tasks_waiting /\
       mutex_del_success_mode_prop opt tasks_waiting /\
       mutex_del_exit_critical_anchored_call_prop
         sg critical_anchor commit exited /\
       UCOS2_verification_slice_state_inv sg exited /\
       valid_stable_glob_vars sg /\
       safeExec
         (LastSeen entry)
         (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
               (mutex_del_observe_ptr pevent)) X).

(** NO_PEND has no scheduler call after leaving the critical section.  This
    branch-specific package records that fact explicitly, rather than asking
    a generic exit wrapper to rule out the ALWAYS/nonempty case later. *)
Definition mutex_del_no_pend_exit_inv
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (opt : MutexDelOpt)
  (pevent : addr) (tasks_waiting : Z) X : Assertion :=
  EX critical_anchor commit exited : UCOS2_Verify_State,
    Ucos2Verify.lib.ucos2_rules_lib.OutsideCritical sg exited **
    UCOS2_verification_slice_inv sg exited **
    coq_prop
      (mutex_del_success_commit_anchor_prop
         sg initial_event entry eid opt critical_anchor commit /\
       mutex_del_source_entry_prop
         sg initial_event entry eid pevent tasks_waiting /\
       mutex_del_no_pend_mode_prop opt tasks_waiting /\
       mutex_del_exit_critical_anchored_call_prop
         sg critical_anchor commit exited /\
       valid_stable_glob_vars sg /\
       safeExec
         (LastSeen entry)
         (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
               (mutex_del_observe_ptr pevent)) X).

Definition mutex_del_success_out_inv
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (opt : MutexDelOpt)
  (pevent : addr) (tasks_waiting : Z) X : Assertion :=
  EX critical_anchor commit exited out : UCOS2_Verify_State,
    Ucos2Verify.lib.ucos2_rules_lib.OutsideCritical sg out **
    UCOS2_verification_slice_inv sg out **
    coq_prop
      (mutex_del_success_commit_anchor_prop
         sg initial_event entry eid opt critical_anchor commit /\
       mutex_del_source_entry_prop
         sg initial_event entry eid pevent tasks_waiting /\
       mutex_del_success_mode_prop opt tasks_waiting /\
       mutex_del_exit_critical_anchored_call_prop
         sg critical_anchor commit exited /\
       (if Z.eqb tasks_waiting 1
        then mutex_del_sched_stage_prop exited out
        else out = exited) /\
       valid_stable_glob_vars sg /\
       safeExec
         (LastSeen entry)
         (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
               (mutex_del_observe_ptr pevent)) X).

Definition mutex_del_unchanged_inside_inv
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (pevent : addr)
  (opt : MutexDelOpt) (tasks_waiting err : Z) X : Assertion :=
  Ucos2Verify.lib.ucos2_rules_lib.InsideCritical sg entry **
  UCOS2_verification_slice_inv sg entry **
  coq_prop
    (mutex_del_source_entry_prop
       sg initial_event entry eid pevent tasks_waiting /\
     mutex_del_error_mode_prop opt tasks_waiting err /\
     safeExec
       (LastSeen entry)
       (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
             (mutex_del_observe_ptr pevent)) X).

Definition mutex_del_unchanged_exit_inv
  (sg : StableGlobVars) (initial_event : OSEventAbstractState)
  (entry : UCOS2_Verify_State) (eid : EventID) (pevent : addr)
  (opt : MutexDelOpt) (tasks_waiting err : Z) X : Assertion :=
  EX exited : UCOS2_Verify_State,
    Ucos2Verify.lib.ucos2_rules_lib.OutsideCritical sg exited **
    mutex_del_restore_rep false sg entry exited **
    coq_prop
      (mutex_del_source_entry_prop
         sg initial_event entry eid pevent tasks_waiting /\
       mutex_del_error_mode_prop opt tasks_waiting err /\
       mutex_del_exit_critical_call_prop sg entry exited /\
       safeExec
         (LastSeen entry)
         (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
               (mutex_del_observe_ptr pevent)) X).

(** Direct caller-to-owner-stage bridge. *)
Lemma mutex_del_owner_ready_call_refines_owner_stage :
  forall sg e m ls1 ls2 owner_tid owner_t owner_ptr pcp owner_orig,
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some owner_tid ->
    m.(mfOwnerOrigPrio) = Some owner_orig ->
    m.(mfPCP) = pcp ->
    ls1.(TskState).(inUsedTaskStates) owner_tid = Some owner_t ->
    owner_t.(curPrio) = pcp ->
    pcp <> sg.(osPrioMutexCeilDis) ->
    mutex_del_owner_ready_call_prop
      sg owner_tid owner_ptr owner_orig ls1 ls2 ->
    mutex_del_rdyatprio_stage_prop sg e ls1 ls2.
Proof.
  intros sg e m ls1 ls2 owner_tid owner_t owner_ptr pcp owner_orig
    Htype Hmutex Howner Horig Hpcp Htask Htaskprio Henabled Hcall.
  unfold mutex_del_owner_ready_call_prop,
    mutex_del_owner_ready_call_sem in Hcall.
  destruct Hcall as [_ Hatomic].
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total.
  exists m. split; [exact Htype|].
  split; [exact Hmutex|].
  split.
  - rewrite Howner, Horig. exact I.
  - rewrite Hpcp.
    destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
    + apply Z.eqb_eq in Hdisabled. contradiction.
    + rewrite Howner, Horig.
      exists owner_t. split; [exact Htask|].
      rewrite Htaskprio, Z.eqb_refl.
      exact Hatomic.
Qed.

Lemma mutex_del_owner_restore_disabled_identity :
  forall sg e m ls,
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfPCP) = sg.(osPrioMutexCeilDis) ->
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None | Some _, Some _ => True
     | _, _ => False
     end) ->
    mutex_del_owner_restore_total sg e ls tt ls.
Proof.
  intros sg e m ls Htype Hmutex Hpcp Hshape.
  unfold mutex_del_owner_restore_total.
  exists m. repeat split; try assumption.
  rewrite Hpcp, Z.eqb_refl. reflexivity.
Qed.

(** Premise-closed bridges for the four source branches surrounding the
    owner-priority call.  They deliberately consume only the snapshot,
    source-value lineage, and the C guards that survive at those program
    points. *)
Lemma mutex_del_owner_null_refines_owner_stage :
  forall sg ls e owner_tid owner_t owner_prio prio_addr,
    mutex_del_owner_snapshot_prop
      sg ls e 0 owner_tid owner_t owner_prio prio_addr ->
    mutex_del_rdyatprio_stage_prop sg e ls ls.
Proof.
  intros sg ls e owner_tid owner_t owner_prio prio_addr Hsnapshot.
  unfold mutex_del_owner_snapshot_prop in Hsnapshot.
  destruct Hsnapshot as [_ [m [Htype [Hmutex Hshape]]]].
  destruct m.(mfOwner) as [tid|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hshape.
  - destruct Hshape as [_ [_ [Hnonnull _]]]. contradiction.
  - contradiction.
  - contradiction.
  - unfold mutex_del_rdyatprio_stage_prop,
      mutex_del_owner_restore_total.
    exists m. split; [exact Htype|].
    split; [exact Hmutex|].
    split.
    + rewrite Howner, Horig. exact I.
    + destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis));
        [reflexivity|].
      rewrite Howner, Horig. reflexivity.
Qed.

Lemma mutex_del_owner_mismatch_refines_owner_stage :
  forall sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
         ecnt pcp owner_orig,
    owner_ptr <> 0 ->
    mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    mutex_del_owner_value_lineage_prop e ecnt pcp owner_orig ->
    owner_prio <> pcp ->
    mutex_del_rdyatprio_stage_prop sg e ls ls.
Proof.
  intros sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
    ecnt pcp owner_orig Hnonnull Hsnapshot Hlineage Hmismatch.
  unfold mutex_del_owner_snapshot_prop in Hsnapshot.
  destruct Hsnapshot as [_ [m [Htype [Hmutex Hshape]]]].
  destruct m.(mfOwner) as [tid|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hshape.
  - destruct Hshape as
      [_ [Hlookup [_ [_ [Hprio [_ _]]]]]].
    unfold mutex_del_owner_value_lineage_prop in Hlineage.
    destruct Hlineage as
      [m' [_ [Hmutex' [_ [_ [Hpcp _]]]]]].
    rewrite Hmutex in Hmutex'. inversion Hmutex'; subst m'.
    assert (Hcur_ne : owner_t.(curPrio) <> m.(mfPCP)).
    { rewrite <- Hprio, Hpcp. exact Hmismatch. }
    apply Z.eqb_neq in Hcur_ne.
    unfold mutex_del_rdyatprio_stage_prop,
      mutex_del_owner_restore_total.
    exists m. split; [exact Htype|].
    split; [exact Hmutex|].
    split.
    + rewrite Howner, Horig. exact I.
    + destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis));
        [reflexivity|].
      rewrite Howner, Horig.
      exists owner_t. split; [exact Hlookup|].
      rewrite Hcur_ne. reflexivity.
  - contradiction.
  - contradiction.
  - exfalso. apply Hnonnull. exact Hshape.
Qed.

Lemma mutex_del_owner_call_snapshot_refines_owner_stage :
  forall sg ls1 ls2 e owner_ptr owner_tid owner_t owner_prio prio_addr
         ecnt pcp owner_orig,
    owner_ptr <> 0 ->
    mutex_del_owner_snapshot_prop
      sg ls1 e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    mutex_del_owner_value_lineage_prop e ecnt pcp owner_orig ->
    owner_prio = pcp ->
    pcp <> 255 ->
    mutex_del_owner_ready_call_prop
      sg owner_tid owner_ptr owner_orig ls1 ls2 ->
    mutex_del_rdyatprio_stage_prop sg e ls1 ls2.
Proof.
  intros sg ls1 ls2 e owner_ptr owner_tid owner_t owner_prio prio_addr
    ecnt pcp owner_orig Hnonnull Hsnapshot Hlineage Howner_prio Hpcp
    Hcall.
  unfold mutex_del_owner_snapshot_prop in Hsnapshot.
  destruct Hsnapshot as [Hceil [m [Htype [Hmutex Hshape]]]].
  destruct m.(mfOwner) as [tid|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hshape.
  - destruct Hshape as
      [Howner_tid [Hlookup [_ [_ [Hprio [_ _]]]]]].
    subst owner_tid.
    unfold mutex_del_owner_value_lineage_prop in Hlineage.
    destruct Hlineage as
      [m' [_ [Hmutex' [_ [_ [HmPCP Howner_orig]]]]]].
    rewrite Hmutex in Hmutex'. inversion Hmutex'; subst m'.
    rewrite Howner, Horig in Howner_orig. simpl in Howner_orig.
    subst owner_orig.
    eapply mutex_del_owner_ready_call_refines_owner_stage
      with (m := m) (owner_t := owner_t) (pcp := pcp) (owner_ptr := owner_ptr).
    + exact Htype.
    + exact Hmutex.
    + exact Howner.
    + exact Horig.
    + exact HmPCP.
    + exact Hlookup.
    + lia.
    + rewrite Hceil. exact Hpcp.
    + exact Hcall.
  - contradiction.
  - contradiction.
  - exfalso. apply Hnonnull. exact Hshape.
Qed.

Lemma mutex_del_owner_disabled_snapshot_identity :
  forall sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
         ecnt pcp owner_orig,
    mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    mutex_del_owner_value_lineage_prop e ecnt pcp owner_orig ->
    pcp = 255 ->
    mutex_del_rdyatprio_stage_prop sg e ls ls.
Proof.
  intros sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
    ecnt pcp owner_orig Hsnapshot Hlineage Hpcp.
  unfold mutex_del_owner_snapshot_prop in Hsnapshot.
  destruct Hsnapshot as [Hceil [m [Htype [Hmutex Hshape]]]].
  unfold mutex_del_owner_value_lineage_prop in Hlineage.
  destruct Hlineage as
    [m' [_ [Hmutex' [_ [_ [HmPCP _]]]]]].
  rewrite Hmutex in Hmutex'. inversion Hmutex'; subst m'.
  unfold mutex_del_rdyatprio_stage_prop.
  eapply mutex_del_owner_restore_disabled_identity with (m := m).
  - exact Htype.
  - exact Hmutex.
  - rewrite HmPCP, Hpcp, Hceil. reflexivity.
  - destruct m.(mfOwner); destruct m.(mfOwnerOrigPrio);
      simpl in Hshape |- *; tauto.
Qed.

Lemma mutex_del_nonready_relocation_preserves_scheduler_cache :
  forall sg tid prio ls1 ls2,
    (atomic_task_set_curPrio_waiting sg tid prio ls1 tt ls2 \/
     atomic_task_set_curPrio_dormant sg tid prio ls1 tt ls2) ->
    ls2.(SchedState).(curSchedPrio) =
    ls1.(SchedState).(curSchedPrio).
Proof.
  intros sg tid prio ls1 ls2 [Hwaiting | Hdormant].
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
       evSt2 & pty & Hnot_ready & Htask & Hold & Hne & Hlo & Hhi &
       Hpt & Hpend & Hevent & Hmulti & Hget & Htype & Hin & Ht' &
       Htsk & Hwait' & Hev & Hls2).
    rewrite Hls2. reflexivity.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask & Hold & Hne &
       Hlo & Hhi & Hpt & Hevent & Hmulti & Hnot_effective & Ht' &
       Htsk & Hls2).
    rewrite Hls2. reflexivity.
Qed.

Lemma mutex_del_owner_ready_call_selected_event_noninterference :
  forall sg eid e m owner_tid ptcb prio ls1 ls2,
    ls1.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfOwner) = Some owner_tid ->
    verification_slice_cross_module_consistency sg ls1 ->
    mutex_del_owner_ready_call_prop
      sg owner_tid ptcb prio ls1 ls2 ->
    mutex_del_selected_event_noninterference_prop eid ls1 ls2.
Proof.
  intros sg eid e m owner_tid ptcb prio ls1 ls2
    Hevent Htype Hfields Howner Hcross Hcall.
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as [_ [_ [Howners _]]].
  unfold mutex_owner_consistency in Howners.
  pose proof
    (Howners eid e m (conj Hevent (conj Htype Hfields)))
    as Howner_consistency.
  rewrite Howner in Howner_consistency.
  destruct Howner_consistency as
    (owner_t & owner_orig & Howner_task & Howner_orig &
     Howner_prio & Howner_notin).
  unfold mutex_del_owner_ready_call_prop,
    mutex_del_owner_ready_call_sem in Hcall.
  destruct Hcall as [_ Hraw].
  unfold mutex_del_selected_event_noninterference_prop.
  intros selected Hselected.
  rewrite Hevent in Hselected. inversion Hselected; subst selected.
  destruct Hraw as [Hready | [Hwaiting | Hdormant]].
  - unfold atomic_task_set_curPrio_ready in Hready.
    destruct Hready as [t [oldPrio [t'
      [_ [_ [_ [_ [_ [_ [_ [_ Hpost]]]]]]]]]]].
    cbv zeta in Hpost. subst ls2. cbn.
    split; [exact Hevent|].
    intros wait_tid Hin.
    assert (Hneq : wait_tid <> owner_tid).
    { intro Heq. subst wait_tid. exact (Howner_notin Hin). }
    apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity.
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
       evSt2 & pty & Hnot_ready & Htask & Hold & Hne & Hlo & Hhi &
       Hslot & Hpend & Hptr & Hmulti & Hwait_get & Hwait_type &
       Hwait_in & Ht' & Htsk & Hwait' & Hev & Hpost).
    assert (Heid_neq : eid <> wait_eid).
    { intro Heq. subst wait_eid.
      rewrite Hevent in Hwait_get. inversion Hwait_get; subst wait_e.
      exact (Howner_notin Hwait_in). }
    apply Z.eqb_neq in Heid_neq.
    rewrite Hpost, Hev, Htsk. cbn. rewrite Heid_neq.
    split; [exact Hevent|].
    intros wait_tid Hin.
    assert (Hneq : wait_tid <> owner_tid).
    { intro Heq. subst wait_tid. exact (Howner_notin Hin). }
    apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask & Hold & Hne &
       Hlo & Hhi & Hslot & Hptr & Hmulti & Hnot_effective & Ht' &
       Htsk & Hpost).
    rewrite Hpost, Htsk. cbn.
    split; [exact Hevent|].
    intros wait_tid Hin.
    assert (Hneq : wait_tid <> owner_tid).
    { intro Heq. subst wait_tid. exact (Howner_notin Hin). }
    apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity.
Qed.

(** Extensionality of the concrete event-wait encoders over precisely the
    tasks mentioned by the selected wait list.  This is the representation
    bridge used by the derived call footprint below; no global task-state
    equality is required. *)
Lemma mutex_del_encode_event_wait_grp_ext :
  forall wl tskSt1 tskSt2,
    (forall tid,
       In tid wl ->
       tskSt1.(inUsedTaskStates) tid =
       tskSt2.(inUsedTaskStates) tid) ->
    encode_event_wait_grp wl tskSt1 =
    encode_event_wait_grp wl tskSt2.
Proof.
  induction wl as [|tid rest IH]; intros tskSt1 tskSt2 Hext; simpl.
  - reflexivity.
  - rewrite (Hext tid ltac:(left; reflexivity)).
    destruct (tskSt2.(inUsedTaskStates) tid); simpl;
      rewrite (IH tskSt1 tskSt2 ltac:(
        intros tid' Hin; apply Hext; right; exact Hin));
      reflexivity.
Qed.

Lemma mutex_del_encode_event_wait_tbl_at_ext :
  forall wl tskSt1 tskSt2 y,
    (forall tid,
       In tid wl ->
       tskSt1.(inUsedTaskStates) tid =
       tskSt2.(inUsedTaskStates) tid) ->
    encode_event_wait_tbl_at wl tskSt1 y =
    encode_event_wait_tbl_at wl tskSt2 y.
Proof.
  intros wl tskSt1 tskSt2 y Hext.
  unfold encode_event_wait_tbl_at.
  generalize 0 as acc.
  induction wl as [|tid rest IH]; intro acc; simpl.
  - reflexivity.
  - rewrite (Hext tid ltac:(left; reflexivity)).
    apply IH.
    intros tid' Hin. apply Hext. right. exact Hin.
Qed.

Lemma mutex_del_selected_event_snapshot_transport :
  forall sg eid ls1 ls2 e etype ecnt eptr egrp etbl,
    mutex_del_selected_event_noninterference_prop eid ls1 ls2 ->
    event_snapshot_of_prop
      sg ls1.(TskState) ls1.(EventState) eid e
      etype ecnt eptr egrp etbl ->
    event_snapshot_of_prop
      sg ls2.(TskState) ls2.(EventState) eid e
      etype ecnt eptr egrp etbl.
Proof.
  intros sg eid ls1 ls2 e etype ecnt eptr egrp etbl
    Hnoninterference Hsnapshot.
  unfold event_snapshot_of_prop in Hsnapshot |- *.
  destruct Hsnapshot as
    [Hused [Htype [Hcnt [Hptr [Hgrp Htbl]]]]].
  unfold mutex_del_selected_event_noninterference_prop
    in Hnoninterference.
  destruct (Hnoninterference e Hused) as [Hused' Htask].
  assert (Hgrp_ext :
    encode_event_wait_grp e.(waitList) ls2.(TskState) =
    encode_event_wait_grp e.(waitList) ls1.(TskState)).
  {
    apply mutex_del_encode_event_wait_grp_ext.
    exact Htask.
  }
  assert (Htbl_ext :
    encode_event_wait_tbl_values e ls2.(TskState) =
    encode_event_wait_tbl_values e ls1.(TskState)).
  {
    unfold encode_event_wait_tbl_values.
    assert (Hat : forall y,
      encode_event_wait_tbl_at e.(waitList) ls2.(TskState) y =
      encode_event_wait_tbl_at e.(waitList) ls1.(TskState) y).
    {
      intro y.
      apply mutex_del_encode_event_wait_tbl_at_ext.
      exact Htask.
    }
    rewrite !Hat. reflexivity.
  }
  repeat split; try assumption.
  - rewrite Hgrp. symmetry. exact Hgrp_ext.
  - rewrite Htbl. symmetry. exact Htbl_ext.
Qed.

Lemma mutex_del_selected_event_wait_table_storage_eq :
  forall eid ls1 ls2 e base,
    mutex_del_selected_event_noninterference_prop eid ls1 ls2 ->
    ls1.(EventState).(inUsedEventStates) eid = Some e ->
    used_event_wait_table_storage ls2.(TskState) base e =
    used_event_wait_table_storage ls1.(TskState) base e.
Proof.
  intros eid ls1 ls2 e base Hnoninterference Hused.
  unfold mutex_del_selected_event_noninterference_prop
    in Hnoninterference.
  destruct (Hnoninterference e Hused) as [_ Htask].
  assert (Hat : forall y,
    encode_event_wait_tbl_at e.(waitList) ls2.(TskState) y =
    encode_event_wait_tbl_at e.(waitList) ls1.(TskState) y).
  {
    intro y.
    apply mutex_del_encode_event_wait_tbl_at_ext.
    exact Htask.
  }
  unfold used_event_wait_table_storage.
  rewrite !Hat. reflexivity.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Bool.Bool.
Local Open Scope sac_scope.
Lemma store_osrdytbl_Znth_uchar_range__g01_scan_snapshot :
  forall sg l i,
    osrdytbl_index_in_range i ->
    store_osrdytbl sg l |--
      coq_prop (0 <= Znth i l 0 <= 255).
Proof.
  intros sg l i Hindex.
  unfold store_osrdytbl, osrdytbl_element_store.
  sep_apply (store_array_split_to_missing_i
    Z (fun base idx value => store_uchar (base + idx * sizeof_OS_PRIO) value)
    (g_OSRdyTbl sg) i OS_RDY_TBL_SIZE l 0).
  - prop_apply_p (store_uchar_range
      (g_OSRdyTbl sg + i * sizeof_OS_PRIO) (Znth i l 0)).
    Intros_p Hrange.
    apply derivable1s_coq_prop_r.
    change (0 <= Znth i l 0 <= 255) in Hrange.
    exact Hrange.
  - exact Hindex.
Qed.
Lemma mutex_del_first_set8_range__g02_refresh_close :
  forall bits,
    0 <= mutex_del_first_set8 bits < 8.
Proof.
  intros bits.
  unfold mutex_del_first_set8.
  destruct (negb (Z.eqb (Z.land bits 1) 0)); [lia |].
  destruct (negb (Z.eqb (Z.land bits 2) 0)); [lia |].
  destruct (negb (Z.eqb (Z.land bits 4) 0)); [lia |].
  destruct (negb (Z.eqb (Z.land bits 8) 0)); [lia |].
  destruct (negb (Z.eqb (Z.land bits 16) 0)); [lia |].
  destruct (negb (Z.eqb (Z.land bits 32) 0)); [lia |].
  destruct (negb (Z.eqb (Z.land bits 64) 0)); lia.
Qed.
Lemma mutex_del_raw_stage_refresh_expose__g02_refresh_close :
  forall sg entry post,
    UCOS2_verification_slice_state_inv sg post ->
    ((UCOS2_verification_slice_raw_rep sg post ||
      UCOS2_verification_slice_raw_ready_prio_stage sg entry post)%sac) |--
      EX old_high_tcb old_high_prio,
        sg.(g_OSRdyGrp) # UChar |->
          mutex_del_refresh_grp_value post **
        store_osrdytbl sg (mutex_del_refresh_ready_tbl_values post) **
        sg.(g_OSPrioHighRdy) # UChar |-> old_high_prio **
        sg.(g_OSTCBHighRdy) # Ptr |-> old_high_tcb **
        verification_slice_store_priotbl_list sg
          (mutex_del_refresh_prio_tbl_values sg post) **
        mutex_del_refresh_residual sg post.
Proof.
  intros sg entry post Hvalid.
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [Htask [Hsched [_ _]]].
  assert (Heq : forall y,
    encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) y =
    encode_ready_tbl_at_or post.(SchedState).(readyList) post.(TskState) y).
  { intro y. apply (sched_stable_tbl_eq_or
      sg post.(TskState) post.(SchedState) y); assumption. }
  apply derivable1_orp_elim.
  - unfold UCOS2_verification_slice_raw_rep.
    sep_apply_l_atomic
      (verification_slice_task_raw_rep_split_priotbl sg post.(TskState)).
    unfold verification_slice_sched_raw_rep.
    rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
      <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
    Exists
      (match post.(SchedState).(highRdyTid) with
       | Some tid => verification_slice_tcb_addr sg tid | None => 0 end)
      (match post.(SchedState).(highRdyPrio) with
       | Some p => p | None => 0xFF end).
    unfold mutex_del_refresh_grp_value,
      mutex_del_refresh_ready_tbl_values,
      mutex_del_refresh_prio_tbl_values,
      mutex_del_refresh_residual,
      mutex_del_sched_refresh_rest,
      verification_slice_store_prio_tbl,
      store_osrdytbl, store_array.
    cbn [store_array_rec osrdytbl_element_store sizeof_OS_PRIO].
    unfold osrdytbl_element_store, sizeof_OS_PRIO.
    replace (0 * 1) with (0 : Z) by reflexivity.
    replace ((0 + 1) * 1) with (1 : Z) by reflexivity.
    replace ((0 + 1 + 1) * 1) with (2 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1) * 1) with (3 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1) * 1) with (4 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1) * 1) with (5 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1 + 1) * 1) with (6 : Z)
      by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 1) with (7 : Z)
      by reflexivity.
    andp_cancel.
    sepcon_assoc_change.
    cancel.
  - unfold UCOS2_verification_slice_raw_ready_prio_stage.
    sep_apply_l_atomic
      (verification_slice_task_raw_rep_split_priotbl sg post.(TskState)).
    unfold verification_slice_sched_raw_ready_prio_stage.
    rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
      <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
    Exists
      (match entry.(SchedState).(highRdyTid) with
       | Some tid => verification_slice_tcb_addr sg tid | None => 0 end)
      (match entry.(SchedState).(highRdyPrio) with
       | Some p => p | None => 0xFF end).
    unfold mutex_del_refresh_grp_value,
      mutex_del_refresh_ready_tbl_values,
      mutex_del_refresh_prio_tbl_values,
      mutex_del_refresh_residual,
      mutex_del_sched_refresh_rest,
      verification_slice_store_prio_tbl,
      store_osrdytbl, store_array.
    cbn [store_array_rec osrdytbl_element_store sizeof_OS_PRIO].
    unfold osrdytbl_element_store, sizeof_OS_PRIO.
    replace (0 * 1) with (0 : Z) by reflexivity.
    replace ((0 + 1) * 1) with (1 : Z) by reflexivity.
    replace ((0 + 1 + 1) * 1) with (2 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1) * 1) with (3 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1) * 1) with (4 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1) * 1) with (5 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1 + 1) * 1) with (6 : Z)
      by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 1) with (7 : Z)
      by reflexivity.
    andp_cancel.
    sepcon_assoc_change.
    cancel.
Qed.
Lemma mutex_del_first_set8_min_bit__g02_refresh_close :
  forall bits i,
    0 <= i < 8 ->
    (forall j, 0 <= j < i ->
      Z.land bits (Z.shiftl 1 j) = 0) ->
    Z.land bits (Z.shiftl 1 i) <> 0 ->
    mutex_del_first_set8 bits = i.
Proof.
  intros bits i Hi Hlower Hhit.
  assert (Hcases :
    i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
    i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
  - change (Z.land bits 1 <> 0) in Hhit.
    unfold mutex_del_first_set8.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 1) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    change (Z.land bits 2 <> 0) in Hhit.
    unfold mutex_del_first_set8.
    rewrite H0.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 2) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    change (Z.land bits 4 <> 0) in Hhit.
    unfold mutex_del_first_set8.
    rewrite H0, H1.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 4) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    change (Z.land bits 8 <> 0) in Hhit.
    unfold mutex_del_first_set8.
    rewrite H0, H1, H2.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 8) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    assert (H3 : Z.land bits 8 = 0).
    { change (Z.land bits (Z.shiftl 1 3) = 0).
      apply Hlower; lia. }
    change (Z.land bits 16 <> 0) in Hhit.
    unfold mutex_del_first_set8.
    rewrite H0, H1, H2, H3.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 16) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    assert (H3 : Z.land bits 8 = 0).
    { change (Z.land bits (Z.shiftl 1 3) = 0).
      apply Hlower; lia. }
    assert (H4 : Z.land bits 16 = 0).
    { change (Z.land bits (Z.shiftl 1 4) = 0).
      apply Hlower; lia. }
    change (Z.land bits 32 <> 0) in Hhit.
    unfold mutex_del_first_set8.
    rewrite H0, H1, H2, H3, H4.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 32) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    assert (H3 : Z.land bits 8 = 0).
    { change (Z.land bits (Z.shiftl 1 3) = 0).
      apply Hlower; lia. }
    assert (H4 : Z.land bits 16 = 0).
    { change (Z.land bits (Z.shiftl 1 4) = 0).
      apply Hlower; lia. }
    assert (H5 : Z.land bits 32 = 0).
    { change (Z.land bits (Z.shiftl 1 5) = 0).
      apply Hlower; lia. }
    change (Z.land bits 64 <> 0) in Hhit.
    unfold mutex_del_first_set8.
    rewrite H0, H1, H2, H3, H4, H5.
    rewrite (proj2 (Z.eqb_neq (Z.land bits 64) 0) Hhit).
    reflexivity.
  - assert (H0 : Z.land bits 1 = 0).
    { change (Z.land bits (Z.shiftl 1 0) = 0).
      apply Hlower; lia. }
    assert (H1 : Z.land bits 2 = 0).
    { change (Z.land bits (Z.shiftl 1 1) = 0).
      apply Hlower; lia. }
    assert (H2 : Z.land bits 4 = 0).
    { change (Z.land bits (Z.shiftl 1 2) = 0).
      apply Hlower; lia. }
    assert (H3 : Z.land bits 8 = 0).
    { change (Z.land bits (Z.shiftl 1 3) = 0).
      apply Hlower; lia. }
    assert (H4 : Z.land bits 16 = 0).
    { change (Z.land bits (Z.shiftl 1 4) = 0).
      apply Hlower; lia. }
    assert (H5 : Z.land bits 32 = 0).
    { change (Z.land bits (Z.shiftl 1 5) = 0).
      apply Hlower; lia. }
    assert (H6 : Z.land bits 64 = 0).
    { change (Z.land bits (Z.shiftl 1 6) = 0).
      apply Hlower; lia. }
    unfold mutex_del_first_set8.
    rewrite H0, H1, H2, H3, H4, H5, H6.
    reflexivity.
Qed.
Lemma mutex_del_sorted_head_le__g02_refresh_close :
  forall (A : Type) (key : A -> Z) head tail x,
    Ucos2Verify.lib.helpers.strictly_sorted_by key (head :: tail) ->
    In x (head :: tail) ->
    key head <= key x.
Proof.
  intros A key head tail.
  revert head.
  induction tail as [| next rest IH]; intros head x Hsorted Hin.
  - simpl in Hin. destruct Hin as [-> | []]. lia.
  - simpl in Hsorted. destruct Hsorted as [Hhead Hrest].
    simpl in Hin. destruct Hin as [-> | Hin]; [lia |].
    specialize (IH next x Hrest Hin). lia.
Qed.
Lemma mutex_del_no_group_row__g02_refresh_close :
  forall l st y,
    0 <= y ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
      0 <= t.(curPrio) / 8) ->
    (forall tid t, In tid l -> st.(inUsedTaskStates) tid = Some t ->
      t.(curPrio) / 8 <> y) ->
    Z.land (Z.shiftl 1 y) (encode_ready_grp l st) = 0.
Proof.
  induction l as [| a rest IH]; intros st y Hy Hrange Hnorow; simpl.
  - apply Z.land_0_r.
  - destruct (st.(inUsedTaskStates) a) as [ta |] eqn:Hgeta.
    + rewrite Z.land_lor_distr_r.
      rewrite IH with (st := st) (y := y).
      2: exact Hy.
      2: { intros; eapply Hrange; [right; eassumption | eassumption]. }
      2: { intros; eapply Hnorow; [right; eassumption | eassumption]. }
      rewrite Z.lor_0_r.
      apply sched_land_single_bits_neq.
      * exact Hy.
      * eapply Hrange; [left; reflexivity | exact Hgeta].
      * intro Heq. apply (Hnorow a ta ltac:(left; reflexivity) Hgeta).
        symmetry. exact Heq.
    + apply IH with (st := st) (y := y); auto.
      * intros; eapply Hrange; [right; eassumption | eassumption].
      * intros; eapply Hnorow; [right; eassumption | eassumption].
Qed.
Lemma mutex_del_group_head_bit__g02_refresh_close :
  forall head tail st t,
    st.(inUsedTaskStates) head = Some t ->
    0 <= t.(curPrio) ->
    Z.land (encode_ready_grp (head :: tail) st)
      (Z.shiftl 1 (t.(curPrio) / 8)) <> 0.
Proof.
  intros head tail st t Hlookup Hprio Hzero.
  assert (Hrow : 0 <= t.(curPrio) / 8) by (apply Z.div_pos; lia).
  assert (Hencbit :
    Z.testbit (encode_ready_grp (head :: tail) st)
      (t.(curPrio) / 8) = true).
  {
    simpl. rewrite Hlookup, Z.lor_spec,
      Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl by exact Hrow.
    reflexivity.
  }
  assert (Hmaskbit :
    Z.testbit (Z.shiftl 1 (t.(curPrio) / 8))
      (t.(curPrio) / 8) = true).
  { rewrite Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl by exact Hrow.
    reflexivity. }
  assert (Hlandbit :
    Z.testbit
      (Z.land (encode_ready_grp (head :: tail) st)
        (Z.shiftl 1 (t.(curPrio) / 8)))
      (t.(curPrio) / 8) = true).
  { rewrite Z.land_spec, Hencbit, Hmaskbit. reflexivity. }
  rewrite Hzero, Z.testbit_0_l in Hlandbit.
  discriminate.
Qed.
Lemma mutex_del_tbl_head_bit__g02_refresh_close :
  forall head tail st t,
    st.(inUsedTaskStates) head = Some t ->
    0 <= t.(curPrio) ->
    Z.land (encode_ready_tbl_at_or (head :: tail) st (t.(curPrio) / 8))
      (Z.shiftl 1 (t.(curPrio) mod 8)) <> 0.
Proof.
  intros head tail st t Hlookup Hprio Hzero.
  assert (Hcol : 0 <= t.(curPrio) mod 8) by (apply Z.mod_pos_bound; lia).
  assert (Hencbit :
    Z.testbit
      (encode_ready_tbl_at_or (head :: tail) st (t.(curPrio) / 8))
      (t.(curPrio) mod 8) = true).
  {
    simpl. rewrite Hlookup, Z.eqb_refl, Z.lor_spec,
      Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl by exact Hcol.
    reflexivity.
  }
  assert (Hmaskbit :
    Z.testbit (Z.shiftl 1 (t.(curPrio) mod 8))
      (t.(curPrio) mod 8) = true).
  { rewrite Z.shiftl_1_l, Z.pow2_bits_eqb, Z.eqb_refl by exact Hcol.
    reflexivity. }
  assert (Hlandbit :
    Z.testbit
      (Z.land
        (encode_ready_tbl_at_or (head :: tail) st (t.(curPrio) / 8))
        (Z.shiftl 1 (t.(curPrio) mod 8)))
      (t.(curPrio) mod 8) = true).
  { rewrite Z.land_spec, Hencbit, Hmaskbit. reflexivity. }
  rewrite Hzero, Z.testbit_0_l in Hlandbit.
  discriminate.
Qed.
Lemma mutex_del_refresh_tbl_Znth__g02_refresh_close :
  forall post y,
    0 <= y < 8 ->
    Znth y (mutex_del_refresh_ready_tbl_values post) 0 =
      encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) y.
Proof.
  intros post y Hy.
  assert (Hcases :
    y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/
    y = 4 \/ y = 5 \/ y = 6 \/ y = 7) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    reflexivity.
Qed.
Lemma mutex_del_prioTbl_to_addrs_rec_seq__g02_refresh_close :
  forall sg f n acc,
    verification_slice_prioTbl_to_addrs_rec sg f n acc =
      List.app
        (map (fun k => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)))
          (seq 0 n))
        acc.
Proof.
  intros sg f n. induction n as [| n IH]; intro acc.
  - reflexivity.
  - simpl verification_slice_prioTbl_to_addrs_rec.
    rewrite IH, seq_S, map_app. simpl.
    rewrite <- app_assoc. reflexivity.
Qed.
Lemma mutex_del_prioTbl_to_addrs_Znth__g02_refresh_close :
  forall sg f p,
    0 <= p < 64 ->
    Znth p (verification_slice_prioTbl_to_addrs sg f) 0 =
      verification_slice_prio_tbl_entry_to_addr sg (f p).
Proof.
  intros sg f p Hp.
  unfold verification_slice_prioTbl_to_addrs.
  rewrite mutex_del_prioTbl_to_addrs_rec_seq__g02_refresh_close.
  rewrite app_nil_r.
  unfold Znth.
  assert (Hnat : (Z.to_nat p < 64)%nat) by lia.
  assert (Hdefault :
    nth (Z.to_nat p)
      (map (fun k : nat => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)))
        (seq 0 64)) 0 =
    nth (Z.to_nat p)
      (map (fun k : nat => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)))
        (seq 0 64))
      (verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat 0)))).
  { apply nth_indep. rewrite length_map, length_seq. exact Hnat. }
  rewrite Hdefault.
  change
    (nth (Z.to_nat p)
      (map
        (fun k : nat => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)))
        (seq 0 64))
      ((fun k : nat => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k))) 0%nat) =
     verification_slice_prio_tbl_entry_to_addr sg (f p)).
  rewrite map_nth.
  rewrite seq_nth by exact Hnat.
  simpl Nat.add.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma mutex_del_transition_raw_stage_validity__g02_refresh_close :
  forall sg entry post,
    mutex_del_transition_rep sg entry post |--
      (UCOS2_verification_slice_raw_rep sg post ||
       UCOS2_verification_slice_raw_ready_prio_stage sg entry post) &&
      coq_prop (UCOS2_verification_slice_state_inv sg post).
Proof.
  intros sg entry post h Hrep.
  unfold mutex_del_transition_rep, orp, andp, coq_prop in Hrep |- *.
  destruct Hrep as [Hfull | Hstage].
  - pose proof
      (UCOS2_verification_slice_inv_split_raw_validity sg post h Hfull)
      as Hsplit.
    unfold andp, coq_prop in Hsplit.
    destruct Hsplit as [Hraw Hvalid].
    split.
    + left. exact Hraw.
    + exact Hvalid.
  - exact Hstage.
Qed.
Lemma mutex_del_refresh_snapshot_from_validity__g02_refresh_close :
  forall sg post,
    valid_stable_glob_vars sg ->
    UCOS2_verification_slice_state_inv sg post ->
    mutex_del_refresh_snapshot_prop sg post
      (mutex_del_refresh_grp_value post)
      (mutex_del_refresh_ready_tbl_values post)
      (mutex_del_refresh_prio_tbl_values sg post).
Proof.
  intros sg post Hstable Hvalid.
  unfold mutex_del_refresh_snapshot_prop.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  pose proof Hvalid as Hvalid_all.
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [Htask [Hsched [_ _]]].
  pose proof Htask as Htask_all.
  pose proof Hsched as Hsched_all.
  destruct post.(SchedState).(readyList) as [| head tail] eqn:Hready.
  - unfold verification_slice_sched_in_range in Hsched.
    destruct Hsched as [_ [_ [_ [_ [_ [Hhigh _]]]]]].
    unfold sched_high_ready_consistency in Hhigh.
    rewrite Hready in Hhigh.
    destruct Hhigh as [Htid Hprio].
    unfold mutex_del_refresh_grp_value.
    rewrite Hready.
    simpl.
    repeat split; assumption.
  - unfold verification_slice_sched_in_range in Hsched.
    destruct Hsched as
      [Hmembers [Hsorted [_ [Hnodup [_ [Hhigh _]]]]]].
    assert (Hinhead : In head post.(SchedState).(readyList)).
    { rewrite Hready. left; reflexivity. }
    destruct (Hmembers head Hinhead)
      as [head_t [Hlookup _]].
    rewrite Hready in Hsorted, Hnodup.
    pose proof Htask as Htask_parts.
    unfold verification_slice_task_validity in Htask_parts.
    destruct Htask_parts as [Htask_valid Htask_fields].
    specialize (Htask_fields head head_t Hlookup).
    destruct Htask_fields as [Hhead_valid _].
    unfold valid_task_prio in Hhead_valid.
    destruct Hhead_valid as [Hhead_nonneg Hhead_lt_low].
    pose proof Hstable as Hstable_parts.
    unfold valid_stable_glob_vars in Hstable_parts.
    destruct Hstable_parts as
      [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    assert (Hhead_range : 0 <= head_t.(curPrio) < 64) by lia.
    assert (Hrow_range : 0 <= head_t.(curPrio) / 8 < 8).
    { split.
      - apply Z.div_pos; lia.
      - apply (Z.div_lt_upper_bound head_t.(curPrio) 8); lia. }
    assert (Hcol_range : 0 <= head_t.(curPrio) mod 8 < 8).
    { apply Z.mod_pos_bound. lia. }
    assert (Hminimum :
      forall tid t,
        In tid (head :: tail) ->
        post.(TskState).(inUsedTaskStates) tid = Some t ->
        head_t.(curPrio) <= t.(curPrio)).
    {
      intros tid t Hin Hget.
      pose proof
        (mutex_del_sorted_head_le__g02_refresh_close
          TaskID
          (fun tid0 =>
            match post.(TskState).(inUsedTaskStates) tid0 with
            | Some t0 => t0.(curPrio)
            | None => sg.(osLowestPrio) + 1
            end)
          head tail tid Hsorted Hin) as Hle.
      cbn in Hle.
      rewrite Hlookup, Hget in Hle.
      exact Hle.
    }
    assert (Hall_nonneg :
      forall tid t,
        In tid (head :: tail) ->
        post.(TskState).(inUsedTaskStates) tid = Some t ->
        0 <= t.(curPrio)).
    {
      intros tid t Hin Hget.
      unfold verification_slice_task_validity in Htask_all.
      destruct Htask_all as [_ Hfields].
      specialize (Hfields tid t Hget).
      unfold valid_task_prio in Hfields.
      lia.
    }
    assert (Hgrp_hit :
      Z.land (mutex_del_refresh_grp_value post)
        (Z.shiftl 1 (head_t.(curPrio) / 8)) <> 0).
    {
      unfold mutex_del_refresh_grp_value.
      rewrite Hready.
      apply mutex_del_group_head_bit__g02_refresh_close
        with (head := head) (tail := tail) (t := head_t);
        assumption.
    }
    assert (Hgrp_lower :
      forall j,
        0 <= j < head_t.(curPrio) / 8 ->
        Z.land (mutex_del_refresh_grp_value post)
          (Z.shiftl 1 j) = 0).
    {
      intros j Hj.
      rewrite Z.land_comm.
      unfold mutex_del_refresh_grp_value.
      rewrite Hready.
      apply mutex_del_no_group_row__g02_refresh_close.
      - lia.
      - intros tid t Hin Hget.
        pose proof (Hall_nonneg tid t Hin Hget) as Hnonneg.
        apply Z.div_pos; lia.
      - intros tid t Hin Hget Heq.
        pose proof (Hminimum tid t Hin Hget) as Hle.
        assert (Hdivle : head_t.(curPrio) / 8 <= t.(curPrio) / 8).
        { apply Z.div_le_mono; lia. }
        lia.
    }
    assert (Hgrp_first :
      mutex_del_first_set8 (mutex_del_refresh_grp_value post) =
        head_t.(curPrio) / 8).
    {
      apply mutex_del_first_set8_min_bit__g02_refresh_close;
        assumption.
    }
    assert (Hgrp_nonzero : mutex_del_refresh_grp_value post <> 0).
    { intro Hzero. rewrite Hzero, Z.land_0_l in Hgrp_hit. contradiction. }
    assert (Htbl_eq_or :
      encode_ready_tbl_at (head :: tail) post.(TskState)
        (head_t.(curPrio) / 8) =
      encode_ready_tbl_at_or (head :: tail) post.(TskState)
        (head_t.(curPrio) / 8)).
    {
      pose proof
        (sched_stable_tbl_eq_or sg post.(TskState) post.(SchedState)
          (head_t.(curPrio) / 8) Htask_all Hsched_all) as Heq.
      rewrite Hready in Heq.
      exact Heq.
    }
    assert (Htbl_hit :
      Z.land
        (encode_ready_tbl_at (head :: tail) post.(TskState)
          (head_t.(curPrio) / 8))
        (Z.shiftl 1 (head_t.(curPrio) mod 8)) <> 0).
    {
      rewrite Htbl_eq_or.
      apply mutex_del_tbl_head_bit__g02_refresh_close
        with (head := head) (tail := tail) (t := head_t);
        assumption.
    }
    assert (Htbl_lower :
      forall j,
        0 <= j < head_t.(curPrio) mod 8 ->
        Z.land
          (encode_ready_tbl_at (head :: tail) post.(TskState)
            (head_t.(curPrio) / 8))
          (Z.shiftl 1 j) = 0).
    {
      intros j Hj.
      rewrite Htbl_eq_or, Z.land_comm.
      set (candidate := head_t.(curPrio) / 8 * 8 + j).
      assert (Hcandidate_nonneg : 0 <= candidate) by (unfold candidate; lia).
      assert (Hcandidate_div : candidate / 8 = head_t.(curPrio) / 8).
      { unfold candidate.
        rewrite Z.add_comm, Z.div_add by lia.
        rewrite Z.div_small by lia.
        lia. }
      assert (Hcandidate_mod : candidate mod 8 = j).
      { unfold candidate.
        rewrite Z.add_comm, Z.mod_add by lia.
        apply Z.mod_small; lia. }
      rewrite <- Hcandidate_mod.
      apply sched_bit_disjoint_tbl_or.
      - exact Hcandidate_nonneg.
      - exact Hcandidate_div.
      - exact Hall_nonneg.
      - intros tid t Hin Hget Heq.
        pose proof (Hminimum tid t Hin Hget) as Hle.
        pose proof (Z.div_mod head_t.(curPrio) 8 ltac:(lia)) as Hdm.
        subst candidate.
        lia.
    }
    assert (Htbl_nth :
      Znth (head_t.(curPrio) / 8)
        (mutex_del_refresh_ready_tbl_values post) 0 =
      encode_ready_tbl_at (head :: tail) post.(TskState)
        (head_t.(curPrio) / 8)).
    {
      rewrite (mutex_del_refresh_tbl_Znth__g02_refresh_close
        post (head_t.(curPrio) / 8) Hrow_range).
      rewrite Hready.
      reflexivity.
    }
    assert (Htbl_nonzero :
      Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
        (mutex_del_refresh_ready_tbl_values post) 0 <> 0).
    {
      rewrite Hgrp_first, Htbl_nth.
      intro Hzero. rewrite Hzero, Z.land_0_l in Htbl_hit. contradiction.
    }
    assert (Htbl_first :
      mutex_del_first_set8
        (Znth (mutex_del_first_set8 (mutex_del_refresh_grp_value post))
          (mutex_del_refresh_ready_tbl_values post) 0) =
      head_t.(curPrio) mod 8).
    {
      rewrite Hgrp_first, Htbl_nth.
      apply mutex_del_first_set8_min_bit__g02_refresh_close;
        assumption.
    }
    assert (Hprio_registered :
      post.(TskState).(prioTbl) head_t.(curPrio) = PTTask head).
    {
      unfold verification_slice_task_validity in Htask.
      destruct Htask as [Htask_valid' _].
      apply (verification_slice_task_in_range_current_prio_registered
        sg post.(TskState) Htask_valid' head head_t Hlookup).
    }
    assert (Hprio_addr :
      Znth head_t.(curPrio)
        (mutex_del_refresh_prio_tbl_values sg post) 0 =
      verification_slice_tcb_addr sg head).
    {
      unfold mutex_del_refresh_prio_tbl_values.
      rewrite mutex_del_prioTbl_to_addrs_Znth__g02_refresh_close
        by exact Hhead_range.
      rewrite Hprio_registered.
      reflexivity.
    }
    unfold sched_high_ready_consistency in Hhigh.
    rewrite Hready in Hhigh.
    simpl in Hhigh.
    destruct Hhigh as [Hhigh_tid [head_t' [Hlookup' Hhigh_prio]]].
    rewrite Hlookup in Hlookup'. inversion Hlookup'; subst head_t'.
    exists head_t.
    split; [exact Hlookup |].
    split; [exact Hhead_range |].
    split; [exact Hgrp_nonzero |].
    split; [exact Hgrp_first |].
    split; [exact Htbl_nonzero |].
    split; [exact Htbl_first |].
    split; [exact Hprio_addr |].
    split; [exact Hhigh_prio | exact Hhigh_tid].
Qed.
Lemma mutex_del_refresh_spatial_closed__g02_refresh_close :
  forall sg post,
    UCOS2_verification_slice_state_inv sg post ->
    mutex_del_refresh_spatial sg post |--
      mutex_del_refresh_closed_inv sg post.
Proof.
  intros sg post Hvalid.
  unfold mutex_del_refresh_closed_inv.
  apply _derivable1_andp_intros.
  - pose proof Hvalid as Hparts.
    unfold UCOS2_verification_slice_state_inv in Hparts.
    destruct Hparts as [Htask [Hsched [_ _]]].
    assert (Heq : forall y,
      encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) y =
      encode_ready_tbl_at_or post.(SchedState).(readyList) post.(TskState) y).
    { intro y. apply (sched_stable_tbl_eq_or
        sg post.(TskState) post.(SchedState) y); assumption. }
    unfold mutex_del_refresh_spatial,
      mutex_del_refresh_residual,
      mutex_del_sched_refresh_rest,
      UCOS2_verification_slice_raw_rep,
      verification_slice_task_raw_rep,
      verification_slice_task_raw_rep_no_priotbl,
      verification_slice_sched_raw_rep,
      verification_slice_store_prio_tbl,
      store_osrdytbl, store_array,
      mutex_del_refresh_ready_tbl_values,
      mutex_del_refresh_grp_value.
    rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
      <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
    cbn [store_array_rec osrdytbl_element_store sizeof_OS_PRIO].
    unfold osrdytbl_element_store, sizeof_OS_PRIO.
    replace (0 * 1) with (0 : Z) by reflexivity.
    replace ((0 + 1) * 1) with (1 : Z) by reflexivity.
    replace ((0 + 1 + 1) * 1) with (2 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1) * 1) with (3 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1) * 1) with (4 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1) * 1) with (5 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1 + 1) * 1) with (6 : Z)
      by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 1) with (7 : Z)
      by reflexivity.
    sepcon_assoc_change.
    cancel.
    apply derivable1_truep_intros.
  - apply derivable1s_coq_prop_r. exact Hvalid.
Qed.
Lemma mutex_del_refresh_spatial_framed_closed__g02_refresh_close :
  forall sg post,
    UCOS2_verification_slice_state_inv sg post ->
    TT ** (TT **
      (sg.(g_OSRdyGrp) # UChar |-> mutex_del_refresh_grp_value post **
       (store_osrdytbl sg (mutex_del_refresh_ready_tbl_values post) **
        (sg.(g_OSPrioHighRdy) # UChar |->
           (match post.(SchedState).(highRdyPrio) with
            | Some p => p | None => 0xFF end) **
         (sg.(g_OSTCBHighRdy) # Ptr |->
            (match post.(SchedState).(highRdyTid) with
             | Some tid => verification_slice_tcb_addr sg tid | None => 0 end) **
          (verification_slice_store_priotbl_list sg
             (verification_slice_prioTbl_to_addrs sg post.(TskState).(prioTbl)) **
           mutex_del_refresh_residual sg post)))))) |--
      mutex_del_refresh_closed_inv sg post.
Proof.
  intros sg post Hvalid.
  unfold mutex_del_refresh_closed_inv.
  apply _derivable1_andp_intros.
  - pose proof Hvalid as Hparts.
    unfold UCOS2_verification_slice_state_inv in Hparts.
    destruct Hparts as [Htask [Hsched [_ _]]].
    assert (Heq : forall y,
      encode_ready_tbl_at post.(SchedState).(readyList) post.(TskState) y =
      encode_ready_tbl_at_or post.(SchedState).(readyList) post.(TskState) y).
    { intro y. apply (sched_stable_tbl_eq_or
        sg post.(TskState) post.(SchedState) y); assumption. }
    unfold mutex_del_refresh_residual,
      mutex_del_sched_refresh_rest,
      UCOS2_verification_slice_raw_rep.
    pose (sink := TT).
    match goal with
    | |- ?P |-- _ =>
        change
          (P |--
           interrupt_inv sg post.(IntrState) **
           verification_slice_task_raw_rep sg post.(TskState) **
           verification_slice_sched_raw_rep sg post.(TskState) post.(SchedState) **
           verification_slice_event_raw_rep sg post.(TskState) post.(EventState) **
           verification_slice_tick_inv sg post.(TickState) ** sink)
    end.
    assert (Hsink : sink = TT) by reflexivity.
    clearbody sink.
    unfold
      verification_slice_task_raw_rep,
      verification_slice_task_raw_rep_no_priotbl,
      verification_slice_sched_raw_rep,
      verification_slice_store_prio_tbl,
      store_osrdytbl, store_array,
      mutex_del_refresh_ready_tbl_values,
      mutex_del_refresh_grp_value.
    rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
      <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
    cbn [store_array_rec osrdytbl_element_store sizeof_OS_PRIO].
    unfold osrdytbl_element_store, sizeof_OS_PRIO.
    replace (0 * 1) with (0 : Z) by reflexivity.
    replace ((0 + 1) * 1) with (1 : Z) by reflexivity.
    replace ((0 + 1 + 1) * 1) with (2 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1) * 1) with (3 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1) * 1) with (4 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1) * 1) with (5 : Z) by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1 + 1) * 1) with (6 : Z)
      by reflexivity.
    replace ((0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 1) with (7 : Z)
      by reflexivity.
    sepcon_assoc_change.
    repeat progress cancel.
    andp_cancel.
    rewrite Hsink.
    apply derivable1_truep_intros.
  - apply derivable1s_coq_prop_r. exact Hvalid.
Qed.
Lemma mutex_del_wait_grp_zero_iff_empty__g03_owner_entry :
  forall sg tskSt wl,
    Ucos2Verify.lib.event_wait.event_waitList_canonical sg tskSt wl ->
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
  - intros Hnil. subst wl. reflexivity.
Qed.
Lemma mutex_del_owner_lineage_decode__g03_owner_entry :
  forall e ecnt pcp owner_orig,
    mutex_del_owner_value_lineage_prop e ecnt pcp owner_orig ->
    pcp = decode_PCP_from_cnt ecnt /\
    owner_orig = decode_OwnerPrio_from_cnt ecnt /\
    mutex_del_owner_value_lineage_prop e ecnt
      (decode_PCP_from_cnt ecnt) (decode_OwnerPrio_from_cnt ecnt).
Proof.
  intros e ecnt pcp owner_orig Hlineage.
  unfold mutex_del_owner_value_lineage_prop in Hlineage |- *.
  destruct Hlineage as
    (m & Htype & Hfields & Hpcp & Howner & HmPCP & Hshape).
  split; [exact Hpcp|]. split; [exact Howner|].
  exists m. repeat split; try assumption.
  - rewrite <- Hpcp. exact HmPCP.
  - destruct m.(mfOwner); destruct m.(mfOwnerOrigPrio);
      simpl in Hshape |- *; try contradiction; auto.
    rewrite <- Howner. exact Hshape.
Qed.
Lemma mutex_del_source_entry_from_focus_facts__g03_owner_entry :
  forall sg e entry eid pevent tasks_waiting etype ecnt eptr egrp etbl
         pcp owner_orig,
    verification_slice_cross_module_consistency sg entry ->
    event_snapshot_of_prop sg entry.(TskState) entry.(EventState) eid e
      etype ecnt eptr egrp etbl ->
    pevent = event_addr sg eid ->
    valid_event_id sg eid ->
    entry.(IntrState).(intNesting) <= 0 ->
    etype = 4 ->
    mutex_del_owner_value_lineage_prop e ecnt pcp owner_orig ->
    ((unsigned_last_nbits egrp 32 = 0 /\ tasks_waiting = 0) \/
     (unsigned_last_nbits egrp 32 <> 0 /\ tasks_waiting = 1)) ->
    0 <= egrp <= 255 ->
    mutex_del_source_entry_prop
      sg e entry eid pevent tasks_waiting.
Proof.
  intros sg e entry eid pevent tasks_waiting etype ecnt eptr egrp etbl
    pcp owner_orig Hcross Hsnapshot Hpevent Hvalid Hintr _ Hlineage
    Hbranch Hegrp_range.
  pose proof Hsnapshot as Hsnapshot0.
  unfold event_snapshot_of_prop in Hsnapshot0.
  destruct Hsnapshot0 as
    [Hused [_ [_ [_ [Hegrp _]]]]].
  pose proof Hlineage as Hlineage0.
  unfold mutex_del_owner_value_lineage_prop in Hlineage0.
  destruct Hlineage0 as
    (m & Htype & Hfields & _ & _ & _ & _).
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as [_ [_ [Howners [Hwait _]]]].
  pose proof
    (mutex_del_owner_entry_consistency_from_cross
       sg entry eid e Hused Htype (ex_intro _ m Hfields) Howners)
    as Howner_entry.
  unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_object_consistency
    in Hwait.
  destruct Hwait as [Hwait_entries _].
  specialize (Hwait_entries eid e Hused).
  destruct Hwait_entries as [Hcanonical _].
  assert (Hegrp_self : egrp = unsigned_last_nbits egrp 32).
  {
    apply UInt_unsigned_eq.
    split; [lia|].
    change (egrp <= 4294967295).
    lia.
  }
  unfold mutex_del_source_entry_prop.
  split; [exact Hpevent|].
  split; [exact Hvalid|].
  split; [exact Hused|].
  split; [exact Htype|].
  split; [exists m; exact Hfields|].
  split; [exact Hintr|].
  split.
  - unfold mutex_del_tasks_waiting_prop.
    destruct Hbranch as [[Hzero Htasks] | [Hnonzero Htasks]].
    + left. split; [exact Htasks|].
      apply
        (proj1
           (mutex_del_wait_grp_zero_iff_empty__g03_owner_entry
              sg entry.(TskState) e.(waitList) Hcanonical)).
      rewrite <- Hegrp. rewrite Hegrp_self. exact Hzero.
    + right. split; [exact Htasks|].
      intro Hempty.
      apply Hnonzero.
      rewrite <- Hegrp_self, Hegrp, Hempty. reflexivity.
  - exact Howner_entry.
Qed.
Lemma mutex_del_no_pend_zero_facts__g03_owner_entry :
  forall sg e entry eid pevent tasks_waiting ecnt eptr egrp etbl
         opt_in opt,
    mutex_del_source_entry_prop
      sg e entry eid pevent tasks_waiting ->
    event_snapshot_of_prop sg entry.(TskState) entry.(EventState) eid e
      4 ecnt eptr egrp etbl ->
    unsigned_last_nbits tasks_waiting 32 = 0 ->
    mutex_del_option_decode_prop opt_in opt ->
    0 = opt_in ->
    egrp = 0 /\
    event_snapshot_of_prop sg entry.(TskState) entry.(EventState) eid e
      4 ecnt eptr 0 etbl /\
    mutex_del_success_mode_prop opt tasks_waiting /\
    mutex_del_no_pend_mode_prop opt tasks_waiting.
Proof.
  intros sg e entry eid pevent tasks_waiting ecnt eptr egrp etbl
    opt_in opt Hsource Hsnapshot Htasks_bits Hdecode Hopt.
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as
    [_ [_ [_ [_ [_ [_ [Htasks _]]]]]]].
  unfold mutex_del_tasks_waiting_prop in Htasks.
  destruct Htasks as [[Htasks Hempty] | [Htasks Hnonempty]].
  - subst tasks_waiting.
    pose proof Hsnapshot as Hsnapshot0.
    unfold event_snapshot_of_prop in Hsnapshot0.
    destruct Hsnapshot0 as [_ [_ [_ [_ [Hegrp _]]]]].
    rewrite Hempty in Hegrp. cbn in Hegrp. subst egrp.
    unfold mutex_del_option_decode_prop in Hdecode.
    destruct Hdecode as [[Hopt0 Hno_pend] |
      [[Hopt1 Halways] | [Hbad0 [Hbad1 Hinvalid]]]].
    + subst opt.
      split; [reflexivity|].
      split; [exact Hsnapshot|].
      split.
      * reflexivity.
      * unfold mutex_del_no_pend_mode_prop. split; reflexivity.
    + lia.
    + lia.
  - subst tasks_waiting. cbn in Htasks_bits. discriminate.
Qed.
Lemma mutex_del_event_focus_to_ready_identity__g03_owner_entry :
  forall sg ls eid,
    mutex_del_event_focus_inv sg ls eid |--
      mutex_del_event_ready_focus_inv sg ls ls eid.
Proof.
  intros sg ls eid.
  unfold mutex_del_event_focus_inv, mutex_del_event_ready_focus_inv.
  unfold verification_slice_task_inv, verification_slice_sched_inv.
  pureIntros.
  assert (Heq : forall y,
    encode_ready_tbl_at ls.(SchedState).(readyList) ls.(TskState) y =
    encode_ready_tbl_at_or ls.(SchedState).(readyList) ls.(TskState) y).
  {
    intro y.
    apply (sched_stable_tbl_eq_or
      sg ls.(TskState) ls.(SchedState) y); assumption.
  }
  unfold verification_slice_store_sched_state, verification_slice_sched_raw_ready_prio_stage.
  rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
    <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
  cancel.
  andp_cancel.
Qed.
Lemma mutex_del_owner_stage_empty_event_noninterference__g03_owner_entry :
  forall sg e entry post eid,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(waitList) = [] ->
    mutex_del_rdyatprio_stage_prop sg e entry post ->
    mutex_del_selected_event_noninterference_prop eid entry post.
Proof.
  intros sg e entry post eid Hused Hempty Hstage.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as (m & Htype & Hfields & Hshape & Hexec).
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis))
    eqn:Hdisabled.
  - subst post.
    unfold mutex_del_selected_event_noninterference_prop.
    intros selected Hselected. split; [exact Hselected|].
    intros tid Hin. reflexivity.
  - destruct m.(mfOwner) as [owner_tid|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [owner_orig|] eqn:Horig;
      simpl in Hexec.
    + destruct Hexec as (owner_t & Howner_task & Hexec).
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Hprio.
      * unfold atomic_task_set_curPrio in Hexec.
        destruct Hexec as [Hready | [Hwaiting | Hdormant]].
        -- unfold atomic_task_set_curPrio_ready in Hready.
           destruct Hready as [t [oldPrio [t'
             [_ [_ [_ [_ [_ [_ [_ [_ Hpost]]]]]]]]]]].
           cbv zeta in Hpost. subst post. cbn.
           unfold mutex_del_selected_event_noninterference_prop.
           intros selected Hselected.
           rewrite Hused in Hselected. inversion Hselected; subst selected.
           split; [exact Hused|].
           intros tid Hin. rewrite Hempty in Hin. contradiction.
        -- unfold atomic_task_set_curPrio_waiting in Hwaiting.
           destruct Hwaiting as
             (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
              evSt2 & pty & Hnot_ready & Htask & Hold & Hne & Hlo & Hhi &
              Hslot & Hpend & Hptr & Hmulti & Hwait_get & Hwait_type &
              Hwait_in & Ht' & Htsk & Hwait' & Hev & Hpost).
           assert (Heid_neq : eid <> wait_eid).
           {
             intro Heq. subst wait_eid.
             rewrite Hused in Hwait_get. inversion Hwait_get; subst wait_e.
             rewrite Hempty in Hwait_in. contradiction.
           }
           apply Z.eqb_neq in Heid_neq.
           unfold mutex_del_selected_event_noninterference_prop.
           intros selected Hselected.
           rewrite Hused in Hselected. inversion Hselected; subst selected.
           rewrite Hpost, Hev, Htsk. cbn. rewrite Heid_neq.
           split; [exact Hused|].
           intros tid Hin. rewrite Hempty in Hin. contradiction.
        -- unfold atomic_task_set_curPrio_dormant in Hdormant.
           destruct Hdormant as
             (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask & Hold & Hne &
              Hlo & Hhi & Hslot & Hptr & Hmulti & Hnot_effective & Ht' &
              Htsk & Hpost).
           unfold mutex_del_selected_event_noninterference_prop.
           intros selected Hselected.
           rewrite Hused in Hselected. inversion Hselected; subst selected.
           rewrite Hpost, Htsk. cbn.
           split; [exact Hused|].
           intros tid Hin. rewrite Hempty in Hin. contradiction.
      * subst post.
        unfold mutex_del_selected_event_noninterference_prop.
        intros selected Hselected. split; [exact Hselected|].
        intros tid Hin. reflexivity.
    + contradiction.
    + contradiction.
    + subst post.
      unfold mutex_del_selected_event_noninterference_prop.
      intros selected Hselected. split; [exact Hselected|].
      intros tid Hin. reflexivity.
Qed.
Lemma mutex_del_event_owner_open_merge_physical__g03_owner_entry :
  forall sg ls eid owner_tid owner_t owner_ptr owner_prio prio_addr,
    task_prio_snapshot_of_prop
      sg ls.(TskState) owner_tid owner_t owner_ptr owner_prio ->
    task_prio_field_layout_prop owner_ptr prio_addr ->
    prio_addr # UChar |-> owner_prio **
    mutex_del_event_owner_open_inv sg ls eid owner_tid owner_t |--
      mutex_del_event_focus_inv sg ls eid.
Proof.
  intros sg ls eid owner_tid owner_t owner_ptr owner_prio prio_addr
    Hsnapshot Hlayout.
  unfold mutex_del_event_owner_open_inv, mutex_del_event_focus_inv.
  sep_apply_l_atomic
    (mutex_del_task_open_merge
       sg ls.(TskState) owner_tid owner_t owner_ptr owner_prio prio_addr
       Hsnapshot Hlayout).
  cancel.
  andp_cancel.
Qed.
Lemma mutex_del_owner_stage_preserves_selected_mutex_fields__g04_no_pend_errors :
  forall sg e entry post eid m,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_rdyatprio_stage_prop sg e entry post ->
    exists epost,
      post.(EventState).(inUsedEventStates) eid = Some epost /\
      epost.(eventType) = OS_EVENT_TYPE_MUTEX /\
      epost.(mutexFields) = Some m.
Proof.
  intros sg e entry post eid m Hentry Htype Hfields Hstage.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as (m' & Htype' & Hfields' & Hshape & Hexec).
  rewrite Hfields in Hfields'. inversion Hfields'; subst m'.
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - subst post. exists e. repeat split; assumption.
  - destruct m.(mfOwner) as [owner_tid|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [owner_orig|] eqn:Horig;
      simpl in Hshape, Hexec; try contradiction.
    + destruct Hexec as (owner_t & Htask & Hexec).
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Hcur.
      * destruct Hexec as [Hready | [Hwaiting | Hdormant]].
        -- unfold atomic_task_set_curPrio_ready in Hready.
           destruct Hready as
             (t & oldPrio & t' & Hin & Htask' & Hold & Hne & Hlo & Hhi &
              Hslot & Ht' & Hpost).
           cbv zeta in Hpost. subst post.
           exists e. cbn. repeat split; assumption.
        -- unfold atomic_task_set_curPrio_waiting in Hwaiting.
           destruct Hwaiting as
             (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
              evSt2 & pty & Hnot_ready & Htask' & Hold & Hne & Hlo & Hhi &
              Hslot & Hpend & Hptr & Hmulti & Hwait_get & Hwait_type &
              Hwait_in & Ht' & Htsk & Hwait' & Hev & Hpost).
           destruct (Z.eq_dec eid wait_eid) as [Heq | Hneq].
           ++ subst wait_eid.
              rewrite Hentry in Hwait_get. inversion Hwait_get; subst wait_e.
              subst wait_e'. subst evSt2. subst post.
              exists
                {| eventGeneration := e.(eventGeneration);
                   eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
                   eventType := eventType e;
                   mutexFields := mutexFields e;
                   semFields := semFields e;
                   mboxFields := mboxFields e;
                   queueFields := queueFields e;
                   waitList :=
                     Ucos2Verify.lib.helpers.insert_sorted_by
                       (Ucos2Verify.lib.event_wait.wait_prio_key sg tskSt2)
                       owner_tid
                       (Ucos2Verify.lib.helpers.remove_Z_eqb
                          owner_tid (waitList e)) |}.
              cbn. rewrite Z.eqb_refl. cbn.
              repeat split; assumption.
           ++ subst evSt2. subst post.
              exists e. cbn.
              rewrite (proj2 (Z.eqb_neq eid wait_eid) Hneq).
              repeat split; assumption.
        -- unfold atomic_task_set_curPrio_dormant in Hdormant.
           destruct Hdormant as
             (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask' & Hold &
              Hne & Hlo & Hhi & Hslot & Hptr & Hmulti & Hnot_effective &
              Ht' & Htsk & Hpost).
           subst post. exists e. cbn. repeat split; assumption.
      * subst post. exists e. repeat split; assumption.
    + subst post. exists e. repeat split; assumption.
Qed.
Lemma mutex_del_owner_stage_enabled_pcp_range__g04_no_pend_errors :
  forall sg e entry post eid pevent tasks_waiting ecnt pcp owner_orig
         rdy_grp rdy_tbl prio_high tcb_high prio_tbl,
    mutex_del_refresh_context_prop
      sg rdy_grp rdy_tbl prio_high tcb_high prio_tbl ->
    mutex_del_source_entry_prop
      sg e entry eid pevent tasks_waiting ->
    mutex_del_owner_value_lineage_prop e ecnt pcp owner_orig ->
    mutex_del_rdyatprio_stage_prop sg e entry post ->
    verification_slice_cross_module_consistency sg post ->
    pcp <> 255 ->
    0 <= pcp /\ pcp < 64.
Proof.
  intros sg e entry post eid pevent tasks_waiting ecnt pcp owner_orig
    rdy_grp rdy_tbl prio_high tcb_high prio_tbl
    Hrefresh Hsource Hlineage Hstage Hcross Henabled.
  unfold mutex_del_refresh_context_prop in Hrefresh.
  destruct Hrefresh as [Hstable _].
  unfold mutex_del_source_entry_prop in Hsource.
  destruct Hsource as
    (_ & _ & Hentry & Htype & [m Hfields] & _ & _ & _).
  unfold mutex_del_owner_value_lineage_prop in Hlineage.
  destruct Hlineage as
    (m' & _ & Hfields' & _ & _ & Hpcp & _).
  rewrite Hfields in Hfields'. inversion Hfields'; subst m'.
  destruct
    (mutex_del_owner_stage_preserves_selected_mutex_fields__g04_no_pend_errors
       sg e entry post eid m Hentry Htype Hfields Hstage)
    as (epost & Hpost & Hpost_type & Hpost_fields).
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hprotocol & _).
  unfold mutex_protocol_consistency in Hprotocol.
  specialize (Hprotocol eid epost m Hpost Hpost_type Hpost_fields).
  destruct Hprotocol as [Hvalid _].
  unfold valid_mutex_pcp in Hvalid.
  unfold valid_stable_glob_vars in Hstable.
  destruct Hstable as
    (_ & _ & _ & _ & _ & Hlowest & _ & _ & Hdisabled & _).
  rewrite Hpcp in Hvalid.
  destruct Hvalid as [Hdisabled_pcp | Hrange].
  - rewrite Hdisabled in Hdisabled_pcp. contradiction.
  - rewrite Hlowest in Hrange. lia.
Qed.

(** Owner restoration cannot rewrite the mutex being deleted.  In the only
    branch that rewrites an event wait list, mutex-owner consistency says
    that the owner is not waiting on this same mutex. *)
Lemma mutex_del_owner_stage_preserves_selected_event__g04_no_pend_errors :
  forall sg e entry post eid m,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    verification_slice_cross_module_consistency sg entry ->
    mutex_del_rdyatprio_stage_prop sg e entry post ->
    post.(EventState).(inUsedEventStates) eid = Some e.
Proof.
  intros sg e entry post eid m Hentry Htype Hfields Hcross Hstage.
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as (_ & _ & Howners & _).
  unfold mutex_owner_consistency in Howners.
  specialize (Howners eid e m (conj Hentry (conj Htype Hfields))).
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as (m' & Htype' & Hfields' & Hshape & Hexec).
  rewrite Hfields in Hfields'. inversion Hfields'; subst m'.
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - subst post. exact Hentry.
  - destruct m.(mfOwner) as [owner_tid|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [owner_orig|] eqn:Horig;
      simpl in Hshape, Hexec, Howners; try contradiction.
    + destruct Howners as
        (owner_t0 & owner_orig0 & Htask0 & Horig0 & Hprio0 & Hnotin).
      destruct Hexec as (owner_t & Htask & Hexec).
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Hcur.
      * destruct Hexec as [Hready | [Hwaiting | Hdormant]].
        -- unfold atomic_task_set_curPrio_ready in Hready.
           destruct Hready as
             (t & oldPrio & t' & Hin & Htask' & Hold & Hne & Hlo & Hhi &
              Hslot & Ht' & Hpost).
           cbv zeta in Hpost. subst post. cbn. exact Hentry.
        -- unfold atomic_task_set_curPrio_waiting in Hwaiting.
           destruct Hwaiting as
             (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
              evSt2 & pty & Hnot_ready & Htask' & Hold & Hne & Hlo & Hhi &
              Hslot & Hpend & Hptr & Hmulti & Hwait_get & Hwait_type &
              Hwait_in & Ht' & Htsk & Hwait' & Hev & Hpost).
           assert (Hneq : eid <> wait_eid).
           {
             intro Heq. subst wait_eid.
             rewrite Hentry in Hwait_get. inversion Hwait_get; subst wait_e.
             rewrite Htask in Htask0. inversion Htask0; subst owner_t0.
             exact (Hnotin Hwait_in).
           }
           subst evSt2. subst post. cbn.
           rewrite (proj2 (Z.eqb_neq eid wait_eid) Hneq).
           exact Hentry.
        -- unfold atomic_task_set_curPrio_dormant in Hdormant.
           destruct Hdormant as
             (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask' & Hold &
              Hne & Hlo & Hhi & Hslot & Hptr & Hmulti & Hnot_effective &
              Ht' & Htsk & Hpost).
           subst post. cbn. exact Hentry.
      * subst post. exact Hentry.
    + subst post. exact Hentry.
Qed.
Lemma mutex_del_free_task_after__g04_no_pend_errors
  (sg : StableGlobVars) (pcp : Priority)
  (before : Glob_TaskAbstractState) : Glob_TaskAbstractState.
Proof.
  exact
    {| inUsedTaskStates := before.(inUsedTaskStates);
       unUsedTaskStates := before.(unUsedTaskStates);
       tcbListHead := before.(tcbListHead);
       prioTbl := fun p =>
         if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
             Z.eqb p pcp)%bool
         then PTFree
         else before.(prioTbl) p;
       taskRegNextID := before.(taskRegNextID);
       parkedTaskStacks := before.(parkedTaskStacks);
       taskLifecycle := before.(taskLifecycle);
     taskCount := before.(taskCount) |}.
Defined.
Lemma mutex_del_free_event_after__g04_no_pend_errors
  (eid : EventID) (before : Glob_EventAbstractState)
  : Glob_EventAbstractState.
Proof.
  exact
    {| inUsedEventStates := fun other =>
         if Z.eqb other eid then None else before.(inUsedEventStates) other;
       eventLifecycle := before.(eventLifecycle);
       publishedQueueBytes := before.(publishedQueueBytes);
       unUsedEventStates := eid :: before.(unUsedEventStates) |}.
Defined.
Lemma mutex_del_free_commit_after__g04_no_pend_errors
  (sg : StableGlobVars) (eid : EventID) (pcp : Priority)
  (before : UCOS2_Verify_State) : UCOS2_Verify_State.
Proof.
  exact
    {| IntrState := before.(IntrState);
       TskState := mutex_del_free_task_after__g04_no_pend_errors
         sg pcp before.(TskState);
       SchedState := before.(SchedState);
       EventState := mutex_del_free_event_after__g04_no_pend_errors
         eid before.(EventState);
       TickState := before.(TickState);
       FlagState := before.(FlagState);
       MemoryState := before.(MemoryState);
       TimerState := before.(TimerState);
       StatsState := before.(StatsState);
       ControlState := before.(ControlState);
       NameState := before.(NameState) |}.
Defined.
Lemma mutex_del_release_task_after__g04_no_pend_errors
  (sg : StableGlobVars) (pcp : Priority)
  (before : Glob_TaskAbstractState) : Glob_TaskAbstractState.
Proof.
  exact
    {| inUsedTaskStates := before.(inUsedTaskStates);
       unUsedTaskStates := before.(unUsedTaskStates);
       tcbListHead := before.(tcbListHead);
       prioTbl := fun p =>
         if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
             Z.eqb p pcp)%bool
         then PTReserved
         else before.(prioTbl) p;
       taskRegNextID := before.(taskRegNextID);
       parkedTaskStacks := before.(parkedTaskStacks);
       taskLifecycle := before.(taskLifecycle);
     taskCount := before.(taskCount) |}.
Defined.
Lemma mutex_del_stable_release_after__g04_no_pend_errors
  (sg : StableGlobVars) (eid : EventID)
  (old : OSEventAbstractState) (m : MutexFields)
  (before : UCOS2_Verify_State) : UCOS2_Verify_State.
Proof.
  exact
    {| IntrState := before.(IntrState);
       TskState := mutex_del_release_task_after__g04_no_pend_errors
         sg m.(mfPCP) before.(TskState);
       SchedState := before.(SchedState);
       EventState := owner_release_update
         before.(EventState) eid old m.(mfPCP);
       TickState := before.(TickState);
       FlagState := before.(FlagState);
       MemoryState := before.(MemoryState);
       TimerState := before.(TimerState);
       StatsState := before.(StatsState);
       ControlState := before.(ControlState);
       NameState := before.(NameState) |}.
Defined.
Lemma mutex_del_prepare_after__g04_no_pend_errors
  (eid : EventID) (old : OSEventAbstractState) (m : MutexFields)
  (before : UCOS2_Verify_State) : UCOS2_Verify_State.
Proof.
  exact
    {| IntrState := before.(IntrState);
       TskState := before.(TskState);
       SchedState := before.(SchedState);
       EventState := owner_release_update
         before.(EventState) eid old m.(mfPCP);
       TickState := before.(TickState);
       FlagState := before.(FlagState);
       MemoryState := before.(MemoryState);
       TimerState := before.(TimerState);
       StatsState := before.(StatsState);
       ControlState := before.(ControlState);
       NameState := before.(NameState) |}.
Defined.
Lemma mutex_del_release_task_valid__g04_no_pend_errors :
  forall sg pcp before,
    verification_slice_task_validity sg before ->
    no_live_task_at_priority before pcp ->
    verification_slice_task_validity sg
      (mutex_del_release_task_after__g04_no_pend_errors sg pcp before).
Proof.
  intros sg pcp before Hvalid Hno_live.
  unfold verification_slice_task_validity, verification_slice_task_in_range,
    verification_slice_task_in_range in Hvalid |- *.
  destruct Hvalid as
    ((Hids & Hnodup & Hfree_range & Hpartition & Htable &
      Hregistered & Hunique) & Hprio).
  split.
  - cbn.
    split; [exact Hids|].
    split; [exact Hnodup|].
    split; [exact Hfree_range|].
    split; [exact Hpartition|].
    split.
    + intros p tid Hslot.
      destruct
        ((negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
          Z.eqb p pcp)%bool) eqn:Hcond; [discriminate|].
      eapply Htable. exact Hslot.
    + split.
      * unfold task_current_prio_registered in *.
        intros tid t Hlookup. cbn in Hlookup |- *.
        specialize (Hno_live tid t Hlookup).
        assert (Hneqb : Z.eqb t.(curPrio) pcp = false).
        { apply Z.eqb_neq. exact Hno_live. }
        rewrite Hneqb, Bool.andb_false_r.
        exact (Hregistered tid t Hlookup).
      * exact Hunique.
  - cbn. exact Hprio.
Qed.
Lemma mutex_del_event_valid_task_ext__g04_no_pend_errors :
  forall sg tskSt1 tskSt2 evSt,
    (forall tid,
      tskSt1.(inUsedTaskStates) tid =
      tskSt2.(inUsedTaskStates) tid) ->
    verification_slice_event_in_range sg tskSt1 evSt ->
    verification_slice_event_in_range sg tskSt2 evSt.
Proof.
  intros sg tskSt1 tskSt2 evSt Hext Hvalid.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hvalid |- *.
  destruct Hvalid as
    (Hrange & Hnodup & Hfree_range & Hpartition & Hfields &
     Hpayload & Hqueue & Hwait).
  split; [exact Hrange|].
  split; [exact Hnodup|].
  split; [exact Hfree_range|].
  split; [exact Hpartition|].
  split; [exact Hfields|].
  split; [exact Hpayload|].
  split; [exact Hqueue|].
  intros eid0 ev Hlookup.
  eapply
    Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency_preserved_by_tskSt_ext.
  - exact Hext.
  - eapply Hwait. exact Hlookup.
Qed.
Lemma mutex_del_free_task_valid__g04_no_pend_errors :
  forall sg pcp before,
    verification_slice_task_validity sg before ->
    no_live_task_at_priority before pcp ->
    verification_slice_task_validity sg
      (mutex_del_free_task_after__g04_no_pend_errors sg pcp before).
Proof.
  intros sg pcp before Hvalid Hno_live.
  unfold verification_slice_task_validity, verification_slice_task_in_range,
    verification_slice_task_in_range in Hvalid |- *.
  destruct Hvalid as
    ((Hids & Hnodup & Hfree_range & Hpartition & Htable &
      Hregistered & Hunique) & Hprio).
  split.
  - cbn.
    split; [exact Hids|].
    split; [exact Hnodup|].
    split; [exact Hfree_range|].
    split; [exact Hpartition|].
    split.
    + intros p0 tid0 Hslot.
      destruct
        ((negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
          Z.eqb p0 pcp)%bool) eqn:Hcond; [discriminate|].
      eapply Htable. exact Hslot.
    + split.
      * unfold task_current_prio_registered in *.
        intros tid0 t0 Hlookup. cbn in Hlookup |- *.
        specialize (Hno_live tid0 t0 Hlookup).
        assert (Hneqb : Z.eqb t0.(curPrio) pcp = false).
        { apply Z.eqb_neq. exact Hno_live. }
        rewrite Hneqb, Bool.andb_false_r.
        exact (Hregistered tid0 t0 Hlookup).
      * exact Hunique.
  - cbn. exact Hprio.
Qed.
Lemma mutex_del_wait_grp_zero_iff_empty__g04_no_pend_errors :
  forall sg tskSt wl,
    Ucos2Verify.lib.event_wait.event_waitList_canonical sg tskSt wl ->
    (encode_event_wait_grp wl tskSt = 0 <-> wl = nil).
Proof.
  intros sg tskSt wl Hcanonical.
  split.
  - intro Hgrp.
    destruct wl as [|tid rest]; [reflexivity |].
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
  - intros Hnil. subst wl. reflexivity.
Qed.
Lemma mutex_del_freed_lookup_some_before__g04_no_pend_errors :
  forall eid before other ev,
    (mutex_del_free_event_after__g04_no_pend_errors eid before)
      .(inUsedEventStates) other = Some ev ->
    before.(inUsedEventStates) other = Some ev.
Proof.
  intros eid before other ev Hlookup.
  unfold mutex_del_free_event_after__g04_no_pend_errors in Hlookup.
  cbn in Hlookup.
  destruct (Z.eqb other eid); [discriminate | exact Hlookup].
Qed.
Lemma mutex_del_freed_lookup_other__g04_no_pend_errors :
  forall eid before other,
    other <> eid ->
    (mutex_del_free_event_after__g04_no_pend_errors eid before)
      .(inUsedEventStates) other = before.(inUsedEventStates) other.
Proof.
  intros eid before other Hneq.
  unfold mutex_del_free_event_after__g04_no_pend_errors. cbn.
  destruct (Z.eqb other eid) eqn:Heq; [|reflexivity].
  apply Z.eqb_eq in Heq. contradiction.
Qed.
Lemma mutex_del_free_event_valid__g04_no_pend_errors :
  forall sg pcp tskSt evSt eid old,
    evSt.(inUsedEventStates) eid = Some old ->
    verification_slice_event_in_range sg tskSt evSt ->
    verification_slice_event_in_range sg
      (mutex_del_free_task_after__g04_no_pend_errors sg pcp tskSt)
      (mutex_del_free_event_after__g04_no_pend_errors eid evSt).
Proof.
  intros sg pcp tskSt evSt eid old Hused Hvalid.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in *.
  destruct Hvalid as
    (Hrange & Hnodup & Hfree_range & Hpartition & Hfields &
     Hpayload & Hqueue & Hwait).
  split.
  - intros other ev Hlookup.
    eapply Hrange.
    eapply mutex_del_freed_lookup_some_before__g04_no_pend_errors;
      eauto.
  - split.
    + cbn. constructor.
      * eapply event_slot_partition_used_not_free; eauto.
      * exact Hnodup.
    + split.
      * cbn. constructor.
        -- eapply Hrange; eauto.
        -- exact Hfree_range.
      * split.
        -- unfold mutex_del_free_event_after__g04_no_pend_errors. cbn.
           eapply event_slot_partition_preserved_delete; eauto.
        -- split.
           ++ intros other ev Hlookup.
              eapply Hfields.
              eapply mutex_del_freed_lookup_some_before__g04_no_pend_errors;
                eauto.
           ++ split.
              ** intros other ev Hlookup.
                 eapply Hpayload.
                 eapply mutex_del_freed_lookup_some_before__g04_no_pend_errors;
                   eauto.
              ** split.
                 --- unfold queue_binding_unique in *.
                     intros eid1 eid2 e1 e2 qid Hget1 Hget2 Hqid1 Hqid2.
                     eapply Hqueue; eauto using
                       mutex_del_freed_lookup_some_before__g04_no_pend_errors.
                 --- intros other ev Hlookup.
                     cbn.
                     eapply Hwait.
                     eapply mutex_del_freed_lookup_some_before__g04_no_pend_errors;
                       eauto.
Qed.
Lemma mutex_del_freed_event_wait_consistency__g04_no_pend_errors :
  forall sg pre eid pcp,
    verification_slice_event_wait_object_consistency sg pre ->
    Ucos2Verify.lib.event_wait.task_event_id_unreferenced_prop pre eid ->
    verification_slice_event_wait_object_consistency sg
      (mutex_del_free_commit_after__g04_no_pend_errors sg eid pcp pre).
Proof.
  intros sg pre eid pcp Hconsistent Hunreferenced.
  unfold verification_slice_event_wait_object_consistency in *.
  destruct Hconsistent as [Hentry [Htotal Hclosed]].
  split; [|split].
  - intros other ev Hlookup. cbn in Hlookup |- *.
    change
      (Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency
         sg pre.(TskState) other ev).
    apply Hentry.
    exact
      (mutex_del_freed_lookup_some_before__g04_no_pend_errors
         eid pre.(EventState) other ev Hlookup).
  - unfold Ucos2Verify.lib.event_wait.task_event_reference_backlink_consistency
      in *.
    intros tid t other ev Htask Hlookup Hreference.
    cbn in Htask, Hlookup |- *.
    destruct (Z.eq_dec other eid) as [Heq | Hneq].
    + subst other.
      specialize (Hunreferenced tid t Htask) as [Hsingle Hmulti].
      destruct Hreference as [Hreference | Hreference]; contradiction.
    + eapply Htotal; eauto.
      exact
        (mutex_del_freed_lookup_some_before__g04_no_pend_errors
           eid pre.(EventState) other ev Hlookup).
  - unfold Ucos2Verify.lib.event_wait.task_event_reference_closure in *.
    intros tid t Htask. cbn in Htask |- *.
    specialize (Hclosed tid t Htask) as [Hsingle Hmulti].
    specialize (Hunreferenced tid t Htask) as [Hsingle_neq Hmulti_neq].
    split.
    + intros other Hptr.
      destruct (Z.eq_dec other eid) as [Heq | Hneq].
      * subst other. contradiction.
      * destruct (Hsingle other Hptr) as [ev Hlookup].
        exists ev. cbn.
        rewrite (proj2 (Z.eqb_neq other eid) Hneq). exact Hlookup.
    + intros other Hin.
      destruct (Z.eq_dec other eid) as [Heq | Hneq].
      * subst other. contradiction.
      * destruct (Hmulti other Hin) as [ev Hlookup].
        exists ev. cbn.
        rewrite (proj2 (Z.eqb_neq other eid) Hneq). exact Hlookup.
Qed.
Lemma mutex_del_free_cross_module_consistency__g04_no_pend_errors :
  forall sg pre eid old m,
    pre.(EventState).(inUsedEventStates) eid = Some old ->
    old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    old.(mutexFields) = Some m ->
    m.(mfOwner) = None ->
    no_live_task_at_priority pre.(TskState) m.(mfPCP) ->
    Ucos2Verify.lib.event_wait.task_event_id_unreferenced_prop pre eid ->
    verification_slice_cross_module_consistency sg pre ->
    verification_slice_cross_module_consistency sg
      (mutex_del_free_commit_after__g04_no_pend_errors
         sg eid m.(mfPCP) pre).
Proof.
  intros sg pre eid old m Hused Htype Hfields Howner
    Hno_live Hunreferenced Hcross.
  assert (Hlookup_back : forall mid ev,
    (mutex_del_free_commit_after__g04_no_pend_errors
       sg eid m.(mfPCP) pre).(EventState).(inUsedEventStates) mid = Some ev ->
    pre.(EventState).(inUsedEventStates) mid = Some ev).
  {
    intros mid ev Hlookup. cbn in Hlookup.
    exact
      (mutex_del_freed_lookup_some_before__g04_no_pend_errors
         eid pre.(EventState) mid ev Hlookup).
  }
  unfold verification_slice_cross_module_consistency in Hcross |- *.
  destruct Hcross as
    (Hosprio & Hpriotbl & Howners & Hwait & Hready_complete &
     Hready_order & Hceiling & Htask_unique & Hprotocol & Hpcp_unique).
  split.
  - eapply osprio_cur_consistency_indep_prioTbl_EventState.
    + reflexivity.
    + reflexivity.
    + exact Hosprio.
  - split.
    + unfold priotbl_consistency in Hpriotbl |- *.
      intro p. specialize (Hpriotbl p). cbn.
      destruct
        ((negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
          Z.eqb p m.(mfPCP))%bool) eqn:Hcond.
      * apply Bool.andb_true_iff in Hcond as [Henabled_b Hp_b].
        apply Bool.negb_true_iff in Henabled_b.
        apply Z.eqb_neq in Henabled_b.
        apply Z.eqb_eq in Hp_b.
        split.
        -- intros (tid & Hin & t & Htask & Hprio).
           apply (Hno_live tid t Htask).
           rewrite Hprio. exact Hp_b.
        -- intros (mid & ev & m2 & Hlookup & Htype2 & Hfields2 & Hreserve).
           destruct Hreserve as [Henabled2 Hpcp2].
           assert (Hmid : mid = eid).
           {
             symmetry.
             eapply Hpcp_unique.
             - exact Hused.
             - exact Htype.
             - exact Hfields.
             - eapply Hlookup_back. exact Hlookup.
             - exact Htype2.
             - exact Hfields2.
             - rewrite Hpcp2. symmetry. exact Hp_b.
             - exact Henabled_b.
           }
           subst mid. cbn in Hlookup. rewrite Z.eqb_refl in Hlookup.
           discriminate.
      * destruct (pre.(TskState).(prioTbl) p) eqn:Hslot.
        -- destruct Hpriotbl as [Hno_ready Hno_mutex].
           split.
           ++ exact Hno_ready.
           ++ intros (mid & ev & m2 & Hlookup & Htype2 & Hfields2 & Hreserve).
              apply Hno_mutex. exists mid, ev, m2.
              split; [eapply Hlookup_back; exact Hlookup|].
              split; [exact Htype2|].
              split; [exact Hfields2|exact Hreserve].
        -- destruct Hpriotbl as
             (mid & ev & m2 & Hlookup & Htype2 & Hfields2 & Hpcp2 & Hshape).
           assert (Hp_enabled : p <> sg.(osPrioMutexCeilDis)).
           {
             intro Hp. rewrite Hp in Hslot.
             unfold ceiling_priotbl_free in Hceiling.
             rewrite Hceiling in Hslot. discriminate.
           }
           assert (Hmid_neq : mid <> eid).
           {
             intro Hmid. subst mid.
             rewrite Hused in Hlookup. inversion Hlookup; subst ev.
             rewrite Hfields in Hfields2. inversion Hfields2; subst m2.
             assert (Htrue :
               (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
                Z.eqb p m.(mfPCP))%bool = true).
             {
               apply Bool.andb_true_iff. split.
               - apply Bool.negb_true_iff, Z.eqb_neq.
                 rewrite Hpcp2. exact Hp_enabled.
               - apply Z.eqb_eq. symmetry. exact Hpcp2.
             }
             rewrite Htrue in Hcond. discriminate.
           }
           exists mid, ev, m2. cbn.
           rewrite (proj2 (Z.eqb_neq mid eid) Hmid_neq).
           repeat split; assumption.
        -- destruct Hpriotbl as [t [Htask [Htask_prio | Hmutex_source]]].
           ++ exists t. split; [exact Htask | left; exact Htask_prio].
           ++ destruct Hmutex_source as
                (mid & ev & m2 & Hlookup & Htype2 & Hfields2 &
                 Howner2 & Hsource).
              assert (Hmid_neq : mid <> eid).
              {
                intro Hmid. subst mid.
                rewrite Hused in Hlookup. inversion Hlookup; subst ev.
                rewrite Hfields in Hfields2. inversion Hfields2; subst m2.
                rewrite Howner in Howner2. discriminate.
              }
              exists t. split; [exact Htask | right].
              exists mid, ev, m2. cbn.
              rewrite (proj2 (Z.eqb_neq mid eid) Hmid_neq).
              repeat split; assumption.
    + split.
      * unfold mutex_owner_consistency in Howners |- *.
        intros mid ev m2 (Hlookup & Htype2 & Hfields2).
        apply (Howners mid ev m2).
        repeat split; try assumption.
        eapply Hlookup_back. exact Hlookup.
      * split.
        -- eapply mutex_del_freed_event_wait_consistency__g04_no_pend_errors;
             eauto.
        -- split.
           ++ eapply ready_list_completeness_preserved_by_release.
              ** reflexivity.
              ** reflexivity.
              ** exact Hready_complete.
           ++ split.
              ** eapply ready_list_order_preserved_by_release.
                 --- reflexivity.
                 --- reflexivity.
                 --- exact Hready_order.
              ** split.
                 --- unfold ceiling_priotbl_free in Hceiling |- *.
                     cbn.
                     destruct
                       (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis))
                       eqn:Hdisabled.
                     +++ simpl. exact Hceiling.
                     +++ assert (Hneqb :
                           Z.eqb sg.(osPrioMutexCeilDis) m.(mfPCP) = false).
                         {
                           apply Z.eqb_neq. apply Z.eqb_neq in Hdisabled.
                           congruence.
                         }
                         rewrite Hneqb. exact Hceiling.
                 --- split.
                     +++ unfold task_priority_unique_prop in Htask_unique |- *.
                         exact Htask_unique.
                     +++ split.
                         *** unfold mutex_protocol_consistency in Hprotocol |- *.
                             intros mid ev m2 Hlookup Htype2 Hfields2.
                             assert (Hold_lookup :
                               pre.(EventState).(inUsedEventStates) mid = Some ev).
                             { eapply Hlookup_back. exact Hlookup. }
                             specialize
                               (Hprotocol mid ev m2 Hold_lookup Htype2 Hfields2).
                             destruct Hprotocol as
                               [Hvalid [Howner_shape Hslot2]].
                             split; [exact Hvalid | split; [exact Howner_shape |]].
                             destruct Hslot2 as [Hdisabled2 | [Henabled2 Hslot2]].
                             ---- left. exact Hdisabled2.
                             ---- right. split; [exact Henabled2 |].
                                  assert (Hpcp_neq :
                                    m2.(mfPCP) <> m.(mfPCP)).
                                  {
                                    intro Heq.
                                    assert (Hmid : mid = eid).
                                    {
                                      eapply Hpcp_unique.
                                      - exact Hold_lookup.
                                      - exact Htype2.
                                      - exact Hfields2.
                                      - exact Hused.
                                      - exact Htype.
                                      - exact Hfields.
                                      - exact Heq.
                                      - exact Henabled2.
                                    }
                                    subst mid. cbn in Hlookup.
                                    rewrite Z.eqb_refl in Hlookup. discriminate.
                                  }
                                  cbn.
                                  rewrite (proj2 (Z.eqb_neq m2.(mfPCP) m.(mfPCP))
                                             Hpcp_neq), Bool.andb_false_r.
                                  exact Hslot2.
                         *** eapply mutex_enabled_pcp_unique_transport
                               with (lvs1 := pre).
                             ---- intros mid ev m2 Hlookup Htype2 Hfields2.
                                  exists ev, m2. repeat split; try assumption.
                                  eapply Hlookup_back. exact Hlookup.
                             ---- exact Hpcp_unique.
Qed.
Lemma atomic_event_free_with_priotbl_free_preserves_validity__g04_no_pend_errors :
  forall sg mid pre post,
    UCOS2_verification_slice_state_inv sg pre ->
    atomic_event_free_with_priotbl_free sg mid pre tt post ->
    UCOS2_verification_slice_state_inv sg post.
Proof.
  intros sg mid pre post Hvalid Hfree.
  unfold atomic_event_free_with_priotbl_free in Hfree.
  destruct Hfree as
    (old & m & evSt2 & tskSt2 & Hused & Htype & Hfields & Howner &
     Hempty & HevSt2 & HtskSt2 & Hpost).
  subst evSt2. subst tskSt2. subst post.
  change
    (UCOS2_verification_slice_state_inv sg
       (mutex_del_free_commit_after__g04_no_pend_errors
          sg mid m.(mfPCP) pre)).
  unfold UCOS2_verification_slice_state_inv in Hvalid |- *.
  destruct Hvalid as [Htask [Hsched [Hevent Hcross]]].
  assert (Hregistered : task_current_prio_registered pre.(TskState)).
  {
    eapply task_vaild_cond_current_prio_registered. exact Htask.
  }
  assert (Hno_live :
    no_live_task_at_priority pre.(TskState) m.(mfPCP)).
  {
    unfold verification_slice_cross_module_consistency in Hcross.
    destruct Hcross as
      (_ & _ & _ & _ & _ & _ & Hceiling & _ & Hprotocol & _).
    unfold mutex_protocol_consistency in Hprotocol.
    specialize (Hprotocol mid old m Hused Htype Hfields).
    destruct Hprotocol as (_ & _ & Hslot).
    destruct Hslot as [Hdisabled | [Henabled [Hreserved | Howned]]].
    - eapply task_current_prio_registered_free_slot_is_unused.
      + exact Hregistered.
      + unfold ceiling_priotbl_free in Hceiling.
        rewrite Hdisabled. exact Hceiling.
    - eapply task_current_prio_registered_reserved_slot_is_unused;
        eauto.
    - destruct Howned as (owner & Howner' & _).
      rewrite Howner in Howner'. discriminate.
  }
  assert (Hunreferenced :
    Ucos2Verify.lib.event_wait.task_event_id_unreferenced_prop pre mid).
  {
    unfold verification_slice_cross_module_consistency in Hcross.
    destruct Hcross as (_ & _ & _ & Hwait & _).
    eapply Ucos2Verify.lib.event_wait.event_wait_empty_implies_unreferenced;
      eauto.
  }
  split.
  - eapply mutex_del_free_task_valid__g04_no_pend_errors; eauto.
  - split.
    + pose proof
        (verification_slice_sched_in_range_ext sg pre.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg m.(mfPCP) pre.(TskState))
           pre.(SchedState) eq_refl) as Hsched_ext.
      change
        (verification_slice_sched_in_range sg
           (mutex_del_free_task_after__g04_no_pend_errors
              sg m.(mfPCP) pre.(TskState)) pre.(SchedState)).
      rewrite <- Hsched_ext. exact Hsched.
    + split.
      * eapply mutex_del_free_event_valid__g04_no_pend_errors; eauto.
      * eapply mutex_del_free_cross_module_consistency__g04_no_pend_errors;
          eauto.
Qed.
Lemma mutex_del_stable_release_validity__g04_no_pend_errors :
  forall sg before eid old m owner_tid owner_t orig,
    before.(EventState).(inUsedEventStates) eid = Some old ->
    old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    old.(mutexFields) = Some m ->
    m.(mfOwner) = Some owner_tid ->
    before.(TskState).(inUsedTaskStates) owner_tid = Some owner_t ->
    m.(mfOwnerOrigPrio) = Some orig ->
    owner_t.(curPrio) = orig ->
    old.(waitList) = nil ->
    no_live_task_at_priority before.(TskState) m.(mfPCP) ->
    UCOS2_verification_slice_state_inv sg before ->
    UCOS2_verification_slice_state_inv sg
      (mutex_del_stable_release_after__g04_no_pend_errors
         sg eid old m before).
Proof.
  intros sg before eid old m owner_tid owner_t orig
    Hused Htype Hfields Howner Htask_lookup Horig Howner_prio
    Hempty Hno_live Hvalid.
  unfold UCOS2_verification_slice_state_inv in Hvalid |- *.
  destruct Hvalid as [Htask [Hsched [Hevent Hcross]]].
  split.
  - eapply mutex_del_release_task_valid__g04_no_pend_errors; eauto.
  - split.
    + pose proof
        (verification_slice_sched_in_range_ext sg before.(TskState)
           (mutex_del_release_task_after__g04_no_pend_errors
              sg m.(mfPCP) before.(TskState))
           before.(SchedState) eq_refl) as Hsched_ext.
      change
        (verification_slice_sched_in_range sg
           (mutex_del_release_task_after__g04_no_pend_errors
              sg m.(mfPCP) before.(TskState)) before.(SchedState)).
      rewrite <- Hsched_ext. exact Hsched.
    + split.
      * assert (Hevent' :
          verification_slice_event_in_range sg
            (mutex_del_release_task_after__g04_no_pend_errors
               sg m.(mfPCP) before.(TskState))
            before.(EventState)).
        {
          eapply mutex_del_event_valid_task_ext__g04_no_pend_errors.
          - intro tid. reflexivity.
          - exact Hevent.
        }
        unfold verification_slice_event_in_range, verification_slice_event_in_range in *.
        change
          (verification_slice_event_in_range sg
             (mutex_del_release_task_after__g04_no_pend_errors
                sg m.(mfPCP) before.(TskState))
             (owner_release_update before.(EventState) eid old m.(mfPCP))).
        unfold owner_release_update, update_event_field_raw. cbn.
        rewrite Hempty.
        eapply verification_slice_event_in_range_preserved_by_mutex_owner_clear;
          eauto.
      * unfold mutex_del_stable_release_after__g04_no_pend_errors.
        eapply verification_slice_cross_module_consistency_preserved_by_release.
        -- exact Hused.
        -- exact Htype.
        -- exact Hfields.
        -- exact Howner.
        -- exact Htask_lookup.
        -- exact Horig.
        -- exact Howner_prio.
        -- reflexivity.
        -- exact Hcross.
Qed.
Lemma mutex_del_owner_stage_restores_owner_original__g04_no_pend_errors :
  forall sg e entry post m,
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_owner_entry_consistency_prop sg e entry ->
    mutex_del_rdyatprio_stage_prop sg e entry post ->
    match m.(mfOwner), m.(mfOwnerOrigPrio) with
    | None, None => True
    | Some tid, Some op =>
        exists t,
          post.(TskState).(inUsedTaskStates) tid = Some t /\
          t.(curPrio) = op
    | _, _ => False
    end.
Proof.
  intros sg e entry post m Htype Hfields Hentry_owner Hstage.
  unfold mutex_del_owner_entry_consistency_prop in Hentry_owner.
  destruct Hentry_owner as (m0 & Htype0 & Hfields0 & Hentry_owner).
  rewrite Hfields in Hfields0. inversion Hfields0; subst m0.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as (m0 & Htype1 & Hfields1 & Hshape & Hexec).
  rewrite Hfields in Hfields1. inversion Hfields1; subst m0.
  destruct m.(mfOwner) as [owner_tid|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [owner_orig|] eqn:Horig;
    simpl in Hentry_owner, Hshape, Hexec |- *; try contradiction.
  - destruct Hentry_owner as
      (owner_t0 & op & Htask0 & Horig0 & Hprio0).
    inversion Horig0; subst op.
    destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis))
      eqn:Hdisabled.
    + subst post. exists owner_t0. split; [exact Htask0|].
      destruct Hprio0 as [Hprio0 | [Henabled Hprio0]];
        [exact Hprio0|].
      apply Z.eqb_eq in Hdisabled. contradiction.
    + destruct Hexec as (owner_t & Htask & Hexec).
      rewrite Htask0 in Htask. inversion Htask; subst owner_t.
      destruct (Z.eqb owner_t0.(curPrio) m.(mfPCP)) eqn:Hcur.
      * destruct Hexec as [Hready | [Hwaiting | Hdormant]].
        -- unfold atomic_task_set_curPrio_ready in Hready.
           destruct Hready as
             (t & oldPrio & t' & Hin & Htask' & Hold & Hne & Hlo & Hhi &
              Hslot & Ht' & Hpost).
           cbv zeta in Hpost. subst post.
           exists t'. split.
           ++ cbn. rewrite Z.eqb_refl. reflexivity.
           ++ subst t'. reflexivity.
        -- unfold atomic_task_set_curPrio_waiting in Hwaiting.
           destruct Hwaiting as
             (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
              evSt2 & pty & Hnot_ready & Htask' & Hold & Hne & Hlo & Hhi &
              Hslot & Hpend & Hptr & Hmulti & Hwait_get & Hwait_type &
              Hwait_in & Ht' & Htsk & Hwait' & Hev & Hpost).
           subst tskSt2. subst post.
           exists t'. split.
           ++ cbn. rewrite Z.eqb_refl. reflexivity.
           ++ subst t'. reflexivity.
        -- unfold atomic_task_set_curPrio_dormant in Hdormant.
           destruct Hdormant as
             (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask' & Hold &
              Hne & Hlo & Hhi & Hslot & Hptr & Hmulti & Hnot_effective &
              Ht' & Htsk & Hpost).
           subst tskSt2. subst post.
           exists t'. split.
           ++ cbn. rewrite Z.eqb_refl. reflexivity.
           ++ subst t'. reflexivity.
      * subst post. exists owner_t0. split; [exact Htask0|].
        destruct Hprio0 as [Hprio0 | [_ Hprio0]]; [exact Hprio0|].
        apply Z.eqb_neq in Hcur. contradiction.
  - exact I.
Qed.
Lemma mutex_del_owner_stage_no_live_at_pcp__g04_no_pend_errors :
  forall sg e entry post eid current_event m,
    post.(EventState).(inUsedEventStates) eid = Some current_event ->
    current_event.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current_event.(mutexFields) = Some m ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_owner_entry_consistency_prop sg e entry ->
    mutex_del_rdyatprio_stage_prop sg e entry post ->
    verification_slice_task_validity sg post.(TskState) ->
    verification_slice_cross_module_consistency sg post ->
    m.(mfPCP) <> sg.(osPrioMutexCeilDis) ->
    no_live_task_at_priority post.(TskState) m.(mfPCP).
Proof.
  intros sg e entry post eid current_event m Hlookup Hcurrent_type
    Hcurrent_fields Htype Hfields Hentry_owner Hstage Htask Hcross Henabled.
  pose proof
    (mutex_del_owner_stage_restores_owner_original__g04_no_pend_errors
       sg e entry post m Htype Hfields Hentry_owner Hstage)
    as Hrestored.
  pose proof
    (task_vaild_cond_current_prio_registered sg post.(TskState) Htask)
    as Hregistered.
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hprotocol & _).
  unfold mutex_protocol_consistency in Hprotocol.
  specialize
    (Hprotocol eid current_event m Hlookup Hcurrent_type Hcurrent_fields).
  destruct Hprotocol as (Hvalid & Howner_shape & Hslot).
  unfold no_live_task_at_priority.
  intros tid t Htid Hprio.
  pose proof (Hregistered tid t Htid) as Hregistered_tid.
  rewrite Hprio in Hregistered_tid.
  destruct Hslot as [Hdisabled | [_ [Hreserved | Howned]]].
  - contradiction.
  - rewrite Hreserved in Hregistered_tid. discriminate.
  - destruct Howned as (owner & Howner & Hslot).
    rewrite Hslot in Hregistered_tid. inversion Hregistered_tid; subst owner.
    destruct m.(mfOwner) as [owner_tid|] eqn:Howner_eq;
      [|discriminate Howner].
    inversion Howner; subst owner_tid.
    destruct m.(mfOwnerOrigPrio) as [op|] eqn:Horig;
      simpl in Hrestored, Howner_shape; try contradiction.
    destruct Hrestored as (owner_t & Howner_t & Howner_prio).
    rewrite Htid in Howner_t. inversion Howner_t; subst owner_t.
    destruct Howner_shape as (_ & Hop_ne).
    specialize (Hop_ne Henabled).
    apply Hop_ne. rewrite <- Howner_prio. exact Hprio.
Qed.
Lemma mutex_del_free_commit_after_stable_release_eq__g04_no_pend_errors :
  forall sg eid old m before,
    mutex_del_free_commit_after__g04_no_pend_errors
      sg eid m.(mfPCP)
      (mutex_del_stable_release_after__g04_no_pend_errors
         sg eid old m before) =
    mutex_del_free_commit_after__g04_no_pend_errors
      sg eid m.(mfPCP) before.
Proof.
  intros sg eid old m before.
  destruct before as [bi bt bs be bk bf bm btm bst bc bn].
  destruct bt as [btin btun bthead btprio btcount btlife btrid btstacks].
  destruct be as [bein beun bequeue belife].
  unfold mutex_del_free_commit_after__g04_no_pend_errors,
    mutex_del_stable_release_after__g04_no_pend_errors,
    mutex_del_free_task_after__g04_no_pend_errors,
    mutex_del_release_task_after__g04_no_pend_errors,
    mutex_del_free_event_after__g04_no_pend_errors,
    owner_release_update, update_event_field_raw.
  cbn.
  assert (Hprio :
    (fun p =>
       if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
           Z.eqb p m.(mfPCP))%bool
       then PTFree
       else if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
                Z.eqb p m.(mfPCP))%bool
            then PTReserved else btprio p) =
    (fun p =>
       if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
           Z.eqb p m.(mfPCP))%bool
       then PTFree else btprio p)).
  {
    apply functional_extensionality. intro p.
    destruct
      ((negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
        Z.eqb p m.(mfPCP))%bool); reflexivity.
  }
  assert (Hevent :
    (fun other =>
       if Z.eqb other eid then None
       else if Z.eqb other eid then
              Some
                {| eventGeneration := old.(eventGeneration);
                   eventName := old.(eventName);
     eventPadding1 := old.(eventPadding1);
     eventPadding2 := old.(eventPadding2);
     eventPadding3 := old.(eventPadding3);
     eventPadding19 := old.(eventPadding19);
                   eventType := old.(eventType);
                   mutexFields :=
                     Some
                       {| mfPCP := m.(mfPCP);
                          mfOwner := None;
                          mfOwnerOrigPrio := None |};
                   semFields := old.(semFields);
                   mboxFields := old.(mboxFields);
                   queueFields := old.(queueFields);
                   waitList := old.(waitList) |}
            else bein other) =
    (fun other => if Z.eqb other eid then None else bein other)).
  {
    apply functional_extensionality. intro other.
    destruct (Z.eqb other eid); reflexivity.
  }
  assert (Htask_record :
    {| inUsedTaskStates := btin;
       unUsedTaskStates := btun;
       tcbListHead := bthead;
       prioTbl := fun p =>
         if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
             Z.eqb p m.(mfPCP))%bool
         then PTFree
         else if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
                  Z.eqb p m.(mfPCP))%bool
              then PTReserved else btprio p;
       taskRegNextID := btrid;
       parkedTaskStacks := btstacks;
       taskLifecycle := btlife;
     taskCount := btcount |} =
    {| inUsedTaskStates := btin;
       unUsedTaskStates := btun;
       tcbListHead := bthead;
       prioTbl := fun p =>
         if (negb (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) &&
             Z.eqb p m.(mfPCP))%bool
         then PTFree else btprio p;
       taskRegNextID := btrid;
       parkedTaskStacks := btstacks;
       taskLifecycle := btlife;
     taskCount := btcount |}).
  { f_equal. exact Hprio. }
  assert (Hevent_record :
    {| inUsedEventStates := fun other =>
         if Z.eqb other eid then None
         else if Z.eqb other eid then
                Some
                  {| eventGeneration := old.(eventGeneration);
                     eventName := old.(eventName);
     eventPadding1 := old.(eventPadding1);
     eventPadding2 := old.(eventPadding2);
     eventPadding3 := old.(eventPadding3);
     eventPadding19 := old.(eventPadding19);
                     eventType := old.(eventType);
                     mutexFields :=
                       Some
                         {| mfPCP := m.(mfPCP);
                            mfOwner := None;
                            mfOwnerOrigPrio := None |};
                     semFields := old.(semFields);
                     mboxFields := old.(mboxFields);
                     queueFields := old.(queueFields);
                     waitList := old.(waitList) |}
              else bein other;
       eventLifecycle := belife;
       publishedQueueBytes := bequeue;
       unUsedEventStates := eid :: beun |} =
    {| inUsedEventStates := fun other =>
         if Z.eqb other eid then None else bein other;
       eventLifecycle := belife;
       publishedQueueBytes := bequeue;
       unUsedEventStates := eid :: beun |}).
  { f_equal. exact Hevent. }
  rewrite Htask_record, Hevent_record. reflexivity.
Qed.
Lemma mutex_del_free_commit_after_prepare_eq__g04_no_pend_errors :
  forall sg eid old m before,
    mutex_del_free_commit_after__g04_no_pend_errors
      sg eid m.(mfPCP)
      (mutex_del_prepare_after__g04_no_pend_errors eid old m before) =
    mutex_del_free_commit_after__g04_no_pend_errors
      sg eid m.(mfPCP) before.
Proof.
  intros sg eid old m before.
  destruct before as [bi bt bs be bk bf bm btm bst bc bn].
  destruct be as [bein beun bequeue belife].
  unfold mutex_del_free_commit_after__g04_no_pend_errors,
    mutex_del_prepare_after__g04_no_pend_errors,
    mutex_del_free_task_after__g04_no_pend_errors,
    mutex_del_free_event_after__g04_no_pend_errors,
    owner_release_update, update_event_field_raw.
  cbn.
  assert (Hevent :
    (fun other =>
       if Z.eqb other eid then None
       else if Z.eqb other eid then
              Some
                {| eventGeneration := old.(eventGeneration);
                   eventName := old.(eventName);
     eventPadding1 := old.(eventPadding1);
     eventPadding2 := old.(eventPadding2);
     eventPadding3 := old.(eventPadding3);
     eventPadding19 := old.(eventPadding19);
                   eventType := old.(eventType);
                   mutexFields :=
                     Some
                       {| mfPCP := m.(mfPCP);
                          mfOwner := None;
                          mfOwnerOrigPrio := None |};
                   semFields := old.(semFields);
                   mboxFields := old.(mboxFields);
                   queueFields := old.(queueFields);
                   waitList := old.(waitList) |}
            else bein other) =
    (fun other => if Z.eqb other eid then None else bein other)).
  {
    apply functional_extensionality. intro other.
    destruct (Z.eqb other eid); reflexivity.
  }
  assert (Hevent_record :
    {| inUsedEventStates := fun other =>
         if Z.eqb other eid then None
         else if Z.eqb other eid then
                Some
                  {| eventGeneration := old.(eventGeneration);
                     eventName := old.(eventName);
     eventPadding1 := old.(eventPadding1);
     eventPadding2 := old.(eventPadding2);
     eventPadding3 := old.(eventPadding3);
     eventPadding19 := old.(eventPadding19);
                     eventType := old.(eventType);
                     mutexFields :=
                       Some
                         {| mfPCP := m.(mfPCP);
                            mfOwner := None;
                            mfOwnerOrigPrio := None |};
                     semFields := old.(semFields);
                     mboxFields := old.(mboxFields);
                     queueFields := old.(queueFields);
                     waitList := old.(waitList) |}
              else bein other;
       eventLifecycle := belife;
       publishedQueueBytes := bequeue;
       unUsedEventStates := eid :: beun |} =
    {| inUsedEventStates := fun other =>
         if Z.eqb other eid then None else bein other;
       eventLifecycle := belife;
       publishedQueueBytes := bequeue;
       unUsedEventStates := eid :: beun |}).
  { f_equal. exact Hevent. }
  rewrite Hevent_record. reflexivity.
Qed.
Lemma mutex_del_stable_release_atomic_free__g04_no_pend_errors :
  forall sg eid old m before,
    before.(EventState).(inUsedEventStates) eid = Some old ->
    old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    old.(waitList) = nil ->
    atomic_event_free_with_priotbl_free sg eid
      (mutex_del_stable_release_after__g04_no_pend_errors
         sg eid old m before) tt
      (mutex_del_free_commit_after__g04_no_pend_errors
         sg eid m.(mfPCP)
         (mutex_del_stable_release_after__g04_no_pend_errors
            sg eid old m before)).
Proof.
  intros sg eid old m before Hused Htype Hempty.
  unfold atomic_event_free_with_priotbl_free.
  exists
    {| eventGeneration := old.(eventGeneration);
       eventName := old.(eventName);
     eventPadding1 := old.(eventPadding1);
     eventPadding2 := old.(eventPadding2);
     eventPadding3 := old.(eventPadding3);
     eventPadding19 := old.(eventPadding19);
       eventType := old.(eventType);
       mutexFields :=
         Some
           {| mfPCP := m.(mfPCP);
              mfOwner := None;
              mfOwnerOrigPrio := None |};
       semFields := old.(semFields);
       mboxFields := old.(mboxFields);
       queueFields := old.(queueFields);
       waitList := old.(waitList) |}.
  exists
    {| mfPCP := m.(mfPCP);
       mfOwner := None;
       mfOwnerOrigPrio := None |}.
  exists
    (mutex_del_free_event_after__g04_no_pend_errors eid
       (mutex_del_stable_release_after__g04_no_pend_errors
          sg eid old m before).(EventState)).
  exists
    (mutex_del_free_task_after__g04_no_pend_errors sg m.(mfPCP)
       (mutex_del_stable_release_after__g04_no_pend_errors
          sg eid old m before).(TskState)).
  split.
  - unfold mutex_del_stable_release_after__g04_no_pend_errors.
    cbn. unfold owner_release_update, update_event_field_raw. cbn.
    rewrite Z.eqb_refl. reflexivity.
  - split; [cbn; exact Htype|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [cbn; exact Hempty|].
    split; [reflexivity|].
    split; [reflexivity|].
    reflexivity.
Qed.
Lemma mutex_del_direct_atomic_free__g04_no_pend_errors :
  forall sg eid old m before,
    before.(EventState).(inUsedEventStates) eid = Some old ->
    old.(eventType) = OS_EVENT_TYPE_MUTEX ->
    old.(mutexFields) = Some m ->
    m.(mfOwner) = None ->
    old.(waitList) = nil ->
    atomic_event_free_with_priotbl_free sg eid before tt
      (mutex_del_free_commit_after__g04_no_pend_errors
         sg eid m.(mfPCP) before).
Proof.
  intros sg eid old m before Hused Htype Hfields Howner Hempty.
  unfold atomic_event_free_with_priotbl_free.
  exists old, m,
    (mutex_del_free_event_after__g04_no_pend_errors
       eid before.(EventState)),
    (mutex_del_free_task_after__g04_no_pend_errors
       sg m.(mfPCP) before.(TskState)).
  repeat split; try assumption; reflexivity.
Qed.
Lemma mutex_del_owner_stage_commit_validity__g04_no_pend_errors :
  forall sg initial entry before eid current m,
    initial.(eventType) = OS_EVENT_TYPE_MUTEX ->
    initial.(mutexFields) = Some m ->
    before.(EventState).(inUsedEventStates) eid = Some current ->
    current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some m ->
    mutex_del_owner_entry_consistency_prop sg initial entry ->
    mutex_del_rdyatprio_stage_prop sg initial entry before ->
    current.(waitList) = nil ->
    no_live_task_at_priority before.(TskState) m.(mfPCP) ->
    UCOS2_verification_slice_state_inv sg before ->
    UCOS2_verification_slice_state_inv sg
      (mutex_del_free_commit_after__g04_no_pend_errors
         sg eid m.(mfPCP) before).
Proof.
  intros sg initial entry before eid current m Hinitial_type
    Hinitial_fields Hlookup Htype Hfields Hentry_owner Hstage Hempty
    Hno_live Hvalid.
  pose proof
    (mutex_del_owner_stage_restores_owner_original__g04_no_pend_errors
       sg initial entry before m Hinitial_type Hinitial_fields
       Hentry_owner Hstage) as Hrestored.
  destruct m.(mfOwner) as [owner_tid|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hrestored; try contradiction.
  - destruct Hrestored as (owner_t & Htask & Howner_prio).
    pose proof
      (mutex_del_stable_release_validity__g04_no_pend_errors
         sg before eid current m owner_tid owner_t orig
         Hlookup Htype Hfields Howner Htask Horig Howner_prio Hempty
         Hno_live Hvalid) as Hrelease_valid.
    pose proof
      (mutex_del_stable_release_atomic_free__g04_no_pend_errors
         sg eid current m before Hlookup Htype Hempty) as Hfree.
    pose proof
      (atomic_event_free_with_priotbl_free_preserves_validity__g04_no_pend_errors
         sg eid
         (mutex_del_stable_release_after__g04_no_pend_errors
            sg eid current m before)
         (mutex_del_free_commit_after__g04_no_pend_errors
            sg eid m.(mfPCP)
            (mutex_del_stable_release_after__g04_no_pend_errors
               sg eid current m before))
         Hrelease_valid Hfree) as Hcommit.
    rewrite
      mutex_del_free_commit_after_stable_release_eq__g04_no_pend_errors
      in Hcommit.
    exact Hcommit.
  - eapply
      atomic_event_free_with_priotbl_free_preserves_validity__g04_no_pend_errors.
    + exact Hvalid.
    + eapply mutex_del_direct_atomic_free__g04_no_pend_errors; eauto.
Qed.
Lemma mutex_del_owner_stage_no_live_total__g04_no_pend_errors :
  forall sg initial entry before eid current m,
    before.(EventState).(inUsedEventStates) eid = Some current ->
    current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some m ->
    initial.(eventType) = OS_EVENT_TYPE_MUTEX ->
    initial.(mutexFields) = Some m ->
    mutex_del_owner_entry_consistency_prop sg initial entry ->
    mutex_del_rdyatprio_stage_prop sg initial entry before ->
    UCOS2_verification_slice_state_inv sg before ->
    no_live_task_at_priority before.(TskState) m.(mfPCP).
Proof.
  intros sg initial entry before eid current m Hlookup Hcurrent_type
    Hcurrent_fields Hinitial_type Hinitial_fields Hentry_owner Hstage
    Hvalid.
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - apply Z.eqb_eq in Hdisabled.
    unfold UCOS2_verification_slice_state_inv in Hvalid.
    destruct Hvalid as [Htask [_ [_ Hcross]]].
    pose proof
      (task_vaild_cond_current_prio_registered
         sg before.(TskState) Htask) as Hregistered.
    unfold verification_slice_cross_module_consistency in Hcross.
    destruct Hcross as (_ & _ & _ & _ & _ & _ & Hceiling & _).
    eapply task_current_prio_registered_free_slot_is_unused.
    + exact Hregistered.
    + rewrite Hdisabled. exact Hceiling.
  - apply Z.eqb_neq in Hdisabled.
    unfold UCOS2_verification_slice_state_inv in Hvalid.
    destruct Hvalid as [Htask [_ [_ Hcross]]].
    eapply mutex_del_owner_stage_no_live_at_pcp__g04_no_pend_errors;
      eauto.
Qed.
Lemma mutex_del_prepare_and_free_stage__g04_no_pend_errors :
  forall sg before eid current m,
    before.(EventState).(inUsedEventStates) eid = Some current ->
    current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some m ->
    current.(waitList) = nil ->
    exists prepare,
      mutex_del_no_pend_prepare_stage_prop eid before prepare /\
      mutex_del_free_stage_prop sg eid prepare
        (mutex_del_free_commit_after__g04_no_pend_errors
           sg eid m.(mfPCP) before).
Proof.
  intros sg before eid current m Hlookup Htype Hfields Hempty.
  exists
    (mutex_del_prepare_after__g04_no_pend_errors
       eid current m before).
  split.
  - unfold mutex_del_no_pend_prepare_stage_prop,
      mutex_del_no_pend_prepare.
    exists current, m,
      (owner_release_update before.(EventState) eid current m.(mfPCP)).
    split; [exact Hlookup|].
    split; [exact Htype|].
    split; [exact Hfields|].
    split; [exact Hempty|].
    split.
    + unfold owner_release_update. rewrite Hempty. reflexivity.
    + reflexivity.
  - unfold mutex_del_free_stage_prop.
    assert (Hcleared :
      (mutex_del_prepare_after__g04_no_pend_errors
         eid current m before).(EventState).(inUsedEventStates) eid =
      Some
        {| eventGeneration := current.(eventGeneration);
           eventName := current.(eventName);
     eventPadding1 := current.(eventPadding1);
     eventPadding2 := current.(eventPadding2);
     eventPadding3 := current.(eventPadding3);
     eventPadding19 := current.(eventPadding19);
           eventType := current.(eventType);
           mutexFields :=
             Some
               {| mfPCP := m.(mfPCP);
                  mfOwner := None;
                  mfOwnerOrigPrio := None |};
           semFields := current.(semFields);
           mboxFields := current.(mboxFields);
           queueFields := current.(queueFields);
           waitList := current.(waitList) |}).
    {
      unfold mutex_del_prepare_after__g04_no_pend_errors,
        owner_release_update, update_event_field_raw.
      cbn. rewrite Z.eqb_refl. reflexivity.
    }
    pose proof
      (mutex_del_direct_atomic_free__g04_no_pend_errors
         sg eid
         {| eventGeneration := current.(eventGeneration);
            eventName := current.(eventName);
     eventPadding1 := current.(eventPadding1);
     eventPadding2 := current.(eventPadding2);
     eventPadding3 := current.(eventPadding3);
     eventPadding19 := current.(eventPadding19);
            eventType := current.(eventType);
            mutexFields :=
              Some
                {| mfPCP := m.(mfPCP);
                   mfOwner := None;
                   mfOwnerOrigPrio := None |};
            semFields := current.(semFields);
            mboxFields := current.(mboxFields);
            queueFields := current.(queueFields);
            waitList := current.(waitList) |}
         {| mfPCP := m.(mfPCP);
            mfOwner := None;
            mfOwnerOrigPrio := None |}
         (mutex_del_prepare_after__g04_no_pend_errors
            eid current m before)
         Hcleared Htype eq_refl eq_refl Hempty) as Hfree.
    cbn in Hfree.
    rewrite mutex_del_free_commit_after_prepare_eq__g04_no_pend_errors
      in Hfree.
    exact Hfree.
Qed.
Lemma mutex_del_used_event_missing_stable_to_raw__g04_no_pend_errors :
  forall sg tskSt evSt eid,
    verification_slice_task_validity sg tskSt ->
    verification_slice_event_in_range sg tskSt evSt ->
    store_used_event_map_missing_i
      sg tskSt evSt.(inUsedEventStates) eid |--
    store_used_event_map_raw_missing_i
      sg tskSt evSt.(inUsedEventStates) eid.
Proof.
  intros sg tskSt evSt eid Htask Hevent.
  unfold store_used_event_map_missing_i,
    store_used_event_map_raw_missing_i, store_map_missing_i.
  Intros l. pureIntros. Exists l.
  assert (Hmap :
    map
      (fun eid0 =>
         match evSt.(inUsedEventStates) eid0 with
         | Some e0 =>
             used_complete_event
               sg tskSt (event_addr sg eid0) eid0 e0
         | None => emp
         end) l =
    map
      (fun eid0 =>
         match evSt.(inUsedEventStates) eid0 with
         | Some e0 =>
             used_complete_event_raw
               sg tskSt (event_addr sg eid0) eid0 e0
         | None => emp
         end) l).
  {
    apply map_ext_in.
    intros eid0 Hin.
    destruct (evSt.(inUsedEventStates) eid0) as [e0|] eqn:Hlookup;
      [|reflexivity].
    apply used_complete_event_stable_eq_raw.
    - unfold verification_slice_event_in_range, verification_slice_event_in_range,
        verification_slice_event_in_range in Hevent.
      destruct Hevent as (_ & _ & _ & _ & _ & _ & _ & Hentry).
      exact (proj1 (Hentry eid0 e0 Hlookup)).
    - unfold verification_slice_task_validity, verification_slice_task_in_range,
        verification_slice_task_in_range in Htask.
      destruct Htask as [Htask _].
      destruct Htask as (_ & _ & _ & _ & _ & _ & Hunique).
      exact Hunique.
  }
  rewrite <- Hmap.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + apply derivable1s_coq_prop_r. exact H.
    + apply derivable1s_coq_prop_r. exact H0.
Qed.
Lemma mutex_del_freed_event_storage_merge__g04_no_pend_errors :
  forall sg tskSt eid current_event base
         type_addr ptr_addr cnt_addr grp_addr tbl_addr free_head,
    base = event_addr sg eid ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    type_addr # UChar |-> 0 **
    ptr_addr # Ptr |-> free_head **
    cnt_addr # UShort |-> 0 **
    grp_addr # UChar |-> 0 **
    used_event_wait_table_storage tskSt base current_event |--
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    free_event_node_rest_no_type sg eid free_head.
Proof.
  intros sg tskSt eid current_event base
    type_addr ptr_addr cnt_addr grp_addr tbl_addr free_head
    Hbase Hcore Hwait.
  unfold event_core_fields_layout_prop in Hcore.
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hcore as [Htype [Hptr Hcnt]].
  destruct Hwait as [Hgrp Htbl].
  subst base; subst type_addr; subst ptr_addr; subst cnt_addr;
    subst grp_addr; subst tbl_addr.
  unfold used_event_wait_table_storage,
    free_event_node_rest_no_type.
  repeat rewrite Z.add_0_r.
  sep_apply_l_atomic
    (store_ushort_undef_store_ushort
      (event_addr sg eid + OSEventCnt_off) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventGrp_off) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off)
      (encode_event_wait_tbl_at current_event.(waitList) tskSt 0)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 1)
      (encode_event_wait_tbl_at current_event.(waitList) tskSt 1)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 2)
      (encode_event_wait_tbl_at current_event.(waitList) tskSt 2)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 3)
      (encode_event_wait_tbl_at current_event.(waitList) tskSt 3)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 4)
      (encode_event_wait_tbl_at current_event.(waitList) tskSt 4)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 5)
      (encode_event_wait_tbl_at current_event.(waitList) tskSt 5)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 6)
      (encode_event_wait_tbl_at current_event.(waitList) tskSt 6)).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 7)
      (encode_event_wait_tbl_at current_event.(waitList) tskSt 7)).
  cancel.
Qed.
Lemma mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors :
  forall wl tskSt1 tskSt2 y,
    (forall tid,
       In tid wl ->
       tskSt1.(inUsedTaskStates) tid =
       tskSt2.(inUsedTaskStates) tid) ->
    encode_event_wait_tbl_at_or wl tskSt1 y =
    encode_event_wait_tbl_at_or wl tskSt2 y.
Proof.
  induction wl as [|tid rest IH]; intros tskSt1 tskSt2 y Hext; simpl.
  - reflexivity.
  - rewrite (Hext tid ltac:(left; reflexivity)).
    rewrite (IH tskSt1 tskSt2 y ltac:(
      intros tid' Hin; apply Hext; right; exact Hin)).
    reflexivity.
Qed.
Lemma mutex_del_freed_event_raw_rep_merge__g04_no_pend_errors :
  forall sg current eid pcp,
    store_used_event_map_raw_missing_i
      sg current.(TskState) current.(EventState).(inUsedEventStates) eid **
    sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid **
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    free_event_node_rest_no_type sg eid
      (free_event_head sg current.(EventState).(unUsedEventStates)) **
    store_free_event_nodes sg current.(EventState).(unUsedEventStates) |--
    verification_slice_event_raw_rep sg
      (mutex_del_free_task_after__g04_no_pend_errors
         sg pcp current.(TskState))
      (mutex_del_free_event_after__g04_no_pend_errors
         eid current.(EventState)).
Proof.
  intros sg current eid pcp.
  unfold verification_slice_event_raw_rep, store_used_event_map_raw,
    store_used_event_map_raw_missing_i, store_free_event_list,
    free_event_node_rest_no_type.
  unfold mutex_del_free_event_after__g04_no_pend_errors.
  cbn.
  cbn [free_event_head store_free_event_nodes encode_event_type].
  assert (Hnone :
    (fun other : EventID =>
       if Z.eqb other eid then None
       else current.(EventState).(inUsedEventStates) other) eid = None).
  {
    destruct (Z.eqb eid eid) eqn:Heq.
    - reflexivity.
    - apply Z.eqb_neq in Heq. contradiction.
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
  assert (Hraw : forall eid0 e0,
    used_complete_event_raw
      sg current.(TskState) (event_addr sg eid0) eid0 e0 =
    used_complete_event_raw sg
      (mutex_del_free_task_after__g04_no_pend_errors
         sg pcp current.(TskState))
      (event_addr sg eid0) eid0 e0).
  {
    intros eid0 e0.
    unfold used_complete_event_raw.
    assert (Hpoint : forall tid,
      In tid e0.(waitList) ->
      current.(TskState).(inUsedTaskStates) tid =
      (mutex_del_free_task_after__g04_no_pend_errors
         sg pcp current.(TskState)).(inUsedTaskStates) tid).
    { intros tid Hin. reflexivity. }
    rewrite
      (mutex_del_encode_event_wait_grp_ext
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) Hpoint).
    rewrite
      (mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) 0 Hpoint).
    rewrite
      (mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) 1 Hpoint).
    rewrite
      (mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) 2 Hpoint).
    rewrite
      (mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) 3 Hpoint).
    rewrite
      (mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) 4 Hpoint).
    rewrite
      (mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) 5 Hpoint).
    rewrite
      (mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) 6 Hpoint).
    rewrite
      (mutex_del_encode_event_wait_tbl_at_or_ext__g04_no_pend_errors
        e0.(waitList) current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
          sg pcp current.(TskState)) 7 Hpoint).
    reflexivity.
  }
  assert (HP :
    (fun (eid0 : EventID) (e0 : OSEventAbstractState) =>
       used_complete_event_raw
         sg current.(TskState) (event_addr sg eid0) eid0 e0) =
    (fun (eid0 : EventID) (e0 : OSEventAbstractState) =>
       used_complete_event_raw sg
         (mutex_del_free_task_after__g04_no_pend_errors
            sg pcp current.(TskState))
         (event_addr sg eid0) eid0 e0)).
  {
    apply functional_extensionality. intro eid0.
    apply functional_extensionality. intro e0.
    apply Hraw.
  }
  rewrite <- HP.
  cancel.
Qed.
Lemma mutex_del_prioTbl_to_addrs_set_free__g04_no_pend_errors :
  forall sg f p,
    0 <= p < OS_PRIO_TBL_SIZE ->
    replace_Znth p 0 (verification_slice_prioTbl_to_addrs sg f) =
    verification_slice_prioTbl_to_addrs sg
      (fun q => if Z.eqb q p then PTFree else f q).
Proof.
  intros sg f p Hp.
  assert (Hseq : forall
    (f0 : Priority -> PrioTblEntry) n acc,
    verification_slice_prioTbl_to_addrs_rec sg f0 n acc =
      map (fun k => verification_slice_prio_tbl_entry_to_addr sg (f0 (Z.of_nat k)))
        (seq 0 n) ++ acc).
  {
    intros f0 n. induction n as [|n IH]; intro acc.
    - reflexivity.
    - simpl verification_slice_prioTbl_to_addrs_rec.
      rewrite IH, seq_S, map_app. simpl.
      rewrite <- app_assoc. reflexivity.
  }
  assert (Hrel : forall f0,
    Zlength (verification_slice_prioTbl_to_addrs sg f0) = OS_PRIO_TBL_SIZE /\
    forall q, 0 <= q < OS_PRIO_TBL_SIZE ->
      Znth q (verification_slice_prioTbl_to_addrs sg f0) 0 =
      verification_slice_prio_tbl_entry_to_addr sg (f0 q)).
  {
    intro f0. split.
    - unfold verification_slice_prioTbl_to_addrs, OS_PRIO_TBL_SIZE, Zlength.
      rewrite Hseq, app_nil_r. vm_compute. reflexivity.
    - intros q Hq.
      unfold verification_slice_prioTbl_to_addrs, OS_PRIO_TBL_SIZE in *.
      rewrite Hseq, app_nil_r.
      unfold Znth.
      assert (Hnat : (Z.to_nat q < 64)%nat) by lia.
      assert (Hdefault :
        nth (Z.to_nat q)
          (map
            (fun k : nat => verification_slice_prio_tbl_entry_to_addr sg (f0 (Z.of_nat k)))
            (seq 0 64)) 0 =
        nth (Z.to_nat q)
          (map
            (fun k : nat => verification_slice_prio_tbl_entry_to_addr sg (f0 (Z.of_nat k)))
            (seq 0 64))
          (verification_slice_prio_tbl_entry_to_addr sg (f0 (Z.of_nat 0)))).
      {
        apply nth_indep. rewrite length_map, length_seq. exact Hnat.
      }
      rewrite Hdefault.
      change
        (nth (Z.to_nat q)
          (map
            (fun k : nat => verification_slice_prio_tbl_entry_to_addr sg (f0 (Z.of_nat k)))
            (seq 0 64))
          ((fun k : nat =>
              verification_slice_prio_tbl_entry_to_addr sg (f0 (Z.of_nat k))) 0%nat) =
         verification_slice_prio_tbl_entry_to_addr sg (f0 q)).
      rewrite map_nth, seq_nth by exact Hnat.
      simpl Nat.add. rewrite Z2Nat.id by lia. reflexivity.
  }
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - transitivity (Zlength (verification_slice_prioTbl_to_addrs sg f)).
    + apply Zlength_replace_Znth_gen. lia.
    + transitivity OS_PRIO_TBL_SIZE.
      * exact (proj1 (Hrel f)).
      * symmetry. exact (proj1 (Hrel
          (fun q => if Z.eqb q p then PTFree else f q))).
  - intros q Hq.
    assert (Hq' : 0 <= q < OS_PRIO_TBL_SIZE).
    {
      rewrite Zlength_replace_Znth_gen in Hq by lia.
      pose proof (proj1 (Hrel f)) as Hlen.
      split; [exact (proj1 Hq)|].
      rewrite <- Hlen. exact (proj2 Hq).
    }
    assert (Hpbase :
      0 <= p < Zlength (verification_slice_prioTbl_to_addrs sg f)).
    {
      pose proof (proj1 (Hrel f)) as Hlen.
      split; [exact (proj1 Hp)|].
      rewrite Hlen. exact (proj2 Hp).
    }
    assert (Hqbase :
      0 <= q < Zlength (verification_slice_prioTbl_to_addrs sg f)).
    {
      pose proof (proj1 (Hrel f)) as Hlen.
      split; [exact (proj1 Hq')|].
      rewrite Hlen. exact (proj2 Hq').
    }
    destruct (Z.eq_dec q p) as [Heq|Hneq].
    + subst q.
      rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_eq_gen by
        exact Hpbase.
      symmetry.
      transitivity (verification_slice_prio_tbl_entry_to_addr sg
        ((fun q => if Z.eqb q p then PTFree else f q) p)).
      * exact (proj2 (Hrel
          (fun q => if Z.eqb q p then PTFree else f q)) p Hp).
      * rewrite Z.eqb_refl. reflexivity.
    + rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_neq_gen.
      2: exact Hneq.
      2: exact Hqbase.
      2: exact Hpbase.
      transitivity (verification_slice_prio_tbl_entry_to_addr sg (f q)).
      * exact (proj2 (Hrel f) q Hq').
      * symmetry.
        transitivity (verification_slice_prio_tbl_entry_to_addr sg
          ((fun q0 => if Z.eqb q0 p then PTFree else f q0) q)).
        -- exact (proj2 (Hrel
             (fun q0 => if Z.eqb q0 p then PTFree else f q0)) q Hq').
        -- rewrite (proj2 (Z.eqb_neq q p) Hneq). reflexivity.
Qed.
Lemma mutex_del_store_prio_tbl_missing_free_merge__g04_no_pend_errors :
  forall sg f p,
    priotbl_index_in_range p ->
    priotbl_element_store sg.(g_OSTCBPrioTbl) p 0 **
    verification_slice_store_prio_tbl_missing_i sg f p |--
    verification_slice_store_prio_tbl sg
      (fun q => if Z.eqb q p then PTFree else f q).
Proof.
  intros sg f p Hp.
  unfold verification_slice_store_prio_tbl_missing_i, verification_slice_store_prio_tbl.
  rewrite <-
    (mutex_del_prioTbl_to_addrs_set_free__g04_no_pend_errors
       sg f p Hp).
  apply verification_slice_store_priotbl_list_merge.
  - exact Hp.
  - exact (mutex_del_prioTbl_to_addrs_Zlength sg f).
Qed.
Lemma mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors :
  forall rl t1 t2 y,
    inUsedTaskStates t1 = inUsedTaskStates t2 ->
    encode_ready_tbl_at_or rl t1 y =
    encode_ready_tbl_at_or rl t2 y.
Proof.
  induction rl as [|tid rest IH]; intros t1 t2 y Hmap.
  - reflexivity.
  - simpl. rewrite Hmap. rewrite (IH t1 t2 y Hmap). reflexivity.
Qed.
Lemma mutex_del_pcp_release_freed_raw_ready_fold__g04_no_pend_errors :
  forall sg anchor current eid pcp current_event
         base type_addr ptr_addr cnt_addr grp_addr tbl_addr free_head,
    UCOS2_verification_slice_state_inv sg current ->
    (Z.eqb pcp sg.(osPrioMutexCeilDis) = false ->
       priotbl_index_in_range pcp) ->
    base = event_addr sg eid ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    free_head = free_event_head sg current.(EventState).(unUsedEventStates) ->
    mutex_del_pcp_release_focus sg anchor current eid pcp **
    type_addr # UChar |-> 0 **
    ptr_addr # Ptr |-> free_head **
    used_event_wait_table_storage
      current.(TskState) base current_event **
    cnt_addr # UShort |-> 0 **
    grp_addr # UChar |-> 0 **
    sg.(g_OSEventFreeList) # Ptr |-> base
    |--
    UCOS2_verification_slice_raw_ready_prio_stage sg anchor
      (mutex_del_free_commit_after__g04_no_pend_errors
         sg eid pcp current).
Proof.
  intros sg anchor current eid pcp current_event
    base type_addr ptr_addr cnt_addr grp_addr tbl_addr free_head
    Hvalid Hrange Hbase Hcore Hwait Hfree.
  destruct Hvalid as [Htask [Hsched [Hevent Hcross]]].
  subst base; subst free_head.
  sep_apply_l_atomic
    (mutex_del_freed_event_storage_merge__g04_no_pend_errors
       sg current.(TskState) eid current_event (event_addr sg eid)
       type_addr ptr_addr cnt_addr grp_addr tbl_addr
       (free_event_head sg current.(EventState).(unUsedEventStates))
       eq_refl Hcore Hwait).
  unfold mutex_del_pcp_release_focus.
  destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdis.
  - unfold mutex_del_event_ready_focus_inv,
      mutex_del_event_inv_no_eid_no_free_head, verification_slice_task_inv.
    pureIntros.
    sep_apply_l_atomic
      (mutex_del_used_event_missing_stable_to_raw__g04_no_pend_errors
         sg current.(TskState) current.(EventState) eid
         Htask Hevent).
    sep_apply_l_atomic
      (mutex_del_freed_event_raw_rep_merge__g04_no_pend_errors
         sg current eid pcp).
    assert (Htask_after :
      mutex_del_free_task_after__g04_no_pend_errors
        sg pcp current.(TskState) = current.(TskState)).
    { unfold mutex_del_free_task_after__g04_no_pend_errors.
      rewrite Hdis. cbn.
      destruct (current.(TskState)) as
        [used unused head table count life] eqn:Hcurrent_task.
      cbn. f_equal. }
    unfold mutex_del_free_commit_after__g04_no_pend_errors.
    cbn.
    rewrite Htask_after.
    cbn.
    unfold UCOS2_verification_slice_raw_ready_prio_stage, verification_slice_task_raw_rep, verification_slice_store_prio_tbl.
    cbn.
    sepcon_assoc_change.
    cancel.
  - specialize (Hrange eq_refl).
    assert (Hmap :
      inUsedTaskStates current.(TskState) =
      inUsedTaskStates
        (mutex_del_free_task_after__g04_no_pend_errors
           sg pcp current.(TskState))).
    { reflexivity. }
    assert (Hsched_stage_eq :
      verification_slice_sched_raw_ready_prio_stage
        sg anchor.(SchedState) current.(SchedState) current.(TskState) =
      verification_slice_sched_raw_ready_prio_stage
        sg anchor.(SchedState) current.(SchedState)
          (mutex_del_free_task_after__g04_no_pend_errors
             sg pcp current.(TskState))).
    {
      unfold verification_slice_sched_raw_ready_prio_stage.
      rewrite (encode_ready_grp_ext
        current.(SchedState).(readyList)
        current.(TskState)
        (mutex_del_free_task_after__g04_no_pend_errors
           sg pcp current.(TskState)) Hmap).
      rewrite
        (mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors
           current.(SchedState).(readyList) current.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg pcp current.(TskState)) 0 Hmap),
        (mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors
           current.(SchedState).(readyList) current.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg pcp current.(TskState)) 1 Hmap),
        (mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors
           current.(SchedState).(readyList) current.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg pcp current.(TskState)) 2 Hmap),
        (mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors
           current.(SchedState).(readyList) current.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg pcp current.(TskState)) 3 Hmap),
        (mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors
           current.(SchedState).(readyList) current.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg pcp current.(TskState)) 4 Hmap),
        (mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors
           current.(SchedState).(readyList) current.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg pcp current.(TskState)) 5 Hmap),
        (mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors
           current.(SchedState).(readyList) current.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg pcp current.(TskState)) 6 Hmap),
        (mutex_del_encode_ready_tbl_at_or_task_ext__g04_no_pend_errors
           current.(SchedState).(readyList) current.(TskState)
           (mutex_del_free_task_after__g04_no_pend_errors
              sg pcp current.(TskState)) 7 Hmap).
      reflexivity.
    }
    unfold mutex_del_event_missing_priotbl_focus,
      mutex_del_event_inv_no_eid_no_free_head,
      verification_slice_task_inv_missing_priotbl.
    pureIntros.
    sep_apply_l_atomic
      (mutex_del_used_event_missing_stable_to_raw__g04_no_pend_errors
         sg current.(TskState) current.(EventState) eid
         Htask Hevent).
    sep_apply_l_atomic
      (mutex_del_store_prio_tbl_missing_free_merge__g04_no_pend_errors
         sg current.(TskState).(prioTbl) pcp Hrange).
    sep_apply_l_atomic
      (mutex_del_freed_event_raw_rep_merge__g04_no_pend_errors
         sg current eid pcp).
    rewrite Hsched_stage_eq.
    unfold mutex_del_free_commit_after__g04_no_pend_errors.
    cbn.
    unfold UCOS2_verification_slice_raw_ready_prio_stage, verification_slice_task_raw_rep, verification_slice_store_prio_tbl,
      mutex_del_free_task_after__g04_no_pend_errors.
    rewrite Hdis. cbn.
    sepcon_assoc_change.
    cancel.
Qed.
Lemma mutex_del_pcp_release_focus_validity__g04_no_pend_errors :
  forall sg anchor post eid pcp,
    mutex_del_pcp_release_focus sg anchor post eid pcp |--
    coq_prop (UCOS2_verification_slice_state_inv sg post).
Proof.
  intros sg anchor post eid pcp.
  unfold mutex_del_pcp_release_focus.
  destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)).
  - unfold mutex_del_event_ready_focus_inv, verification_slice_task_inv,
      mutex_del_event_inv_no_eid_no_free_head.
    pureIntros.
    apply derivable1s_coq_prop_r.
    unfold UCOS2_verification_slice_state_inv.
    exact (conj H0 (conj (proj1 H1) (conj H (proj2 H1)))).
  - unfold mutex_del_event_missing_priotbl_focus,
      verification_slice_task_inv_missing_priotbl,
      mutex_del_event_inv_no_eid_no_free_head.
    pureIntros.
    apply derivable1s_coq_prop_r.
    unfold UCOS2_verification_slice_state_inv.
    exact (conj H0 (conj (proj1 H1) (conj H (proj2 H1)))).
Qed.
Lemma UCOS2_verification_slice_inv_expose_validity__g05_always_loop :
  forall sg s,
    UCOS2_verification_slice_inv sg s |--
      coq_prop (UCOS2_verification_slice_state_inv sg s) &&
      UCOS2_verification_slice_inv sg s.
Proof.
  intros sg s.
  apply _derivable1_andp_intros.
  - unfold UCOS2_verification_slice_inv, UCOS2_verification_slice_state_inv,
      verification_slice_task_inv, verification_slice_sched_inv, verification_slice_event_inv.
    pureIntros.
    apply derivable1s_coq_prop_r.
    exact (conj H1 (conj H0 (conj H H2))).
  - unfold UCOS2_verification_slice_inv.
    cancel.
Qed.
Lemma mutex_del_event_owner_open_merge_pure__g05_always_loop :
  forall sg ls eid e owner_ptr owner_tid owner_t owner_prio prio_addr,
    owner_ptr <> 0 ->
    mutex_del_owner_snapshot_prop
      sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr ->
    prio_addr # UChar |-> owner_prio **
    mutex_del_event_owner_open_inv sg ls eid owner_tid owner_t |--
      mutex_del_event_focus_inv sg ls eid ** TT.
Proof.
  intros sg ls eid e owner_ptr owner_tid owner_t owner_prio prio_addr
    Hnonnull Hsnapshot.
  pose proof
    (mutex_del_owner_snapshot_nonnull_components
       sg ls e owner_ptr owner_tid owner_t owner_prio prio_addr
       Hnonnull Hsnapshot) as [Hprio_snapshot Hlayout].
  unfold mutex_del_event_owner_open_inv,
    mutex_del_event_focus_inv.
  sep_apply_l_atomic
    (mutex_del_task_open_merge
       sg ls.(TskState) owner_tid owner_t
       owner_ptr owner_prio prio_addr Hprio_snapshot Hlayout).
  cancel.
  andp_cancel.
  apply derivable1_truep_intros.
Qed.
Lemma mutex_del_event_focus_to_ready_focus__g05_always_loop :
  forall sg ls eid,
    mutex_del_event_focus_inv sg ls eid |--
      mutex_del_event_ready_focus_inv sg ls ls eid.
Proof.
  intros sg ls eid.
  unfold mutex_del_event_focus_inv,
    mutex_del_event_ready_focus_inv,
    verification_slice_task_inv, verification_slice_sched_inv.
  pureIntros.
  assert (Heq : forall y,
    encode_ready_tbl_at ls.(SchedState).(readyList) ls.(TskState) y =
    encode_ready_tbl_at_or ls.(SchedState).(readyList) ls.(TskState) y).
  {
    intro y.
    eapply sched_stable_tbl_eq_or; eassumption.
  }
  unfold verification_slice_store_sched_state, verification_slice_sched_raw_ready_prio_stage.
  rewrite <- (Heq 0), <- (Heq 1), <- (Heq 2), <- (Heq 3),
    <- (Heq 4), <- (Heq 5), <- (Heq 6), <- (Heq 7).
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. eassumption.
  - apply _derivable1_andp_intros.
    + apply derivable1s_coq_prop_r. split; eassumption.
    + cancel.
Qed.
Lemma mutex_del_owner_stage_preserves_event_core__g05_always_loop :
  forall sg initial entry owner_post eid,
    entry.(EventState).(inUsedEventStates) eid = Some initial ->
    mutex_del_rdyatprio_stage_prop sg initial entry owner_post ->
    exists current,
      owner_post.(EventState).(inUsedEventStates) eid = Some current /\
      current.(eventType) = initial.(eventType) /\
      current.(mutexFields) = initial.(mutexFields).
Proof.
  intros sg initial entry owner_post eid Hlookup Hstage.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as (m & Htype & Hfields & Hshape & Hexec).
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - subst owner_post. exists initial. auto.
  - destruct m.(mfOwner) as [owner_tid|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [owner_orig|] eqn:Horig;
      simpl in Hexec.
    + destruct Hexec as (owner_t & Howner_lookup & Hexec).
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Hprio.
      * unfold atomic_task_set_curPrio in Hexec.
        destruct Hexec as [Hready | [Hwaiting | Hdormant]].
        -- unfold atomic_task_set_curPrio_ready in Hready.
           destruct Hready as
             (t & oldPrio & t' & _ & _ & _ & _ & _ & _ & _ & _ & Hpost).
           cbv zeta in Hpost. subst owner_post.
           exists initial. simpl. auto.
        -- unfold atomic_task_set_curPrio_waiting in Hwaiting.
           destruct Hwaiting as
             (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
              evSt2 & pty & Hnot_ready & Htask & Hold & Hne & Hlo & Hhi &
              Hpt & Hpend & Hevent & Hmulti & Hget & Hwaittype & Hin & Ht' &
              Htsk & Hwait' & Hev & Hpost).
           subst owner_post evSt2.
           unfold update_event_field_raw; simpl.
           destruct (Z.eqb eid wait_eid) eqn:Heq.
           ++ apply Z.eqb_eq in Heq. subst wait_eid.
              rewrite Hlookup in Hget. inversion Hget; subst wait_e.
              exists wait_e'.
              simpl in Hwait'. subst wait_e'.
              simpl. auto.
           ++ exists initial. auto.
        -- unfold atomic_task_set_curPrio_dormant in Hdormant.
           destruct Hdormant as
             (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask & Hold & Hne &
              Hlo & Hhi & Hpt & Hevent & Hmulti & Hnot_effective & Ht' &
              Htsk & Hpost).
           subst owner_post. exists initial. simpl. auto.
      * subst owner_post. exists initial. auto.
    + contradiction.
    + contradiction.
    + subst owner_post. exists initial. auto.
Qed.
Lemma mutex_del_wake_step_preserves_event_core__g05_always_loop :
  forall sg eid pre post initial,
    pre.(EventState).(inUsedEventStates) eid = Some initial ->
    mutex_del_wake_step sg eid pre post ->
    exists current,
      post.(EventState).(inUsedEventStates) eid = Some current /\
      current.(eventType) = initial.(eventType) /\
      current.(mutexFields) = initial.(mutexFields).
Proof.
  intros sg eid pre post initial Hlookup Hstep.
  unfold mutex_del_wake_step in Hstep.
  destruct Hstep as
    (returned_prio & canonical_waiter & table_owner & _ & Hatomic).
  unfold atomic_event_task_rdy, atomic_event_task_rdy_one in Hatomic.
  destruct Hatomic as
    (e1 & e2 & canonical_t & table_t & table_t' &
     Hevent & Hpend & Hnonempty & Hcanonical &
     Hcanonical_get & Hreturned & Htable_slot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hpost).
  rewrite Hlookup in Hevent. inversion Hevent; subst e1.
  cbv zeta in Hpost. subst post.
  exists e2.
  unfold update_event_field_raw; simpl.
  rewrite Z.eqb_refl.
  subst e2. simpl. auto.
Qed.
Lemma mutex_del_wake_steps_preserve_event_core__g05_always_loop :
  forall sg eid pre post initial,
    pre.(EventState).(inUsedEventStates) eid = Some initial ->
    mutex_del_wake_steps sg eid pre post ->
    exists current,
      post.(EventState).(inUsedEventStates) eid = Some current /\
      current.(eventType) = initial.(eventType) /\
      current.(mutexFields) = initial.(mutexFields).
Proof.
  intros sg eid pre post initial Hlookup Hsteps.
  revert initial Hlookup.
  induction Hsteps as [s | s0 s1 s2 Hprefix IH Hlast];
    intros initial Hlookup.
  - exists initial. auto.
  - destruct (IH initial Hlookup) as
      (middle & Hmiddle & Hmiddle_type & Hmiddle_fields).
    destruct
      (mutex_del_wake_step_preserves_event_core__g05_always_loop
         sg eid s1 s2 middle Hmiddle Hlast) as
      (current & Hcurrent & Hcurrent_type & Hcurrent_fields).
    exists current. repeat split; try assumption; congruence.
Qed.
Lemma mutex_del_success_exit_pack__g05_always_loop :
  forall sg e entry eid opt pevent tasks_waiting X
         critical_anchor commit exited,
    mutex_del_success_commit_anchor_prop
      sg e entry eid opt critical_anchor commit ->
    mutex_del_source_entry_prop
      sg e entry eid pevent tasks_waiting ->
    mutex_del_success_mode_prop opt tasks_waiting ->
    mutex_del_exit_critical_anchored_call_prop
      sg critical_anchor commit exited ->
    valid_stable_glob_vars sg ->
    safeExec
      (LastSeen entry)
      (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
            (mutex_del_observe_ptr pevent)) X ->
    Ucos2Verify.lib.ucos2_rules_lib.OutsideCritical sg exited **
    UCOS2_verification_slice_inv sg exited |--
      mutex_del_success_exit_inv
        sg e entry eid opt pevent tasks_waiting X.
Proof.
  intros sg e entry eid opt pevent tasks_waiting X
    critical_anchor commit exited
    Hcommit Hsource Hmode Hexit Hvalid Hsafe.
  unfold mutex_del_success_exit_inv.
  Exists critical_anchor commit exited.
  unfold UCOS2_verification_slice_inv, UCOS2_verification_slice_state_inv,
    verification_slice_task_inv, verification_slice_sched_inv, verification_slice_event_inv.
  pureIntros.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r. exact H.
  - apply _derivable1_andp_intros.
    + apply derivable1s_coq_prop_r. exact H0.
    + apply _derivable1_andp_intros.
      * apply derivable1s_coq_prop_r. exact H1.
      * apply _derivable1_andp_intros.
        -- apply derivable1s_coq_prop_r. exact H2.
        -- apply _derivable1_andp_intros.
           ++ apply derivable1s_coq_prop_r.
              exact
                (conj Hcommit
                   (conj Hsource
                      (conj Hmode
                         (conj Hexit
                            (conj
                               (conj H1 (conj H0 (conj H H2)))
                               (conj Hvalid Hsafe)))))).
           ++ sepcon_assoc_change.
              unfold derivable1, truep, sepcon.
              intros h Hspatial.
              destruct Hspatial as
                (m1 & m2 & Hjoin1 & Houtside &
                 m3 & m4 & Hjoin2 & Hinterrupt &
                 m5 & m6 & Hjoin3 & Hused_tasks &
                 m7 & m8 & Hjoin4 & Hfree_tasks &
                 m9 & m10 & Hjoin5 & Hprio_tbl &
                 m11 & m12 & Hjoin6 & Htcb_list &
                 m13 & m14 & Hjoin7 & Htask_ctr &
                 m15 & m16 & Hjoin8 & Hsched &
                 m17 & m18 & Hjoin9 & Hused_events &
                 m19 & m20 & Hjoin10 & Hfree_events &
                 m21 & m22 & Hjoin11 & Htick & _).
              exists m1, m2.
              split; [exact Hjoin1 |].
              split; [exact Houtside |].
              exists m3, m4.
              split; [exact Hjoin2 |].
              split; [exact Hinterrupt |].
              exists m5, m6.
              split; [exact Hjoin3 |].
              split; [exact Hused_tasks |].
              exists m7, m8.
              split; [exact Hjoin4 |].
              split; [exact Hfree_tasks |].
              exists m9, m10.
              split; [exact Hjoin5 |].
              split; [exact Hprio_tbl |].
              exists m11, m12.
              split; [exact Hjoin6 |].
              split; [exact Htcb_list |].
              exists m13, m14.
              split; [exact Hjoin7 |].
              split; [exact Htask_ctr |].
              exists m15, m16.
              split; [exact Hjoin8 |].
              split; [exact Hsched |].
              exists m17, m18.
              split; [exact Hjoin9 |].
              split; [exact Hused_events |].
              exists m19, m20.
              split; [exact Hjoin10 |].
              split; [exact Hfree_events |].
              exists m21, m22.
              split; [exact Hjoin11 |].
              split; [exact Htick |].
              destruct (unit_join m22) as [u [Hunit Hjoin]].
              exists m22, u.
              split; [exact Hjoin |].
              split; exact I.
Qed.
Lemma mutex_del_prepare_event__g05_always_loop
  (e : OSEventAbstractState) (m : MutexFields) : OSEventAbstractState.
Proof.
  exact
    {| eventGeneration := e.(eventGeneration);
       eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
       eventType := e.(eventType);
       mutexFields := Some
         {| mfPCP := m.(mfPCP);
            mfOwner := None;
            mfOwnerOrigPrio := None |};
       semFields := e.(semFields);
       mboxFields := e.(mboxFields);
       queueFields := e.(queueFields);
       waitList := [] |}.
Defined.
Lemma mutex_del_prepare_state__g05_always_loop
  (eid : EventID) (e : OSEventAbstractState) (m : MutexFields)
  (before : UCOS2_Verify_State) : UCOS2_Verify_State.
Proof.
  exact
    (replace_EventS
       (update_event_field_raw before.(EventState) eid
          (mutex_del_prepare_event__g05_always_loop e m))
       before).
Defined.
Lemma mutex_del_free_task_after__g05_always_loop
  (sg : StableGlobVars) (pcp : Priority)
  (before : Glob_TaskAbstractState) : Glob_TaskAbstractState.
Proof.
  exact
    {| inUsedTaskStates := before.(inUsedTaskStates);
       unUsedTaskStates := before.(unUsedTaskStates);
       tcbListHead := before.(tcbListHead);
       prioTbl := fun p =>
         if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
             Z.eqb p pcp)%bool
         then PTFree
         else before.(prioTbl) p;
       taskRegNextID := before.(taskRegNextID);
       parkedTaskStacks := before.(parkedTaskStacks);
       taskLifecycle := before.(taskLifecycle);
     taskCount := before.(taskCount) |}.
Defined.
Lemma mutex_del_free_event_after__g05_always_loop
  (eid : EventID) (before : Glob_EventAbstractState)
  : Glob_EventAbstractState.
Proof.
  exact
    {| inUsedEventStates := fun other =>
         if Z.eqb other eid then None
         else before.(inUsedEventStates) other;
       eventLifecycle := before.(eventLifecycle);
       publishedQueueBytes := before.(publishedQueueBytes);
       unUsedEventStates := eid :: before.(unUsedEventStates) |}.
Defined.
Lemma mutex_del_free_state_after__g05_always_loop
  (sg : StableGlobVars) (eid : EventID) (pcp : Priority)
  (before : UCOS2_Verify_State) : UCOS2_Verify_State.
Proof.
  exact
    {| IntrState := before.(IntrState);
       TskState := mutex_del_free_task_after__g05_always_loop
         sg pcp before.(TskState);
       SchedState := before.(SchedState);
       EventState := mutex_del_free_event_after__g05_always_loop
         eid before.(EventState);
       TickState := before.(TickState);
       FlagState := before.(FlagState);
       MemoryState := before.(MemoryState);
       TimerState := before.(TimerState);
       StatsState := before.(StatsState);
       ControlState := before.(ControlState);
       NameState := before.(NameState) |}.
Defined.
Lemma mutex_del_prepare_free_relations__g05_always_loop :
  forall sg eid current e m,
    current.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    e.(waitList) = [] ->
    mutex_del_no_pend_prepare_stage_prop eid current
      (mutex_del_prepare_state__g05_always_loop eid e m current) /\
    mutex_del_free_stage_prop sg eid
      (mutex_del_prepare_state__g05_always_loop eid e m current)
      (mutex_del_free_state_after__g05_always_loop
         sg eid m.(mfPCP) current).
Proof.
  intros sg eid current e m Hused Htype Hfields Hempty.
  split.
  - unfold mutex_del_no_pend_prepare_stage_prop,
      mutex_del_no_pend_prepare,
      mutex_del_prepare_state__g05_always_loop.
    exists e, m,
      (update_event_field_raw current.(EventState) eid
        (mutex_del_prepare_event__g05_always_loop e m)).
    repeat split; try assumption; reflexivity.
  - unfold mutex_del_free_stage_prop,
      atomic_event_free_with_priotbl_free,
      mutex_del_prepare_state__g05_always_loop,
      mutex_del_free_state_after__g05_always_loop,
      mutex_del_free_task_after__g05_always_loop,
      mutex_del_free_event_after__g05_always_loop.
    exists (mutex_del_prepare_event__g05_always_loop e m),
      {| mfPCP := m.(mfPCP);
         mfOwner := None;
         mfOwnerOrigPrio := None |}.
    eexists. eexists.
    cbn.
    rewrite Z.eqb_refl.
    repeat split; try reflexivity; try assumption.
    f_equal.
    f_equal.
    apply functional_extensionality. intro other.
    destruct (Z.eqb other eid); reflexivity.
Qed.
Lemma mutex_del_event_missing_stable_to_raw__g05_always_loop :
  forall sg tskSt eventSt eid,
    verification_slice_task_validity sg tskSt ->
    verification_slice_event_in_range sg tskSt eventSt ->
    store_used_event_map_missing_i
      sg tskSt eventSt.(inUsedEventStates) eid |--
    store_used_event_map_raw_missing_i
      sg tskSt eventSt.(inUsedEventStates) eid.
Proof.
  intros sg tskSt eventSt eid Htask Hevent.
  unfold store_used_event_map_missing_i,
    store_used_event_map_raw_missing_i, store_map_missing_i.
  Intros l. Exists l.
  assert (Hmap :
    map
      (fun eid0 =>
         match eventSt.(inUsedEventStates) eid0 with
         | Some e =>
             used_complete_event sg tskSt
               (event_addr sg eid0) eid0 e
         | None => emp
         end) l =
    map
      (fun eid0 =>
         match eventSt.(inUsedEventStates) eid0 with
         | Some e =>
             used_complete_event_raw sg tskSt
               (event_addr sg eid0) eid0 e
         | None => emp
         end) l).
  {
    apply map_ext_in.
    intros eid0 Hin.
    destruct (eventSt.(inUsedEventStates) eid0) as [e|] eqn:Hlookup;
      [|reflexivity].
    apply used_complete_event_stable_eq_raw.
    - unfold verification_slice_event_in_range, verification_slice_event_in_range,
        verification_slice_event_in_range in Hevent.
      destruct Hevent as [_ [_ [_ [_ [_ [_ [_ Hentry]]]]]]].
      specialize (Hentry eid0 e Hlookup).
      unfold Ucos2Verify.lib.event_wait.verification_slice_event_wait_entry_consistency
        in Hentry.
      exact (proj1 Hentry).
    - unfold verification_slice_task_validity, verification_slice_task_in_range,
        verification_slice_task_in_range in Htask.
      destruct Htask as [Htask _].
      destruct Htask as [_ [_ [_ [_ [_ [_ Hunique]]]]]].
      exact Hunique.
  }
  rewrite <- Hmap.
  apply _derivable1_andp_intros.
  - apply _derivable1_andp_intros.
    + apply derivable1s_coq_prop_r. exact H.
    + apply derivable1s_coq_prop_r. exact H0.
  - unfold derivable1.
    intros h Hrep.
    exact Hrep.
Qed.
Lemma mutex_del_freed_event_cells_merge__g05_always_loop :
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
Lemma mutex_del_encode_event_wait_tbl_at_or_ext__g05_always_loop :
  forall wl tskSt1 tskSt2 y,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    encode_event_wait_tbl_at_or wl tskSt1 y =
      encode_event_wait_tbl_at_or wl tskSt2 y.
Proof.
  induction wl as [|tid rest IH]; intros tskSt1 tskSt2 y Hmap; simpl.
  - reflexivity.
  - rewrite Hmap. rewrite (IH tskSt1 tskSt2 y Hmap). reflexivity.
Qed.
Lemma mutex_del_used_complete_event_raw_task_ext__g05_always_loop :
  forall sg tskSt1 tskSt2 base eid e,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    used_complete_event_raw sg tskSt1 base eid e =
      used_complete_event_raw sg tskSt2 base eid e.
Proof.
  intros sg tskSt1 tskSt2 base eid e Hmap.
  unfold used_complete_event_raw.
  rewrite (mutex_del_encode_event_wait_grp_ext
    e.(waitList) tskSt1 tskSt2 ltac:(intros tid Hin; rewrite Hmap; reflexivity)).
  rewrite !(mutex_del_encode_event_wait_tbl_at_or_ext__g05_always_loop
    e.(waitList) tskSt1 tskSt2 _ Hmap).
  reflexivity.
Qed.
Lemma mutex_del_freed_event_raw_rep_merge__g05_always_loop :
  forall sg current eid pcp,
    store_used_event_map_raw_missing_i
      sg current.(TskState) current.(EventState).(inUsedEventStates) eid **
    sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid **
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    free_event_node_rest_no_type sg eid
      (free_event_head sg current.(EventState).(unUsedEventStates)) **
    store_free_event_nodes sg current.(EventState).(unUsedEventStates) |--
    verification_slice_event_raw_rep sg
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).(TskState)
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).(EventState).
Proof.
  intros sg current eid pcp.
  unfold verification_slice_event_raw_rep, store_used_event_map_raw,
    store_used_event_map_raw_missing_i, store_free_event_list,
    free_event_node_rest_no_type.
  unfold mutex_del_free_state_after__g05_always_loop,
    mutex_del_free_event_after__g05_always_loop,
    mutex_del_free_task_after__g05_always_loop.
  cbn.
  cbn [free_event_head store_free_event_nodes encode_event_type].
  assert (Hnone :
    (fun other : EventID =>
       if Z.eqb other eid then None
       else current.(EventState).(inUsedEventStates) other) eid = None).
  {
    rewrite Z.eqb_refl. reflexivity.
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
  assert (Hfun :
    (fun (eid0 : EventID) (e0 : OSEventAbstractState) =>
       used_complete_event_raw sg current.(TskState)
         (event_addr sg eid0) eid0 e0) =
    (fun (eid0 : EventID) (e0 : OSEventAbstractState) =>
       used_complete_event_raw sg
         {|
           inUsedTaskStates := current.(TskState).(inUsedTaskStates);
           unUsedTaskStates := current.(TskState).(unUsedTaskStates);
           tcbListHead := current.(TskState).(tcbListHead);
           prioTbl := fun p =>
             if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
                 Z.eqb p pcp)%bool
             then PTFree else current.(TskState).(prioTbl) p;
           taskRegNextID := current.(TskState).(taskRegNextID);
           parkedTaskStacks := current.(TskState).(parkedTaskStacks);
           taskLifecycle := current.(TskState).(taskLifecycle);
     taskCount := current.(TskState).(taskCount)
         |}
         (event_addr sg eid0) eid0 e0)).
  {
    apply functional_extensionality. intro eid0.
    apply functional_extensionality. intro e0.
    apply mutex_del_used_complete_event_raw_task_ext__g05_always_loop.
    reflexivity.
  }
  rewrite Hfun.
  cancel.
Qed.
Lemma mutex_del_task_prio_observation__g05_always_loop
  (st : Glob_TaskAbstractState) (tid : TaskID) : option Priority.
Proof.
  exact
    (match st.(inUsedTaskStates) tid with
     | Some t => Some t.(curPrio)
     | None => None
     end).
Defined.
Lemma mutex_del_atomic_task_set_curPrio_observation__g05_always_loop :
  forall sg tid prio pre post,
    atomic_task_set_curPrio sg tid prio pre tt post ->
    mutex_del_task_prio_observation__g05_always_loop
      post.(TskState) tid = Some prio.
Proof.
  intros sg tid prio pre post Hstep.
  unfold atomic_task_set_curPrio in Hstep.
  destruct Hstep as [Hready | [Hwaiting | Hdormant]].
  - unfold atomic_task_set_curPrio_ready in Hready.
    destruct Hready as
      (t & oldPrio & t' & Hlookup & Hold & Hne & Hlo & Hhi & Hpt &
       Hready & Ht' & Hpost).
    cbv zeta in Hpost. subst post t'.
    unfold mutex_del_task_prio_observation__g05_always_loop.
    cbn. rewrite Z.eqb_refl. reflexivity.
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
       evSt2 & pty & Hnot_ready & Hlookup & Hold & Hne & Hlo & Hhi &
       Hpt & Hpend & Hevent & Hmulti & Hget & Hwaittype & Hin & Ht' &
       Htsk & Hwait' & Hev & Hpost).
    subst post tskSt2 t'.
    unfold mutex_del_task_prio_observation__g05_always_loop.
    cbn. rewrite Z.eqb_refl. reflexivity.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Hlookup & Hold & Hne &
       Hlo & Hhi & Hpt & Hevent & Hmulti & Hnot_effective & Ht' &
       Htsk & Hpost).
    subst post tskSt2 t'.
    unfold mutex_del_task_prio_observation__g05_always_loop.
    cbn. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma mutex_del_wake_step_prio_observation__g05_always_loop :
  forall sg eid pre post tid,
    mutex_del_wake_step sg eid pre post ->
    mutex_del_task_prio_observation__g05_always_loop post.(TskState) tid =
    mutex_del_task_prio_observation__g05_always_loop pre.(TskState) tid.
Proof.
  intros sg eid pre post tid Hstep.
  unfold mutex_del_wake_step, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hstep.
  destruct Hstep as
    (returned_prio & canonical_waiter & table_owner & Hsame &
     e1 & e2 & canonical_t & table_t & table_t' &
     Hevent & Hpend & Hnonempty & Hcanonical & Hcanonical_get &
     Hreturned & Htable_slot & Htable_get & Htable_prio & Htable_t' &
     He2 & Hpost).
  cbv zeta in Hpost. subst post.
  unfold mutex_del_task_prio_observation__g05_always_loop.
  cbn.
  destruct (Z.eqb tid table_owner) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst tid.
    rewrite Htable_get. subst table_t'. reflexivity.
  - reflexivity.
Qed.
Lemma mutex_del_wake_steps_prio_observation__g05_always_loop :
  forall sg eid pre post tid,
    mutex_del_wake_steps sg eid pre post ->
    mutex_del_task_prio_observation__g05_always_loop post.(TskState) tid =
    mutex_del_task_prio_observation__g05_always_loop pre.(TskState) tid.
Proof.
  intros sg eid pre post tid Hsteps.
  induction Hsteps as [s | s0 s1 s2 Hprefix IH Hlast].
  - reflexivity.
  - rewrite (mutex_del_wake_step_prio_observation__g05_always_loop
      sg eid s1 s2 tid Hlast).
    exact IH.
Qed.
Lemma mutex_del_current_owner_restored__g05_always_loop :
  forall sg initial entry eid owner_post current m,
    entry.(EventState).(inUsedEventStates) eid = Some initial ->
    initial.(eventType) = OS_EVENT_TYPE_MUTEX ->
    initial.(mutexFields) = Some m ->
    mutex_del_owner_entry_consistency_prop sg initial entry ->
    mutex_del_rdyatprio_stage_prop sg initial entry owner_post ->
    mutex_del_wake_steps sg eid owner_post current ->
    m.(mfPCP) <> sg.(osPrioMutexCeilDis) ->
    match m.(mfOwner), m.(mfOwnerOrigPrio) with
    | None, None => True
    | Some owner, Some orig =>
        mutex_del_task_prio_observation__g05_always_loop
          current.(TskState) owner = Some orig
    | _, _ => False
    end.
Proof.
  intros sg initial entry eid owner_post current m Hused Htype Hfields
    Hentry_owner Hstage Hwakes Henabled.
  unfold mutex_del_owner_entry_consistency_prop in Hentry_owner.
  destruct Hentry_owner as
    (m0 & Htype0 & Hfields0 & Hentry_owner).
  rewrite Hfields in Hfields0. inversion Hfields0; subst m0.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as
    (m0 & Htype1 & Hfields1 & Hshape & Hexec).
  rewrite Hfields in Hfields1. inversion Hfields1; subst m0.
  destruct m.(mfOwner) as [owner|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hshape, Hentry_owner |- *.
  - destruct Hentry_owner as
      (entry_t & entry_orig & Hentry_lookup & Hentry_orig & Hentry_prio).
    inversion Hentry_orig; subst entry_orig.
    assert (Hdisabled : Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis) = false).
    { apply Z.eqb_neq. exact Henabled. }
    rewrite Hdisabled in Hexec.
    destruct Hexec as (owner_t & Howner_lookup & Hexec).
    rewrite Hentry_lookup in Howner_lookup.
    inversion Howner_lookup; subst owner_t.
    destruct (Z.eqb entry_t.(curPrio) m.(mfPCP)) eqn:Hat_pcp.
    + pose proof
        (mutex_del_atomic_task_set_curPrio_observation__g05_always_loop
          sg owner orig entry owner_post Hexec) as Howner_post.
      rewrite (mutex_del_wake_steps_prio_observation__g05_always_loop
        sg eid owner_post current owner Hwakes).
      exact Howner_post.
    + subst owner_post.
      rewrite (mutex_del_wake_steps_prio_observation__g05_always_loop
        sg eid entry current owner Hwakes).
      unfold mutex_del_task_prio_observation__g05_always_loop.
      rewrite Hentry_lookup.
      destruct Hentry_prio as [Horig_prio | [Henabled0 Hpcp_prio]].
      * rewrite Horig_prio. reflexivity.
      * exfalso.
        apply Z.eqb_neq in Hat_pcp.
        exact (Hat_pcp Hpcp_prio).
  - contradiction.
  - contradiction.
  - exact I.
Qed.
Lemma mutex_del_no_live_task_at_freed_pcp__g05_always_loop :
  forall sg current eid e m pcp owner_orig,
    UCOS2_verification_slice_state_inv sg current ->
    current.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    m.(mfPCP) = pcp ->
    pcp <> sg.(osPrioMutexCeilDis) ->
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None => True
     | Some owner, Some orig =>
         owner_orig = orig /\
         mutex_del_task_prio_observation__g05_always_loop
           current.(TskState) owner = Some orig
     | _, _ => False
     end) ->
    no_live_task_at_priority current.(TskState) pcp.
Proof.
  intros sg current eid e m pcp owner_orig Hvalid Hused Htype Hfields
    Hpcp Henabled Hrestored.
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [Htask [_ [_ Hcross]]].
  destruct Htask as [Htask_range _].
  pose proof
    (verification_slice_task_in_range_current_prio_registered
      sg current.(TskState) Htask_range) as Hregistered.
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hprotocol _]]]]]]]]].
  specialize (Hprotocol eid e m Hused Htype Hfields).
  destruct Hprotocol as [Hvalid_pcp [Howner_shape Hslot]].
  rewrite Hpcp in Hslot.
  destruct Hslot as [Hdisabled | [Henabled0 [Hreserved | Howned]]].
  - contradiction.
  - unfold no_live_task_at_priority.
    intros tid t Hlookup Heq.
    pose proof (Hregistered tid t Hlookup) as Htable.
    rewrite Heq, Hreserved in Htable. discriminate.
  - unfold no_live_task_at_priority.
    intros tid t Hlookup Heq.
    pose proof (Hregistered tid t Hlookup) as Htable.
    rewrite Heq in Htable.
    destruct Howned as (owner & Howner & Htable_owner).
    rewrite Htable_owner in Htable. inversion Htable; subst tid.
    destruct m.(mfOwner) as [owner0|] eqn:Howner0;
      destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
      simpl in Hrestored, Howner_shape.
    + inversion Howner; subst owner0.
      destruct Hrestored as [-> Hobs].
      unfold mutex_del_task_prio_observation__g05_always_loop in Hobs.
      rewrite Hlookup in Hobs. inversion Hobs.
      destruct Howner_shape as [Horig_valid Horig_ne].
      apply Horig_ne; [rewrite Hpcp; exact Henabled|]. congruence.
    + contradiction.
    + contradiction.
    + discriminate.
Qed.
Lemma mutex_del_wait_grp_zero_implies_empty__g05_always_loop :
  forall sg tskSt wl,
    Ucos2Verify.lib.event_wait.event_waitList_canonical sg tskSt wl ->
    encode_event_wait_grp wl tskSt = 0 ->
    wl = [].
Proof.
  intros sg tskSt wl Hcanonical Hgrp.
  destruct wl as [|tid rest]; [reflexivity |].
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
Qed.
Lemma mutex_del_free_lookup_some_before__g05_always_loop :
  forall sg current eid pcp other ev,
    (mutex_del_free_state_after__g05_always_loop
       sg eid pcp current).(EventState).(inUsedEventStates) other = Some ev ->
    current.(EventState).(inUsedEventStates) other = Some ev.
Proof.
  intros sg current eid pcp other ev Hlookup.
  unfold mutex_del_free_state_after__g05_always_loop,
    mutex_del_free_event_after__g05_always_loop in Hlookup.
  cbn in Hlookup.
  destruct (Z.eqb other eid); [discriminate | exact Hlookup].
Qed.
Lemma mutex_del_free_lookup_other__g05_always_loop :
  forall sg current eid pcp other,
    other <> eid ->
    (mutex_del_free_state_after__g05_always_loop
       sg eid pcp current).(EventState).(inUsedEventStates) other =
    current.(EventState).(inUsedEventStates) other.
Proof.
  intros sg current eid pcp other Hneq.
  unfold mutex_del_free_state_after__g05_always_loop,
    mutex_del_free_event_after__g05_always_loop.
  cbn.
  destruct (Z.eqb other eid) eqn:Heq; [|reflexivity].
  apply Z.eqb_eq in Heq. contradiction.
Qed.
Lemma mutex_del_free_task_validity__g05_always_loop :
  forall sg current pcp,
    verification_slice_task_validity sg current.(TskState) ->
    (pcp <> sg.(osPrioMutexCeilDis) ->
      no_live_task_at_priority current.(TskState) pcp) ->
    verification_slice_task_validity sg
      (mutex_del_free_task_after__g05_always_loop
         sg pcp current.(TskState)).
Proof.
  intros sg current pcp Hvalid Hno_live.
  unfold verification_slice_task_validity in Hvalid |- *.
  destruct Hvalid as [Hrange Hfields].
  split.
  - unfold verification_slice_task_in_range in Hrange |- *.
    destruct Hrange as
      [Hused_range [Hnodup [Hfree_range [Hpartition
       [Htable [Hregistered Hunique]]]]]].
    cbn.
    split; [exact Hused_range|].
    split; [exact Hnodup|].
    split; [exact Hfree_range|].
    split; [exact Hpartition|].
    split.
    + intros p0 tid0 Hslot.
      destruct
        (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) && Z.eqb p0 pcp)%bool
        eqn:Hoverwrite; [discriminate|].
      eapply Htable; eauto.
    + split.
      * intros tid0 t0 Hlookup.
      pose proof (Hregistered tid0 t0 Hlookup) as Hold.
      cbn.
      destruct (Z.eq_dec pcp sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled].
      -- subst pcp. rewrite Z.eqb_refl. cbn. exact Hold.
      -- assert (Henabledb : Z.eqb pcp sg.(osPrioMutexCeilDis) = false).
         { apply Z.eqb_neq. exact Henabled. }
        rewrite Henabledb. cbn.
        destruct (Z.eqb t0.(curPrio) pcp) eqn:Heq.
        ++ apply Z.eqb_eq in Heq.
           exfalso.
           exact ((Hno_live Henabled tid0 t0 Hlookup) Heq).
        ++ exact Hold.
      * exact Hunique.
  - intros tid0 t0 Hlookup.
    cbn in Hlookup.
    eapply Hfields; eauto.
Qed.
Lemma mutex_del_freed_event_validity__g05_always_loop :
  forall sg current eid pcp old,
    current.(EventState).(inUsedEventStates) eid = Some old ->
    verification_slice_event_in_range sg current.(TskState) current.(EventState) ->
    verification_slice_event_in_range sg
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).(TskState)
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).(EventState).
Proof.
  intros sg current eid pcp old Hused Hvalid.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in *.
  destruct Hvalid as
    [Hrange [Hnodup [Hfree_range [Hpartition
     [Hfields [Hpayload [Hqueue Hwait]]]]]]].
  split.
  { intros other ev Hlookup. eapply Hrange.
    eapply mutex_del_free_lookup_some_before__g05_always_loop; eauto. }
  split.
  { cbn. constructor.
    - eapply event_slot_partition_used_not_free; eauto.
    - exact Hnodup. }
  split.
  { cbn. constructor.
    - eapply Hrange; eauto.
    - exact Hfree_range. }
  split.
  { unfold mutex_del_free_state_after__g05_always_loop,
      mutex_del_free_event_after__g05_always_loop.
    cbn. eapply event_slot_partition_preserved_delete; eauto. }
  split.
  { intros other ev Hlookup. eapply Hfields.
    eapply mutex_del_free_lookup_some_before__g05_always_loop; eauto. }
  split.
  { intros other ev Hlookup. eapply Hpayload.
    eapply mutex_del_free_lookup_some_before__g05_always_loop; eauto. }
  split.
  { unfold queue_binding_unique in *.
    intros eid1 eid2 e1 e2 qid Hget1 Hget2 Hqid1 Hqid2.
    eapply Hqueue; eauto using mutex_del_free_lookup_some_before__g05_always_loop. }
  intros other ev Hlookup.
  eapply Hwait.
  eapply mutex_del_free_lookup_some_before__g05_always_loop; eauto.
Qed.
Lemma mutex_del_freed_event_wait_consistency__g05_always_loop :
  forall sg current eid pcp,
    verification_slice_event_wait_object_consistency sg current ->
    Ucos2Verify.lib.event_wait.task_event_id_unreferenced_prop current eid ->
    verification_slice_event_wait_object_consistency sg
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).
Proof.
  intros sg current eid pcp Hconsistent Hunreferenced.
  unfold verification_slice_event_wait_object_consistency in *.
  destruct Hconsistent as [Hentry [Htotal Hclosed]].
  split; [|split].
  - intros other ev Hlookup. eapply Hentry.
    eapply mutex_del_free_lookup_some_before__g05_always_loop; eauto.
  - unfold Ucos2Verify.lib.event_wait.task_event_reference_backlink_consistency in *.
    intros tid t other ev Htask Hlookup Hreference.
    destruct (Z.eq_dec other eid) as [Heq | Hneq].
    + subst other.
      specialize (Hunreferenced tid t Htask) as [Hsingle Hmulti].
      destruct Hreference as [Hreference | Hreference]; contradiction.
    + eapply Htotal; eauto.
      eapply mutex_del_free_lookup_some_before__g05_always_loop; eauto.
  - unfold Ucos2Verify.lib.event_wait.task_event_reference_closure in *.
    intros tid t Htask.
    specialize (Hclosed tid t Htask) as [Hsingle Hmulti].
    specialize (Hunreferenced tid t Htask) as [Hsingle_neq Hmulti_neq].
    split.
    + intros other Hptr.
      destruct (Z.eq_dec other eid) as [Heq | Hneq].
      * subst other. contradiction.
      * destruct (Hsingle other Hptr) as [ev Hlookup].
        exists ev. rewrite mutex_del_free_lookup_other__g05_always_loop; auto.
    + intros other Hin.
      destruct (Z.eq_dec other eid) as [Heq | Hneq].
      * subst other. contradiction.
      * destruct (Hmulti other Hin) as [ev Hlookup].
        exists ev. rewrite mutex_del_free_lookup_other__g05_always_loop; auto.
Qed.
Lemma mutex_del_free_cross_consistency__g05_always_loop :
  forall sg current eid selected m pcp,
    current.(EventState).(inUsedEventStates) eid = Some selected ->
    selected.(eventType) = OS_EVENT_TYPE_MUTEX ->
    selected.(mutexFields) = Some m ->
    m.(mfPCP) = pcp ->
    selected.(waitList) = [] ->
    (pcp <> sg.(osPrioMutexCeilDis) ->
      no_live_task_at_priority current.(TskState) pcp) ->
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None => True
     | Some owner, Some orig =>
         mutex_del_task_prio_observation__g05_always_loop
           current.(TskState) owner = Some orig
     | _, _ => False
     end) ->
    verification_slice_cross_module_consistency sg current ->
    verification_slice_cross_module_consistency sg
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).
Proof.
  intros sg current eid selected m pcp Hselected Htype Hfields Hpcp
    Hempty Hno_live Hrestored Hcross.
  set (post := mutex_del_free_state_after__g05_always_loop
    sg eid pcp current).
  assert (Htaskmap : post.(TskState).(inUsedTaskStates) =
      current.(TskState).(inUsedTaskStates)).
  { subst post. reflexivity. }
  assert (Hsched : post.(SchedState) = current.(SchedState)).
  { subst post. reflexivity. }
  assert (Htable_post : forall p,
      post.(TskState).(prioTbl) p =
      if (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
          Z.eqb p pcp)%bool
      then PTFree else current.(TskState).(prioTbl) p).
  { intro p. subst post. reflexivity. }
  assert (Hevent_back : forall mid ev,
      post.(EventState).(inUsedEventStates) mid = Some ev ->
      current.(EventState).(inUsedEventStates) mid = Some ev).
  { intros mid ev Hlookup. subst post.
    eapply mutex_del_free_lookup_some_before__g05_always_loop; eauto. }
  assert (Hevent_other : forall mid,
      mid <> eid ->
      post.(EventState).(inUsedEventStates) mid =
      current.(EventState).(inUsedEventStates) mid).
  { intros mid Hneq. subst post.
    apply mutex_del_free_lookup_other__g05_always_loop. exact Hneq. }
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as
    [Hosprio [Hpriotbl [Howner [Hwait
     [Hready_complete [Hready_order [Hceiling
      [Htask_unique [Hprotocol Hpcp_unique]]]]]]]]].
  assert (Hunreferenced :
    Ucos2Verify.lib.event_wait.task_event_id_unreferenced_prop current eid).
  { eapply Ucos2Verify.lib.event_wait.event_wait_empty_implies_unreferenced;
      eauto. }
  assert (Hremaining_pcp : forall mid ev mf,
    post.(EventState).(inUsedEventStates) mid = Some ev ->
    ev.(eventType) = OS_EVENT_TYPE_MUTEX ->
    ev.(mutexFields) = Some mf ->
    pcp <> sg.(osPrioMutexCeilDis) ->
    mf.(mfPCP) <> pcp).
  {
    intros mid ev mf Hlookup Hmutex Hmf Henabled Heq.
    assert (Hmid_neq : mid <> eid).
    { intro Hmid. subst mid.
      subst post. cbn in Hlookup.
      rewrite Z.eqb_refl in Hlookup. discriminate. }
    apply Hmid_neq.
    eapply Hpcp_unique.
    - eapply Hevent_back; eauto.
    - exact Hmutex.
    - exact Hmf.
    - exact Hselected.
    - exact Htype.
    - exact Hfields.
    - congruence.
    - rewrite Heq. exact Henabled.
  }
  unfold verification_slice_cross_module_consistency.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  - unfold osprio_cur_consistency in Hosprio |- *.
    rewrite Hsched, Htaskmap. exact Hosprio.
  - unfold priotbl_consistency in Hpriotbl |- *.
    intro p. specialize (Hpriotbl p).
    rewrite Htable_post.
    destruct
      (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) && Z.eqb p pcp)%bool
      eqn:Hoverwrite.
    + apply andb_true_iff in Hoverwrite.
      destruct Hoverwrite as [Henabled_b Hp_b].
      apply negb_true_iff in Henabled_b.
      apply Z.eqb_neq in Henabled_b.
      apply Z.eqb_eq in Hp_b. subst p.
      split.
      * intros (tid & Hready & t & Hlookup & Hprio).
        rewrite Htaskmap in Hlookup.
        exact ((Hno_live Henabled_b tid t Hlookup) Hprio).
      * intros (mid & ev & mf & Hlookup & Hmutex & Hmf & Hreserve).
        destruct Hreserve as [Hmf_enabled Hmf_pcp].
        eapply (Hremaining_pcp mid ev mf Hlookup Hmutex Hmf Henabled_b).
        exact Hmf_pcp.
    + destruct (current.(TskState).(prioTbl) p) eqn:Hslot.
      * destruct Hpriotbl as [Hno_ready Hno_mutex]. split.
        -- intros (tid & Hready & t & Hlookup & Hprio).
           apply Hno_ready. exists tid. split; [rewrite Hsched in Hready; exact Hready|].
           exists t. split; [rewrite Htaskmap in Hlookup; exact Hlookup|exact Hprio].
        -- intros (mid & ev & mf & Hlookup & Hmutex & Hmf & Hreserve).
           apply Hno_mutex. exists mid, ev, mf.
           split; [eapply Hevent_back; eauto|].
           split; [exact Hmutex|].
           split; [exact Hmf|exact Hreserve].
      * destruct Hpriotbl as
          (mid & ev & mf & Hlookup & Hmutex & Hmf & Hmf_pcp & Howner_state).
        assert (Hmid_neq : mid <> eid).
        { intro Hmid. subst mid.
          rewrite Hselected in Hlookup. inversion Hlookup; subst ev.
          rewrite Hfields in Hmf. inversion Hmf; subst mf.
          assert (Hp : p = pcp) by congruence.
          destruct (Z.eq_dec pcp sg.(osPrioMutexCeilDis))
            as [Hdisabled|Henabled].
          - unfold ceiling_priotbl_free in Hceiling.
            congruence.
          - assert (Hovertrue :
              (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
               Z.eqb p pcp)%bool = true).
            { apply andb_true_iff. split.
              - apply negb_true_iff, Z.eqb_neq. exact Henabled.
              - apply Z.eqb_eq. exact Hp. }
            congruence. }
        exists mid, ev, mf. repeat split; try assumption.
        rewrite Hevent_other; assumption.
      * destruct Hpriotbl as [t [Htask [Hdirect | Hmutex_source]]].
        -- exists t. split; [rewrite Htaskmap; exact Htask|].
           left. exact Hdirect.
        -- exists t. split; [rewrite Htaskmap; exact Htask|].
           destruct Hmutex_source as
          (mid & ev & mf & Hlookup & Hmutex & Hmf & Howner_id & Hsource).
           destruct (Z.eq_dec mid eid) as [Hmid|Hmid].
           ++ subst mid. rewrite Hselected in Hlookup.
              inversion Hlookup; subst ev.
              rewrite Hfields in Hmf. inversion Hmf; subst mf.
              destruct Hsource as [Hpcp_source | Horig_source].
              ** assert (Hp : p = pcp) by congruence.
                 destruct (Z.eq_dec pcp sg.(osPrioMutexCeilDis))
                   as [Hdisabled|Henabled].
                 --- unfold ceiling_priotbl_free in Hceiling.
                     congruence.
                 --- assert (Hovertrue :
                      (negb (Z.eqb pcp sg.(osPrioMutexCeilDis)) &&
                       Z.eqb p pcp)%bool = true).
                     { apply andb_true_iff. split.
                       - apply negb_true_iff, Z.eqb_neq. exact Henabled.
                       - apply Z.eqb_eq. exact Hp. }
                     congruence.
              ** left.
                 destruct m.(mfOwner) as [owner|] eqn:Howner_m;
                   destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig_m;
                   simpl in Hrestored.
                 --- inversion Howner_id; subst owner.
                     inversion Horig_source; subst orig.
                     unfold mutex_del_task_prio_observation__g05_always_loop
                       in Hrestored.
                     rewrite Htask in Hrestored. congruence.
                 --- discriminate.
                 --- discriminate.
                 --- discriminate.
           ++ right. exists mid, ev, mf. repeat split; try assumption.
              rewrite Hevent_other; assumption.
  - unfold mutex_owner_consistency in Howner |- *.
    intros mid ev mf [Hlookup [Hmutex Hmf]].
    apply (Howner mid ev mf). repeat split; try assumption.
    eapply Hevent_back; eauto.
  - unfold post.
    eapply mutex_del_freed_event_wait_consistency__g05_always_loop; eauto.
  - unfold ready_list_completeness in Hready_complete |- *.
    cbn. exact Hready_complete.
  - unfold ready_list_order in Hready_order |- *.
    cbn. exact Hready_order.
  - unfold ceiling_priotbl_free in Hceiling |- *.
    rewrite Htable_post.
    destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
    + cbn. exact Hceiling.
    + assert (Hdisabled_neq : pcp <> sg.(osPrioMutexCeilDis)).
      { apply Z.eqb_neq. exact Hdisabled. }
      assert (Hneqb : Z.eqb sg.(osPrioMutexCeilDis) pcp = false).
      { apply Z.eqb_neq. congruence. }
      rewrite Hneqb. cbn. exact Hceiling.
  - unfold task_priority_unique_prop in Htask_unique |- *.
    unfold task_priority_unique in Htask_unique |- *.
    cbn. exact Htask_unique.
  - unfold mutex_protocol_consistency in Hprotocol |- *.
    intros mid ev mf Hlookup Hmutex Hmf.
    pose proof (Hprotocol mid ev mf (Hevent_back mid ev Hlookup)
      Hmutex Hmf) as Hproto.
    destruct Hproto as [Hvalid_pcp [Howner_shape Hslot]].
    repeat split; try assumption.
    destruct Hslot as [Hdisabled | [Henabled [Hreserved | Howned]]].
    + left. exact Hdisabled.
    + right. split; [exact Henabled|]. left.
      rewrite Htable_post.
      destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hsel.
      * cbn. exact Hreserved.
      * assert (Hsel_enabled : pcp <> sg.(osPrioMutexCeilDis)).
        { apply Z.eqb_neq. exact Hsel. }
        assert (Hmf_neq : mf.(mfPCP) <> pcp).
        { eapply Hremaining_pcp; eauto. }
        assert (Hidxb : Z.eqb mf.(mfPCP) pcp = false).
        { apply Z.eqb_neq. exact Hmf_neq. }
        rewrite Hidxb. cbn. exact Hreserved.
    + right. split; [exact Henabled|]. right.
      destruct Howned as (owner & Howner_id & Htable_owner).
      exists owner. split; [exact Howner_id|].
      rewrite Htable_post.
      destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hsel.
      * cbn. exact Htable_owner.
      * assert (Hsel_enabled : pcp <> sg.(osPrioMutexCeilDis)).
        { apply Z.eqb_neq. exact Hsel. }
        assert (Hmf_neq : mf.(mfPCP) <> pcp).
        { eapply Hremaining_pcp; eauto. }
        assert (Hidxb : Z.eqb mf.(mfPCP) pcp = false).
        { apply Z.eqb_neq. exact Hmf_neq. }
        rewrite Hidxb. cbn. exact Htable_owner.
  - eapply mutex_enabled_pcp_unique_transport.
    + intros mid ev mf Hlookup Hmutex Hmf.
      exists ev, mf. repeat split; try assumption; try reflexivity.
      eapply Hevent_back; eauto.
    + exact Hpcp_unique.
Qed.
Lemma mutex_del_no_live_task_at_freed_pcp_simple__g05_always_loop :
  forall sg current eid selected m pcp,
    UCOS2_verification_slice_state_inv sg current ->
    current.(EventState).(inUsedEventStates) eid = Some selected ->
    selected.(eventType) = OS_EVENT_TYPE_MUTEX ->
    selected.(mutexFields) = Some m ->
    m.(mfPCP) = pcp ->
    pcp <> sg.(osPrioMutexCeilDis) ->
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None => True
     | Some owner, Some orig =>
         mutex_del_task_prio_observation__g05_always_loop
           current.(TskState) owner = Some orig
     | _, _ => False
     end) ->
    no_live_task_at_priority current.(TskState) pcp.
Proof.
  intros sg current eid selected m pcp Hvalid Hlookup Htype Hfields
    Hpcp Henabled Hrestored.
  eapply (mutex_del_no_live_task_at_freed_pcp__g05_always_loop
    sg current eid selected m pcp
    (match m.(mfOwnerOrigPrio) with Some p => p | None => 0 end));
    try eassumption.
  destruct m.(mfOwner) as [owner|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hrestored |- *; try contradiction; auto.
Qed.
Lemma mutex_del_free_validity_bundle__g05_always_loop :
  forall sg current eid selected m pcp,
    current.(EventState).(inUsedEventStates) eid = Some selected ->
    selected.(eventType) = OS_EVENT_TYPE_MUTEX ->
    selected.(mutexFields) = Some m ->
    m.(mfPCP) = pcp ->
    selected.(waitList) = [] ->
    (pcp <> sg.(osPrioMutexCeilDis) ->
      no_live_task_at_priority current.(TskState) pcp) ->
    (match m.(mfOwner), m.(mfOwnerOrigPrio) with
     | None, None => True
     | Some owner, Some orig =>
         mutex_del_task_prio_observation__g05_always_loop
           current.(TskState) owner = Some orig
     | _, _ => False
     end) ->
    UCOS2_verification_slice_state_inv sg current ->
    UCOS2_verification_slice_state_inv sg
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).
Proof.
  intros sg current eid selected m pcp Hlookup Htype Hfields Hpcp
    Hempty Hno_live Hrestored Hvalid.
  unfold UCOS2_verification_slice_state_inv in Hvalid |- *.
  destruct Hvalid as [Htask [Hsched [Hevent Hcross]]].
  split.
  - eapply mutex_del_free_task_validity__g05_always_loop; eauto.
  - split.
    + cbn.
      rewrite <- (verification_slice_sched_in_range_ext sg current.(TskState)
        (mutex_del_free_task_after__g05_always_loop
           sg pcp current.(TskState)) current.(SchedState));
        [exact Hsched|reflexivity].
    + split.
      * eapply mutex_del_freed_event_validity__g05_always_loop; eauto.
      * eapply mutex_del_free_cross_consistency__g05_always_loop; eauto.
Qed.
Lemma mutex_del_pcp_release_focus_expose_validity__g05_always_loop :
  forall sg anchor current eid pcp,
    mutex_del_pcp_release_focus sg anchor current eid pcp |--
      coq_prop (UCOS2_verification_slice_state_inv sg current) &&
      mutex_del_pcp_release_focus sg anchor current eid pcp.
Proof.
  intros sg anchor current eid pcp.
  unfold mutex_del_pcp_release_focus.
  destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hpcp.
  - unfold mutex_del_event_ready_focus_inv,
      verification_slice_task_inv, mutex_del_event_inv_no_eid_no_free_head.
    apply _derivable1_andp_intros.
    + pureIntros.
      apply derivable1s_coq_prop_r.
      unfold UCOS2_verification_slice_state_inv. tauto.
    + cancel.
  - unfold mutex_del_event_missing_priotbl_focus,
      verification_slice_task_inv_missing_priotbl,
      mutex_del_event_inv_no_eid_no_free_head.
    apply _derivable1_andp_intros.
    + pureIntros.
      apply derivable1s_coq_prop_r.
      unfold UCOS2_verification_slice_state_inv. tauto.
    + cancel.
Qed.
Lemma mutex_del_prioTbl_to_addrs_rec_seq__g05_always_loop :
  forall sg f n acc,
    verification_slice_prioTbl_to_addrs_rec sg f n acc =
      map (fun k => verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)))
        (seq 0 n) ++ acc.
Proof.
  intros sg f n. induction n as [|n IH]; intro acc.
  - reflexivity.
  - simpl verification_slice_prioTbl_to_addrs_rec.
    rewrite IH, seq_S, map_app. simpl.
    rewrite <- app_assoc. reflexivity.
Qed.
Lemma mutex_del_prioTbl_to_addrs_Znth__g05_always_loop :
  forall sg table p,
    0 <= p < OS_PRIO_TBL_SIZE ->
    Znth p (verification_slice_prioTbl_to_addrs sg table) 0 =
      verification_slice_prio_tbl_entry_to_addr sg (table p).
Proof.
  intros sg table p Hp.
  unfold verification_slice_prioTbl_to_addrs.
  rewrite mutex_del_prioTbl_to_addrs_rec_seq__g05_always_loop.
  rewrite app_nil_r.
  unfold OS_PRIO_TBL_SIZE in Hp.
  unfold Znth.
  assert (Hnat : (Z.to_nat p < 64)%nat) by lia.
  assert (Hdefault :
    nth (Z.to_nat p)
      (map (fun k : nat =>
        verification_slice_prio_tbl_entry_to_addr sg (table (Z.of_nat k))) (seq 0 64)) 0 =
    nth (Z.to_nat p)
      (map (fun k : nat =>
        verification_slice_prio_tbl_entry_to_addr sg (table (Z.of_nat k))) (seq 0 64))
      (verification_slice_prio_tbl_entry_to_addr sg (table (Z.of_nat 0)))).
  {
    apply nth_indep.
    rewrite length_map, length_seq.
    exact Hnat.
  }
  rewrite Hdefault.
  change
    (nth (Z.to_nat p)
       (map (fun k : nat =>
         verification_slice_prio_tbl_entry_to_addr sg (table (Z.of_nat k))) (seq 0 64))
       ((fun k : nat =>
         verification_slice_prio_tbl_entry_to_addr sg (table (Z.of_nat k))) 0%nat) =
     verification_slice_prio_tbl_entry_to_addr sg (table p)).
  rewrite map_nth.
  rewrite seq_nth by exact Hnat.
  simpl Nat.add.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma mutex_del_prioTbl_to_addrs_free_enabled__g05_always_loop :
  forall sg st pcp,
    Ucos2Verify.lib.array_abstraction.priotbl_index_in_range pcp ->
    pcp <> sg.(osPrioMutexCeilDis) ->
    replace_Znth pcp 0 (verification_slice_prioTbl_to_addrs sg st.(prioTbl)) =
      verification_slice_prioTbl_to_addrs sg
        (mutex_del_free_task_after__g05_always_loop sg pcp st).(prioTbl).
Proof.
  intros sg st pcp Hrange Henabled.
  unfold Ucos2Verify.lib.array_abstraction.priotbl_index_in_range in Hrange.
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Zlength_replace_Znth.
    rewrite !mutex_del_prioTbl_to_addrs_Zlength.
    reflexivity.
  - intros q Hq.
    assert (Hqrange : 0 <= q < OS_PRIO_TBL_SIZE).
    {
      rewrite Zlength_replace_Znth,
        mutex_del_prioTbl_to_addrs_Zlength in Hq.
      exact Hq.
    }
    destruct (Z.eq_dec q pcp) as [Heq | Hneq].
    + subst q.
      rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_eq_gen by
        (rewrite mutex_del_prioTbl_to_addrs_Zlength; exact Hrange).
      symmetry.
      etransitivity.
      * apply mutex_del_prioTbl_to_addrs_Znth__g05_always_loop.
        exact Hrange.
      * unfold mutex_del_free_task_after__g05_always_loop.
        cbn.
        rewrite (proj2 (Z.eqb_neq pcp sg.(osPrioMutexCeilDis)) Henabled).
        cbn. rewrite Z.eqb_refl. reflexivity.
    + rewrite Ucos2Verify.lib.array_abstraction.Znth_replace_Znth_neq_gen.
      2: exact Hneq.
      2: rewrite mutex_del_prioTbl_to_addrs_Zlength; exact Hqrange.
      2: rewrite mutex_del_prioTbl_to_addrs_Zlength; exact Hrange.
      etransitivity.
      * apply mutex_del_prioTbl_to_addrs_Znth__g05_always_loop.
        exact Hqrange.
      * symmetry.
        etransitivity.
        -- apply mutex_del_prioTbl_to_addrs_Znth__g05_always_loop.
           exact Hqrange.
        -- unfold mutex_del_free_task_after__g05_always_loop.
           cbn.
           rewrite (proj2 (Z.eqb_neq pcp sg.(osPrioMutexCeilDis)) Henabled).
           cbn. rewrite (proj2 (Z.eqb_neq q pcp) Hneq).
           reflexivity.
Qed.
Lemma mutex_del_task_raw_rep_after_pcp_release__g05_always_loop :
  forall sg st pcp,
    Ucos2Verify.lib.array_abstraction.priotbl_index_in_range pcp ->
    (if Z.eqb pcp sg.(osPrioMutexCeilDis)
     then verification_slice_task_inv sg st
     else priotbl_element_store sg.(g_OSTCBPrioTbl) pcp 0 **
          verification_slice_task_inv_missing_priotbl sg st pcp) |--
    verification_slice_task_raw_rep sg
      (mutex_del_free_task_after__g05_always_loop sg pcp st).
Proof.
  intros sg st pcp Hrange.
  destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - unfold mutex_del_free_task_after__g05_always_loop.
    cbn. rewrite Hdisabled. cbn.
    unfold verification_slice_task_inv, verification_slice_task_raw_rep.
    pureIntros.
    destruct st; cbn in *.
    cancel.
  - assert (Henabled : pcp <> sg.(osPrioMutexCeilDis)).
    { apply Z.eqb_neq. exact Hdisabled. }
    unfold verification_slice_task_inv_missing_priotbl.
    pureIntros.
    unfold verification_slice_store_prio_tbl_missing_i.
    sep_apply_l_atomic
      (Ucos2Verify.lib.array_abstraction.verification_slice_store_priotbl_list_merge sg
        (verification_slice_prioTbl_to_addrs sg st.(prioTbl)) pcp 0 Hrange
        (mutex_del_prioTbl_to_addrs_Zlength sg st.(prioTbl))).
    pose proof
      (mutex_del_prioTbl_to_addrs_free_enabled__g05_always_loop
        sg st pcp Hrange Henabled) as Hlist.
    unfold verification_slice_task_raw_rep, verification_slice_store_prio_tbl.
    rewrite <- Hlist.
    unfold mutex_del_free_task_after__g05_always_loop.
    cbn [inUsedTaskStates unUsedTaskStates tcbListHead taskCount].
    cancel.
    sepcon_assoc_change.
    cancel.
    unfold derivable1; intros h Hstore; exact Hstore.
Qed.
Lemma mutex_del_encode_ready_tbl_at_or_ext__g05_always_loop :
  forall rl tskSt1 tskSt2 y,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    encode_ready_tbl_at_or rl tskSt1 y =
      encode_ready_tbl_at_or rl tskSt2 y.
Proof.
  induction rl as [|tid rest IH]; intros tskSt1 tskSt2 y Hmap; simpl.
  - reflexivity.
  - rewrite Hmap. rewrite (IH tskSt1 tskSt2 y Hmap). reflexivity.
Qed.
Lemma mutex_del_sched_raw_ready_task_ext__g05_always_loop :
  forall sg pre post tskSt1 tskSt2,
    tskSt1.(inUsedTaskStates) = tskSt2.(inUsedTaskStates) ->
    verification_slice_sched_raw_ready_prio_stage sg pre post tskSt1 =
      verification_slice_sched_raw_ready_prio_stage sg pre post tskSt2.
Proof.
  intros sg pre post tskSt1 tskSt2 Hmap.
  unfold verification_slice_sched_raw_ready_prio_stage.
  rewrite (encode_ready_grp_ext post.(readyList) tskSt1 tskSt2 Hmap).
  rewrite !(mutex_del_encode_ready_tbl_at_or_ext__g05_always_loop
    post.(readyList) tskSt1 tskSt2 _ Hmap).
  reflexivity.
Qed.
Lemma mutex_del_freed_event_cells_from_storage__g05_always_loop :
  forall sg current eid selected base
         type_addr ptr_addr cnt_addr grp_addr tbl_addr free_head,
    selected.(waitList) = [] ->
    base = event_addr sg eid ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    free_head = free_event_head sg current.(EventState).(unUsedEventStates) ->
    type_addr # UChar |-> 0 **
    ptr_addr # Ptr |-> free_head **
    cnt_addr # UShort |-> 0 **
    grp_addr # UChar |-> 0 **
    used_event_wait_table_storage current.(TskState) base selected |--
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    free_event_node_rest_no_type sg eid
      (free_event_head sg current.(EventState).(unUsedEventStates)).
Proof.
  intros sg current eid selected base
    type_addr ptr_addr cnt_addr grp_addr tbl_addr free_head
    Hempty Hbase Hcore Hwait Hhead.
  subst base.
  unfold event_core_fields_layout_prop in Hcore.
  unfold event_wait_fields_layout_prop in Hwait.
  destruct Hcore as [Htype [Hptr Hcnt]].
  destruct Hwait as [Hgrp Htbl].
  subst type_addr; subst ptr_addr; subst cnt_addr;
    subst grp_addr; subst tbl_addr.
  unfold used_event_wait_table_storage.
  rewrite Hempty. cbn. repeat rewrite Z.add_0_r.
  subst free_head.
  unfold free_event_node_rest_no_type.
  repeat rewrite Z.add_0_r.
  sep_apply_l_atomic
    (store_ushort_undef_store_ushort
      (event_addr sg eid + OSEventCnt_off) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventGrp_off) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 1) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 2) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 3) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 4) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 5) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 6) 0).
  sep_apply_l_atomic
    (store_uchar_undef_store_uchar
      (event_addr sg eid + OSEventTbl_off + 7) 0).
  cancel.
Qed.
Lemma mutex_del_pcp_release_focus_raw_components__g05_always_loop :
  forall sg anchor current eid pcp,
    Ucos2Verify.lib.array_abstraction.priotbl_index_in_range pcp ->
    verification_slice_task_validity sg current.(TskState) ->
    verification_slice_event_in_range
      sg current.(TskState) current.(EventState) ->
    mutex_del_pcp_release_focus sg anchor current eid pcp |--
    Ucos2Verify.lib.interrupt.interrupt_inv sg current.(IntrState) **
    verification_slice_task_raw_rep sg
      (mutex_del_free_task_after__g05_always_loop
         sg pcp current.(TskState)) **
    verification_slice_sched_raw_ready_prio_stage
      sg anchor.(SchedState) current.(SchedState) current.(TskState) **
    store_used_event_map_raw_missing_i
      sg current.(TskState)
      current.(EventState).(inUsedEventStates) eid **
    store_free_event_nodes sg current.(EventState).(unUsedEventStates) **
    Ucos2Verify.lib.tick.verification_slice_tick_inv sg current.(TickState) ** TT.
Proof.
  intros sg anchor current eid pcp Hrange Htask Hevent.
  unfold mutex_del_pcp_release_focus.
  destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - unfold mutex_del_event_ready_focus_inv.
    pose proof
      (mutex_del_task_raw_rep_after_pcp_release__g05_always_loop
        sg current.(TskState) pcp Hrange) as Htaskraw.
    rewrite Hdisabled in Htaskraw.
    sep_apply_l_atomic Htaskraw.
    unfold mutex_del_event_inv_no_eid_no_free_head.
    pureIntros.
    sep_apply_l_atomic
      (mutex_del_event_missing_stable_to_raw__g05_always_loop
        sg current.(TskState) current.(EventState) eid Htask Hevent).
    cancel.
  - unfold mutex_del_event_missing_priotbl_focus.
    pose proof
      (mutex_del_task_raw_rep_after_pcp_release__g05_always_loop
        sg current.(TskState) pcp Hrange) as Htaskraw.
    rewrite Hdisabled in Htaskraw.
    sep_apply_l_atomic Htaskraw.
    unfold mutex_del_event_inv_no_eid_no_free_head.
    pureIntros.
    sep_apply_l_atomic
      (mutex_del_event_missing_stable_to_raw__g05_always_loop
        sg current.(TskState) current.(EventState) eid Htask Hevent).
    cancel.
Qed.
Lemma mutex_del_free_transition_rep__g05_always_loop :
  forall sg anchor current eid pcp selected base
         type_addr ptr_addr cnt_addr grp_addr tbl_addr
         free_addr free_head,
    Ucos2Verify.lib.array_abstraction.priotbl_index_in_range pcp ->
    selected.(waitList) = [] ->
    base = event_addr sg eid ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    os_event_free_list_addr sg free_addr ->
    event_free_list_head_prop sg current.(EventState) free_head ->
    UCOS2_verification_slice_state_inv sg current ->
    UCOS2_verification_slice_state_inv sg
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current) ->
    mutex_del_pcp_release_focus sg anchor current eid pcp **
    type_addr # UChar |-> 0 **
    ptr_addr # Ptr |-> free_head **
    used_event_wait_table_storage current.(TskState) base selected **
    free_addr # Ptr |-> base **
    cnt_addr # UShort |-> 0 **
    grp_addr # UChar |-> 0 |--
    mutex_del_transition_rep sg anchor
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).
Proof.
  intros sg anchor current eid pcp selected base
    type_addr ptr_addr cnt_addr grp_addr tbl_addr
    free_addr free_head Hrange Hempty Hbase Hcore Hwait
    Hfreeaddr Hfreehead Hvalid Hpostvalid.
  pose proof Hvalid as Hvalid0.
  unfold UCOS2_verification_slice_state_inv in Hvalid0.
  destruct Hvalid0 as [Htask [_ [Hevent _]]].
  unfold os_event_free_list_addr in Hfreeaddr.
  unfold event_free_list_head_prop in Hfreehead.
  subst base; subst free_addr; subst free_head.
  sep_apply_l_atomic
    (mutex_del_pcp_release_focus_raw_components__g05_always_loop
      sg anchor current eid pcp Hrange Htask Hevent).
  sep_apply_l_atomic
    (mutex_del_freed_event_cells_from_storage__g05_always_loop
      sg current eid selected (event_addr sg eid)
      type_addr ptr_addr cnt_addr grp_addr tbl_addr
      (free_event_head sg current.(EventState).(unUsedEventStates))
      Hempty eq_refl Hcore Hwait eq_refl).
  sep_apply_l_atomic
    (mutex_del_freed_event_raw_rep_merge__g05_always_loop
      sg current eid pcp).
  assert (Hsched :
    verification_slice_sched_raw_ready_prio_stage
      sg anchor.(SchedState) current.(SchedState) current.(TskState) =
    verification_slice_sched_raw_ready_prio_stage
      sg anchor.(SchedState) current.(SchedState)
      (mutex_del_free_task_after__g05_always_loop
         sg pcp current.(TskState))).
  {
    apply mutex_del_sched_raw_ready_task_ext__g05_always_loop.
    reflexivity.
  }
  unfold mutex_del_transition_rep.
  Right.
  apply _derivable1_andp_intros.
  - Right.
    unfold UCOS2_verification_slice_raw_ready_prio_stage.
    unfold mutex_del_free_state_after__g05_always_loop.
    cbn [IntrState TskState SchedState EventState TickState].
    rewrite <- Hsched.
    cancel.
    sepcon_assoc_change.
    cancel.
  - apply derivable1s_coq_prop_r. exact Hpostvalid.
Qed.
Lemma mutex_del_current_owner_restored_total__g05_always_loop :
  forall sg initial entry eid owner_post current m,
    entry.(EventState).(inUsedEventStates) eid = Some initial ->
    initial.(eventType) = OS_EVENT_TYPE_MUTEX ->
    initial.(mutexFields) = Some m ->
    mutex_del_owner_entry_consistency_prop sg initial entry ->
    mutex_del_rdyatprio_stage_prop sg initial entry owner_post ->
    mutex_del_wake_steps sg eid owner_post current ->
    match m.(mfOwner), m.(mfOwnerOrigPrio) with
    | None, None => True
    | Some owner, Some orig =>
        mutex_del_task_prio_observation__g05_always_loop
          current.(TskState) owner = Some orig
    | _, _ => False
    end.
Proof.
  intros sg initial entry eid owner_post current m Hused Htype Hfields
    Hentry_owner Hstage Hwakes.
  destruct (Z.eq_dec m.(mfPCP) sg.(osPrioMutexCeilDis))
    as [Hdisabled | Henabled].
  - pose proof Hentry_owner as Hentry_owner0.
    unfold mutex_del_owner_entry_consistency_prop in Hentry_owner0.
    destruct Hentry_owner0 as
      (m0 & Htype0 & Hfields0 & Hentry_owner0).
    rewrite Hfields in Hfields0. inversion Hfields0; subst m0.
    unfold mutex_del_rdyatprio_stage_prop,
      mutex_del_owner_restore_total in Hstage.
    destruct Hstage as (m0 & Htype1 & Hfields1 & Hshape & Hexec).
    rewrite Hfields in Hfields1. inversion Hfields1; subst m0.
    rewrite (proj2 (Z.eqb_eq _ _) Hdisabled) in Hexec.
    subst owner_post.
    destruct m.(mfOwner) as [owner|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
      simpl in Hentry_owner0 |- *.
    + destruct Hentry_owner0 as
        (entry_t & entry_orig & Hentry_lookup & Hentry_orig & Hentry_prio).
      inversion Hentry_orig; subst entry_orig.
      rewrite (mutex_del_wake_steps_prio_observation__g05_always_loop
        sg eid entry current owner Hwakes).
      unfold mutex_del_task_prio_observation__g05_always_loop.
      rewrite Hentry_lookup.
      destruct Hentry_prio as [Horig_prio | [Hnot_disabled Hpcp_prio]].
      * rewrite Horig_prio. reflexivity.
      * contradiction.
    + contradiction.
    + contradiction.
    + exact I.
  - eapply mutex_del_current_owner_restored__g05_always_loop; eauto.
Qed.
Lemma mutex_del_selected_pcp_case__g05_always_loop :
  forall sg current eid selected m pcp,
    valid_stable_glob_vars sg ->
    UCOS2_verification_slice_state_inv sg current ->
    current.(EventState).(inUsedEventStates) eid = Some selected ->
    selected.(eventType) = OS_EVENT_TYPE_MUTEX ->
    selected.(mutexFields) = Some m ->
    m.(mfPCP) = pcp ->
    pcp = sg.(osPrioMutexCeilDis) \/
    Ucos2Verify.lib.array_abstraction.priotbl_index_in_range pcp.
Proof.
  intros sg current eid selected m pcp Hstable Hvalid Hlookup Htype
    Hfields Hpcp.
  unfold UCOS2_verification_slice_state_inv in Hvalid.
  destruct Hvalid as [_ [_ [_ Hcross]]].
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as
    [_ [_ [_ [_ [_ [_ [_ [_ [Hprotocol _]]]]]]]]].
  specialize (Hprotocol eid selected m Hlookup Htype Hfields).
  destruct Hprotocol as [Hvalid_pcp _].
  unfold valid_mutex_pcp in Hvalid_pcp.
  rewrite Hpcp in Hvalid_pcp.
  destruct Hvalid_pcp as [Hdisabled | Hrange].
  - left. exact Hdisabled.
  - right.
    unfold Ucos2Verify.lib.array_abstraction.priotbl_index_in_range,
      OS_PRIO_TBL_SIZE.
    unfold valid_stable_glob_vars in Hstable.
    lia.
Qed.
Lemma mutex_del_task_raw_rep_after_pcp_release_total__g05_always_loop :
  forall sg st pcp,
    (pcp = sg.(osPrioMutexCeilDis) \/
     Ucos2Verify.lib.array_abstraction.priotbl_index_in_range pcp) ->
    (if Z.eqb pcp sg.(osPrioMutexCeilDis)
     then verification_slice_task_inv sg st
     else priotbl_element_store sg.(g_OSTCBPrioTbl) pcp 0 **
          verification_slice_task_inv_missing_priotbl sg st pcp) |--
    verification_slice_task_raw_rep sg
      (mutex_del_free_task_after__g05_always_loop sg pcp st).
Proof.
  intros sg st pcp Hcase.
  destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - unfold mutex_del_free_task_after__g05_always_loop.
    cbn. rewrite Hdisabled. cbn.
    unfold verification_slice_task_inv, verification_slice_task_raw_rep.
    pureIntros.
    destruct st; cbn in *.
    cancel.
  - destruct Hcase as [Heq | Hrange].
    + apply Z.eqb_neq in Hdisabled. contradiction.
    + pose proof
        (mutex_del_task_raw_rep_after_pcp_release__g05_always_loop
          sg st pcp Hrange) as Hraw.
      rewrite Hdisabled in Hraw.
      exact Hraw.
Qed.
Lemma mutex_del_pcp_release_focus_raw_components_total__g05_always_loop :
  forall sg anchor current eid pcp,
    (pcp = sg.(osPrioMutexCeilDis) \/
     Ucos2Verify.lib.array_abstraction.priotbl_index_in_range pcp) ->
    verification_slice_task_validity sg current.(TskState) ->
    verification_slice_event_in_range
      sg current.(TskState) current.(EventState) ->
    mutex_del_pcp_release_focus sg anchor current eid pcp |--
    Ucos2Verify.lib.interrupt.interrupt_inv sg current.(IntrState) **
    verification_slice_task_raw_rep sg
      (mutex_del_free_task_after__g05_always_loop
         sg pcp current.(TskState)) **
    verification_slice_sched_raw_ready_prio_stage
      sg anchor.(SchedState) current.(SchedState) current.(TskState) **
    store_used_event_map_raw_missing_i
      sg current.(TskState)
      current.(EventState).(inUsedEventStates) eid **
    store_free_event_nodes sg current.(EventState).(unUsedEventStates) **
    Ucos2Verify.lib.tick.verification_slice_tick_inv sg current.(TickState) ** TT.
Proof.
  intros sg anchor current eid pcp Hcase Htask Hevent.
  unfold mutex_del_pcp_release_focus.
  destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - unfold mutex_del_event_ready_focus_inv.
    pose proof
      (mutex_del_task_raw_rep_after_pcp_release_total__g05_always_loop
        sg current.(TskState) pcp Hcase) as Htaskraw.
    rewrite Hdisabled in Htaskraw.
    sep_apply_l_atomic Htaskraw.
    unfold mutex_del_event_inv_no_eid_no_free_head.
    pureIntros.
    sep_apply_l_atomic
      (mutex_del_event_missing_stable_to_raw__g05_always_loop
        sg current.(TskState) current.(EventState) eid Htask Hevent).
    cancel.
  - unfold mutex_del_event_missing_priotbl_focus.
    pose proof
      (mutex_del_task_raw_rep_after_pcp_release_total__g05_always_loop
        sg current.(TskState) pcp Hcase) as Htaskraw.
    rewrite Hdisabled in Htaskraw.
    sep_apply_l_atomic Htaskraw.
    unfold mutex_del_event_inv_no_eid_no_free_head.
    pureIntros.
    sep_apply_l_atomic
      (mutex_del_event_missing_stable_to_raw__g05_always_loop
        sg current.(TskState) current.(EventState) eid Htask Hevent).
    cancel.
Qed.
Lemma mutex_del_free_transition_rep_total__g05_always_loop :
  forall sg anchor current eid pcp selected base
         type_addr ptr_addr cnt_addr grp_addr tbl_addr
         free_addr free_head,
    (pcp = sg.(osPrioMutexCeilDis) \/
     Ucos2Verify.lib.array_abstraction.priotbl_index_in_range pcp) ->
    selected.(waitList) = [] ->
    base = event_addr sg eid ->
    event_core_fields_layout_prop
      sg eid type_addr ptr_addr cnt_addr ->
    event_wait_fields_layout_prop sg eid grp_addr tbl_addr ->
    os_event_free_list_addr sg free_addr ->
    event_free_list_head_prop sg current.(EventState) free_head ->
    UCOS2_verification_slice_state_inv sg current ->
    UCOS2_verification_slice_state_inv sg
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current) ->
    mutex_del_pcp_release_focus sg anchor current eid pcp **
    type_addr # UChar |-> 0 **
    ptr_addr # Ptr |-> free_head **
    used_event_wait_table_storage current.(TskState) base selected **
    free_addr # Ptr |-> base **
    cnt_addr # UShort |-> 0 **
    grp_addr # UChar |-> 0 |--
    mutex_del_transition_rep sg anchor
      (mutex_del_free_state_after__g05_always_loop
         sg eid pcp current).
Proof.
  intros sg anchor current eid pcp selected base
    type_addr ptr_addr cnt_addr grp_addr tbl_addr
    free_addr free_head Hcase Hempty Hbase Hcore Hwait
    Hfreeaddr Hfreehead Hvalid Hpostvalid.
  pose proof Hvalid as Hvalid0.
  unfold UCOS2_verification_slice_state_inv in Hvalid0.
  destruct Hvalid0 as [Htask [_ [Hevent _]]].
  unfold os_event_free_list_addr in Hfreeaddr.
  unfold event_free_list_head_prop in Hfreehead.
  subst base; subst free_addr; subst free_head.
  sep_apply_l_atomic
    (mutex_del_pcp_release_focus_raw_components_total__g05_always_loop
      sg anchor current eid pcp Hcase Htask Hevent).
  sep_apply_l_atomic
    (mutex_del_freed_event_cells_from_storage__g05_always_loop
      sg current eid selected (event_addr sg eid)
      type_addr ptr_addr cnt_addr grp_addr tbl_addr
      (free_event_head sg current.(EventState).(unUsedEventStates))
      Hempty eq_refl Hcore Hwait eq_refl).
  sep_apply_l_atomic
    (mutex_del_freed_event_raw_rep_merge__g05_always_loop
      sg current eid pcp).
  assert (Hsched :
    verification_slice_sched_raw_ready_prio_stage
      sg anchor.(SchedState) current.(SchedState) current.(TskState) =
    verification_slice_sched_raw_ready_prio_stage
      sg anchor.(SchedState) current.(SchedState)
      (mutex_del_free_task_after__g05_always_loop
         sg pcp current.(TskState))).
  {
    apply mutex_del_sched_raw_ready_task_ext__g05_always_loop.
    reflexivity.
  }
  unfold mutex_del_transition_rep.
  Right.
  apply _derivable1_andp_intros.
  - Right.
    unfold UCOS2_verification_slice_raw_ready_prio_stage.
    unfold mutex_del_free_state_after__g05_always_loop.
    cbn [IntrState TskState SchedState EventState TickState].
    rewrite <- Hsched.
    cancel.
    sepcon_assoc_change.
    cancel.
  - apply derivable1s_coq_prop_r. exact Hpostvalid.
Qed.
Lemma mutex_del_success_commit_pack__g05_always_loop :
  forall sg initial entry eid opt pevent tasks_waiting X
         critical_anchor commit,
    mutex_del_success_commit_anchor_prop
      sg initial entry eid opt critical_anchor commit ->
    mutex_del_source_entry_prop
      sg initial entry eid pevent tasks_waiting ->
    mutex_del_success_mode_prop opt tasks_waiting ->
    safeExec
      (LastSeen entry)
      (bind (atomic_cmd (OSMutexDel_full_sem sg pevent opt))
            (mutex_del_observe_ptr pevent)) X ->
    Ucos2Verify.lib.ucos2_rules_lib.InsideCritical sg critical_anchor **
    mutex_del_transition_rep sg entry commit |--
    mutex_del_success_commit_inv
      sg initial entry eid opt pevent tasks_waiting X.
Proof.
  intros sg initial entry eid opt pevent tasks_waiting X
    critical_anchor commit Hcommit Hsource Hmode Hsafe.
  unfold mutex_del_success_commit_inv.
  Exists critical_anchor commit.
  apply sepcon_cancel_end.
  - cancel.
  - apply derivable1s_coq_prop_r.
    exact (conj Hcommit (conj Hsource (conj Hmode Hsafe))).
Qed.
Lemma mutex_del_decode_pcp_encode__g05_always_loop :
  forall pcp low,
    0 <= pcp < 256 ->
    0 <= low < 256 ->
    decode_PCP_from_cnt (pcp * 256 + low) = pcp.
Proof.
  intros pcp low Hpcp Hlow.
  unfold decode_PCP_from_cnt.
  rewrite Z.shiftr_div_pow2 by lia.
  cbn.
  rewrite Z.add_comm, Z.div_add by lia.
  rewrite Z.div_small by lia.
  rewrite Z.add_0_l.
  apply unsigned_last_nbits_eq.
  cbn. lia.
Qed.
Lemma mutex_snapshot_pcp_lt64__g05_always_loop :
  forall sg ls eid e m etype ecnt eptr egrp etbl,
    valid_stable_glob_vars sg ->
    verification_slice_cross_module_consistency sg ls ->
    event_snapshot_of_prop
      sg ls.(TskState) ls.(EventState) eid e
      etype ecnt eptr egrp etbl ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    decode_PCP_from_cnt ecnt <> 255 ->
    0 <= decode_PCP_from_cnt ecnt < 64.
Proof.
  intros sg ls eid e m etype ecnt eptr egrp etbl
    Hvalid Hcross Hsnapshot Htype Hfields Henabled.
  pose proof Hsnapshot as Hsnapshot0.
  unfold event_snapshot_of_prop in Hsnapshot0.
  destruct Hsnapshot0 as
    (Hlookup & Hencoded_type & Hcnt & Hptr & Hgrp & Htbl).
  unfold verification_slice_cross_module_consistency in Hcross.
  destruct Hcross as
    (Hcur & Hprio & Howners & Hwait & Hready_complete & Hready_order &
     Hceiling_free & Hunique & Hprotocol & Hpcp_unique).
  specialize (Hprotocol eid e m Hlookup Htype Hfields).
  destruct Hprotocol as (Hpcp & Hshape & Hslot).
  unfold valid_stable_glob_vars in Hvalid.
  destruct Hvalid as
    (Hmax_events & Hmax_qs & Hmax_tasks & Hnsys & Hlow_range & Hlowest &
     Hidle & Hstat & Hceil & Hself & Hrdy_size & Hevent_size & Haddresses).
  destruct m.(mfOwner) as [owner|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hshape.
  - destruct Hshape as (Horig_range & Horig_ne).
    unfold encode_event_cnt_value in Hcnt.
    rewrite Htype, Hfields, Howner, Horig in Hcnt. simpl in Hcnt.
    assert (Hdecode : decode_PCP_from_cnt ecnt = m.(mfPCP)).
    {
      rewrite Hcnt.
      apply mutex_del_decode_pcp_encode__g05_always_loop.
      - destruct Hpcp as [Hdisabled | Hpcp_range].
        + rewrite Hdisabled, Hceil. lia.
        + rewrite Hlowest in Hpcp_range. lia.
      - unfold valid_task_prio in Horig_range.
        rewrite Hlowest in Horig_range. lia.
    }
    rewrite Hdecode in Henabled |- *.
    destruct Hpcp as [Hdisabled | Hpcp_range].
    + rewrite Hdisabled, Hceil in Henabled. contradiction.
    + rewrite Hlowest in Hpcp_range. lia.
  - contradiction.
  - contradiction.
  - unfold encode_event_cnt_value in Hcnt.
    rewrite Htype, Hfields, Howner, Horig in Hcnt. simpl in Hcnt.
    assert (Hdecode : decode_PCP_from_cnt ecnt = m.(mfPCP)).
    {
      rewrite Hcnt.
      apply mutex_del_decode_pcp_encode__g05_always_loop.
      - destruct Hpcp as [Hdisabled | Hpcp_range].
        + rewrite Hdisabled, Hceil. lia.
        + rewrite Hlowest in Hpcp_range. lia.
      - lia.
    }
    rewrite Hdecode in Henabled |- *.
    destruct Hpcp as [Hdisabled | Hpcp_range].
    + rewrite Hdisabled, Hceil in Henabled. contradiction.
    + rewrite Hlowest in Hpcp_range. lia.
Qed.
Lemma mutex_del_ucos2_inv_int_nesting_byte_range__g06_exit_observation :
  forall sg ls,
    UCOS2_verification_slice_inv sg ls |--
      UCOS2_verification_slice_inv sg ls &&
      coq_prop (0 <= intNesting (IntrState ls) <= 255).
Proof.
  intros sg ls.
  apply _derivable1_andp_intros.
  - cancel (UCOS2_verification_slice_inv sg ls).
  - unfold UCOS2_verification_slice_inv, interrupt_inv,
      interrupt_in_range, store_int_state.
    pureIntros.
    prop_apply_p
      (store_uchar_range
         (g_OSIntNesting sg) (intNesting (IntrState ls))).
    Intros_p Hrange.
    dump_pre_spatial.
    exact Hrange.
Qed.
(** The mask cleared by Mutex Delete accounts for every non-suspension
    bit of a linked single waiter.  Zero also covers timeout cleanup.
    This is a caller protocol fact, not an execution guard. *)
Definition mutex_waiters_status_consistent
  (tasks : Glob_TaskAbstractState) (waiters : list TaskID) : Prop :=
  forall tid t,
    In tid waiters ->
    tasks.(inUsedTaskStates) tid = Some t ->
    task_non_suspension_bits t.(stat) = task_pend_mask PendMutex \/
    task_non_suspension_bits t.(stat) = 0.

Lemma mutex_waiters_status_from_event_wait_entry :
  forall sg tasks eid e,
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    event_wait_entry_consistency sg tasks eid e ->
    mutex_waiters_status_consistent tasks e.(waitList).
Proof.
  intros sg tasks eid e Htype [_ Hentry] tid t Hin Hget.
  rewrite Htype in Hentry; cbn in Hentry.
  destruct (Hentry tid Hin) as [found [Hfound [_ [_ Hphase]]]].
  assert (Heq : found = t) by congruence; subst found.
  unfold task_linked_wait_phase in Hphase.
  destruct Hphase as [Hpending | [Hzero _]]; [left | right]; assumption.
Qed.

Lemma mutex_waiters_status_from_verification_slice_event_validity :
  forall sg tasks events eid e,
    verification_slice_event_in_range sg tasks events ->
    events.(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    mutex_waiters_status_consistent tasks e.(waitList).
Proof.
  intros sg tasks events eid e Hvalid Hget Htype.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ Hentries]]]]]]].
  eapply mutex_waiters_status_from_event_wait_entry; [exact Htype |].
  apply event_wait_active_implies_linked.
  exact (Hentries eid e Hget).
Qed.

Lemma mutex_del_wake_step_advances_waiter_effect__g06_exit_observation :
  forall sg eid pre post e m tid,
    pre.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_wake_step sg eid pre post ->
    mutex_waiters_status_consistent pre.(TskState) e.(waitList) ->
    (In tid e.(waitList) \/
     (~ In tid e.(waitList) /\
      exists t,
        pre.(TskState).(inUsedTaskStates) tid = Some t /\
        (task_non_suspension_bits t.(stat)) = 0 /\
        t.(statPend) = PendAbort /\
        t.(dly) = 0 /\
        t.(eventPtr) = None /\
        ((task_is_suspended t.(stat)) = false ->
         In tid pre.(SchedState).(readyList)))) ->
    exists e',
      post.(EventState).(inUsedEventStates) eid = Some e' /\
      e'.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e'.(mutexFields) = Some m /\
      mutex_waiters_status_consistent post.(TskState) e'.(waitList) /\
      (In tid e'.(waitList) \/
       (~ In tid e'.(waitList) /\
        exists t,
          post.(TskState).(inUsedTaskStates) tid = Some t /\
          (task_non_suspension_bits t.(stat)) = 0 /\
          t.(statPend) = PendAbort /\
          t.(dly) = 0 /\
          t.(eventPtr) = None /\
          ((task_is_suspended t.(stat)) = false ->
           In tid post.(SchedState).(readyList)))).
Proof.
  intros sg eid pre post e m tid Hget Htype Hfields Hstep Hwaiters Hstatus.
  unfold mutex_del_wake_step, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hstep.
  destruct Hstep as
    (returned_prio & canonical_waiter & table_owner & Hsame &
     e1 & e2 & canonical_t & table_t & table_t' & Hevent & Hpend &
     Hnonempty & Hcanonical & Hcanonical_get & Hreturned & Hslot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hpost).
  assert (He1 : e1 = e) by congruence.
  subst e1.
  subst canonical_waiter.
  assert (Hselected_in : In table_owner e.(waitList)).
  { rewrite Hcanonical.
    destruct e.(waitList) as [| h tl]; simpl in *; contradiction || auto. }
  cbv zeta in Hpost.
  subst post.
  subst e2.
  assert (Hcleared : task_non_suspension_bits table_t'.(stat) = 0).
  { rewrite Htable_t'.
    change (task_non_suspension_bits
      (task_clear_pending_status table_t.(stat) PendMutex) = 0).
    destruct (Hwaiters table_owner table_t Hselected_in Htable_get)
      as [Hpending | Hzero].
    - apply task_clear_pending_status_same_kind; exact Hpending.
    - rewrite task_clear_pending_status_none by exact Hzero.
      exact Hzero. }
  exists
    {| eventGeneration := e.(eventGeneration);
       eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
       eventType := e.(eventType);
       mutexFields := e.(mutexFields);
       semFields := e.(semFields);
       mboxFields := e.(mboxFields);
       queueFields := e.(queueFields);
       waitList :=
         Ucos2Verify.lib.helpers.remove_Z_eqb table_owner e.(waitList) |}.
  cbn.
  rewrite Z.eqb_refl.
  split; [reflexivity |].
  split; [exact Htype |].
  split; [exact Hfields |].
  split.
  { intros other found Hin Hlookup.
    cbn in Hlookup.
    assert (Hneq : other <> table_owner).
    { intro Heq; subst other.
      exact (Ucos2Verify.lib.helpers.remove_Z_eqb_notin
        table_owner e.(waitList) Hin). }
    rewrite (proj2 (Z.eqb_neq other table_owner) Hneq) in Hlookup.
    apply (Hwaiters other found).
    - eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in; exact Hin.
    - exact Hlookup. }
  destruct Hstatus as [Hin | [Hnin Heffect]].
  - destruct (Z.eq_dec tid table_owner) as [Heq | Hneq].
    + subst tid.
      right.
      split.
      * exact
          (Ucos2Verify.lib.helpers.remove_Z_eqb_notin
             table_owner e.(waitList)).
      * exists table_t'.
        rewrite Z.eqb_refl.
        split; [reflexivity |].
        split; [exact Hcleared |].
        split; [rewrite Htable_t'; reflexivity |].
        split; [rewrite Htable_t'; reflexivity |].
        split; [rewrite Htable_t'; reflexivity |].
        intro Hnot_suspended.
        rewrite Hnot_suspended.
        apply (proj2
          (Ucos2Verify.lib.helpers.insert_sorted_by_in
             Z
             (fun tid0 : Z =>
                match pre.(TskState).(inUsedTaskStates) tid0 with
                | Some task => task.(curPrio)
                | None => sg.(osLowestPrio) + 1
                end)
             table_owner
             table_owner
             (Ucos2Verify.lib.helpers.remove_Z_eqb
                table_owner pre.(SchedState).(readyList)))).
        left. reflexivity.
    + left.
      eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in_neq;
        eassumption.
  - right.
    split.
    + intro Hin_post.
      apply Hnin.
      eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in.
      exact Hin_post.
    + destruct Heffect as
        [t [Htask [Hpend_none [Habort [Hdly [Hevent_none Hready]]]]]].
      exists t.
      assert (Hneq : tid <> table_owner).
      { intro Heq. subst tid. contradiction. }
      assert (Heqb : Z.eqb tid table_owner = false).
      { apply Z.eqb_neq. exact Hneq. }
      rewrite Heqb.
      split; [exact Htask |].
      split; [exact Hpend_none |].
      split; [exact Habort |].
      split; [exact Hdly |].
      split; [exact Hevent_none |].
      intro Hnot_suspended.
      specialize (Hready Hnot_suspended).
      destruct (task_is_suspended table_t'.(stat)) eqn:Hselected_suspended.
      * exact Hready.
      * apply (proj2
          (Ucos2Verify.lib.helpers.insert_sorted_by_in
             Z
             (fun tid0 : Z =>
                match pre.(TskState).(inUsedTaskStates) tid0 with
                | Some task => task.(curPrio)
                | None => sg.(osLowestPrio) + 1
                end)
             table_owner
             tid
             (Ucos2Verify.lib.helpers.remove_Z_eqb
                table_owner pre.(SchedState).(readyList)))).
        right.
        eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in_neq;
          eassumption.
Qed.
Lemma mutex_del_wake_steps_track_waiter_effect__g06_exit_observation :
  forall sg eid pre post e m tid,
    pre.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_wake_steps sg eid pre post ->
    mutex_waiters_status_consistent pre.(TskState) e.(waitList) ->
    In tid e.(waitList) ->
    exists e',
      post.(EventState).(inUsedEventStates) eid = Some e' /\
      e'.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e'.(mutexFields) = Some m /\
      mutex_waiters_status_consistent post.(TskState) e'.(waitList) /\
      (In tid e'.(waitList) \/
       (~ In tid e'.(waitList) /\
        exists t,
          post.(TskState).(inUsedTaskStates) tid = Some t /\
          (task_non_suspension_bits t.(stat)) = 0 /\
          t.(statPend) = PendAbort /\
          t.(dly) = 0 /\
          t.(eventPtr) = None /\
          ((task_is_suspended t.(stat)) = false ->
           In tid post.(SchedState).(readyList)))).
Proof.
  intros sg eid pre post e m tid Hget Htype Hfields Hsteps Hwaiters Hin.
  revert e m tid Hget Htype Hfields Hwaiters Hin.
  induction Hsteps as [s | s0 s1 s2 Hprefix IH Hlast];
    intros e m tid Hget Htype Hfields Hwaiters Hin.
  - exists e.
    split; [exact Hget |].
    split; [exact Htype |].
    split; [exact Hfields |].
    split; [exact Hwaiters |].
    left. exact Hin.
  - destruct (IH e m tid Hget Htype Hfields Hwaiters Hin) as
      [e1 [Hget1 [Htype1 [Hfields1 [Hwaiters1 Hstatus1]]]]].
    eapply
      mutex_del_wake_step_advances_waiter_effect__g06_exit_observation;
      eassumption.
Qed.
Lemma mutex_del_wake_steps_complete_waiter_effect__g06_exit_observation :
  forall sg eid pre post e m final_e,
    pre.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_wake_steps sg eid pre post ->
    mutex_waiters_status_consistent pre.(TskState) e.(waitList) ->
    post.(EventState).(inUsedEventStates) eid = Some final_e ->
    final_e.(waitList) = nil ->
    mutex_del_waiters_aborted_effective_prop
      e post.(TskState) post.(SchedState).
Proof.
  intros sg eid pre post e m final_e Hget Htype Hfields Hsteps Hwaiters
    Hfinal_get Hfinal_empty.
  unfold mutex_del_waiters_aborted_effective_prop.
  intros tid Hin.
  destruct
    (mutex_del_wake_steps_track_waiter_effect__g06_exit_observation
       sg eid pre post e m tid Hget Htype Hfields Hsteps Hwaiters Hin)
    as [e' [Hget' [Htype' [Hfields' [_ Hstatus]]]]].
  assert (Heq : e' = final_e) by congruence.
  subst e'.
  destruct Hstatus as [Hstill | [Hnot_still Heffect]].
  - rewrite Hfinal_empty in Hstill. contradiction.
  - exact Heffect.
Qed.
Lemma mutex_del_wait_grp_zero_iff_empty__g06_exit_observation :
  forall sg tskSt wl,
    Ucos2Verify.lib.event_wait.event_waitList_canonical sg tskSt wl ->
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
Lemma mutex_del_ucos2_inv_event_validity__g06_exit_observation :
  forall sg ls,
    UCOS2_verification_slice_inv sg ls |--
      UCOS2_verification_slice_inv sg ls &&
      coq_prop
        (verification_slice_event_in_range sg ls.(TskState) ls.(EventState)).
Proof.
  intros sg ls.
  apply _derivable1_andp_intros.
  - cancel (UCOS2_verification_slice_inv sg ls).
  - unfold UCOS2_verification_slice_inv, verification_slice_event_inv.
    pureIntros.
    dump_pre_spatial.
    assumption.
Qed.
Lemma mutex_del_atomic_task_set_curPrio_sets_lookup__g06_exit_observation :
  forall sg tid prio pre post,
    atomic_task_set_curPrio sg tid prio pre tt post ->
    exists t,
      post.(TskState).(inUsedTaskStates) tid = Some t /\
      t.(curPrio) = prio.
Proof.
  intros sg tid prio pre post Hstep.
  unfold atomic_task_set_curPrio in Hstep.
  destruct Hstep as [Hready | [Hwaiting | Hdormant]].
  - unfold atomic_task_set_curPrio_ready in Hready.
    destruct Hready as
      (t & oldPrio & t' & Hin & Hget & Hold & Hneq & Hlo & Hhi &
       Hslot & Ht' & Hpost).
    cbv zeta in Hpost.
    subst post.
    cbn.
    rewrite Z.eqb_refl.
    exists t'.
    split; [reflexivity |].
    subst t'.
    reflexivity.
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
       evSt2 & pty & Hnot_ready & Hget & Hold & Hneq & Hlo & Hhi &
       Hslot & Hpend & Hevent & Hmulti & Hwait_get & Hwait_type & Hin &
       Ht' & Htsk & Hwait' & Hev & Hpost).
    subst post.
    subst tskSt2.
    cbn.
    rewrite Z.eqb_refl.
    exists t'.
    split; [reflexivity |].
    subst t'.
    reflexivity.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Hget & Hold & Hneq &
       Hlo & Hhi & Hslot & Hevent & Hmulti & Hnot_effective & Ht' &
       Htsk & Hpost).
    subst post.
    subst tskSt2.
    cbn.
    rewrite Z.eqb_refl.
    exists t'.
    split; [reflexivity |].
    subst t'.
    reflexivity.
Qed.
Lemma mutex_del_owner_stage_restores__g06_exit_observation :
  forall sg e entry owner_post,
    mutex_del_owner_entry_consistency_prop sg e entry ->
    mutex_del_rdyatprio_stage_prop sg e entry owner_post ->
    mutex_del_owner_restored_prop e owner_post.(TskState).
Proof.
  intros sg e entry owner_post Hentry Hstage.
  unfold mutex_del_owner_entry_consistency_prop in Hentry.
  destruct Hentry as [m [Htype [Hfields Hentry_owner]]].
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as [m' [Htype' [Hfields' [Hshape Hexec]]]].
  assert (Hm : m' = m) by congruence.
  subst m'.
  unfold mutex_del_owner_restored_prop.
  exists m.
  split; [exact Htype |].
  split; [exact Hfields |].
  destruct m.(mfOwner) as [owner|] eqn:Howner;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Hentry_owner, Hshape, Hexec |- *.
  - destruct Hentry_owner as
      (entry_t & op & Hget & Hop & Hprio).
    inversion Hop; subst op.
    destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis))
      eqn:Hdisabled.
    + subst owner_post.
      exists entry_t.
      split; [exact Hget |].
      destruct Hprio as [Hprio | [Henabled Hprio]].
      * exact Hprio.
      * apply Z.eqb_eq in Hdisabled. contradiction.
    + destruct Hexec as [stage_t [Hstage_get Hexec]].
      assert (Hstage_t : stage_t = entry_t) by congruence.
      subst stage_t.
      destruct (Z.eqb entry_t.(curPrio) m.(mfPCP))
        eqn:Hcurrent.
      * destruct
          (mutex_del_atomic_task_set_curPrio_sets_lookup__g06_exit_observation
             sg owner orig entry owner_post Hexec)
          as [post_t [Hpost_get Hpost_prio]].
        exists post_t.
        split; assumption.
      * subst owner_post.
        exists entry_t.
        split; [exact Hget |].
        destruct Hprio as [Hprio | [Henabled Hprio]].
        -- exact Hprio.
        -- apply Z.eqb_neq in Hcurrent.
           contradiction.
  - contradiction.
  - contradiction.
  - exact I.
Qed.
Lemma mutex_del_wake_step_preserves_lookup_prio__g06_exit_observation :
  forall sg eid pre post tid t,
    mutex_del_wake_step sg eid pre post ->
    pre.(TskState).(inUsedTaskStates) tid = Some t ->
    exists t',
      post.(TskState).(inUsedTaskStates) tid = Some t' /\
      t'.(curPrio) = t.(curPrio).
Proof.
  intros sg eid pre post tid t Hstep Hget.
  unfold mutex_del_wake_step, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hstep.
  destruct Hstep as
    (returned_prio & canonical_waiter & table_owner & Hsame &
     e1 & e2 & canonical_t & table_t & table_t' & Hevent & Hpend &
     Hnonempty & Hcanonical & Hcanonical_get & Hreturned & Hslot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hpost).
  cbv zeta in Hpost.
  subst post.
  cbn.
  destruct (Z.eqb tid table_owner) eqn:Htid.
  - apply Z.eqb_eq in Htid.
    subst tid.
    assert (Ht : t = table_t) by congruence.
    subst t.
    exists table_t'.
    split; [reflexivity |].
    subst table_t'.
    reflexivity.
  - exists t.
    split; [exact Hget | reflexivity].
Qed.
Lemma mutex_del_wake_step_preserves_owner_restored__g06_exit_observation :
  forall sg eid e pre post,
    mutex_del_owner_restored_prop e pre.(TskState) ->
    mutex_del_wake_step sg eid pre post ->
    mutex_del_owner_restored_prop e post.(TskState).
Proof.
  intros sg eid e pre post Hrestored Hstep.
  unfold mutex_del_owner_restored_prop in Hrestored |- *.
  destruct Hrestored as [m [Htype [Hfields Howner]]].
  exists m.
  split; [exact Htype |].
  split; [exact Hfields |].
  destruct m.(mfOwner) as [owner|] eqn:Howner_id;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Howner |- *; try contradiction; try exact I.
  destruct Howner as [owner_t [Hget Hprio]].
  destruct
    (mutex_del_wake_step_preserves_lookup_prio__g06_exit_observation
       sg eid pre post owner owner_t Hstep Hget)
    as [post_t [Hpost_get Hpost_prio]].
  exists post_t.
  split; [exact Hpost_get |].
  rewrite Hpost_prio.
  exact Hprio.
Qed.
Lemma mutex_del_wake_steps_preserves_owner_restored__g06_exit_observation :
  forall sg eid e pre post,
    mutex_del_owner_restored_prop e pre.(TskState) ->
    mutex_del_wake_steps sg eid pre post ->
    mutex_del_owner_restored_prop e post.(TskState).
Proof.
  intros sg eid e pre post Hrestored Hsteps.
  induction Hsteps as [s | s0 s1 s2 Hprefix IH Hlast].
  - exact Hrestored.
  - eapply
      mutex_del_wake_step_preserves_owner_restored__g06_exit_observation.
    + apply IH. exact Hrestored.
    + exact Hlast.
Qed.
Lemma mutex_del_atomic_task_set_curPrio_preserves_selected_mutex__g06_exit_observation :
  forall sg tid prio pre post eid e m,
    pre.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    atomic_task_set_curPrio sg tid prio pre tt post ->
    exists e',
      post.(EventState).(inUsedEventStates) eid = Some e' /\
      e'.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e'.(mutexFields) = Some m.
Proof.
  intros sg tid prio pre post eid e m Hget Htype Hfields Hstep.
  unfold atomic_task_set_curPrio in Hstep.
  destruct Hstep as [Hready | [Hwaiting | Hdormant]].
  - unfold atomic_task_set_curPrio_ready in Hready.
    destruct Hready as
      (t & oldPrio & t' & Hin & Htask & Hold & Hneq & Hlo & Hhi &
       Hslot & Ht' & Hpost).
    cbv zeta in Hpost.
    subst post.
    exists e.
    repeat split; assumption.
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
       evSt2 & pty & Hnot_ready & Htask & Hold & Hneq & Hlo & Hhi &
       Hslot & Hpend & Hevent & Hmulti & Hwait_get & Hwait_type & Hin &
       Ht' & Htsk & Hwait' & Hev & Hpost).
    subst post.
    subst evSt2.
    cbn.
    destruct (Z.eqb eid wait_eid) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      subst wait_eid.
      assert (He : wait_e = e) by congruence.
      subst wait_e.
      exists wait_e'.
      split; [reflexivity |].
      subst wait_e'.
      cbn.
      split; assumption.
    + exists e.
      repeat split; assumption.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask & Hold & Hneq &
       Hlo & Hhi & Hslot & Hevent & Hmulti & Hnot_effective & Ht' &
       Htsk & Hpost).
    subst post.
    exists e.
    repeat split; assumption.
Qed.
Lemma mutex_del_owner_stage_preserves_selected_mutex__g06_exit_observation :
  forall sg e entry owner_post eid m,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_rdyatprio_stage_prop sg e entry owner_post ->
    exists e',
      owner_post.(EventState).(inUsedEventStates) eid = Some e' /\
      e'.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e'.(mutexFields) = Some m.
Proof.
  intros sg e entry owner_post eid m Hget Htype Hfields Hstage.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as [m' [Htype' [Hfields' [Hshape Hexec]]]].
  assert (Hm : m' = m) by congruence.
  subst m'.
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis))
    eqn:Hdisabled.
  - subst owner_post.
    exists e.
    repeat split; assumption.
  - destruct m.(mfOwner) as [owner|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
      simpl in Hshape, Hexec.
    + destruct Hexec as [owner_t [Howner_get Hexec]].
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Hprio.
      * eapply
          mutex_del_atomic_task_set_curPrio_preserves_selected_mutex__g06_exit_observation;
          eassumption.
      * subst owner_post.
        exists e.
        repeat split; assumption.
    + contradiction.
    + contradiction.
    + subst owner_post.
      exists e.
      repeat split; assumption.
Qed.
Lemma mutex_del_wake_step_preserves_selected_mutex__g06_exit_observation :
  forall sg eid pre post e m,
    pre.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_wake_step sg eid pre post ->
    exists e',
      post.(EventState).(inUsedEventStates) eid = Some e' /\
      e'.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e'.(mutexFields) = Some m.
Proof.
  intros sg eid pre post e m Hget Htype Hfields Hstep.
  unfold mutex_del_wake_step, atomic_event_task_rdy,
    atomic_event_task_rdy_one in Hstep.
  destruct Hstep as
    (returned_prio & canonical_waiter & table_owner & Hsame &
     e1 & e2 & canonical_t & table_t & table_t' & Hevent & Hpend &
     Hnonempty & Hcanonical & Hcanonical_get & Hreturned & Hslot &
     Htable_get & Htable_prio & Htable_t' & He2 & Hpost).
  assert (He : e1 = e) by congruence.
  subst e1.
  cbv zeta in Hpost.
  subst post.
  cbn.
  rewrite Z.eqb_refl.
  exists e2.
  split; [reflexivity |].
  subst e2.
  cbn.
  split; assumption.
Qed.
Lemma mutex_del_wake_steps_preserves_selected_mutex__g06_exit_observation :
  forall sg eid pre post e m,
    pre.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_wake_steps sg eid pre post ->
    exists e',
      post.(EventState).(inUsedEventStates) eid = Some e' /\
      e'.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e'.(mutexFields) = Some m.
Proof.
  intros sg eid pre post e m Hget Htype Hfields Hsteps.
  induction Hsteps as [s | s0 s1 s2 Hprefix IH Hlast].
  - exists e. repeat split; assumption.
  - destruct (IH Hget)
      as [e1 [Hget1 [Htype1 Hfields1]]].
    eapply
      mutex_del_wake_step_preserves_selected_mutex__g06_exit_observation;
      eassumption.
Qed.
Lemma mutex_del_owner_restored_inused_ext__g06_exit_observation :
  forall e st1 st2,
    (forall tid,
       st2.(inUsedTaskStates) tid = st1.(inUsedTaskStates) tid) ->
    mutex_del_owner_restored_prop e st1 ->
    mutex_del_owner_restored_prop e st2.
Proof.
  intros e st1 st2 Hext Hrestored.
  unfold mutex_del_owner_restored_prop in Hrestored |- *.
  destruct Hrestored as [m [Htype [Hfields Howner]]].
  exists m.
  split; [exact Htype |].
  split; [exact Hfields |].
  destruct m.(mfOwner) as [owner|] eqn:Howner_id;
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
    simpl in Howner |- *; try contradiction; try exact I.
  destruct Howner as [owner_t [Hget Hprio]].
  exists owner_t.
  split; [rewrite Hext; exact Hget | exact Hprio].
Qed.
Lemma mutex_del_success_commit_public_facts__g06_exit_observation :
  forall sg e entry eid opt critical_anchor commit m,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_owner_entry_consistency_prop sg e entry ->
    mutex_del_success_commit_anchor_prop
      sg e entry eid opt critical_anchor commit ->
    mutex_del_owner_restored_prop e commit.(TskState) /\
    (m.(mfPCP) <> sg.(osPrioMutexCeilDis) ->
       prio_tbl_entry_prop commit.(TskState) m.(mfPCP) PTFree).
Proof.
  intros sg e entry eid opt critical_anchor commit m
    Hentry_get Htype Hfields Hentry_owner Hcommit.
  unfold mutex_del_success_commit_anchor_prop in Hcommit.
  destruct Hcommit as
    [owner_post [prepare [Howner_stage [Hmode [Hprepare Hfree]]]]].
  assert (Howner_restored :
    mutex_del_owner_restored_prop e owner_post.(TskState)).
  { eapply mutex_del_owner_stage_restores__g06_exit_observation;
      eassumption. }
  destruct
    (mutex_del_owner_stage_preserves_selected_mutex__g06_exit_observation
       sg e entry owner_post eid m Hentry_get Htype Hfields Howner_stage)
    as [owner_e [Howner_get [Howner_type Howner_fields]]].
  assert (Hcurrent_restored :
    mutex_del_owner_restored_prop e critical_anchor.(TskState)).
  { unfold mutex_del_mode_wake_prop in Hmode.
    destruct opt.
    - subst critical_anchor. exact Howner_restored.
    - eapply
        mutex_del_wake_steps_preserves_owner_restored__g06_exit_observation;
        eassumption.
    - contradiction. }
  assert (Hcurrent_selected : exists current_e,
    critical_anchor.(EventState).(inUsedEventStates) eid = Some current_e /\
    current_e.(eventType) = OS_EVENT_TYPE_MUTEX /\
    current_e.(mutexFields) = Some m).
  { unfold mutex_del_mode_wake_prop in Hmode.
    destruct opt.
    - subst critical_anchor.
      exists owner_e. repeat split; assumption.
    - eapply
        mutex_del_wake_steps_preserves_selected_mutex__g06_exit_observation;
        eassumption.
    - contradiction. }
  destruct Hcurrent_selected as
    [current_e [Hcurrent_get [Hcurrent_type Hcurrent_fields]]].
  unfold mutex_del_no_pend_prepare_stage_prop,
    mutex_del_no_pend_prepare in Hprepare.
  destruct Hprepare as
    (prepare_e & prepare_m & evSt2 & Hprepare_get & Hprepare_type &
     Hprepare_fields & Hempty & HevSt2 & Hprepare_post).
  assert (Hprepare_e : prepare_e = current_e) by congruence.
  subst prepare_e.
  assert (Hprepare_m : prepare_m = m) by congruence.
  subst prepare_m.
  unfold mutex_del_free_stage_prop,
    atomic_event_free_with_priotbl_free in Hfree.
  destruct Hfree as
    (free_e & free_m & free_evSt & free_tskSt & Hfree_get &
     Hfree_type & Hfree_fields & Hfree_owner & Hfree_empty &
     Hfree_evSt & Hfree_tskSt & Hcommit_post).
  subst prepare.
  subst evSt2.
  cbn in Hfree_get.
  rewrite Z.eqb_refl in Hfree_get.
  inversion Hfree_get; subst free_e.
  cbn in Hfree_fields.
  inversion Hfree_fields; subst free_m.
  subst commit.
  subst free_tskSt.
  split.
  - eapply
      mutex_del_owner_restored_inused_ext__g06_exit_observation.
    + intro tid. reflexivity.
    + exact Hcurrent_restored.
  - intro Henabled.
    unfold prio_tbl_entry_prop.
    cbn.
    apply Z.eqb_neq in Henabled.
    rewrite Henabled, Z.eqb_refl.
    reflexivity.
Qed.
Lemma mutex_del_exit_anchored_preserves_task__g06_exit_observation :
  forall sg critical_anchor commit exited,
    mutex_del_exit_critical_anchored_call_prop
      sg critical_anchor commit exited ->
    exited.(TskState) = commit.(TskState).
Proof.
  intros sg critical_anchor commit exited Hexit.
  unfold mutex_del_exit_critical_anchored_call_prop,
    crit_rel_intr_only in Hexit.
  destruct Hexit as [_ Hshape].
  rewrite Hshape.
  reflexivity.
Qed.
Lemma mutex_del_insert_remove_membership__g06_exit_observation :
  forall (key : Z -> Z) tid wl,
    In tid wl ->
    forall x,
      In x (Ucos2Verify.lib.helpers.insert_sorted_by key tid
        (Ucos2Verify.lib.helpers.remove_Z_eqb tid wl)) <->
      In x wl.
Proof.
  intros key tid wl Htid x.
  rewrite Ucos2Verify.lib.helpers.insert_sorted_by_in.
  simpl.
  split.
  - intros [Heq | Hin].
    + subst x. exact Htid.
    + eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in. exact Hin.
  - intro Hin.
    destruct (Z.eq_dec x tid) as [Heq | Hneq].
    + left. symmetry. exact Heq.
    + right. eapply Ucos2Verify.lib.helpers.remove_Z_eqb_in_neq;
        eassumption.
Qed.
Lemma mutex_del_atomic_task_set_curPrio_preserves_selected_waiters__g06_exit_observation :
  forall sg tid prio pre post eid e m,
    pre.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    atomic_task_set_curPrio sg tid prio pre tt post ->
    exists e',
      post.(EventState).(inUsedEventStates) eid = Some e' /\
      e'.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e'.(mutexFields) = Some m /\
      (forall x, In x e.(waitList) <-> In x e'.(waitList)).
Proof.
  intros sg tid prio pre post eid e m Hget Htype Hfields Hstep.
  unfold atomic_task_set_curPrio in Hstep.
  destruct Hstep as [Hready | [Hwaiting | Hdormant]].
  - unfold atomic_task_set_curPrio_ready in Hready.
    destruct Hready as
      (t & oldPrio & t' & Hin & Htask & Hold & Hneq & Hlo & Hhi &
       Hslot & Ht' & Hpost).
    cbv zeta in Hpost.
    subst post.
    exists e.
    split; [exact Hget |].
    split; [exact Htype |].
    split; [exact Hfields |].
    intro x. reflexivity.
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
       evSt2 & pty & Hnot_ready & Htask & Hold & Hneq & Hlo & Hhi &
       Hslot & Hpend & Hevent & Hmulti & Hwait_get & Hwait_type & Hin &
       Ht' & Htsk & Hwait' & Hev & Hpost).
    subst post.
    subst evSt2.
    cbn.
    destruct (Z.eqb eid wait_eid) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      subst wait_eid.
      assert (He : wait_e = e) by congruence.
      subst wait_e.
      exists wait_e'.
      split; [reflexivity |].
      subst wait_e'.
      cbn.
      split; [exact Htype |].
      split; [exact Hfields |].
      intro x.
      symmetry.
      apply
        (mutex_del_insert_remove_membership__g06_exit_observation
           (Ucos2Verify.lib.event_wait.wait_prio_key sg tskSt2)
           tid e.(waitList) Hin x).
    + exists e.
      split; [exact Hget |].
      split; [exact Htype |].
      split; [exact Hfields |].
      intro x. reflexivity.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Htask & Hold & Hneq &
       Hlo & Hhi & Hslot & Hevent & Hmulti & Hnot_effective & Ht' &
       Htsk & Hpost).
    subst post.
    exists e.
    split; [exact Hget |].
    split; [exact Htype |].
    split; [exact Hfields |].
    intro x. reflexivity.
Qed.
Lemma mutex_del_owner_stage_preserves_selected_waiters__g06_exit_observation :
  forall sg e entry owner_post eid m,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    mutex_del_rdyatprio_stage_prop sg e entry owner_post ->
    exists e',
      owner_post.(EventState).(inUsedEventStates) eid = Some e' /\
      e'.(eventType) = OS_EVENT_TYPE_MUTEX /\
      e'.(mutexFields) = Some m /\
      (forall x, In x e.(waitList) <-> In x e'.(waitList)).
Proof.
  intros sg e entry owner_post eid m Hget Htype Hfields Hstage.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as [m' [Htype' [Hfields' [Hshape Hexec]]]].
  assert (Hm : m' = m) by congruence.
  subst m'.
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis))
    eqn:Hdisabled.
  - subst owner_post.
    exists e.
    split; [exact Hget |].
    split; [exact Htype |].
    split; [exact Hfields |].
    intro x. reflexivity.
  - destruct m.(mfOwner) as [owner|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
      simpl in Hshape, Hexec.
    + destruct Hexec as [owner_t [Howner_get Hexec]].
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Hprio.
      * eapply
          mutex_del_atomic_task_set_curPrio_preserves_selected_waiters__g06_exit_observation;
          eassumption.
      * subst owner_post.
        exists e.
        split; [exact Hget |].
        split; [exact Htype |].
        split; [exact Hfields |].
        intro x. reflexivity.
    + contradiction.
    + contradiction.
    + subst owner_post.
      exists e.
      split; [exact Hget |].
      split; [exact Htype |].
      split; [exact Hfields |].
      intro x. reflexivity.
Qed.
Lemma mutex_del_set_cur_prio_preserves_task_status :
  forall sg tid priority pre post,
    atomic_task_set_curPrio sg tid priority pre tt post ->
    forall slot,
      option_map stat (post.(TskState).(inUsedTaskStates) slot) =
      option_map stat (pre.(TskState).(inUsedTaskStates) slot).
Proof.
  intros sg tid priority pre post Hstep slot.
  unfold atomic_task_set_curPrio in Hstep.
  destruct Hstep as [Hready | [Hwaiting | Hdormant]].
  - unfold atomic_task_set_curPrio_ready in Hready.
    destruct Hready as
      (t & oldPrio & t' & Hin & Hget & Hold & Hneq & Hlo & Hhi &
       Hslot & Ht' & Hpost).
    cbv zeta in Hpost; subst post t'; cbn.
    destruct (Z.eqb slot tid) eqn:Heq; [|reflexivity].
    apply Z.eqb_eq in Heq; subst slot; rewrite Hget; reflexivity.
  - unfold atomic_task_set_curPrio_waiting in Hwaiting.
    destruct Hwaiting as
      (t & oldPrio & t' & wait_eid & wait_e & wait_e' & tskSt2 &
       evSt2 & pty & Hnot_ready & Hget & Hold & Hneq & Hlo & Hhi &
       Hslot & Hpend & Hevent & Hmulti & Hwait_get & Hwait_type & Hin &
       Ht' & Htsk & Hwait' & Hev & Hpost).
    subst post tskSt2 t'; cbn.
    destruct (Z.eqb slot tid) eqn:Heq; [|reflexivity].
    apply Z.eqb_eq in Heq; subst slot; rewrite Hget; reflexivity.
  - unfold atomic_task_set_curPrio_dormant in Hdormant.
    destruct Hdormant as
      (t & oldPrio & t' & tskSt2 & Hnot_ready & Hget & Hold & Hneq &
       Hlo & Hhi & Hslot & Hevent & Hmulti & Hnot_effective & Ht' &
       Htsk & Hpost).
    subst post tskSt2 t'; cbn.
    destruct (Z.eqb slot tid) eqn:Heq; [|reflexivity].
    apply Z.eqb_eq in Heq; subst slot; rewrite Hget; reflexivity.
Qed.

Lemma mutex_del_owner_stage_preserves_task_status :
  forall sg e entry owner_post,
    mutex_del_rdyatprio_stage_prop sg e entry owner_post ->
    forall slot,
      option_map stat (owner_post.(TskState).(inUsedTaskStates) slot) =
      option_map stat (entry.(TskState).(inUsedTaskStates) slot).
Proof.
  intros sg e entry owner_post Hstage slot.
  unfold mutex_del_rdyatprio_stage_prop,
    mutex_del_owner_restore_total in Hstage.
  destruct Hstage as [m [Htype [Hfields [Hshape Hexec]]]].
  destruct (Z.eqb m.(mfPCP) sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - subst owner_post; reflexivity.
  - destruct m.(mfOwner) as [owner|] eqn:Howner;
      destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig;
      simpl in Hshape, Hexec.
    + destruct Hexec as [owner_t [Howner_get Hexec]].
      destruct (Z.eqb owner_t.(curPrio) m.(mfPCP)) eqn:Hprio.
      * exact (mutex_del_set_cur_prio_preserves_task_status
          sg owner orig entry owner_post Hexec slot).
      * subst owner_post; reflexivity.
    + contradiction.
    + contradiction.
    + subst owner_post; reflexivity.
Qed.

Lemma mutex_del_success_commit_waiters_at_anchor__g06_exit_observation :
  forall sg e entry eid critical_anchor commit m,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    verification_slice_event_in_range sg entry.(TskState) entry.(EventState) ->
    mutex_del_success_commit_anchor_prop
      sg e entry eid MutexDelAlways critical_anchor commit ->
    mutex_del_waiters_aborted_effective_prop
      e critical_anchor.(TskState) critical_anchor.(SchedState).
Proof.
  intros sg e entry eid critical_anchor commit m
    Hget Htype Hfields Hvalid Hcommit.
  unfold mutex_del_success_commit_anchor_prop in Hcommit.
  destruct Hcommit as
    [owner_post [prepare [Howner_stage [Hwakes [Hprepare Hfree]]]]].
  destruct
    (mutex_del_owner_stage_preserves_selected_waiters__g06_exit_observation
       sg e entry owner_post eid m Hget Htype Hfields Howner_stage)
    as [owner_e [Howner_get [Howner_type [Howner_fields Hmembers]]]].
  assert (Hentry_waiters :
    mutex_waiters_status_consistent entry.(TskState) e.(waitList)).
  { eapply mutex_waiters_status_from_verification_slice_event_validity;
      eassumption. }
  assert (Howner_status : forall slot,
    option_map stat (owner_post.(TskState).(inUsedTaskStates) slot) =
    option_map stat (entry.(TskState).(inUsedTaskStates) slot)).
  { exact (mutex_del_owner_stage_preserves_task_status
      sg e entry owner_post Howner_stage). }
  assert (Howner_waiters :
    mutex_waiters_status_consistent owner_post.(TskState) owner_e.(waitList)).
  { intros tid t Hin Hlookup.
    pose proof (Howner_status tid) as Hstatus.
    rewrite Hlookup in Hstatus.
    destruct (entry.(TskState).(inUsedTaskStates) tid)
      as [before|] eqn:Hbefore; cbn in Hstatus; [|discriminate].
    inversion Hstatus as [Hstat].
    rewrite Hstat.
    apply (Hentry_waiters tid before).
    - apply (proj2 (Hmembers tid)); exact Hin.
    - exact Hbefore. }
  unfold mutex_del_mode_wake_prop in Hwakes.
  unfold mutex_del_no_pend_prepare_stage_prop,
    mutex_del_no_pend_prepare in Hprepare.
  destruct Hprepare as
    [final_e [final_m [evSt2
      [Hfinal_get [Hfinal_type [Hfinal_fields
        [Hfinal_empty [HevSt2 Hprepare_state]]]]]]]].
  pose proof
    (mutex_del_wake_steps_complete_waiter_effect__g06_exit_observation
       sg eid owner_post critical_anchor owner_e m final_e
       Howner_get Howner_type Howner_fields Hwakes Howner_waiters Hfinal_get Hfinal_empty)
    as Heffect.
  unfold mutex_del_waiters_aborted_effective_prop in Heffect |- *.
  intros tid Hin.
  apply Heffect.
  apply (proj1 (Hmembers tid)).
  exact Hin.
Qed.
Lemma mutex_del_waiters_effect_transport__g06_exit_observation :
  forall e tsk1 sched1 tsk2 sched2,
    (forall tid,
       tsk2.(inUsedTaskStates) tid = tsk1.(inUsedTaskStates) tid) ->
    sched2.(readyList) = sched1.(readyList) ->
    mutex_del_waiters_aborted_effective_prop e tsk1 sched1 ->
    mutex_del_waiters_aborted_effective_prop e tsk2 sched2.
Proof.
  intros e tsk1 sched1 tsk2 sched2 Htasks Hready Heffect.
  unfold mutex_del_waiters_aborted_effective_prop in Heffect |- *.
  intros tid Hin.
  destruct (Heffect tid Hin) as
    [t [Hget [Hpend [Habort [Hdly [Hevent Hready_tid]]]]]].
  exists t.
  rewrite Htasks.
  repeat split; try assumption.
  intro Hnot_suspended.
  rewrite Hready.
  apply Hready_tid.
  exact Hnot_suspended.
Qed.
Lemma mutex_del_success_commit_waiters_at_commit__g06_exit_observation :
  forall sg e entry eid critical_anchor commit m,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    verification_slice_event_in_range sg entry.(TskState) entry.(EventState) ->
    mutex_del_success_commit_anchor_prop
      sg e entry eid MutexDelAlways critical_anchor commit ->
    mutex_del_waiters_aborted_effective_prop
      e commit.(TskState) commit.(SchedState).
Proof.
  intros sg e entry eid critical_anchor commit m
    Hget Htype Hfields Hvalid Hcommit.
  pose proof Hcommit as Hcommit_parts.
  pose proof
    (mutex_del_success_commit_waiters_at_anchor__g06_exit_observation
       sg e entry eid critical_anchor commit m
       Hget Htype Hfields Hvalid Hcommit)
    as Hanchor_effect.
  unfold mutex_del_success_commit_anchor_prop in Hcommit_parts.
  destruct Hcommit_parts as
    [owner_post [prepare [Howner_stage [Hwakes [Hprepare Hfree]]]]].
  unfold mutex_del_no_pend_prepare_stage_prop,
    mutex_del_no_pend_prepare in Hprepare.
  destruct Hprepare as
    [final_e [final_m [evSt2
      [Hfinal_get [Hfinal_type [Hfinal_fields
        [Hfinal_empty [HevSt2 Hprepare_state]]]]]]]].
  unfold mutex_del_free_stage_prop,
    atomic_event_free_with_priotbl_free in Hfree.
  destruct Hfree as
    [free_e [free_m [free_evSt [free_tskSt
      [Hfree_get [Hfree_type [Hfree_fields [Hfree_owner
        [Hfree_empty [Hfree_ev [Hfree_tsk Hcommit_state]]]]]]]]]]].
  eapply
    (mutex_del_waiters_effect_transport__g06_exit_observation
       e critical_anchor.(TskState) critical_anchor.(SchedState)
       commit.(TskState) commit.(SchedState)).
  - intro tid.
    rewrite Hcommit_state, Hfree_tsk, Hprepare_state.
    reflexivity.
  - rewrite Hcommit_state, Hprepare_state.
    reflexivity.
  - exact Hanchor_effect.
Qed.
Lemma mutex_del_atomic_sched_preserves_waiter_maps__g06_exit_observation :
  forall pre res post,
    atomic_sched pre res post ->
    post.(TskState) = pre.(TskState) /\
    post.(SchedState).(readyList) = pre.(SchedState).(readyList).
Proof.
  intros pre res post Hsched.
  unfold atomic_sched in Hsched.
  cbv zeta in Hsched.
  remember
    (Z.eqb pre.(IntrState).(intNesting) 0 &&
     Z.eqb pre.(IntrState).(lockNesting) 0)%bool
    as b_outer in Hsched.
  destruct b_outer.
  - cbv beta iota in Hsched.
    remember pre.(SchedState).(readyList) as rl in Hsched.
    destruct rl as [| h tl].
    + cbv beta iota in Hsched.
      destruct Hsched as [Hpost Hres].
      subst post. split; reflexivity.
    + cbv beta iota in Hsched.
      remember pre.(SchedState).(curTaskID) as ctid in Hsched.
      destruct ctid as [c |].
      * cbv beta iota in Hsched.
        remember (pre.(TskState).(inUsedTaskStates) h) as geth in Hsched.
        destruct geth as [head_t |].
        -- cbv beta iota in Hsched.
           remember (pre.(TskState).(inUsedTaskStates) c) as getc in Hsched.
           destruct getc as [cur_t |].
           ++ cbv beta iota in Hsched.
              remember
                (negb
                   (is_effectively_ready cur_t.(stat) cur_t.(dly) &&
                    existsb (Z.eqb c) (h :: tl)) ||
                 negb (Z.eqb h c))%bool
                as b_inner in Hsched.
              destruct b_inner.
              ** cbv beta iota in Hsched.
                 destruct Hsched as
                   [sched2 [Hsched2 [Hpost Hres]]].
                 rewrite Hpost.
                 split.
                 --- reflexivity.
                 --- rewrite Hsched2. exact Heqrl.
              ** cbv beta iota in Hsched.
                 destruct Hsched as [Hpost Hres].
                 subst post. split; reflexivity.
           ++ cbv beta iota in Hsched.
              destruct Hsched as [Hpost Hres].
              subst post. split; reflexivity.
        -- cbv beta iota in Hsched.
           destruct Hsched as [Hpost Hres].
           subst post. split; reflexivity.
      * cbv beta iota in Hsched.
        destruct Hsched as [Hpost Hres].
        subst post. split; reflexivity.
  - cbv beta iota in Hsched.
    destruct Hsched as [Hpost Hres].
    subst post. split; reflexivity.
Qed.
Lemma mutex_del_success_waiters_after_exit__g06_exit_observation :
  forall sg e entry eid critical_anchor commit exited m,
    entry.(EventState).(inUsedEventStates) eid = Some e ->
    e.(eventType) = OS_EVENT_TYPE_MUTEX ->
    e.(mutexFields) = Some m ->
    verification_slice_event_in_range sg entry.(TskState) entry.(EventState) ->
    mutex_del_success_commit_anchor_prop
      sg e entry eid MutexDelAlways critical_anchor commit ->
    mutex_del_exit_critical_anchored_call_prop
      sg critical_anchor commit exited ->
    mutex_del_waiters_aborted_effective_prop
      e exited.(TskState) exited.(SchedState).
Proof.
  intros sg e entry eid critical_anchor commit exited m
    Hget Htype Hfields Hvalid Hcommit Hexit.
  pose proof
    (mutex_del_success_commit_waiters_at_commit__g06_exit_observation
       sg e entry eid critical_anchor commit m
       Hget Htype Hfields Hvalid Hcommit)
    as Hcommit_effect.
  unfold mutex_del_exit_critical_anchored_call_prop,
    crit_rel_intr_only in Hexit.
  destruct Hexit as [HG Hshape].
  eapply
    (mutex_del_waiters_effect_transport__g06_exit_observation
       e commit.(TskState) commit.(SchedState)
       exited.(TskState) exited.(SchedState)).
  - intro tid. rewrite Hshape. reflexivity.
  - rewrite Hshape. reflexivity.
  - exact Hcommit_effect.
Qed.
Lemma mutex_del_success_waiters_after_sched__g06_exit_observation :
  forall e exited out,
    mutex_del_waiters_aborted_effective_prop
      e exited.(TskState) exited.(SchedState) ->
    mutex_del_sched_stage_prop exited out ->
    mutex_del_waiters_aborted_effective_prop
      e out.(TskState) out.(SchedState).
Proof.
  intros e exited out Heffect Hsched_stage.
  unfold mutex_del_sched_stage_prop in Hsched_stage.
  destruct Hsched_stage as [res Hsched].
  destruct
    (mutex_del_atomic_sched_preserves_waiter_maps__g06_exit_observation
       exited res out Hsched)
    as [Htasks Hready].
  eapply
    (mutex_del_waiters_effect_transport__g06_exit_observation
       e exited.(TskState) exited.(SchedState)
       out.(TskState) out.(SchedState)).
  - intro tid. rewrite Htasks. reflexivity.
  - exact Hready.
  - exact Heffect.
Qed.
Lemma mutex_del_owner_stage_focus_split_priotbl__g07_entry_focus_rules :
  forall sg e entry eid pcp,
    priotbl_index_in_range pcp ->
    mutex_del_owner_stage_focus sg e entry eid |--
      EX old_pcp_cell : addr,
      EX owner_post : UCOS2_Verify_State,
        Ucos2Verify.lib.ucos2_rules_lib.InsideCritical sg owner_post **
        priotbl_element_store
          sg.(g_OSTCBPrioTbl) pcp old_pcp_cell **
        mutex_del_event_missing_priotbl_focus
          sg entry owner_post eid pcp **
        coq_prop
          (mutex_del_rdyatprio_stage_prop sg e entry owner_post).
Proof.
  intros sg e entry eid pcp Hrange.
  unfold mutex_del_owner_stage_focus.
  Intros owner_post.
  sep_apply_l_atomic
    (mutex_del_event_focus_split_priotbl
       sg entry owner_post eid pcp Hrange).
  Intros old_pcp_cell.
  Exists old_pcp_cell owner_post.
  cancel.
  andp_cancel.
  sepcon_assoc_change.
  cancel.
Qed.
