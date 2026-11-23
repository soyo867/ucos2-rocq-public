Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SumLib.ZRange.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.task_status.
Import UCOS2_C_Rules.
Import TaskStateDef.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.
Local Open Scope sac_scope.

(** Tick clears the pending bit at timeout before Event/Flag removes its
    registration. This assertion describes the task side of either linked
    wait; it does not itself own or establish a list registration. *)
Definition task_linked_wait_phase (t : TaskAbstractState) (pty : PendType) : Prop :=
  (task_non_suspension_bits t.(stat)) = task_pend_mask pty \/
  ((task_non_suspension_bits t.(stat)) = 0 /\ t.(statPend) = PendTimeout /\ t.(dly) = 0).

Lemma task_effectively_ready_has_no_pending : forall t,
  is_effectively_ready t.(stat) t.(dly) = true -> (task_non_suspension_bits t.(stat)) = 0.
Proof.
  intros t H; unfold is_effectively_ready in H.
  destruct (Z.eqb (task_non_suspension_bits t.(stat)) 0) eqn:E; [apply Z.eqb_eq; exact E|discriminate].
Qed.

(* ================================================================== *)
(* Phase 3 Task 3.4:encode helpers + verification_slice_tcb_addr                          *)
(* ================================================================== *)

(* 位编码:OSTCBStat 字段编码 *)
(** Preserve qualified clients while the status-byte owner is shared by
    single waits, Multi waits and timeout. *)
Definition encode_pend_type := task_status.encode_pend_type.
Definition encode_task_status := task_status.encode_task_status.

Definition encode_pend_status (ps : PendStatus) : Z :=
  match ps with
  | PendOK      => 0
  | PendTimeout => 1
  | PendAbort   => 2
  end.

Definition encode_event_ptr (p : option EventID) : Z :=
  match p with None => 0 | Some eid => eid end.

Definition encode_event_multi_ptr (p : list EventID) : Z :=
  match p with
  | nil => 0
  | eid :: _ => eid
  end.

Definition encode_msg (p : option addr) : Z :=
  match p with None => 0 | Some a => a end.

Definition encode_bool (b : bool) : Z := if b then 1 else 0.

(* TCB 地址计算:OSTCBTbl[tid] 的起始地址 *)
Definition verification_slice_tcb_size : Z := 68.

Definition verification_slice_tcb_addr (sg : StableGlobVars) (tid : TaskID) : addr :=
  sg.(g_OSTCBTbl) + tid * verification_slice_tcb_size.

(* ================================================================== *)
(* Phase 3 Task 3.3:valid_task_prio + verification_slice_task_in_range                   *)
(* ================================================================== *)

Definition valid_task_prio (sg : StableGlobVars) (p : Priority) : Prop :=
  0 <= p /\ p < sg.(osLowestPrio).

Definition task_priority_unique (gs : Glob_TaskAbstractState) : Prop :=
  forall tid1 tid2 t1 t2,
    gs.(inUsedTaskStates) tid1 = Some t1 ->
    gs.(inUsedTaskStates) tid2 = Some t2 ->
    t1.(curPrio) = t2.(curPrio) ->
    tid1 = tid2.

(* Every live task owns the priority-table entry selected by its current
   priority.  This is the task-owned forward direction of the task/priority
   table relation; [verification_slice_task_in_range] below already carries the converse
   PTTask-to-live-task direction. *)
Definition task_current_prio_registered
  (gs : Glob_TaskAbstractState) : Prop :=
  forall tid t,
    gs.(inUsedTaskStates) tid = Some t ->
    gs.(prioTbl) t.(curPrio) = PTTask tid.

Definition no_live_task_at_priority
  (gs : Glob_TaskAbstractState) (p : Priority) : Prop :=
  forall tid t,
    gs.(inUsedTaskStates) tid = Some t ->
    t.(curPrio) <> p.

Lemma task_current_prio_registered_non_task_slot_is_unused :
  forall st p entry,
    task_current_prio_registered st ->
    st.(prioTbl) p = entry ->
    (forall tid, entry <> PTTask tid) ->
    no_live_task_at_priority st p.
Proof.
  intros st p entry Hregistered Hentry Hnot_task tid t Hlookup Heq.
  subst p.
  pose proof (Hregistered tid t Hlookup) as Htask.
  rewrite Hentry in Htask.
  exact (Hnot_task tid Htask).
Qed.

Lemma task_current_prio_registered_free_slot_is_unused :
  forall st p,
    task_current_prio_registered st ->
    st.(prioTbl) p = PTFree ->
    no_live_task_at_priority st p.
Proof.
  intros st p Hregistered Hfree.
  eapply task_current_prio_registered_non_task_slot_is_unused;
    eauto; discriminate.
Qed.

Lemma task_current_prio_registered_reserved_slot_is_unused :
  forall st p,
    task_current_prio_registered st ->
    st.(prioTbl) p = PTReserved ->
    no_live_task_at_priority st p.
Proof.
  intros st p Hregistered Hreserved.
  eapply task_current_prio_registered_non_task_slot_is_unused;
    eauto; discriminate.
Qed.

Lemma task_current_prio_registered_extensional :
  forall st1 st2,
    (forall tid,
       st2.(inUsedTaskStates) tid = st1.(inUsedTaskStates) tid) ->
    (forall p, st2.(prioTbl) p = st1.(prioTbl) p) ->
    task_current_prio_registered st1 ->
    task_current_prio_registered st2.
Proof.
  intros st1 st2 Hused Hprio Hregistered.
  unfold task_current_prio_registered in *.
  intros tid t Hlookup.
  rewrite Hused in Hlookup.
  rewrite Hprio.
  exact (Hregistered tid t Hlookup).
Qed.

(* Updates to non-priority task fields preserve registration whenever every
   live post-state task can be matched to a pre-state task at the same ID and
   priority, and the priority table itself is framed. *)
Lemma task_current_prio_registered_preserved_by_same_priorities :
  forall st1 st2,
    (forall tid t2,
       st2.(inUsedTaskStates) tid = Some t2 ->
       exists t1,
         st1.(inUsedTaskStates) tid = Some t1 /\
         t2.(curPrio) = t1.(curPrio)) ->
    (forall p, st2.(prioTbl) p = st1.(prioTbl) p) ->
    task_current_prio_registered st1 ->
    task_current_prio_registered st2.
Proof.
  intros st1 st2 Htasks Hprio Hregistered.
  unfold task_current_prio_registered in *.
  intros tid t2 Hlookup2.
  destruct (Htasks tid t2 Hlookup2) as [t1 [Hlookup1 HcurPrio]].
  rewrite Hprio, HcurPrio.
  exact (Hregistered tid t1 Hlookup1).
Qed.

(* Updating one priority-table slot is representation-safe exactly when no
   post-state live task currently occupies that priority.  This captures the
   common reserve/release/free pattern without assigning mutex ownership to
   the task layer. *)
Lemma task_current_prio_registered_preserved_by_slot_overwrite :
  forall st1 st2 p,
    (forall tid t2,
       st2.(inUsedTaskStates) tid = Some t2 ->
       exists t1,
         st1.(inUsedTaskStates) tid = Some t1 /\
         t2.(curPrio) = t1.(curPrio)) ->
    (forall q, q <> p -> st2.(prioTbl) q = st1.(prioTbl) q) ->
    no_live_task_at_priority st2 p ->
    task_current_prio_registered st1 ->
    task_current_prio_registered st2.
Proof.
  intros st1 st2 p Htasks Htable Hunused Hregistered.
  unfold task_current_prio_registered in *.
  intros tid t2 Hlookup2.
  destruct (Htasks tid t2 Hlookup2) as [t1 [Hlookup1 Hprio]].
  assert (Hneq : t2.(curPrio) <> p).
  { exact (Hunused tid t2 Hlookup2). }
  rewrite (Htable t2.(curPrio) Hneq), Hprio.
  exact (Hregistered tid t1 Hlookup1).
Qed.

(* Generic preservation interface for a single task-priority relocation.
   The operation must install the target registration, frame every unrelated
   task and priority slot, and re-establish post-state priority uniqueness.
   This is independent of the ready/waiting/dormant branch that performs the
   relocation. *)
Lemma task_current_prio_registered_preserved_by_priority_update :
  forall st1 st2 tid t_new,
    task_current_prio_registered st1 ->
    task_priority_unique st2 ->
    st2.(inUsedTaskStates) tid = Some t_new ->
    (forall tid', tid' <> tid ->
       st2.(inUsedTaskStates) tid' = st1.(inUsedTaskStates) tid') ->
    (forall p, p <> t_new.(curPrio) ->
       st2.(prioTbl) p = st1.(prioTbl) p) ->
    st2.(prioTbl) t_new.(curPrio) = PTTask tid ->
    task_current_prio_registered st2.
Proof.
  intros st1 st2 tid t_new Hregistered Hunique Htarget
    Hused_frame Hprio_frame Htarget_registered.
  unfold task_current_prio_registered in *.
  intros tid' t' Hlookup.
  destruct (Z.eq_dec tid' tid) as [Heq | Hneq].
  - subst tid'.
    rewrite Htarget in Hlookup.
    inversion Hlookup; subst t'.
    exact Htarget_registered.
  - assert (HcurPrio_neq : t'.(curPrio) <> t_new.(curPrio)).
    { intro HcurPrio.
      apply Hneq.
      eapply Hunique; eauto. }
    rewrite (Hprio_frame t'.(curPrio) HcurPrio_neq).
    apply Hregistered.
    rewrite <- (Hused_frame tid' Hneq).
    exact Hlookup.
Qed.

Definition verification_slice_task_in_range (sg : StableGlobVars)
  (gs : Glob_TaskAbstractState) : Prop :=
  (forall tid t, (gs.(inUsedTaskStates)) tid = Some t ->
               0 <= tid /\ tid < sg.(osMaxTasks) + sg.(osNSysTasks)) /\
  NoDup gs.(unUsedTaskStates) /\
  Forall (fun tid => 0 <= tid /\ tid < sg.(osMaxTasks) + sg.(osNSysTasks)) gs.(unUsedTaskStates) /\
  (forall tid, In tid gs.(unUsedTaskStates) -> (gs.(inUsedTaskStates)) tid = None) /\
  (forall p tid, gs.(prioTbl) p = PTTask tid ->
                valid_task_prio sg p /\
                exists t, gs.(inUsedTaskStates) tid = Some t) /\
  task_current_prio_registered gs /\
  task_priority_unique gs.

Lemma verification_slice_task_in_range_current_prio_registered :
  forall sg st,
    verification_slice_task_in_range sg st ->
    task_current_prio_registered st.
Proof.
  intros sg st Hrange.
  unfold verification_slice_task_in_range in Hrange.
  destruct Hrange as [_ [_ [_ [_ [_ [Hregistered _]]]]]].
  exact Hregistered.
Qed.

(* ================================================================== *)
(* Phase 3 Task 3.5:verification_slice_used_complete_task - TCB 字段内存铺开              *)
(* ================================================================== *)
(* 用 addr + offset 直接表示字段地址(避免依赖 C 结构语法)             *)

Definition verification_slice_OSTCBPrio_off        : Z := 0.
Definition verification_slice_OSTCBStat_off        : Z := 1.
Definition verification_slice_OSTCBStatPend_off    : Z := 2.
Definition verification_slice_OSTCBDly_off         : Z := 4.
Definition verification_slice_OSTCBX_off           : Z := 8.
Definition verification_slice_OSTCBY_off           : Z := 9.
Definition verification_slice_OSTCBBitX_off        : Z := 10.
Definition verification_slice_OSTCBBitY_off        : Z := 11.
Definition verification_slice_OSTCBEventPtr_off    : Z := 12.
Definition verification_slice_OSTCBEventMultiPtr_off : Z := 16.  (* 简化:数组当 option/list 占位 *)
Definition verification_slice_OSTCBEventMultiRdy_off : Z := 20.
Definition verification_slice_OSTCBMsg_off         : Z := 24.
Definition verification_slice_OSTCBNext_off        : Z := 28.
Definition verification_slice_OSTCBPrev_off        : Z := 32.
Definition verification_slice_OSTCBDelReq_off      : Z := 36.

(* ================================================================== *)
(* L1: OS_TCB representation bridges                                    *)
(* ================================================================== *)

(* Shared bridge between QCP's opaque struct-field address and the
   historical base + offset TCB representation.  This fact belongs to the
   task representation and is independent of any mutex control-flow path. *)
Definition task_prio_field_layout_prop
  (tcb prio_addr : addr) : Prop :=
  prio_addr = tcb + verification_slice_OSTCBPrio_off.

(* Canonical layout bridge for the priority-derived TCB fields.  QCP keeps
   structure-field addresses opaque, while the task representation above is
   intentionally stated with a base address and byte offsets.  Keeping the
   complete bridge in the task module makes focused task decomposition
   reversible for every caller that reads or updates a task's ready fields;
   it does not encode an operation result or a task-protocol branch. *)
Definition task_priority_fields_layout_prop
  (tcb prio_addr x_addr y_addr bitx_addr bity_addr : addr) : Prop :=
  prio_addr = tcb + verification_slice_OSTCBPrio_off /\
  x_addr = tcb + verification_slice_OSTCBX_off /\
  y_addr = tcb + verification_slice_OSTCBY_off /\
  bitx_addr = tcb + verification_slice_OSTCBBitX_off /\
  bity_addr = tcb + verification_slice_OSTCBBitY_off.

Definition tcb_x_of_prio (p : Priority) : Z := p mod 8.
Definition tcb_y_of_prio (p : Priority) : Z := p / 8.
Definition tcb_bit_x_of_prio (p : Priority) : Z := Z.shiftl 1 (tcb_x_of_prio p).
Definition tcb_bit_y_of_prio (p : Priority) : Z := Z.shiftl 1 (tcb_y_of_prio p).

Definition verification_slice_used_complete_task (sg : StableGlobVars) (ctrl_start : addr)
  (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  (ctrl_start + verification_slice_OSTCBPrio_off)        # UChar |-> t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBStat_off)        # UChar |-> encode_task_status t.(stat) **
  (ctrl_start + verification_slice_OSTCBStatPend_off)    # UChar |-> encode_pend_status t.(statPend) **
  (ctrl_start + verification_slice_OSTCBDly_off)         # UInt  |-> t.(dly) **
  (ctrl_start + verification_slice_OSTCBX_off)           # UChar |-> tcb_x_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBY_off)           # UChar |-> tcb_y_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBBitX_off)        # UChar |-> tcb_bit_x_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBBitY_off)        # UChar |-> tcb_bit_y_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBEventPtr_off)    # Ptr  |-> encode_event_ptr t.(eventPtr) **
  (ctrl_start + verification_slice_OSTCBEventMultiPtr_off) # Ptr |-> encode_event_multi_ptr t.(eventMultiWaitEvents) **
  (ctrl_start + verification_slice_OSTCBEventMultiRdy_off) # Ptr |-> encode_event_ptr t.(eventMultiRdy) **
  (ctrl_start + verification_slice_OSTCBMsg_off)         # Ptr  |-> encode_msg t.(msg) **
  (ctrl_start + verification_slice_OSTCBNext_off)        # Ptr  |-> (match t.(nextTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBPrev_off)        # Ptr  |-> (match t.(prevTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBDelReq_off)      # UChar |-> encode_bool t.(delReq).

Definition task_prio_snapshot_of_prop
  (sg : StableGlobVars) (st : Glob_TaskAbstractState)
  (tid : TaskID) (t : TaskAbstractState) (tcb prio : Z) : Prop :=
  st.(inUsedTaskStates) tid = Some t /\
  tcb = verification_slice_tcb_addr sg tid /\
  prio = t.(curPrio).

(* L3 task-protocol focus used by non-blocking synchronization operations:
   the focused TCB is a live task, its concrete priority matches the abstract
   task, and it is not currently pending on an event.  Scheduler/current-TCB
   selection remains a separate scheduler or cross-module premise. *)
Definition task_runnable_prio_snapshot_prop
  (sg : StableGlobVars) (st : Glob_TaskAbstractState)
  (tid : TaskID) (t : TaskAbstractState)
  (tcb prio : Z) : Prop :=
  task_prio_snapshot_of_prop sg st tid t tcb prio /\
  (task_non_suspension_bits (t.(stat))) = 0.

Definition used_task_no_prio (sg : StableGlobVars) (ctrl_start : addr)
  (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  (ctrl_start + verification_slice_OSTCBStat_off)        # UChar |-> encode_task_status t.(stat) **
  (ctrl_start + verification_slice_OSTCBStatPend_off)    # UChar |-> encode_pend_status t.(statPend) **
  (ctrl_start + verification_slice_OSTCBDly_off)         # UInt  |-> t.(dly) **
  (ctrl_start + verification_slice_OSTCBX_off)           # UChar |-> tcb_x_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBY_off)           # UChar |-> tcb_y_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBBitX_off)        # UChar |-> tcb_bit_x_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBBitY_off)        # UChar |-> tcb_bit_y_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBEventPtr_off)    # Ptr  |-> encode_event_ptr t.(eventPtr) **
  (ctrl_start + verification_slice_OSTCBEventMultiPtr_off) # Ptr |-> encode_event_multi_ptr t.(eventMultiWaitEvents) **
  (ctrl_start + verification_slice_OSTCBEventMultiRdy_off) # Ptr |-> encode_event_ptr t.(eventMultiRdy) **
  (ctrl_start + verification_slice_OSTCBMsg_off)         # Ptr  |-> encode_msg t.(msg) **
  (ctrl_start + verification_slice_OSTCBNext_off)        # Ptr  |->
    (match t.(nextTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBPrev_off)        # Ptr  |->
    (match t.(prevTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBDelReq_off)      # UChar |-> encode_bool t.(delReq).

Definition task_mutex_full_snapshot_of_prop
  (sg : StableGlobVars) (st : Glob_TaskAbstractState)
  (tid : TaskID) (t : TaskAbstractState)
  (tcb_v prio_v stat_v statpend_v dly_v eventptr_v
   eventmultiptr_v eventmultirdy_v : Z) : Prop :=
  st.(inUsedTaskStates) tid = Some t /\
  tcb_v = verification_slice_tcb_addr sg tid /\
  prio_v = t.(curPrio) /\
  stat_v = encode_task_status t.(stat) /\
  statpend_v = encode_pend_status t.(statPend) /\
  dly_v = t.(dly) /\
  eventptr_v = encode_event_ptr t.(eventPtr) /\
  eventmultiptr_v = encode_event_multi_ptr t.(eventMultiWaitEvents) /\
  eventmultirdy_v = encode_event_ptr t.(eventMultiRdy).

Definition task_mutex_pend_entry_prop (t : TaskAbstractState) : Prop :=
  (task_non_suspension_bits (t.(stat))) = 0 /\
  (task_is_suspended (t.(stat))) = false /\
  t.(statPend) = PendOK /\
  t.(dly) = 0 /\
  t.(eventPtr) = None /\
  t.(eventMultiWaitEvents) = [] /\
  t.(eventMultiRdy) = None.

Definition task_mutex_pend_clean_prop (t : TaskAbstractState) : Prop :=
  (task_non_suspension_bits (t.(stat))) = 0 /\
  (task_is_suspended (t.(stat))) = false /\
  t.(statPend) = PendOK /\
  t.(dly) = 0 /\
  t.(eventPtr) = None /\
  t.(eventMultiWaitEvents) = [] /\
  t.(eventMultiRdy) = None.

(* Current-task residual for OSMutexPend.  All fields written during pend
   setup/cleanup are deliberately excluded and must be owned explicitly. *)
Definition used_task_pend_rest (sg : StableGlobVars) (ctrl_start : addr)
  (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  (ctrl_start + verification_slice_OSTCBX_off)           # UChar |-> tcb_x_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBY_off)           # UChar |-> tcb_y_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBBitX_off)        # UChar |-> tcb_bit_x_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBBitY_off)        # UChar |-> tcb_bit_y_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBMsg_off)         # Ptr |-> encode_msg t.(msg) **
  (ctrl_start + verification_slice_OSTCBNext_off)        # Ptr |->
    (match t.(nextTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBPrev_off)        # Ptr |->
    (match t.(prevTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBDelReq_off)      # UChar |-> encode_bool t.(delReq).

(* Owner residual for priority inheritance.  Priority-derived fields and
   OSTCBEventPtr are exposed by the caller; unrelated task state remains here. *)
Definition used_task_inherit_rest (sg : StableGlobVars) (ctrl_start : addr)
  (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  (ctrl_start + verification_slice_OSTCBStat_off)        # UChar |-> encode_task_status t.(stat) **
  (ctrl_start + verification_slice_OSTCBStatPend_off)    # UChar |-> encode_pend_status t.(statPend) **
  (ctrl_start + verification_slice_OSTCBDly_off)         # UInt |-> t.(dly) **
  (ctrl_start + verification_slice_OSTCBEventMultiPtr_off) # Ptr |-> encode_event_multi_ptr t.(eventMultiWaitEvents) **
  (ctrl_start + verification_slice_OSTCBEventMultiRdy_off) # Ptr |-> encode_event_ptr t.(eventMultiRdy) **
  (ctrl_start + verification_slice_OSTCBMsg_off)         # Ptr |-> encode_msg t.(msg) **
  (ctrl_start + verification_slice_OSTCBNext_off)        # Ptr |->
    (match t.(nextTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBPrev_off)        # Ptr |->
    (match t.(prevTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBDelReq_off)      # UChar |-> encode_bool t.(delReq).

(* Current-task residual for the resume/cleanup phase of OSMutexPend.
   Stat, StatPend, Dly and EventPtr remain explicit because the C function
   branches on or clears them after returning from the scheduler. *)
Definition used_task_cleanup_rest (sg : StableGlobVars) (ctrl_start : addr)
  (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  (ctrl_start + verification_slice_OSTCBPrio_off)        # UChar |-> t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBX_off)           # UChar |-> tcb_x_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBY_off)           # UChar |-> tcb_y_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBBitX_off)        # UChar |-> tcb_bit_x_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBBitY_off)        # UChar |-> tcb_bit_y_of_prio t.(curPrio) **
  (ctrl_start + verification_slice_OSTCBEventMultiPtr_off) # Ptr |-> encode_event_multi_ptr t.(eventMultiWaitEvents) **
  (ctrl_start + verification_slice_OSTCBEventMultiRdy_off) # Ptr |-> encode_event_ptr t.(eventMultiRdy) **
  (ctrl_start + verification_slice_OSTCBMsg_off)         # Ptr |-> encode_msg t.(msg) **
  (ctrl_start + verification_slice_OSTCBNext_off)        # Ptr |->
    (match t.(nextTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBPrev_off)        # Ptr |->
    (match t.(prevTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBDelReq_off)      # UChar |-> encode_bool t.(delReq).

Definition task_rdy_snapshot_of_prop
  (sg : StableGlobVars) (st : Glob_TaskAbstractState)
  (tid : TaskID) (t : TaskAbstractState)
  (tcb_v prio_v x_v y_v bitx_v bity_v : Z) : Prop :=
  st.(inUsedTaskStates) tid = Some t /\
  tcb_v = verification_slice_tcb_addr sg tid /\
  prio_v = t.(curPrio) /\
  x_v = tcb_x_of_prio t.(curPrio) /\
  y_v = tcb_y_of_prio t.(curPrio) /\
  bitx_v = tcb_bit_x_of_prio t.(curPrio) /\
  bity_v = tcb_bit_y_of_prio t.(curPrio).

(* Focused representation of the five fields that encode a task's current
   ready priority.  The addresses are parameters because QCP keeps C
   structure-field addresses opaque; [task_priority_fields_layout_prop]
   connects them to the canonical task representation. *)
Definition used_task_priority_fields_at
  (prio_addr x_addr y_addr bitx_addr bity_addr : addr)
  (t : TaskAbstractState) : Assertion :=
  prio_addr # UChar |-> t.(curPrio) **
  x_addr # UChar |-> tcb_x_of_prio t.(curPrio) **
  y_addr # UChar |-> tcb_y_of_prio t.(curPrio) **
  bitx_addr # UChar |-> tcb_bit_x_of_prio t.(curPrio) **
  bity_addr # UChar |-> tcb_bit_y_of_prio t.(curPrio).

(* Priority inheritance reads the same derived priority fields as the ready
   path, but it also branches on OSTCBEventPtr when the owner is blocked. *)
Definition task_inherit_snapshot_of_prop
  (sg : StableGlobVars) (st : Glob_TaskAbstractState)
  (tid : TaskID) (t : TaskAbstractState)
  (tcb_v prio_v x_v y_v bitx_v bity_v eventptr_v : Z) : Prop :=
  task_rdy_snapshot_of_prop sg st tid t
    tcb_v prio_v x_v y_v bitx_v bity_v /\
  eventptr_v = encode_event_ptr t.(eventPtr).

Definition used_task_rdy_rest (sg : StableGlobVars) (ctrl_start : addr)
  (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  (ctrl_start + verification_slice_OSTCBStat_off)        # UChar |-> encode_task_status t.(stat) **
  (ctrl_start + verification_slice_OSTCBStatPend_off)    # UChar |-> encode_pend_status t.(statPend) **
  (ctrl_start + verification_slice_OSTCBDly_off)         # UInt  |-> t.(dly) **
  (ctrl_start + verification_slice_OSTCBEventPtr_off)    # Ptr |-> encode_event_ptr t.(eventPtr) **
  (ctrl_start + verification_slice_OSTCBEventMultiPtr_off) # Ptr |-> encode_event_multi_ptr t.(eventMultiWaitEvents) **
  (ctrl_start + verification_slice_OSTCBEventMultiRdy_off) # Ptr |-> encode_event_ptr t.(eventMultiRdy) **
  (ctrl_start + verification_slice_OSTCBMsg_off)         # Ptr  |-> encode_msg t.(msg) **
  (ctrl_start + verification_slice_OSTCBNext_off)        # Ptr  |->
    (match t.(nextTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBPrev_off)        # Ptr  |->
    (match t.(prevTCB) with None => 0 | Some tid' => verification_slice_tcb_addr sg tid' end) **
  (ctrl_start + verification_slice_OSTCBDelReq_off)      # UChar |-> encode_bool t.(delReq).

Lemma verification_slice_used_complete_task_split_priority_fields_at :
  forall sg ctrl_start tid t
         prio_addr x_addr y_addr bitx_addr bity_addr,
    task_priority_fields_layout_prop
      ctrl_start prio_addr x_addr y_addr bitx_addr bity_addr ->
    verification_slice_used_complete_task sg ctrl_start tid t |--
      used_task_priority_fields_at
        prio_addr x_addr y_addr bitx_addr bity_addr t **
      used_task_rdy_rest sg ctrl_start tid t.
Proof.
  intros sg ctrl_start tid t
    prio_addr x_addr y_addr bitx_addr bity_addr Hlayout.
  unfold task_priority_fields_layout_prop in Hlayout.
  destruct Hlayout as [Hprio [Hx [Hy [Hbitx Hbity]]]].
  subst prio_addr. subst x_addr. subst y_addr.
  subst bitx_addr. subst bity_addr.
  unfold verification_slice_used_complete_task, used_task_priority_fields_at,
    used_task_rdy_rest.
  entailer!.
Qed.

Lemma verification_slice_used_complete_task_merge_priority_fields_at :
  forall sg ctrl_start tid t
         prio_addr x_addr y_addr bitx_addr bity_addr,
    task_priority_fields_layout_prop
      ctrl_start prio_addr x_addr y_addr bitx_addr bity_addr ->
    used_task_priority_fields_at
      prio_addr x_addr y_addr bitx_addr bity_addr t **
    used_task_rdy_rest sg ctrl_start tid t |--
      verification_slice_used_complete_task sg ctrl_start tid t.
Proof.
  intros sg ctrl_start tid t
    prio_addr x_addr y_addr bitx_addr bity_addr Hlayout.
  unfold task_priority_fields_layout_prop in Hlayout.
  destruct Hlayout as [Hprio [Hx [Hy [Hbitx Hbity]]]].
  subst prio_addr. subst x_addr. subst y_addr.
  subst bitx_addr. subst bity_addr.
  unfold verification_slice_used_complete_task, used_task_priority_fields_at,
    used_task_rdy_rest.
  entailer!.
Qed.

(* ================================================================== *)
(* Phase 3 Task 3.6:verification_slice_store_used_task_map                               *)
(* ================================================================== *)

Definition verification_slice_store_used_task_map (sg : StableGlobVars)
  (m : TaskID -> option TaskAbstractState) : Assertion :=
  store_map
    (fun tid t => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid) tid t)
    m.

Definition verification_slice_store_used_task_map_missing_i (sg : StableGlobVars)
  (m : TaskID -> option TaskAbstractState) (exclude_tid : TaskID) : Assertion :=
  store_map_missing_i
    (fun tid t => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid) tid t)
    m exclude_tid.

Definition remove_two_task_entries
  (m : TaskID -> option TaskAbstractState) (tid1 tid2 : TaskID)
  : TaskID -> option TaskAbstractState :=
  fun tid =>
    if Z.eqb tid tid1 then None
    else if Z.eqb tid tid2 then None
    else m tid.

Definition verification_slice_store_used_task_map_missing_two (sg : StableGlobVars)
  (m : TaskID -> option TaskAbstractState) (tid1 tid2 : TaskID) : Assertion :=
  verification_slice_store_used_task_map sg (remove_two_task_entries m tid1 tid2).

(* ================================================================== *)
(* Phase 3 Task 3.7:verification_slice_store_free_task_list + verification_slice_store_prio_tbl             *)
(* ================================================================== *)
(* free list 与 prioTbl 均使用可展开的 list 表示。                    *)

Definition free_task_head (sg : StableGlobVars) (l : list TaskID) : addr :=
  match l with
  | [] => 0
  | tid :: _ => verification_slice_tcb_addr sg tid
  end.

Fixpoint verification_slice_store_free_task_nodes (sg : StableGlobVars)
  (l : list TaskID) : Assertion :=
  match l with
  | [] => emp
  | tid :: rest =>
      (verification_slice_tcb_addr sg tid + verification_slice_OSTCBNext_off) # Ptr |-> free_task_head sg rest **
      verification_slice_store_free_task_nodes sg rest
  end.

Definition verification_slice_store_free_task_list (sg : StableGlobVars)
  (l : list TaskID) : Assertion :=
  sg.(g_OSTCBFreeList) # Ptr |-> free_task_head sg l **
  verification_slice_store_free_task_nodes sg l.

(* ------------------------------------------------------------------ *)
(* OSTCBPrioTbl 数组的 list 抽象基础设施                              *)
(* ------------------------------------------------------------------ *)

(* 32 位平台 OS_TCB* 为 4 字节,与 task.v 中其他偏移(verification_slice_OSTCBEventPtr_off=12 *)
(* 等隐含的 4 字节指针布局)保持一致                                    *)
Definition sizeof_OSTCB_ptr : Z := 4.

Lemma sizeof_OSTCB_ptr_pos : 0 < sizeof_OSTCB_ptr.
Proof. unfold sizeof_OSTCB_ptr. lia. Qed.

Definition OS_PRIO_TBL_SIZE : Z := 64.

(* PrioTblEntry 枚举到指针值的映射:PTFree/PTReserved 用哨兵值 0/1, *)
(* PTTask tid 映射到对应 TCB 地址                                       *)
Definition verification_slice_prio_tbl_entry_to_addr (sg : StableGlobVars)
           (e : PrioTblEntry) : addr :=
  match e with
  | PTFree => 0
  | PTReserved => 1
  | PTTask tid => verification_slice_tcb_addr sg tid
  end.

(* A concrete null entry denotes [PTFree].  The only nontrivial case is a
   task pointer: task validity supplies a live, nonnegative task identifier,
   while stable-global validity makes the TCB table base strictly positive. *)
Lemma verification_slice_prio_tbl_entry_to_addr_zero_is_free :
  forall sg st p,
    valid_stable_glob_vars sg ->
    verification_slice_task_in_range sg st ->
    verification_slice_prio_tbl_entry_to_addr sg (st.(prioTbl) p) = 0 ->
    st.(prioTbl) p = PTFree.
Proof.
  intros sg st p Hstable Hvalid Hzero.
  destruct (st.(prioTbl) p) as [| | tid] eqn:Hentry.
  - reflexivity.
  - discriminate.
  - exfalso.
    unfold verification_slice_task_in_range in Hvalid.
    destruct Hvalid as [Hids [_ [_ [_ [Htable _]]]]].
    destruct (Htable p tid Hentry) as [_ [t Hlookup]].
    destruct (Hids tid t Hlookup) as [Htid _].
    unfold verification_slice_prio_tbl_entry_to_addr, verification_slice_tcb_addr, verification_slice_tcb_size in Hzero.
    pose proof
      (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable) as Hbase.
    assert (Hin : In sg.(g_OSTCBTbl) (stable_global_addresses sg)).
    { unfold stable_global_addresses. simpl. tauto. }
    specialize (Hbase Hin).
    lia.
Qed.

Fixpoint verification_slice_prioTbl_to_addrs_rec (sg : StableGlobVars)
           (f : Priority -> PrioTblEntry) (n : nat) (acc : list addr)
  : list addr :=
  match n with
  | O => acc
  | S k => verification_slice_prioTbl_to_addrs_rec sg f k (verification_slice_prio_tbl_entry_to_addr sg (f (Z.of_nat k)) :: acc)
  end.

Definition verification_slice_prioTbl_to_addrs (sg : StableGlobVars)
           (f : Priority -> PrioTblEntry) : list addr :=
  verification_slice_prioTbl_to_addrs_rec sg f 64 nil.

Definition priotbl_element_store (base : addr) (i : Z) (v : addr) : Assertion :=
  store_ptr (base + i * sizeof_OSTCB_ptr) v.

Definition verification_slice_store_priotbl_list (sg : StableGlobVars) (l : list addr) : Assertion :=
  store_array priotbl_element_store sg.(g_OSTCBPrioTbl) OS_PRIO_TBL_SIZE l.

Definition verification_slice_store_priotbl_list_missing_i (sg : StableGlobVars)
           (l : list addr) (i : Z) : Assertion :=
  store_array_missing_i_rec priotbl_element_store
                            sg.(g_OSTCBPrioTbl) i 0 OS_PRIO_TBL_SIZE l.

(* verification_slice_store_prio_tbl 现在是基于 list 的非透明 Definition,使桥接 Lemma 可证 *)
Definition verification_slice_store_prio_tbl (sg : StableGlobVars)
           (f : Priority -> PrioTblEntry) : Assertion :=
  verification_slice_store_priotbl_list sg (verification_slice_prioTbl_to_addrs sg f).

Definition verification_slice_store_prio_tbl_missing_i (sg : StableGlobVars)
           (f : Priority -> PrioTblEntry) (p : Priority) : Assertion :=
  verification_slice_store_priotbl_list_missing_i sg (verification_slice_prioTbl_to_addrs sg f) p.

Definition prio_tbl_list_rel (sg : StableGlobVars)
           (st : Glob_TaskAbstractState) (l : list addr) : Prop :=
  Zlength l = OS_PRIO_TBL_SIZE /\
  forall p, 0 <= p < OS_PRIO_TBL_SIZE ->
    Znth p l 0 = verification_slice_prio_tbl_entry_to_addr sg (st.(prioTbl) p).

Definition prio_tbl_entry_prop (st : Glob_TaskAbstractState)
  (p : Priority) (entry : PrioTblEntry) : Prop :=
  st.(prioTbl) p = entry.

(* ================================================================== *)
(* Phase 3 Task 3.8:verification_slice_task_inv + 缺一变体                                *)
(* ================================================================== *)

Definition valid_derived_fields (t : TaskAbstractState) : Prop :=
  0 <= t.(curPrio) mod 8 /\ t.(curPrio) mod 8 < 8 /\
  0 <= t.(curPrio) / 8 /\ t.(curPrio) / 8 < 8.

Definition verification_slice_task_validity (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Prop :=
  verification_slice_task_in_range sg st /\
  (forall tid t, st.(inUsedTaskStates) tid = Some t ->
                valid_task_prio sg t.(curPrio) /\
                valid_derived_fields t).

(* Historical verification-slice representation. This owns the task cells
   modeled by that slice, not the complete configured source layout. It
   carries no lifetime, range, uniqueness or priority-table consistency
   proposition. Those slice validity facts belong to
   [verification_slice_task_validity] and can therefore be lost at a transient source
   stage without losing the concrete heap. *)
Definition verification_slice_task_raw_rep (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  verification_slice_store_used_task_map sg st.(inUsedTaskStates) **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  verification_slice_store_prio_tbl sg st.(prioTbl) **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with
     | Some tid => verification_slice_tcb_addr sg tid
     | None => 0
     end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

(* Structural residual for callers that own the complete priority table
   separately.  Unlike a magic wand, it can be merged with an updated table
   representation. *)
Definition verification_slice_task_raw_rep_no_priotbl (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  verification_slice_store_used_task_map sg st.(inUsedTaskStates) **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with
     | Some tid => verification_slice_tcb_addr sg tid
     | None => 0
     end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

Lemma verification_slice_task_raw_rep_split_priotbl :
  forall sg st,
    verification_slice_task_raw_rep sg st |--
      verification_slice_store_prio_tbl sg st.(prioTbl) **
      verification_slice_task_raw_rep_no_priotbl sg st.
Proof.
  intros sg st.
  unfold verification_slice_task_raw_rep, verification_slice_task_raw_rep_no_priotbl.
  entailer!.
Qed.

Lemma verification_slice_task_raw_rep_merge_priotbl :
  forall sg st,
    verification_slice_store_prio_tbl sg st.(prioTbl) **
    verification_slice_task_raw_rep_no_priotbl sg st |--
      verification_slice_task_raw_rep sg st.
Proof.
  intros sg st.
  unfold verification_slice_task_raw_rep, verification_slice_task_raw_rep_no_priotbl.
  entailer!.
Qed.

Lemma task_vaild_cond_current_prio_registered :
  forall sg st,
    verification_slice_task_validity sg st ->
    task_current_prio_registered st.
Proof.
  intros sg st [Hvalid _].
  exact (verification_slice_task_in_range_current_prio_registered sg st Hvalid).
Qed.

Definition verification_slice_task_inv (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  coq_prop (verification_slice_task_validity sg st) &&
  verification_slice_store_used_task_map sg st.(inUsedTaskStates) **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  verification_slice_store_prio_tbl sg st.(prioTbl) **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with
     | Some tid => verification_slice_tcb_addr sg tid
     | None => 0
     end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

Lemma verification_slice_task_inv_split_raw_validity :
  forall sg st,
    verification_slice_task_inv sg st |--
      verification_slice_task_raw_rep sg st &&
      coq_prop (verification_slice_task_validity sg st).
Proof.
  intros sg st.
  unfold verification_slice_task_inv, verification_slice_task_raw_rep.
  entailer!.
Qed.

Lemma verification_slice_task_inv_current_prio_registered :
  forall sg st h,
    verification_slice_task_inv sg st h ->
    task_current_prio_registered st.
Proof.
  intros sg st h Hinv.
  unfold verification_slice_task_inv, andp, coq_prop in Hinv.
  apply (task_vaild_cond_current_prio_registered sg st).
  exact (proj1 Hinv).
Qed.

Lemma verification_slice_task_inv_entails_current_prio_registered :
  forall sg st,
    verification_slice_task_inv sg st |-- coq_prop (task_current_prio_registered st).
Proof.
  intros sg st h Hinv.
  unfold coq_prop.
  exact (verification_slice_task_inv_current_prio_registered sg st h Hinv).
Qed.

Definition verification_slice_task_inv_no_tid (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (tid : TaskID) : Assertion :=
  coq_prop (verification_slice_task_validity sg st) &&
  verification_slice_store_used_task_map_missing_i sg st.(inUsedTaskStates) tid **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  verification_slice_store_prio_tbl sg st.(prioTbl) **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with Some head => verification_slice_tcb_addr sg head | None => 0 end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

(* Residual task invariant when a caller owns the complete priority table
   separately.  This is the appropriate slice for operations such as mutex
   creation which inspect or update a priority-table entry but no TCB. *)
Definition verification_slice_task_inv_no_priotbl (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  coq_prop (verification_slice_task_validity sg st) &&
  verification_slice_store_used_task_map sg st.(inUsedTaskStates) **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with Some head => verification_slice_tcb_addr sg head | None => 0 end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

(* Reusable pure-fact exposure for reversible task localization.  Reading the
   mathematical validity fact must not consume or unfold the spatial task
   slice: callers still need the same slice in order to merge an updated
   priority table back into [verification_slice_task_inv]. *)
Lemma verification_slice_task_inv_no_priotbl_expose_valid :
  forall sg st,
    verification_slice_task_inv_no_priotbl sg st |--
      coq_prop (verification_slice_task_validity sg st) &&
      verification_slice_task_inv_no_priotbl sg st.
Proof.
  intros sg st h Hinv.
  split.
  - unfold verification_slice_task_inv_no_priotbl, andp, coq_prop in Hinv.
    exact (proj1 Hinv).
  - exact Hinv.
Qed.

Definition verification_slice_task_inv_no_tid_priotbl (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (tid : TaskID) : Assertion :=
  coq_prop (verification_slice_task_validity sg st) &&
  verification_slice_store_used_task_map_missing_i sg st.(inUsedTaskStates) tid **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with Some head => verification_slice_tcb_addr sg head | None => 0 end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

(* Reversible task-level localization used by ready-priority updates.  The
   complete priority table is exposed alongside the selected TCB because
   such updates modify both resources.  No task-state or priority-table
   property is dropped: [verification_slice_task_inv_no_tid_priotbl] retains the original
   validity proposition and every unrelated task resource. *)
Lemma verification_slice_task_inv_split_priority_fields_priotbl_at :
  forall sg st tid t
         prio_addr x_addr y_addr bitx_addr bity_addr,
    st.(inUsedTaskStates) tid = Some t ->
    task_priority_fields_layout_prop
      (verification_slice_tcb_addr sg tid) prio_addr x_addr y_addr bitx_addr bity_addr ->
    verification_slice_task_inv sg st |--
      used_task_priority_fields_at
        prio_addr x_addr y_addr bitx_addr bity_addr t **
      used_task_rdy_rest sg (verification_slice_tcb_addr sg tid) tid t **
      verification_slice_task_inv_no_tid_priotbl sg st tid **
      verification_slice_store_prio_tbl sg st.(prioTbl).
Proof.
  intros sg st tid t
    prio_addr x_addr y_addr bitx_addr bity_addr Hmap Hlayout.
  unfold verification_slice_task_inv, verification_slice_store_used_task_map.
  pureIntros.
  sepcon_lift (store_map
    (fun tid0 t0 => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t0)
    (inUsedTaskStates st)).
  sep_apply_l_atomic (store_map_split
    (fun tid0 t0 => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t0)
    tid t (inUsedTaskStates st) Hmap).
  sep_apply_l_atomic
    (verification_slice_used_complete_task_split_priority_fields_at
       sg (verification_slice_tcb_addr sg tid) tid t
       prio_addr x_addr y_addr bitx_addr bity_addr Hlayout).
  unfold verification_slice_task_inv_no_tid_priotbl, verification_slice_store_used_task_map_missing_i.
  entailer!.
Qed.

Lemma verification_slice_task_inv_merge_priority_fields_priotbl_at :
  forall sg st tid t
         prio_addr x_addr y_addr bitx_addr bity_addr,
    st.(inUsedTaskStates) tid = Some t ->
    task_priority_fields_layout_prop
      (verification_slice_tcb_addr sg tid) prio_addr x_addr y_addr bitx_addr bity_addr ->
    used_task_priority_fields_at
      prio_addr x_addr y_addr bitx_addr bity_addr t **
    used_task_rdy_rest sg (verification_slice_tcb_addr sg tid) tid t **
    verification_slice_task_inv_no_tid_priotbl sg st tid **
    verification_slice_store_prio_tbl sg st.(prioTbl) |--
      verification_slice_task_inv sg st.
Proof.
  intros sg st tid t
    prio_addr x_addr y_addr bitx_addr bity_addr Hmap Hlayout.
  unfold verification_slice_task_inv_no_tid_priotbl, verification_slice_store_used_task_map_missing_i.
  sep_apply_l_atomic
    (verification_slice_used_complete_task_merge_priority_fields_at
       sg (verification_slice_tcb_addr sg tid) tid t
       prio_addr x_addr y_addr bitx_addr bity_addr Hlayout).
  unfold verification_slice_task_inv, verification_slice_store_used_task_map.
  entailer!.
  sep_apply_l_atomic (store_map_merge
    (fun tid0 t0 => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t0)
    tid t (inUsedTaskStates st) Hmap).
  entailer!.
Qed.

Definition verification_slice_task_inv_no_two_tids_priotbl (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (tid1 tid2 : TaskID) : Assertion :=
  coq_prop (verification_slice_task_validity sg st) &&
  verification_slice_store_used_task_map_missing_two sg st.(inUsedTaskStates) tid1 tid2 **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with Some head => verification_slice_tcb_addr sg head | None => 0 end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

Definition verification_slice_task_inv_missing_usedtask (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (tid : TaskID) (t : TaskAbstractState)
  : Assertion :=
  coq_prop (verification_slice_task_validity sg st) &&
  verification_slice_store_used_task_map_missing_i sg st.(inUsedTaskStates) tid **
  verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid) tid t **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  verification_slice_store_prio_tbl sg st.(prioTbl) **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with
     | Some head_tid => verification_slice_tcb_addr sg head_tid
     | None => 0
     end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

Definition verification_slice_task_inv_missing_priotbl (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (p : Priority) : Assertion :=
  coq_prop (verification_slice_task_validity sg st) &&
  verification_slice_store_used_task_map sg st.(inUsedTaskStates) **
  verification_slice_store_free_task_list sg st.(unUsedTaskStates) **
  verification_slice_store_prio_tbl_missing_i sg st.(prioTbl) p **
  sg.(g_OSTCBList) # Ptr |->
    (match st.(tcbListHead) with
     | Some tid => verification_slice_tcb_addr sg tid
     | None => 0
     end) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount).

(* ================================================================== *)
(* Phase 3 Task 3.10: update the used-task map                         *)
(* ================================================================== *)

Definition glob_task_set_usedtask
  (st : Glob_TaskAbstractState) (tid : TaskID) (t' : TaskAbstractState)
  : Glob_TaskAbstractState :=
  {| inUsedTaskStates :=
       fun tid' => if Z.eqb tid' tid then Some t' else st.(inUsedTaskStates) tid';
     unUsedTaskStates := st.(unUsedTaskStates);
     tcbListHead      := st.(tcbListHead);
     prioTbl          := st.(prioTbl);
     taskRegNextID := st.(taskRegNextID);
     parkedTaskStacks := st.(parkedTaskStacks);
     taskLifecycle := st.(taskLifecycle);
     taskCount        := st.(taskCount);
  |}.

(** The stack owner updates its existing Task component only.  This pure
    setter neither allocates a buffer nor establishes any spatial transfer;
    those obligations belong to the resource rules consuming the old/new
    parked fragments. *)
Definition glob_task_set_parked_stacks (st : Glob_TaskAbstractState)
  (stacks : TaskStackMap) : Glob_TaskAbstractState :=
  {| inUsedTaskStates := st.(inUsedTaskStates);
     unUsedTaskStates := st.(unUsedTaskStates);
     tcbListHead := st.(tcbListHead);
     prioTbl := st.(prioTbl);
     taskCount := st.(taskCount);
     taskLifecycle := st.(taskLifecycle);
     taskRegNextID := st.(taskRegNextID);
     parkedTaskStacks := stacks |}.

Lemma glob_task_set_parked_stacks_lookup : forall st stacks,
  (glob_task_set_parked_stacks st stacks).(parkedTaskStacks) = stacks.
Proof. reflexivity. Qed.

Lemma glob_task_set_parked_stacks_put_back : forall st,
  glob_task_set_parked_stacks st st.(parkedTaskStacks) = st.
Proof. intros []; reflexivity. Qed.

Lemma glob_task_set_parked_stacks_last_write : forall st first last,
  glob_task_set_parked_stacks (glob_task_set_parked_stacks st first) last =
    glob_task_set_parked_stacks st last.
Proof. reflexivity. Qed.

Lemma glob_task_set_parked_stacks_non_stack_frame : forall st stacks,
  let post := glob_task_set_parked_stacks st stacks in
  post.(inUsedTaskStates) = st.(inUsedTaskStates) /\
  post.(unUsedTaskStates) = st.(unUsedTaskStates) /\
  post.(tcbListHead) = st.(tcbListHead) /\ post.(prioTbl) = st.(prioTbl) /\
  post.(taskCount) = st.(taskCount) /\
  post.(taskLifecycle) = st.(taskLifecycle) /\
  post.(taskRegNextID) = st.(taskRegNextID).
Proof. intros; repeat split; reflexivity. Qed.

Lemma glob_task_set_usedtask_preserves_current_prio_registered :
  forall st tid t_old t_new,
    st.(inUsedTaskStates) tid = Some t_old ->
    t_new.(curPrio) = t_old.(curPrio) ->
    task_current_prio_registered st ->
    task_current_prio_registered
      (glob_task_set_usedtask st tid t_new).
Proof.
  intros st tid t_old t_new Hlookup_old HcurPrio Hregistered.
  eapply task_current_prio_registered_preserved_by_same_priorities
    with (st1 := st).
  - intros tid' t2 Hlookup2.
    simpl in Hlookup2.
    destruct (Z.eqb tid' tid) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      subst tid'.
      inversion Hlookup2; subst t2.
      exists t_old.
      split; assumption.
    + exists t2.
      split; [exact Hlookup2 | reflexivity].
  - intros p. reflexivity.
  - exact Hregistered.
Qed.

(* No preservation lemma is stated here: replacing an arbitrary used-task
   state requires the caller to establish the updated task validity and the
   corresponding concrete TCB representation.  The former declaration used
   two focused TCBs at the same address and was therefore vacuous. *)

(** Common Pend caller prefix, after the source status byte has been read.
    Only Stat/StatPend/Dly are written here: registration pointers, the
    borrowed Multi array and the ready bitmap belong to later operations.
    This field-image interface does not assert an enabled-Multi TCB layout. *)
Definition tcb_prepare_wait_image (image : TCBCommonImage)
  (next_status timeout : Z) : TCBCommonImage :=
  tcb_write
    (tcb_write (tcb_write image TCBStat (Some next_status))
      TCBStatPend (Some (encode_pend_status PendOK)))
    TCBDly (Some timeout).

Definition tcb_prepare_multi_wait_image (image : TCBCommonImage)
  (bits events_mask timeout : Z) : TCBCommonImage :=
  tcb_prepare_wait_image image (task_status_set_multi_wait bits events_mask) timeout.

Definition tcb_event_wake_image (image : TCBCommonImage)
  (bits mask message : Z) (result : PendStatus) : TCBCommonImage :=
  tcb_write
    (tcb_write
      (tcb_write (tcb_write image TCBDly (Some 0)) TCBMsg (Some message))
      TCBStat (Some (task_status_clear_wait bits mask)))
    TCBStatPend (Some (encode_pend_status result)).

(** The caller has already stored the decremented delay.  Preserve the
    actual no-pending branch: it writes StatPend but not Stat. *)
Definition tcb_expire_status_image (image : TCBCommonImage)
  (bits : Z) : TCBCommonImage :=
  if task_status_has_pending bits then
    tcb_write
      (tcb_write image TCBStat (Some (task_status_clear_wait bits task_pend_any_mask)))
      TCBStatPend (Some (encode_pend_status PendTimeout))
  else tcb_write image TCBStatPend (Some (encode_pend_status PendOK)).

Lemma tcb_prepare_wait_image_observations : forall image bits timeout,
  tcb_prepare_wait_image image bits timeout TCBStat = Some bits /\
  tcb_prepare_wait_image image bits timeout TCBStatPend = Some 0 /\
  tcb_prepare_wait_image image bits timeout TCBDly = Some timeout.
Proof. intros; repeat split; reflexivity. Qed.

Lemma tcb_prepare_wait_image_frame : forall image bits timeout field,
  field <> TCBStat -> field <> TCBStatPend -> field <> TCBDly ->
  tcb_prepare_wait_image image bits timeout field = image field.
Proof.
  intros; unfold tcb_prepare_wait_image;
    repeat rewrite tcb_write_frame by assumption; reflexivity.
Qed.

Lemma tcb_expire_status_image_observations : forall image bits,
  image TCBStat = Some bits ->
  tcb_expire_status_image image bits TCBStat = Some (fst (task_status_timeout bits)) /\
  tcb_expire_status_image image bits TCBStatPend =
    Some (encode_pend_status (snd (task_status_timeout bits))).
Proof.
  intros image bits Hread; unfold tcb_expire_status_image, task_status_timeout.
  destruct task_status_has_pending; split; try reflexivity; exact Hread.
Qed.

Lemma tcb_expire_status_image_frame : forall image bits field,
  field <> TCBStat -> field <> TCBStatPend ->
  tcb_expire_status_image image bits field = image field.
Proof.
  intros; unfold tcb_expire_status_image; destruct task_status_has_pending;
    repeat rewrite tcb_write_frame by assumption; reflexivity.
Qed.

(** Exact TCB effects for the Multi-enabled layout.  These raw source
    phases are shared by the canonical byte-valued Task representation.
    Event/ready stores and the scheduler continuation are separate owners. *)
Definition tcb_multi_wait_image (image : TCBLayoutImage) (array : addr)
  : TCBLayoutImage := tcb_layout_set_multi image array 0.

Definition tcb_multi_pend_image (image : TCBLayoutImage)
  (bits events_mask timeout : Z) (array : addr) : TCBLayoutImage :=
  tcb_multi_wait_image
    (tcb_layout_update_common
      (fun common => tcb_prepare_multi_wait_image common bits events_mask timeout) image)
    array.

(** The MultiPtr-non-NULL branch of EventTaskRdy, including the EventPtr
    clear performed by the single Remove helper.  The Event loops neither
    modify this image nor the borrowed input array. *)
Definition tcb_multi_wake_image (image : TCBLayoutImage)
  (bits mask message : Z) (result : PendStatus) (ready : addr) : TCBLayoutImage :=
  tcb_layout_set_multi
    (tcb_layout_update_common
      (fun common => tcb_write (tcb_event_wake_image common bits mask message result)
        TCBEventPtr (Some 0)) image)
    0 ready.

(** Tick has already decremented Dly to zero at this point.  It leaves
    MultiPtr/MultiRdy and the Event registrations for subsequent cleanup. *)
Definition tcb_multi_timeout_image (image : TCBLayoutImage) (bits : Z)
  : TCBLayoutImage :=
  tcb_layout_update_common (fun common => tcb_expire_status_image common bits) image.

(** Only the normal tail of PendMulti, not its early invalid-type return.
    Source order is Stat, StatPend, MultiPtr, MultiRdy, then Msg.  Dly and
    EventPtr are not written by this tail. *)
Definition tcb_multi_cleanup_image (image : TCBLayoutImage) : TCBLayoutImage :=
  tcb_layout_update_common (fun common => tcb_write common TCBMsg (Some 0))
    (tcb_layout_set_multi
      (tcb_layout_update_common
        (fun common => tcb_write (tcb_write common TCBStat (Some 0))
          TCBStatPend (Some (encode_pend_status PendOK))) image) 0 0).

(** Single-Event Pend tail: Stat, StatPend, EventPtr, optional Multi
    fields, then the optional Msg clear.  Sem leaves Msg unchanged;
    Queue clears it.  These are source-family parameters, not OS fields
    or new runtime tests.  Neither variant writes Dly or ready bits. *)
Definition tcb_event_pend_cleanup_image (multi clear_message : bool)
  (image : TCBLayoutImage) : TCBLayoutImage :=
  let cleared := tcb_layout_update_common
    (fun common => tcb_write
      (tcb_write (tcb_write common TCBStat (Some 0))
        TCBStatPend (Some (encode_pend_status PendOK))) TCBEventPtr (Some 0)) image in
  let fields := if multi then tcb_layout_set_multi cleared 0 0 else cleared in
  if clear_message
  then tcb_layout_update_common (fun common => tcb_write common TCBMsg (Some 0)) fields
  else fields.

Definition tcb_message_pend_cleanup_image (multi : bool)
  (image : TCBLayoutImage) : TCBLayoutImage :=
  tcb_event_pend_cleanup_image multi true image.

Lemma tcb_event_pend_cleanup_image_message_frame : forall multi image,
  tcb_event_pend_cleanup_image multi false image (TCBCommonField TCBMsg) =
    image (TCBCommonField TCBMsg).
Proof. intros []; reflexivity. Qed.

Lemma tcb_multi_wait_image_common_frame : forall image array field,
  tcb_multi_wait_image image array (TCBCommonField field) = image (TCBCommonField field).
Proof. reflexivity. Qed.

(** These predicates observe the actual TCB fields at three source
    boundaries.  They do not allocate an additional phase/status field,
    own the borrowed array, or imply that Event bitmaps are consistent.
    Event registration and ready membership are separate relations. *)
Definition task_multi_registered_fields (image : TCBLayoutImage) (array : addr) : Prop :=
  array <> 0 /\ image TCBEventMultiPtr = Some array /\ image TCBEventMultiRdy = Some 0 /\
  image (TCBCommonField TCBStatPend) = Some (encode_pend_status PendOK) /\
  exists bits, image (TCBCommonField TCBStat) = Some bits /\
    task_status_is_multi bits = true /\ task_status_has_pending bits = true.

Definition task_multi_expired_fields (image : TCBLayoutImage) (array : addr) : Prop :=
  array <> 0 /\ image TCBEventMultiPtr = Some array /\ image TCBEventMultiRdy = Some 0 /\
  image (TCBCommonField TCBDly) = Some 0 /\
  image (TCBCommonField TCBStatPend) = Some (encode_pend_status PendTimeout) /\
  exists bits, image (TCBCommonField TCBStat) = Some bits /\
    task_status_is_multi bits = true /\ task_status_has_pending bits = false.

Definition task_multi_woken_fields (image : TCBLayoutImage) (ready : addr)
  (result : PendStatus) : Prop :=
  ready <> 0 /\ image TCBEventMultiPtr = Some 0 /\ image TCBEventMultiRdy = Some ready /\
  image (TCBCommonField TCBDly) = Some 0 /\
  image (TCBCommonField TCBStatPend) = Some (encode_pend_status result) /\
  exists bits, image (TCBCommonField TCBStat) = Some bits /\ task_status_is_multi bits = true.

Lemma tcb_multi_pend_registered_fields : forall image array mask (suspended : bool) timeout,
  array <> 0 -> 0 < mask < 8 ->
  task_multi_registered_fields
    (tcb_multi_pend_image image (if suspended then task_suspend_mask else 0) mask timeout array) array.
Proof.
  intros image array mask suspended timeout Harray Hmask.
  destruct (encode_multi_wait_status_observations mask suspended ltac:(lia)) as [Hpending [_ Hmulti]].
  split; [exact Harray|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  exists (encode_multi_wait_status mask suspended); split; [reflexivity|]; split; [exact Hmulti|].
  unfold task_status_has_pending; rewrite Hpending.
  rewrite (proj2 (Z.eqb_neq mask 0) ltac:(lia)); reflexivity.
Qed.

Lemma tcb_multi_timeout_expired_fields : forall image array bits,
  task_multi_registered_fields image array -> image (TCBCommonField TCBStat) = Some bits ->
  image (TCBCommonField TCBDly) = Some 0 ->
  task_multi_expired_fields (tcb_multi_timeout_image image bits) array.
Proof.
  intros image array bits [Harray [Hptr [Hrdy [Hresult [old [Hread [Hmulti Hpending]]]]]]] Hbits Hdly.
  assert (old = bits) by congruence; subst old.
  unfold tcb_multi_timeout_image, tcb_expire_status_image; rewrite Hpending.
  split; [exact Harray|]; split; [exact Hptr|]; split; [exact Hrdy|]; split; [exact Hdly|].
  split; [reflexivity|]; exists (task_status_clear_wait bits task_pend_any_mask).
  split; [reflexivity|]; split.
  - rewrite task_status_clear_pend_any_preserves_multi; exact Hmulti.
  - apply task_status_clear_pend_any_clears_pending.
Qed.

Lemma tcb_multi_wake_woken_fields : forall image bits kind message result ready,
  task_status_is_multi bits = true -> kind <> PendMulti -> ready <> 0 ->
  task_multi_woken_fields
    (tcb_multi_wake_image image bits (task_pend_mask kind) message result ready) ready result.
Proof.
  intros image bits kind message result ready Hmulti Hkind Hready.
  split; [exact Hready|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  split; [reflexivity|]; exists (task_status_clear_wait bits (task_pend_mask kind)).
  split; [reflexivity|]; rewrite task_status_clear_kind_preserves_multi by exact Hkind; exact Hmulti.
Qed.

Lemma task_multi_registered_expired_disjoint : forall image array other,
  task_multi_registered_fields image array -> ~ task_multi_expired_fields image other.
Proof.
  intros image array other [_ [_ [_ [Hok _]]]] [_ [_ [_ [_ [Htimeout _]]]]]; discriminate (eq_trans (eq_sym Hok) Htimeout).
Qed.

Lemma task_multi_linked_woken_disjoint : forall image array ready result,
  (task_multi_registered_fields image array \/ task_multi_expired_fields image array) ->
  ~ task_multi_woken_fields image ready result.
Proof.
  intros image array ready result Hlinked [_ [Hnull _]].
  destruct Hlinked as [[Harray [Hptr _]]|[Harray [Hptr _]]]; congruence.
Qed.

Lemma tcb_multi_pend_image_observations : forall image bits events_mask timeout array,
  let written := tcb_multi_pend_image image bits events_mask timeout array in
  written (TCBCommonField TCBStat) = Some (task_status_set_multi_wait bits events_mask) /\
  written (TCBCommonField TCBStatPend) = Some (encode_pend_status PendOK) /\
  written (TCBCommonField TCBDly) = Some timeout /\
  written TCBEventMultiPtr = Some array /\ written TCBEventMultiRdy = Some 0.
Proof. intros; repeat split; reflexivity. Qed.

Lemma tcb_multi_pend_image_frame : forall image bits events_mask timeout array field,
  field <> TCBCommonField TCBStat -> field <> TCBCommonField TCBStatPend ->
  field <> TCBCommonField TCBDly -> field <> TCBEventMultiPtr -> field <> TCBEventMultiRdy ->
  tcb_multi_pend_image image bits events_mask timeout array field = image field.
Proof.
  intros image bits events_mask timeout array [field| | | | | | |] Hstat Hresult Hdly Hptr Hrdy;
    try contradiction; try reflexivity.
  change (tcb_prepare_wait_image (tcb_layout_common_image image)
    (task_status_set_multi_wait bits events_mask) timeout field = image (TCBCommonField field)).
  apply tcb_prepare_wait_image_frame; congruence.
Qed.

Lemma tcb_multi_wake_image_observations : forall image bits mask message result ready,
  let written := tcb_multi_wake_image image bits mask message result ready in
  written (TCBCommonField TCBDly) = Some 0 /\ written (TCBCommonField TCBMsg) = Some message /\
  written (TCBCommonField TCBStat) = Some (task_status_clear_wait bits mask) /\
  written (TCBCommonField TCBStatPend) = Some (encode_pend_status result) /\
  written (TCBCommonField TCBEventPtr) = Some 0 /\
  written TCBEventMultiPtr = Some 0 /\ written TCBEventMultiRdy = Some ready.
Proof. intros; repeat split; reflexivity. Qed.

Lemma tcb_multi_wake_image_frame : forall image bits mask message result ready field,
  field <> TCBCommonField TCBDly -> field <> TCBCommonField TCBMsg ->
  field <> TCBCommonField TCBStat -> field <> TCBCommonField TCBStatPend ->
  field <> TCBCommonField TCBEventPtr -> field <> TCBEventMultiPtr -> field <> TCBEventMultiRdy ->
  tcb_multi_wake_image image bits mask message result ready field = image field.
Proof.
  intros image bits mask message result ready [field| | | | | | |] Hdly Hmsg Hstat Hresult Hevent Hptr Hrdy;
    try contradiction; try reflexivity.
  change (tcb_write
    (tcb_event_wake_image (tcb_layout_common_image image) bits mask message result)
    TCBEventPtr (Some 0) field = image (TCBCommonField field)).
  unfold tcb_event_wake_image; repeat rewrite tcb_write_frame by congruence; reflexivity.
Qed.

Lemma tcb_multi_timeout_image_observations : forall image bits,
  image (TCBCommonField TCBStat) = Some bits ->
  let written := tcb_multi_timeout_image image bits in
  written (TCBCommonField TCBStat) = Some (fst (task_status_timeout bits)) /\
  written (TCBCommonField TCBStatPend) = Some (encode_pend_status (snd (task_status_timeout bits))) /\
  written TCBEventMultiPtr = image TCBEventMultiPtr /\ written TCBEventMultiRdy = image TCBEventMultiRdy.
Proof.
  intros image bits Hread; cbn zeta.
  destruct (tcb_expire_status_image_observations (tcb_layout_common_image image) bits Hread)
    as [Hstat Hresult].
  split; [exact Hstat|]; split; [exact Hresult|]; split; reflexivity.
Qed.

Lemma tcb_multi_timeout_image_frame : forall image bits field,
  field <> TCBCommonField TCBStat -> field <> TCBCommonField TCBStatPend ->
  tcb_multi_timeout_image image bits field = image field.
Proof.
  intros image bits [field| | | | | | |] Hstat Hresult; try reflexivity.
  apply tcb_expire_status_image_frame; congruence.
Qed.

Lemma tcb_multi_cleanup_image_observations : forall image,
  let written := tcb_multi_cleanup_image image in
  written (TCBCommonField TCBStat) = Some 0 /\ written (TCBCommonField TCBStatPend) = Some 0 /\
  written TCBEventMultiPtr = Some 0 /\ written TCBEventMultiRdy = Some 0 /\
  written (TCBCommonField TCBMsg) = Some 0 /\
  written (TCBCommonField TCBDly) = image (TCBCommonField TCBDly) /\
  written (TCBCommonField TCBEventPtr) = image (TCBCommonField TCBEventPtr).
Proof. intros; repeat split; reflexivity. Qed.

Lemma tcb_multi_cleanup_image_frame : forall image field,
  field <> TCBCommonField TCBStat -> field <> TCBCommonField TCBStatPend ->
  field <> TCBCommonField TCBMsg -> field <> TCBEventMultiPtr -> field <> TCBEventMultiRdy ->
  tcb_multi_cleanup_image image field = image field.
Proof.
  intros image [field| | | | | | |] Hstat Hresult Hmsg Hptr Hrdy; try contradiction; try reflexivity.
  change (tcb_write
    (tcb_write (tcb_write (tcb_layout_common_image image) TCBStat (Some 0))
      TCBStatPend (Some 0)) TCBMsg (Some 0) field = image (TCBCommonField field)).
  repeat rewrite tcb_write_frame by congruence; reflexivity.
Qed.


(** Fixed-64 compatibility view.  Current native resources use the
    configured encoder below; this one belongs to task_tcb64_image. *)
Definition encode_tcb64_link (sg : StableGlobVars) (p : option TaskID) : addr :=
  match p with None => 0 | Some tid => tcb64_addr sg tid end.

Definition encode_task_link (sg : StableGlobVars) (p : option TaskID) : addr :=
  match p with None => 0 | Some tid => task_slot_addr sg tid end.

Lemma encode_task_link_tcb64 : forall sg p,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  encode_task_link sg p = encode_tcb64_link sg p.
Proof. intros sg [tid|] Hmulti Hprofile; [apply task_slot_addr_tcb64; assumption|reflexivity]. Qed.

Definition task_slot_storage_rep (sg : StableGlobVars) (tid : TaskID)
  (image : TCBLayoutImage) : Assertion :=
  tcb_configured_storage_rep sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) image.

Lemma task_slot_storage_tcb64 : forall sg tid image,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  task_slot_storage_rep sg tid image --||--
    tcb64_storage_rep (tcb64_addr sg tid) (tcb_layout_common_image image).
Proof.
  intros sg tid image Hmulti Hprofile; unfold task_slot_storage_rep.
  rewrite Hmulti, Hprofile, task_slot_addr_tcb64 by assumption.
  rewrite tcb_configured_storage_no_profile; apply tcb_layout_no_multi_rep_equiv.
Qed.

Definition encode_event_link (sg : StableGlobVars) (p : option EventID) : addr :=
  match p with None => 0 | Some eid => event_pool_addr sg eid end.

Definition encode_task_delete_request (request : bool) : Z :=
  if request then 63 else 0.

Definition task_tcb64_image (sg : StableGlobVars) (t : TaskAbstractState)
  : TCBCommonImage :=
  fun f =>
  match f with
  | TCBStkPtr => Some t.(tcbStkPtr) | TCBExtPtr => Some t.(tcbExtPtr)
  | TCBStkBottom => Some t.(tcbStkBottom) | TCBStkSize => Some t.(tcbStkSize)
  | TCBOpt => Some t.(tcbOpt) | TCBId => Some t.(tcbPublicId)
  | TCBNext => Some (encode_tcb64_link sg t.(nextTCB))
  | TCBPrev => Some (encode_tcb64_link sg t.(prevTCB))
  | TCBEventPtr => Some (encode_event_link sg t.(eventPtr))
  | TCBMsg => Some (encode_msg t.(msg))
  | TCBFlagNode => Some t.(tcbFlagNode) | TCBFlagsRdy => Some t.(tcbFlagsRdy)
  | TCBPadding42 => t.(tcbPadding42) | TCBPadding43 => t.(tcbPadding43)
  | TCBDly => Some t.(dly) | TCBStat => Some (encode_task_status t.(stat))
  | TCBStatPend => Some (encode_pend_status t.(statPend))
  | TCBPrio => Some t.(curPrio) | TCBX => Some (tcb_x_of_prio t.(curPrio))
  | TCBY => Some (tcb_y_of_prio t.(curPrio))
  | TCBBitX => Some (tcb_bit_x_of_prio t.(curPrio))
  | TCBBitY => Some (tcb_bit_y_of_prio t.(curPrio))
  | TCBDelReq => Some (encode_task_delete_request t.(delReq))
  | TCBTaskName => Some t.(tcbTaskName) | TCBReg0 => Some t.(tcbReg0)
  end.

(** The used-task image is derived from the existing abstract task, not a
    second mutable pool.  Common scalar encodings are shared with the fixed
    profile; links use the configured pool and MultiPtr stores the real
    array address, never the first element of eventMultiWaitEvents.  Full raw
    status/continuation validity is separate from this storage interface. *)
Definition task_layout_image (sg : StableGlobVars) (t : TaskAbstractState)
  : TCBLayoutImage :=
  tcb_layout_image
    (fun field => match field with
      | TCBNext => Some (encode_task_link sg t.(nextTCB))
      | TCBPrev => Some (encode_task_link sg t.(prevTCB))
      | _ => task_tcb64_image sg t field
      end)
    (Some t.(tcbEventMultiPtr))
    (Some (encode_event_link sg t.(eventMultiRdy)))
    (Some t.(tcbCtxSwCtr)) (Some t.(tcbCyclesTot)) (Some t.(tcbCyclesStart))
    (Some t.(tcbStkBase)) (Some t.(tcbStkUsed)).

(** Updates of the five real profiling fields keep the rest of the task,
    including its identity, wait state, priority and links, unchanged. *)
Definition task_set_profile (t : TaskAbstractState)
  (switches cycles start stack_base used : Z) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr); tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom); tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt); tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode); tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName); tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := switches; tcbCyclesTot := cycles; tcbCyclesStart := start;
     tcbStkBase := stack_base; tcbStkUsed := used;
     tcbPadding42 := t.(tcbPadding42); tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := t.(stat); statPend := t.(statPend);
     dly := t.(dly); eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg); nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_set_profile_frame : forall sg t switches cycles start stack_base used field,
  ~ In field tcb_profile_fields ->
  task_layout_image sg (task_set_profile t switches cycles start stack_base used) field =
    task_layout_image sg t field.
Proof.
  intros sg t switches cycles start stack_base used field Hfield.
  destruct field; try reflexivity; simpl in Hfield; tauto.
Qed.

(** OS_Sched and OSIntExit increment the selected high-ready task's INT32U
    counter before the platform context switch. This is only that C store,
    not an assertion that the ARM context-switch implementation is proved. *)
Definition task_record_context_switch (t : TaskAbstractState) : TaskAbstractState :=
  task_set_profile t (kernel_u32 (t.(tcbCtxSwCtr) + 1))
    t.(tcbCyclesTot) t.(tcbCyclesStart) t.(tcbStkBase) t.(tcbStkUsed).

Lemma task_record_context_switch_in_range : forall t,
  0 <= (task_record_context_switch t).(tcbCtxSwCtr) < 4294967296.
Proof. intros; apply kernel_u32_in_range. Qed.

Lemma task_record_context_switch_layout_image_eq : forall sg t,
  task_layout_image sg (task_record_context_switch t) =
    tcb_layout_write (task_layout_image sg t) TCBCtxSwCtr
      (Some (kernel_u32 (t.(tcbCtxSwCtr) + 1))).
Proof. intros; apply functional_extensionality; intros []; reflexivity. Qed.

(** The stack checker writes the two profiling stack fields after its
    current priority-table lookup.  This image equation keeps the other
    profiling counters, multi-event cells, common fields and padding at the
    lookup snapshot; the two concrete stores are therefore represented by
    two ordinary field updates rather than a second task record. *)
Lemma task_set_profile_stack_fields_layout_image_eq : forall sg t stack_base used,
  task_layout_image sg
      (task_set_profile t t.(tcbCtxSwCtr) t.(tcbCyclesTot) t.(tcbCyclesStart)
        stack_base used) =
    tcb_layout_write
      (tcb_layout_write (task_layout_image sg t) TCBStkBase (Some stack_base))
      TCBStkUsed (Some used).
Proof.
  intros sg t stack_base used.
  apply functional_extensionality; intros field.
  destruct field; reflexivity.
Qed.

Lemma tcb_configured_storage_merge_context_switch : forall multi base sg t,
  tcb_layout_cell multi base TCBCtxSwCtr (Some (kernel_u32 (t.(tcbCtxSwCtr) + 1))) **
    tcb_configured_storage_without_field multi true base (task_layout_image sg t) TCBCtxSwCtr |--
      tcb_configured_storage_rep multi true base
        (task_layout_image sg (task_record_context_switch t)).
Proof.
  intros; rewrite task_record_context_switch_layout_image_eq.
  apply tcb_configured_storage_merge_updated_field.
  apply tcb_configured_profile_field_in; simpl; tauto.
Qed.

Lemma task_layout_common_image_tcb64 : forall sg t,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tcb_layout_common_image (task_layout_image sg t) = task_tcb64_image sg t.
Proof.
  intros sg t Hmulti Hprofile; apply functional_extensionality; intros []; try reflexivity;
    cbn [tcb_layout_common_image task_layout_image tcb_layout_image task_tcb64_image];
    rewrite encode_task_link_tcb64 by assumption; reflexivity.
Qed.

Definition used_task_rep (sg : StableGlobVars) (tid : TaskID)
  (t : TaskAbstractState) : Assertion :=
  task_slot_storage_rep sg tid (task_layout_image sg t).

Lemma used_task_rep_tcb64 : forall sg tid t,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  used_task_rep sg tid t --||--
    tcb64_storage_rep (tcb64_addr sg tid) (task_tcb64_image sg t).
Proof.
  intros sg tid t Hmulti Hprofile; unfold used_task_rep.
  rewrite task_slot_storage_tcb64 by assumption.
  rewrite task_layout_common_image_tcb64 by assumption; split; reflexivity.
Qed.

Lemma glob_task_set_usedtask_lifecycle_frame : forall st tid t,
  (glob_task_set_usedtask st tid t).(taskLifecycle) = st.(taskLifecycle).
Proof. reflexivity. Qed.

Definition task_lifecycle_set_reservation (life : TaskLifecycleState)
  (p : Priority) (entry : option TaskCreationEntry) : TaskLifecycleState :=
  {| taskFreeStorage := life.(taskFreeStorage);
     taskReservations := fun q => if Z.eq_dec q p then entry else life.(taskReservations) q;
     taskActiveOrder := life.(taskActiveOrder);
     taskNextGeneration := life.(taskNextGeneration);
     taskInvocations := life.(taskInvocations);
     taskRetiredInvocations := life.(taskRetiredInvocations);
     taskNextInvocation := life.(taskNextInvocation);
     taskPublications := life.(taskPublications) |}.

Definition glob_task_set_lifecycle (st : Glob_TaskAbstractState)
  (life : TaskLifecycleState) : Glob_TaskAbstractState :=
  {| inUsedTaskStates := st.(inUsedTaskStates);
     unUsedTaskStates := st.(unUsedTaskStates);
     tcbListHead := st.(tcbListHead);
     prioTbl := st.(prioTbl);
     taskCount := st.(taskCount);
     taskRegNextID := st.(taskRegNextID);
     parkedTaskStacks := st.(parkedTaskStacks);
     taskLifecycle := life |}.

Definition task_private_slot (st : Glob_TaskAbstractState) (tid : TaskID) : Prop :=
  exists p entry allocation,
    st.(taskLifecycle).(taskReservations) p = Some entry /\
    entry.(creationAllocation) = Some allocation /\
    allocation.(privateSlot) = tid.

Definition task_pool_partition (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Prop :=
  (forall tid, task_slot_in_range sg tid <->
     (exists t, st.(inUsedTaskStates) tid = Some t) \/
     In tid st.(unUsedTaskStates) \/ task_private_slot st tid) /\
  (forall tid t, st.(inUsedTaskStates) tid = Some t ->
     ~ In tid st.(unUsedTaskStates) /\ ~ task_private_slot st tid) /\
  (forall tid, In tid st.(unUsedTaskStates) -> ~ task_private_slot st tid) /\
  NoDup st.(unUsedTaskStates) /\
  (forall tid, In tid st.(unUsedTaskStates) <->
     exists image, st.(taskLifecycle).(taskFreeStorage) tid = Some image) /\
  (forall p q e1 e2 a1 a2,
     st.(taskLifecycle).(taskReservations) p = Some e1 ->
     st.(taskLifecycle).(taskReservations) q = Some e2 ->
     e1.(creationAllocation) = Some a1 ->
     e2.(creationAllocation) = Some a2 ->
     a1.(privateSlot) = a2.(privateSlot) -> p = q).

Fixpoint task_active_links
  (used : TaskID -> option TaskAbstractState) (previous : option TaskID)
  (ids : list TaskID) : Prop :=
  match ids with
  | [] => True
  | tid :: rest =>
      exists t, used tid = Some t /\ t.(taskID) = tid /\
        t.(prevTCB) = previous /\ t.(nextTCB) = hd_error rest /\
        task_active_links used (Some tid) rest
  end.

Definition task_active_closure (st : Glob_TaskAbstractState) : Prop :=
  let ids := st.(taskLifecycle).(taskActiveOrder) in
  NoDup ids /\
  st.(tcbListHead) = hd_error ids /\
  st.(taskCount) = Z.of_nat (List.length ids) /\
  (forall tid, In tid ids <-> exists t, st.(inUsedTaskStates) tid = Some t) /\
  task_active_links st.(inUsedTaskStates) None ids.

Fixpoint task_free_links (sg : StableGlobVars)
  (storage : TaskID -> option TCBLayoutImage) (ids : list TaskID) : Prop :=
  match ids with
  | [] => True
  | tid :: rest =>
      exists image, storage tid = Some image /\
        image (TCBCommonField TCBNext) = Some (encode_task_link sg (hd_error rest)) /\
        task_free_links sg storage rest
  end.

Definition task_invocation_origin_live (st : Glob_TaskAbstractState)
  (origin : TaskInvocationOrigin) : Prop :=
  match origin with
  | BootInvocation => True
  | RunningInvocation tid generation =>
      exists t, st.(inUsedTaskStates) tid = Some t /\
        t.(taskGeneration) = generation
  end.

Definition task_reservation_closure (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Prop :=
  (forall p entry,
     st.(taskLifecycle).(taskReservations) p = Some entry ->
     task_priority_in_range sg p /\ st.(prioTbl) p = PTReserved /\
     st.(taskLifecycle).(taskInvocations) entry.(creationInvocation) =
       Some entry.(creationOrigin)) /\
  (forall p q e1 e2,
     st.(taskLifecycle).(taskReservations) p = Some e1 ->
     st.(taskLifecycle).(taskReservations) q = Some e2 ->
     e1.(creationInvocation) = e2.(creationInvocation) -> p = q).

Definition task_generation_closure (st : Glob_TaskAbstractState) : Prop :=
  (forall tid t, st.(inUsedTaskStates) tid = Some t ->
     (t.(taskGeneration) < st.(taskLifecycle).(taskNextGeneration))%nat) /\
  (forall p entry allocation,
     st.(taskLifecycle).(taskReservations) p = Some entry ->
     entry.(creationAllocation) = Some allocation ->
     (allocation.(privateGeneration) < st.(taskLifecycle).(taskNextGeneration))%nat) /\
  (forall invocation origin,
     st.(taskLifecycle).(taskInvocations) invocation = Some origin ->
     (invocation < st.(taskLifecycle).(taskNextInvocation))%nat) /\
  (forall invocation tid generation,
     st.(taskLifecycle).(taskInvocations) invocation =
       Some (RunningInvocation tid generation) ->
     (generation < st.(taskLifecycle).(taskNextGeneration))%nat) /\
  (forall invocation tid generation,
     In (invocation, tid, generation) st.(taskLifecycle).(taskPublications) ->
     (generation < st.(taskLifecycle).(taskNextGeneration))%nat) /\
  (** A detached allocation is fresh for this slot and generation.  Detach
      takes nextGeneration; commit removes the reservation before recording
      its publication.  Old publications remain after slot recycling. *)
  (forall p entry allocation observer,
     st.(taskLifecycle).(taskReservations) p = Some entry ->
     entry.(creationAllocation) = Some allocation ->
     ~ In (observer, allocation.(privateSlot), allocation.(privateGeneration))
         st.(taskLifecycle).(taskPublications)).

(** InitTCBList zeroes FlagsRdy; reuse leaves a previously initialized
    scalar.  OS_TCBInit does not write it.  The other stale free fields are
    still raw storage and need not decode as a live task or list links. *)
Definition task_free_reuse_closure (st : Glob_TaskAbstractState) : Prop :=
  forall tid image, st.(taskLifecycle).(taskFreeStorage) tid = Some image ->
    exists flags, image (TCBCommonField TCBFlagsRdy) = Some flags.

(** Boot may have an empty active list.  Only the running protocol promises
    the idle-priority last node needed by OSTimeTick's non-NULL traversal. *)
Definition task_idle_tail (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Prop :=
  exists prefix idle t,
    st.(taskLifecycle).(taskActiveOrder) = prefix ++ [idle] /\
    st.(inUsedTaskStates) idle = Some t /\ t.(curPrio) = sg.(osLowestPrio) /\
    (forall tid other, In tid prefix ->
       st.(inUsedTaskStates) tid = Some other ->
       other.(curPrio) <> sg.(osLowestPrio)).

Definition valid_task_reg_allocator (sg : StableGlobVars) (st : Glob_TaskAbstractState) : Prop :=
  0 <= st.(taskRegNextID) <= sg.(osKernelConfig).(cfgTaskRegisters).

Definition task_in_range (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Prop :=
  task_pool_partition sg st /\
  task_active_closure st /\
  task_free_links sg st.(taskLifecycle).(taskFreeStorage) st.(unUsedTaskStates) /\
  task_reservation_closure sg st /\
  task_generation_closure st /\
  task_current_prio_registered st /\ task_priority_unique st /\
  (forall tid t, st.(inUsedTaskStates) tid = Some t ->
     task_priority_in_range sg t.(curPrio)) /\
  task_free_reuse_closure st /\ valid_task_reg_allocator sg st.

Fixpoint task_free_storage_rep (sg : StableGlobVars)
  (storage : TaskID -> option TCBLayoutImage) (ids : list TaskID) : Assertion :=
  match ids with
  | [] => emp
  | tid :: rest =>
      (EX image, coq_prop (storage tid = Some image) &&
        task_slot_storage_rep sg tid image) **
      task_free_storage_rep sg storage rest
  end.

Lemma task_free_storage_open_head : forall sg storage tid rest,
  task_free_storage_rep sg storage (tid :: rest) =
  (EX image, coq_prop (storage tid = Some image) &&
    task_slot_storage_rep sg tid image) **
  task_free_storage_rep sg storage rest.
Proof. reflexivity. Qed.

Lemma task_private_excludes_public : forall sg st tid,
  task_pool_partition sg st -> task_private_slot st tid ->
  st.(inUsedTaskStates) tid = None /\ ~ In tid st.(unUsedTaskStates).
Proof.
  intros sg st tid [_ [Hused [Hfree _]]] Hprivate.
  split.
  - destruct (st.(inUsedTaskStates) tid) eqn:Hlookup; [|reflexivity].
    destruct (Hused tid t Hlookup); contradiction.
  - intro Hin; exact (Hfree tid Hin Hprivate).
Qed.

Lemma task_live_has_one_occurrence : forall st tid t,
  task_active_closure st -> st.(inUsedTaskStates) tid = Some t ->
  In tid st.(taskLifecycle).(taskActiveOrder) /\
  NoDup st.(taskLifecycle).(taskActiveOrder).
Proof.
  intros st tid t [Hnodup [_ [_ [Hcover _]]]] Hlookup.
  split; [apply Hcover; eauto | exact Hnodup].
Qed.

Definition task_begin_invocation (origin : TaskInvocationOrigin)
  (st : Glob_TaskAbstractState) : Glob_TaskAbstractState :=
  let life := st.(taskLifecycle) in
  glob_task_set_lifecycle st
    {| taskFreeStorage := life.(taskFreeStorage);
       taskReservations := life.(taskReservations);
       taskActiveOrder := life.(taskActiveOrder);
       taskNextGeneration := life.(taskNextGeneration);
       taskInvocations := fun invocation =>
         if Nat.eq_dec invocation life.(taskNextInvocation)
         then Some origin else life.(taskInvocations) invocation;
       taskRetiredInvocations := fun invocation =>
         if Nat.eq_dec invocation life.(taskNextInvocation)
         then false else life.(taskRetiredInvocations) invocation;
       taskNextInvocation := S life.(taskNextInvocation);
       taskPublications := life.(taskPublications) |}.

Lemma task_begin_invocation_token : forall st origin,
  (task_begin_invocation origin st).(taskLifecycle).(taskInvocations)
    st.(taskLifecycle).(taskNextInvocation) = Some origin.
Proof. intros; simpl; destruct Nat.eq_dec; congruence. Qed.

Lemma task_begin_invocation_fresh : forall st,
  task_generation_closure st ->
  st.(taskLifecycle).(taskInvocations) st.(taskLifecycle).(taskNextInvocation) = None.
Proof.
  intros st [_ [_ [Hbound _]]].
  destruct (st.(taskLifecycle).(taskInvocations)
    st.(taskLifecycle).(taskNextInvocation)) eqn:Hlookup; [|reflexivity].
  specialize (Hbound _ _ Hlookup); lia.
Qed.

Definition task_reserve (st : Glob_TaskAbstractState) (p : Priority)
  (invocation : nat) (origin : TaskInvocationOrigin) : Glob_TaskAbstractState :=
  {| inUsedTaskStates := st.(inUsedTaskStates);
     unUsedTaskStates := st.(unUsedTaskStates);
     tcbListHead := st.(tcbListHead);
     prioTbl := fun q => if Z.eq_dec q p then PTReserved else st.(prioTbl) q;
     taskCount := st.(taskCount);
     taskRegNextID := st.(taskRegNextID);
     parkedTaskStacks := st.(parkedTaskStacks);
     taskLifecycle := task_lifecycle_set_reservation st.(taskLifecycle) p
       (Some {| creationInvocation := invocation; creationOrigin := origin;
                creationAllocation := None |}) |}.

Definition task_reserve_guard (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (p : Priority) (invocation : nat)
  (origin : TaskInvocationOrigin) : Prop :=
  task_priority_in_range sg p /\ st.(prioTbl) p = PTFree /\
  st.(taskLifecycle).(taskInvocations) invocation = Some origin /\
  st.(taskLifecycle).(taskRetiredInvocations) invocation = false /\
  task_invocation_origin_live st origin /\
  (forall q entry, st.(taskLifecycle).(taskReservations) q = Some entry ->
     entry.(creationInvocation) <> invocation).

Lemma task_reserve_state_fields_eq : forall st p invocation origin,
  let post := task_reserve st p invocation origin in
  post.(prioTbl) p = PTReserved /\
  post.(taskLifecycle).(taskReservations) p =
    Some {| creationInvocation := invocation; creationOrigin := origin;
            creationAllocation := None |} /\
  post.(inUsedTaskStates) = st.(inUsedTaskStates) /\
  post.(unUsedTaskStates) = st.(unUsedTaskStates) /\
  post.(taskLifecycle).(taskFreeStorage) = st.(taskLifecycle).(taskFreeStorage).
Proof. intros; simpl; destruct Z.eq_dec; [repeat split; reflexivity | contradiction]. Qed.

Lemma task_reserve_other_priority : forall st p q invocation origin,
  q <> p ->
  (task_reserve st p invocation origin).(prioTbl) q = st.(prioTbl) q /\
  (task_reserve st p invocation origin).(taskLifecycle).(taskReservations) q =
    st.(taskLifecycle).(taskReservations) q.
Proof. intros; simpl; destruct Z.eq_dec; [contradiction | split; reflexivity]. Qed.

Definition task_detach_head (st : Glob_TaskAbstractState)
  (p : Priority) (entry : TaskCreationEntry) (tid : TaskID)
  (rest : list TaskID) (image : TCBLayoutImage) : Glob_TaskAbstractState :=
  let life := st.(taskLifecycle) in
  {| inUsedTaskStates := st.(inUsedTaskStates);
     unUsedTaskStates := rest;
     tcbListHead := st.(tcbListHead);
     prioTbl := st.(prioTbl);
     taskCount := st.(taskCount);
     taskRegNextID := st.(taskRegNextID);
     parkedTaskStacks := st.(parkedTaskStacks);
     taskLifecycle :=
       {| taskFreeStorage := fun slot =>
            if Z.eq_dec slot tid then None else life.(taskFreeStorage) slot;
          taskReservations := fun q => if Z.eq_dec q p then
            Some {| creationInvocation := entry.(creationInvocation);
                    creationOrigin := entry.(creationOrigin);
                    creationAllocation := Some
                      {| privateSlot := tid;
                         privateGeneration := life.(taskNextGeneration);
                         privateStorage := image |} |}
            else life.(taskReservations) q;
          taskActiveOrder := life.(taskActiveOrder);
          taskNextGeneration := S life.(taskNextGeneration);
          taskInvocations := life.(taskInvocations);
     taskRetiredInvocations := life.(taskRetiredInvocations);
          taskNextInvocation := life.(taskNextInvocation);
          taskPublications := life.(taskPublications) |} |}.

Definition task_detach_guard (st : Glob_TaskAbstractState)
  (p : Priority) (entry : TaskCreationEntry) (tid : TaskID)
  (rest : list TaskID) (image : TCBLayoutImage) : Prop :=
  st.(unUsedTaskStates) = tid :: rest /\
  st.(taskLifecycle).(taskReservations) p = Some entry /\
  entry.(creationAllocation) = None /\
  st.(taskLifecycle).(taskFreeStorage) tid = Some image.

Lemma task_detach_transfers_free_head_to_private : forall st p entry tid rest image,
  let post := task_detach_head st p entry tid rest image in
  post.(unUsedTaskStates) = rest /\
  post.(taskLifecycle).(taskFreeStorage) tid = None /\
  post.(inUsedTaskStates) = st.(inUsedTaskStates) /\
  post.(prioTbl) = st.(prioTbl) /\
  post.(taskCount) = st.(taskCount) /\ task_private_slot post tid.
Proof.
  intros; simpl; destruct (Z.eq_dec tid tid); [|contradiction].
  repeat split; try reflexivity.
  unfold task_private_slot; simpl.
  exists p; destruct (Z.eq_dec p p); [|contradiction].
  eexists; eexists; repeat split; reflexivity.
Qed.

Definition task_update_private_image (st : Glob_TaskAbstractState)
  (p : Priority) (entry : TaskCreationEntry) (allocation : TaskPrivateAllocation)
  (image : TCBLayoutImage) : Glob_TaskAbstractState :=
  glob_task_set_lifecycle st
    (task_lifecycle_set_reservation st.(taskLifecycle) p
      (Some {| creationInvocation := entry.(creationInvocation);
               creationOrigin := entry.(creationOrigin);
               creationAllocation := Some
                 {| privateSlot := allocation.(privateSlot);
                    privateGeneration := allocation.(privateGeneration);
                    privateStorage := image |} |})).

Lemma task_private_update_public_frame : forall st p entry allocation image,
  let post := task_update_private_image st p entry allocation image in
  post.(inUsedTaskStates) = st.(inUsedTaskStates) /\
  post.(unUsedTaskStates) = st.(unUsedTaskStates) /\
  post.(prioTbl) = st.(prioTbl) /\ post.(tcbListHead) = st.(tcbListHead) /\
  post.(taskCount) = st.(taskCount) /\
  post.(taskLifecycle).(taskPublications) = st.(taskLifecycle).(taskPublications).
Proof. intros; repeat split; reflexivity. Qed.

Definition task_rollback_reservation (st : Glob_TaskAbstractState)
  (p : Priority) : Glob_TaskAbstractState :=
  {| inUsedTaskStates := st.(inUsedTaskStates);
     unUsedTaskStates := st.(unUsedTaskStates);
     tcbListHead := st.(tcbListHead);
     prioTbl := fun q => if Z.eq_dec q p then PTFree else st.(prioTbl) q;
     taskCount := st.(taskCount);
     taskRegNextID := st.(taskRegNextID);
     parkedTaskStacks := st.(parkedTaskStacks);
     taskLifecycle := task_lifecycle_set_reservation st.(taskLifecycle) p None |}.

Definition task_rollback_guard (st : Glob_TaskAbstractState)
  (p : Priority) (invocation : nat) : Prop :=
  exists entry, st.(taskLifecycle).(taskReservations) p = Some entry /\
    entry.(creationInvocation) = invocation /\ entry.(creationAllocation) = None.

Lemma task_rollback_state_fields_eq : forall st p,
  let post := task_rollback_reservation st p in
  post.(prioTbl) p = PTFree /\
  post.(taskLifecycle).(taskReservations) p = None /\
  post.(inUsedTaskStates) = st.(inUsedTaskStates) /\
  post.(unUsedTaskStates) = st.(unUsedTaskStates) /\
  post.(taskLifecycle).(taskFreeStorage) = st.(taskLifecycle).(taskFreeStorage).
Proof. intros; simpl; destruct Z.eq_dec; [repeat split; reflexivity | contradiction]. Qed.

(** Source-shaped link updates retain every non-link field, including the
    allocation generation and all native-only bytes. *)
Definition task_set_links (t : TaskAbstractState)
  (next previous : option TaskID) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr); curPrio := t.(curPrio); stat := t.(stat);
     statPend := t.(statPend); dly := t.(dly); eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg); nextTCB := next; prevTCB := previous; delReq := t.(delReq) |}.

Definition task_commit (st : Glob_TaskAbstractState)
  (p : Priority) (invocation : nat) (node : TaskAbstractState)
  : Glob_TaskAbstractState :=
  let tid := node.(taskID) in
  let life := st.(taskLifecycle) in
  let update_old_head := fun slot =>
    match st.(tcbListHead), st.(inUsedTaskStates) slot with
    | Some head, Some t => if Z.eq_dec slot head
        then Some (task_set_links t t.(nextTCB) (Some tid)) else Some t
    | _, previous => previous
    end in
  {| inUsedTaskStates := fun slot => if Z.eq_dec slot tid
       then Some (task_set_links node st.(tcbListHead) None)
       else update_old_head slot;
     unUsedTaskStates := st.(unUsedTaskStates);
     tcbListHead := Some tid;
     prioTbl := fun q => if Z.eq_dec q p then PTTask tid else st.(prioTbl) q;
     taskCount := st.(taskCount) + 1;
     taskRegNextID := st.(taskRegNextID);
     parkedTaskStacks := st.(parkedTaskStacks);
     taskLifecycle :=
       {| taskFreeStorage := life.(taskFreeStorage);
          taskReservations := fun q => if Z.eq_dec q p then None else life.(taskReservations) q;
          taskActiveOrder := tid :: life.(taskActiveOrder);
          taskNextGeneration := life.(taskNextGeneration);
          taskInvocations := life.(taskInvocations);
     taskRetiredInvocations := life.(taskRetiredInvocations);
          taskNextInvocation := life.(taskNextInvocation);
          taskPublications := (invocation, tid, node.(taskGeneration)) :: life.(taskPublications) |} |}.

Lemma task_commit_publication_fields_eq : forall st p invocation node,
  let post := task_commit st p invocation node in
  post.(inUsedTaskStates) node.(taskID) =
    Some (task_set_links node st.(tcbListHead) None) /\
  post.(prioTbl) p = PTTask node.(taskID) /\
  post.(tcbListHead) = Some node.(taskID) /\
  post.(taskCount) = st.(taskCount) + 1 /\
  post.(taskLifecycle).(taskReservations) p = None /\
  post.(taskLifecycle).(taskPublications) =
    (invocation, node.(taskID), node.(taskGeneration)) ::
      st.(taskLifecycle).(taskPublications).
Proof.
  intros; simpl.
  destruct (Z.eq_dec (taskID node) (taskID node)); [|contradiction].
  destruct (Z.eq_dec p p); [repeat split; reflexivity | contradiction].
Qed.

Lemma task_commit_non_target_frame : forall st p invocation node slot,
  slot <> node.(taskID) -> st.(tcbListHead) <> Some slot ->
  (task_commit st p invocation node).(inUsedTaskStates) slot =
    st.(inUsedTaskStates) slot.
Proof.
  intros; simpl; destruct (Z.eq_dec slot (taskID node)); [contradiction|].
  destruct (tcbListHead st) as [head|]; [|reflexivity].
  destruct (inUsedTaskStates st slot); [|reflexivity].
  destruct (Z.eq_dec slot head); [subst; contradiction | reflexivity].
Qed.

Definition task_publication_happened (st : Glob_TaskAbstractState)
  (invocation : nat) (slot : TaskID) (generation : nat) : Prop :=
  In (invocation, slot, generation) st.(taskLifecycle).(taskPublications).

Lemma task_commit_records_history : forall st p invocation node,
  task_publication_happened (task_commit st p invocation node)
    invocation node.(taskID) node.(taskGeneration).
Proof. intros; unfold task_publication_happened; simpl; auto. Qed.

(** The reservation ledger remains meaningful after its creator is deleted:
    the C delete path does not reclaim another invocation's reservation or
    private TCB.  Retiring execution is different from erasing its resources. *)
Definition task_retire_invocation (st : Glob_TaskAbstractState)
  (invocation : nat) : Glob_TaskAbstractState :=
  let life := st.(taskLifecycle) in glob_task_set_lifecycle st
    {| taskFreeStorage := life.(taskFreeStorage);
       taskReservations := life.(taskReservations);
       taskActiveOrder := life.(taskActiveOrder);
       taskNextGeneration := life.(taskNextGeneration);
       taskInvocations := life.(taskInvocations);
       taskRetiredInvocations := fun other => if Nat.eq_dec other invocation
         then true else life.(taskRetiredInvocations) other;
       taskNextInvocation := life.(taskNextInvocation);
       taskPublications := life.(taskPublications) |}.

Definition task_invocation_active (st : Glob_TaskAbstractState)
  (invocation : nat) (origin : TaskInvocationOrigin) : Prop :=
  st.(taskLifecycle).(taskInvocations) invocation = Some origin /\
  st.(taskLifecycle).(taskRetiredInvocations) invocation = false /\
  task_invocation_origin_live st origin.

(** Updating the same live instance keeps saved invocation identities.
    This is lifetime preservation, not readiness or a promise to return. *)
Lemma glob_task_set_usedtask_preserves_invocation_active : forall st tid old replacement invocation origin,
  st.(inUsedTaskStates) tid = Some old -> replacement.(taskGeneration) = old.(taskGeneration) ->
  task_invocation_active st invocation origin ->
  task_invocation_active (glob_task_set_usedtask st tid replacement) invocation origin.
Proof.
  intros st tid old replacement invocation origin Hold Hg [Hinv [Hretired Hlive]].
  split; [exact Hinv|]; split; [exact Hretired|].
  destruct origin as [|slot generation]; [exact I|].
  destruct Hlive as [t [Ht Hgeneration]].
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot.
    assert (t = old) by congruence; subst t; exists replacement; split.
    + simpl; rewrite Z.eqb_refl; reflexivity.
    + congruence.
  - exists t; split; [simpl; rewrite Hslot; exact Ht|exact Hgeneration].
Qed.

Lemma task_retire_preserves_pending_resources : forall st invocation,
  (task_retire_invocation st invocation).(taskLifecycle).(taskReservations) =
    st.(taskLifecycle).(taskReservations) /\
  (task_retire_invocation st invocation).(taskLifecycle).(taskFreeStorage) =
    st.(taskLifecycle).(taskFreeStorage).
Proof. intros; split; reflexivity. Qed.

Lemma task_retired_invocation_not_active : forall st invocation origin,
  ~ task_invocation_active
      (task_retire_invocation st invocation) invocation origin.
Proof.
  intros st invocation origin [_ [Hactive _]]; simpl in Hactive.
  destruct (Nat.eq_dec invocation invocation); congruence.
Qed.

Definition prio_tbl_entry_to_addr (sg : StableGlobVars)
  (entry : PrioTblEntry) : addr :=
  match entry with
  | PTFree => 0 | PTReserved => 1 | PTTask tid => task_slot_addr sg tid
  end.

Definition store_used_task_map (sg : StableGlobVars)
  (used : TaskID -> option TaskAbstractState) : Assertion :=
  store_map (used_task_rep sg) used.

Definition store_prio_tbl (sg : StableGlobVars)
  (table : Priority -> PrioTblEntry) : Assertion :=
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (map (fun p => prio_tbl_entry_to_addr sg (table p)) (Zrange 0 64)).

Definition task_reg_allocator_rep (sg : StableGlobVars) (st : Glob_TaskAbstractState) : Assertion :=
  if Z.ltb 0 sg.(osKernelConfig).(cfgTaskRegisters) then
    sg.(g_OSTaskRegNextAvailID) # UChar |-> st.(taskRegNextID)
  else emp.

Definition task_public_storage (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  store_used_task_map sg st.(inUsedTaskStates) **
  task_free_storage_rep sg st.(taskLifecycle).(taskFreeStorage) st.(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error st.(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg st.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount) **
  store_prio_tbl sg st.(prioTbl) ** task_reg_allocator_rep sg st.

(** The complete public owner with only the priority table removed.  Its
    invocation ledger is logical metadata and owns no extra table cells. *)
Definition task_public_storage_without_prio_tbl (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  store_used_task_map sg st.(inUsedTaskStates) **
  task_free_storage_rep sg st.(taskLifecycle).(taskFreeStorage) st.(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error st.(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg st.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount) ** task_reg_allocator_rep sg st.

Lemma task_public_storage_prio_tbl_equiv : forall sg st,
  task_public_storage sg st --||--
    store_prio_tbl sg st.(prioTbl) ** task_public_storage_without_prio_tbl sg st.
Proof.
  intros; unfold task_public_storage, task_public_storage_without_prio_tbl;
    split; entailer!.
Qed.

Definition task_private_allocations_for_invocation
  (st : Glob_TaskAbstractState) (invocation : nat)
  : Priority -> option TaskPrivateAllocation :=
  fun p => match st.(taskLifecycle).(taskReservations) p with
  | None => None
  | Some entry => if Nat.eq_dec entry.(creationInvocation) invocation
      then entry.(creationAllocation) else None
  end.

Definition task_private_storage (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (invocation : nat) : Assertion :=
  store_map (fun _ allocation =>
    task_slot_storage_rep sg allocation.(privateSlot) allocation.(privateStorage))
    (task_private_allocations_for_invocation st invocation).

Definition task_private_storage_without_priority (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (invocation : nat) (p : Priority) : Assertion :=
  store_map_missing_i (fun _ allocation =>
    task_slot_storage_rep sg allocation.(privateSlot) allocation.(privateStorage))
    (task_private_allocations_for_invocation st invocation) p.

Lemma task_private_allocation_lookup : forall st p entry allocation invocation,
  st.(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationInvocation) = invocation -> entry.(creationAllocation) = Some allocation ->
  task_private_allocations_for_invocation st invocation p = Some allocation.
Proof.
  intros st p entry allocation invocation Hentry Hinv Ha.
  unfold task_private_allocations_for_invocation; rewrite Hentry.
  destruct Nat.eq_dec; [exact Ha|contradiction].
Qed.

Lemma task_private_storage_split_allocation : forall sg st p entry allocation invocation,
  st.(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationInvocation) = invocation -> entry.(creationAllocation) = Some allocation ->
  task_private_storage sg st invocation |--
    task_slot_storage_rep sg allocation.(privateSlot) allocation.(privateStorage) **
    task_private_storage_without_priority sg st invocation p.
Proof.
  intros sg st p entry allocation invocation Hentry Hinv Ha.
  unfold task_private_storage, task_private_storage_without_priority.
  sep_apply_l_atomic (store_map_split (fun _ a =>
    task_slot_storage_rep sg a.(privateSlot) a.(privateStorage)) p allocation _
    (task_private_allocation_lookup st p entry allocation invocation Hentry Hinv Ha)).
  entailer!.
Qed.

Lemma task_private_storage_merge_allocation : forall sg st p entry allocation invocation,
  st.(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationInvocation) = invocation -> entry.(creationAllocation) = Some allocation ->
  task_slot_storage_rep sg allocation.(privateSlot) allocation.(privateStorage) **
    task_private_storage_without_priority sg st invocation p |--
    task_private_storage sg st invocation.
Proof.
  intros sg st p entry allocation invocation Hentry Hinv Ha.
  unfold task_private_storage, task_private_storage_without_priority.
  sep_apply_l_atomic (store_map_merge (fun _ a =>
    task_slot_storage_rep sg a.(privateSlot) a.(privateStorage)) p allocation _
    (task_private_allocation_lookup st p entry allocation invocation Hentry Hinv Ha)).
  entailer!.
Qed.

Lemma task_private_storage_merge_updated_image :
  forall sg st p entry allocation invocation image,
    entry.(creationInvocation) = invocation ->
    task_slot_storage_rep sg allocation.(privateSlot) image **
      task_private_storage_without_priority sg st invocation p |--
    task_private_storage sg
      (task_update_private_image st p entry allocation image) invocation.
Proof.
  intros sg st p entry allocation invocation image Hinv.
  let updated := constr:({| privateSlot := allocation.(privateSlot);
    privateGeneration := allocation.(privateGeneration); privateStorage := image |}) in
  assert (Hlookup : task_private_allocations_for_invocation
    (task_update_private_image st p entry allocation image) invocation p = Some updated).
  { unfold task_private_allocations_for_invocation; simpl.
    destruct (Z.eq_dec p p); [|contradiction].
    destruct Nat.eq_dec; [reflexivity|contradiction]. }
  assert (Hoff : forall q, q <> p ->
    task_private_allocations_for_invocation st invocation q =
    task_private_allocations_for_invocation
      (task_update_private_image st p entry allocation image) invocation q).
  { intros q Hneq; unfold task_private_allocations_for_invocation; simpl.
    destruct (Z.eq_dec q p); [contradiction|reflexivity]. }
  unfold task_private_storage, task_private_storage_without_priority.
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (fun _ a =>
    task_slot_storage_rep sg a.(privateSlot) a.(privateStorage)) _ _ p Hoff)).
  sep_apply_l_atomic (store_map_merge (fun _ a =>
    task_slot_storage_rep sg a.(privateSlot) a.(privateStorage)) p _ _ Hlookup).
  entailer!.
Qed.

(** A field cut retains the rest of this exact allocation and every other
    priority owned by this invocation.  Updated merge uses the existing
    reservation, slot and generation; it cannot manufacture a new lifetime. *)
Definition task_private_storage_without_field (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (invocation : nat) (p : Priority)
  (allocation : TaskPrivateAllocation) (field : TCBLayoutField) : Assertion :=
  tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg allocation.(privateSlot))
    allocation.(privateStorage) field **
  task_private_storage_without_priority sg st invocation p.

Lemma task_private_storage_split_field :
  forall sg st p entry allocation invocation field,
    st.(taskLifecycle).(taskReservations) p = Some entry ->
    entry.(creationInvocation) = invocation ->
    entry.(creationAllocation) = Some allocation ->
    In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile)) ->
    task_private_storage sg st invocation |--
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg allocation.(privateSlot))
      field (allocation.(privateStorage) field) **
    task_private_storage_without_field sg st invocation p allocation field.
Proof.
  intros sg st p entry allocation invocation field Hentry Hinv Ha Hin.
  eapply derivable1_trans.
  - eapply task_private_storage_split_allocation; eauto.
  - unfold task_private_storage_without_field.
    rewrite logic_equiv_sepcon_assoc.
    apply derivable1_sepcon_mono; [apply tcb_configured_storage_split_field; exact Hin|reflexivity].
Qed.

Lemma task_private_storage_merge_field :
  forall sg st p entry allocation invocation field,
    st.(taskLifecycle).(taskReservations) p = Some entry ->
    entry.(creationInvocation) = invocation ->
    entry.(creationAllocation) = Some allocation ->
    In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile)) ->
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg allocation.(privateSlot))
      field (allocation.(privateStorage) field) **
    task_private_storage_without_field sg st invocation p allocation field |--
    task_private_storage sg st invocation.
Proof.
  intros sg st p entry allocation invocation field Hentry Hinv Ha Hin.
  unfold task_private_storage_without_field.
  rewrite logic_equiv_sepcon_assoc.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono; [apply tcb_configured_storage_merge_field; exact Hin|reflexivity].
  - eapply task_private_storage_merge_allocation; eauto.
Qed.

Lemma task_private_storage_merge_updated_field :
  forall sg st p entry allocation invocation field value,
    st.(taskLifecycle).(taskReservations) p = Some entry ->
    entry.(creationInvocation) = invocation ->
    entry.(creationAllocation) = Some allocation ->
    In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile)) ->
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg allocation.(privateSlot)) field value **
    task_private_storage_without_field sg st invocation p allocation field |--
    task_private_storage sg
      (task_update_private_image st p entry allocation
        (tcb_layout_write allocation.(privateStorage) field value)) invocation.
Proof.
  intros sg st p entry allocation invocation field value Hentry Hinv Ha Hin.
  unfold task_private_storage_without_field.
  rewrite logic_equiv_sepcon_assoc.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono; [apply tcb_configured_storage_merge_updated_field; exact Hin|reflexivity].
  - apply task_private_storage_merge_updated_image; exact Hinv.
Qed.

Lemma task_update_private_image_preserves_in_range :
  forall sg st p entry allocation image,
    task_in_range sg st ->
    st.(taskLifecycle).(taskReservations) p = Some entry ->
    entry.(creationAllocation) = Some allocation ->
    task_in_range sg (task_update_private_image st p entry allocation image).
Proof.
  intros sg st p entry allocation image
    [Hpool [Hactive [Hlinks [Hres [Hgen [Hregistered [Hunique [Hprios Hreuse]]]]]]]] Hentry Ha.
  assert (Htransport : forall q new,
    (task_update_private_image st p entry allocation image).(taskLifecycle).(taskReservations) q = Some new ->
    exists old, st.(taskLifecycle).(taskReservations) q = Some old /\
      new.(creationInvocation) = old.(creationInvocation) /\
      new.(creationOrigin) = old.(creationOrigin) /\
      (forall a, new.(creationAllocation) = Some a -> exists b,
         old.(creationAllocation) = Some b /\ a.(privateSlot) = b.(privateSlot) /\
         a.(privateGeneration) = b.(privateGeneration))).
  { intros q new Hnew; simpl in Hnew.
    destruct (Z.eq_dec q p) as [->|Hneq].
    - inversion Hnew; subst new; exists entry.
      split; [exact Hentry|]. split; [reflexivity|]. split; [reflexivity|].
      intros a Halloc; simpl in Halloc; inversion Halloc; subst a.
      exists allocation; auto.
    - exists new; repeat split; try assumption; try reflexivity.
      intros a Halloc; exists a; auto. }
  assert (Hprivate : forall slot,
    task_private_slot (task_update_private_image st p entry allocation image) slot <->
    task_private_slot st slot).
  { intro slot; split.
    - intros [q [new [a [Hq [Halloc Hslot]]]]].
      destruct (Htransport q new Hq) as [old [Hold [_ [_ Hallocs]]]].
      destruct (Hallocs a Halloc) as [b [Hb [Hslots Hg]]].
      exists q, old, b; repeat split; try assumption; congruence.
    - intros [q [old [a [Hq [Halloc Hslot]]]]].
      destruct (Z.eq_dec q p) as [->|Hneq].
      + rewrite Hentry in Hq; inversion Hq; subst old.
        rewrite Ha in Halloc; inversion Halloc; subst a.
        exists p; eexists; eexists; simpl.
        destruct (Z.eq_dec p p); [repeat split; try reflexivity; exact Hslot|contradiction].
      + exists q, old, a; simpl; destruct (Z.eq_dec q p); [contradiction|auto]. }
  assert (HpoolPost : task_pool_partition sg
    (task_update_private_image st p entry allocation image)).
  { destruct Hpool as [Hcover [Hused [Hfree [Hnd [Hstorage Hslots]]]]].
    unfold task_pool_partition; split.
    - intro slot; simpl; rewrite Hprivate; exact (Hcover slot).
    - split.
      + intros slot t Ht; destruct (Hused slot t Ht) as [Hnf Hnp].
        split; [exact Hnf|rewrite Hprivate; exact Hnp].
      + split.
        * intros slot Hin; rewrite Hprivate; exact (Hfree slot Hin).
        * split; [exact Hnd|]. split; [exact Hstorage|].
          intros q r e1 e2 a1 a2 Hq Hr Ha1 Ha2 Hsame.
          destruct (Htransport q e1 Hq) as [o1 [Ho1 [_ [_ HT1]]]].
          destruct (Htransport r e2 Hr) as [o2 [Ho2 [_ [_ HT2]]]].
          destruct (HT1 a1 Ha1) as [b1 [Hb1 [Hs1 Hg1]]].
          destruct (HT2 a2 Ha2) as [b2 [Hb2 [Hs2 Hg2]]].
          eapply Hslots; eauto; congruence. }
  assert (HresPost : task_reservation_closure sg
    (task_update_private_image st p entry allocation image)).
  { destruct Hres as [Hbinding Howner]; split.
    - intros q new Hq.
      destruct (Htransport q new Hq) as [old [Hold [Hinv [Horigin _]]]].
      change (task_priority_in_range sg q /\ st.(prioTbl) q = PTReserved /\
        st.(taskLifecycle).(taskInvocations) new.(creationInvocation) = Some new.(creationOrigin)).
      rewrite Hinv, Horigin; exact (Hbinding q old Hold).
    - intros q r e1 e2 Hq Hr Hsame.
      destruct (Htransport q e1 Hq) as [o1 [Ho1 [Hi1 _]]].
      destruct (Htransport r e2 Hr) as [o2 [Ho2 [Hi2 _]]].
      eapply Howner; eauto; congruence. }
  assert (HgenPost : task_generation_closure
    (task_update_private_image st p entry allocation image)).
  { destruct Hgen as [Hlive [HprivateBound [Hinv [Hhistory [Hpublished Hunpublished]]]]].
    split; [exact Hlive|]. split.
    - intros q new a Hq Halloc.
      destruct (Htransport q new Hq) as [old [Hold [_ [_ HT]]]].
      destruct (HT a Halloc) as [b [Hb [Hs Hg]]].
      change (a.(privateGeneration) < st.(taskLifecycle).(taskNextGeneration))%nat.
      rewrite Hg; eapply HprivateBound; eauto.
    - split; [exact Hinv|]. split; [exact Hhistory|].
      split; [exact Hpublished|].
      intros q new a observer Hq Halloc Hin.
      destruct (Htransport q new Hq) as [old [Hold [_ [_ HT]]]].
      destruct (HT a Halloc) as [b [Hb [Hs Hg]]].
      change (In (observer, a.(privateSlot), a.(privateGeneration))
        st.(taskLifecycle).(taskPublications)) in Hin.
      rewrite Hs, Hg in Hin.
      exact (Hunpublished q old b observer Hold Hb Hin). }
  split; [exact HpoolPost|]. split; [exact Hactive|]. split; [exact Hlinks|].
  split; [exact HresPost|]. split; [exact HgenPost|].
  split; [exact Hregistered|]. split; [exact Hunique|]. split; assumption.
Qed.

Definition task_inv (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  coq_prop (selected_kernel_profile sg /\ task_in_range sg st) &&
  task_public_storage sg st.

Lemma task_begin_invocation_unreserved : forall sg st origin p entry,
  task_reservation_closure sg st -> task_generation_closure st ->
  (task_begin_invocation origin st).(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationInvocation) <> st.(taskLifecycle).(taskNextInvocation).
Proof.
  intros sg st origin p entry [Hbinding _] [_ [_ [Hfresh _]]] Hentry Heq.
  simpl in Hentry.
  destruct (Hbinding p entry Hentry) as [_ [_ Hledger]].
  specialize (Hfresh _ _ Hledger); rewrite Heq in Hfresh; lia.
Qed.

Lemma task_reserve_preserves_registration : forall st p invocation origin,
  task_current_prio_registered st -> st.(prioTbl) p = PTFree ->
  task_current_prio_registered (task_reserve st p invocation origin).
Proof.
  intros st p invocation origin Hregistered Hfree tid t Hlookup.
  simpl in Hlookup |- *.
  specialize (Hregistered tid t Hlookup).
  destruct (Z.eq_dec (curPrio t) p); [subst; rewrite Hfree in Hregistered; discriminate |].
  exact Hregistered.
Qed.

Lemma task_reserve_preserves_reservation_closure :
  forall sg st p invocation origin,
    task_reservation_closure sg st ->
    task_reserve_guard sg st p invocation origin ->
    task_reservation_closure sg (task_reserve st p invocation origin).
Proof.
  intros sg st p invocation origin [Hbinding Hunique]
    [Hprio [Hfree [Hledger [Hactive [Hlive Hfresh]]]]].
  split.
  - intros q entry Hentry; simpl in Hentry |- *.
    destruct (Z.eq_dec q p) as [->|Hqp].
    + inversion Hentry; subst; simpl.
      split; [exact Hprio |].
      split; [destruct (Z.eq_dec p p); [reflexivity | contradiction] | exact Hledger].
    + exact (Hbinding q entry Hentry).
  - intros q r e1 e2 Hq Hr Hsame; simpl in Hq, Hr.
    destruct (Z.eq_dec q p) as [->|Hqp];
      destruct (Z.eq_dec r p) as [->|Hrp].
    + reflexivity.
    + inversion Hq; subst; simpl in Hsame.
      exfalso; apply (Hfresh r e2 Hr); symmetry; exact Hsame.
    + inversion Hr; subst; simpl in Hsame.
      exfalso; apply (Hfresh q e1 Hq); exact Hsame.
    + eapply Hunique; eauto.
Qed.

Lemma task_reserve_private_slot_frame : forall st p invocation origin tid,
  st.(taskLifecycle).(taskReservations) p = None ->
  (task_private_slot (task_reserve st p invocation origin) tid <->
   task_private_slot st tid).
Proof.
  intros st p invocation origin tid Hnone; split.
  - intros [q [entry [allocation [Hentry [Hallocation Hslot]]]]].
    simpl in Hentry; destruct (Z.eq_dec q p) as [->|Hqp].
    + inversion Hentry; subst; discriminate.
    + exists q, entry, allocation; auto.
  - intros [q [entry [allocation [Hentry [Hallocation Hslot]]]]].
    exists q, entry, allocation; simpl.
    destruct (Z.eq_dec q p) as [->|Hqp]; [rewrite Hnone in Hentry; discriminate|].
    auto.
Qed.

Lemma task_reserve_preserves_pool_partition : forall sg st p invocation origin,
  task_pool_partition sg st ->
  st.(taskLifecycle).(taskReservations) p = None ->
  task_pool_partition sg (task_reserve st p invocation origin).
Proof.
  intros sg st p invocation origin
    [Hcover [Hused [Hfree [Hnodup [Hstorage Hunique]]]]] Hnone.
  pose proof (task_reserve_private_slot_frame st p invocation origin) as Hprivate.
  unfold task_pool_partition.
  split.
  - intros tid; simpl.
    rewrite Hprivate by exact Hnone; apply Hcover.
  - split.
    + intros tid t Hlookup; simpl in Hlookup |- *.
      destruct (Hused tid t Hlookup) as [Hnotfree Hnotprivate].
      split; [exact Hnotfree | rewrite Hprivate by exact Hnone; exact Hnotprivate].
    + split.
      * intros tid Hin; simpl in Hin.
        rewrite Hprivate by exact Hnone; apply Hfree; exact Hin.
      * split; [exact Hnodup|].
        split; [exact Hstorage|].
        intros q r e1 e2 a1 a2 Hq Hr Ha1 Ha2 Hslots.
        simpl in Hq, Hr.
        destruct (Z.eq_dec q p) as [->|Hqp];
          destruct (Z.eq_dec r p) as [->|Hrp].
        -- inversion Hq; subst; discriminate.
        -- inversion Hq; subst; discriminate.
        -- inversion Hr; subst; discriminate.
        -- eapply Hunique; eauto.
Qed.

Lemma task_detach_private_slot_iff : forall st p entry tid rest image slot,
  task_detach_guard st p entry tid rest image ->
  (task_private_slot (task_detach_head st p entry tid rest image) slot <->
   slot = tid \/ task_private_slot st slot).
Proof.
  intros st p entry tid rest image slot [Hlist [Hentry [Hnone Himage]]]; split.
  - intros [q [e [a [Hq [Ha Hslot]]]]].
    simpl in Hq; destruct (Z.eq_dec q p) as [->|Hqp].
    + inversion Hq; subst e; simpl in Ha; inversion Ha; subst a.
      simpl in Hslot; left; symmetry; exact Hslot.
    + right; exists q, e, a; auto.
  - intros [Hslot | [q [e [a [Hq [Ha Hslot]]]]]].
    + subst slot; exists p; simpl.
      destruct (Z.eq_dec p p); [|contradiction].
      eexists; eexists; repeat split; reflexivity.
    + exists q, e, a; simpl.
      destruct (Z.eq_dec q p) as [->|Hqp].
      * rewrite Hentry in Hq; inversion Hq; subst e.
        rewrite Hnone in Ha; discriminate.
      * auto.
Qed.

Lemma task_detach_preserves_pool_partition :
  forall sg st p entry tid rest image,
    task_pool_partition sg st ->
    task_detach_guard st p entry tid rest image ->
    task_pool_partition sg (task_detach_head st p entry tid rest image).
Proof.
  intros sg st p entry tid rest image
    [Hcover [Hused [Hfree [Hnodup [Hstorage Hunique]]]]] Hguard.
  destruct Hguard as [Hlist [Hentry [Hnone Himage]]].
  assert (Hguard : task_detach_guard st p entry tid rest image).
  { repeat split; assumption. }
  assert (Hprivate := task_detach_private_slot_iff st p entry tid rest image).
  rewrite Hlist in Hnodup; inversion Hnodup as [|? ? Hnotin Hrest]; subst.
  unfold task_pool_partition; split.
  - intro slot; rewrite Hprivate by exact Hguard.
    change (task_slot_in_range sg slot <->
      (exists t, st.(inUsedTaskStates) slot = Some t) \/
      In slot rest \/ slot = tid \/ task_private_slot st slot).
    rewrite Hcover, Hlist; simpl; intuition congruence.
  - split.
    + intros slot t Hlookup; simpl in Hlookup |- *.
      destruct (Hused slot t Hlookup) as [Hnotfree Hnotprivate].
      rewrite Hlist in Hnotfree; simpl in Hnotfree.
      split; [tauto|].
      rewrite Hprivate by exact Hguard; intros [Heq | Hp]; [subst; tauto | contradiction].
    + split.
      * intros slot Hin; simpl in Hin.
        rewrite Hprivate by exact Hguard; intros [Heq | Hp].
        -- subst; contradiction.
        -- apply (Hfree slot); [rewrite Hlist; simpl; auto | exact Hp].
      * split; [exact Hrest|].
        split.
        -- intro slot; simpl.
           destruct (Z.eq_dec slot tid) as [->|Hslot].
           ++ split; [contradiction | intros [i Hi]; discriminate].
           ++ specialize (Hstorage slot); rewrite Hlist in Hstorage; simpl in Hstorage;
                intuition congruence.
        -- intros q r e1 e2 a1 a2 Hq Hr Ha1 Ha2 Hslots.
           simpl in Hq, Hr.
           destruct (Z.eq_dec q p) as [->|Hqp];
             destruct (Z.eq_dec r p) as [->|Hrp].
           ++ reflexivity.
           ++ inversion Hq; subst e1; simpl in Ha1; inversion Ha1; subst a1.
              simpl in Hslots; exfalso; apply (Hfree tid).
              ** rewrite Hlist; simpl; auto.
              ** exists r, e2, a2; repeat split; try assumption; symmetry; exact Hslots.
           ++ inversion Hr; subst e2; simpl in Ha2; inversion Ha2; subst a2.
              simpl in Hslots; exfalso; apply (Hfree tid).
              ** rewrite Hlist; simpl; auto.
              ** exists q, e1, a1; repeat split; assumption.
           ++ eapply Hunique; eauto.
Qed.

Lemma task_detach_preserves_active_closure : forall st p entry tid rest image,
  task_active_closure st ->
  task_active_closure (task_detach_head st p entry tid rest image).
Proof. intros; exact H. Qed.

Lemma task_detach_preserves_reservation_closure :
  forall sg st p entry tid rest image,
    task_reservation_closure sg st ->
    st.(taskLifecycle).(taskReservations) p = Some entry ->
    task_reservation_closure sg (task_detach_head st p entry tid rest image).
Proof.
  intros sg st p entry tid rest image [Hbinding Hunique] Hentry; split.
  - intros q e Hq; simpl in Hq |- *.
    destruct (Z.eq_dec q p) as [->|Hqp].
    + inversion Hq; subst e; simpl; exact (Hbinding p entry Hentry).
    + exact (Hbinding q e Hq).
  - intros q r e1 e2 Hq Hr Hsame; simpl in Hq, Hr.
    destruct (Z.eq_dec q p) as [->|Hqp];
      destruct (Z.eq_dec r p) as [->|Hrp].
    + reflexivity.
    + inversion Hq; subst e1; simpl in Hsame; eapply Hunique; eauto.
    + inversion Hr; subst e2; simpl in Hsame; eapply Hunique; eauto.
    + eapply Hunique; eauto.
Qed.

Lemma task_free_links_storage_ext : forall sg ids old new,
  (forall tid, In tid ids -> new tid = old tid) ->
  task_free_links sg old ids -> task_free_links sg new ids.
Proof.
  intros sg ids; induction ids as [|tid rest IH]; intros old new Heq Hlinks.
  - exact I.
  - destruct Hlinks as [image [Hget [Hnext Htail]]].
    exists image; split; [rewrite Heq by (left; reflexivity); exact Hget|].
    split; [exact Hnext|].
    apply (IH old new); [intros q Hin; apply Heq; right; exact Hin|exact Htail].
Qed.

Lemma task_reserve_preserves_generation : forall st p invocation origin,
  task_generation_closure st ->
  task_generation_closure (task_reserve st p invocation origin).
Proof.
  intros st p invocation origin [Hused [Hprivate [Hinv [Hhistory [Hpub Hunpublished]]]]].
  split; [exact Hused|]. split.
  - intros q entry allocation Hentry Halloc; simpl in Hentry |- *.
    destruct (Z.eq_dec q p).
    + inversion Hentry; subst entry; discriminate.
    + eapply Hprivate; eauto.
  - split; [exact Hinv|]. split; [exact Hhistory|]. split; [exact Hpub|].
    intros q entry allocation observer Hentry Halloc Hin; simpl in Hentry, Hin.
    destruct (Z.eq_dec q p).
    + inversion Hentry; subst entry; discriminate.
    + exact (Hunpublished q entry allocation observer Hentry Halloc Hin).
Qed.

Lemma task_reserve_preserves_in_range : forall sg st p invocation origin,
  task_in_range sg st ->
  task_reserve_guard sg st p invocation origin ->
  task_in_range sg (task_reserve st p invocation origin).
Proof.
  intros sg st p invocation origin Hrange Hguard.
  destruct Hrange as
    [Hpool [Hactive [Hlinks [Hres [Hgen [Hreg [Hunique [Hprio Hreuse]]]]]]]].
  assert (Hfree : st.(prioTbl) p = PTFree) by exact (proj1 (proj2 Hguard)).
  assert (Hnone : st.(taskLifecycle).(taskReservations) p = None).
  { destruct (st.(taskLifecycle).(taskReservations) p) as [entry|] eqn:Hentry; [|reflexivity].
    pose proof (proj1 Hres p entry Hentry) as [_ [Hreserved _]].
    rewrite Hfree in Hreserved; discriminate. }
  split; [apply task_reserve_preserves_pool_partition; assumption|].
  split; [exact Hactive|]. split; [exact Hlinks|].
  split; [apply task_reserve_preserves_reservation_closure; assumption|].
  split; [apply task_reserve_preserves_generation; exact Hgen|].
  split; [apply task_reserve_preserves_registration; assumption|].
  split; [exact Hunique|]. split; assumption.
Qed.

Lemma task_detach_preserves_generation : forall st p entry tid rest image,
  task_generation_closure st ->
  task_generation_closure (task_detach_head st p entry tid rest image).
Proof.
  intros st p entry tid rest image [Hused [Hprivate [Hinv [Hhistory [Hpub Hunpublished]]]]].
  split.
  - intros slot t Hget; simpl in Hget |- *; specialize (Hused slot t Hget); lia.
  - split.
    + intros q e a Hget Ha; simpl in Hget |- *.
      destruct (Z.eq_dec q p).
      * inversion Hget; subst e; simpl in Ha; inversion Ha; subst a; simpl; lia.
      * specialize (Hprivate q e a Hget Ha); lia.
    + split; [exact Hinv|]. split.
      * intros inv slot generation Hget; simpl in Hget |- *.
        specialize (Hhistory inv slot generation Hget); lia.
      * split.
        -- intros inv slot generation Hin; simpl in Hin |- *.
           specialize (Hpub inv slot generation Hin); lia.
        -- intros q e a observer Hget Ha Hin; simpl in Hget, Hin.
           destruct (Z.eq_dec q p).
           ++ inversion Hget; subst e; simpl in Ha; inversion Ha; subst a.
              simpl in Hin; pose proof (Hpub observer tid
                st.(taskLifecycle).(taskNextGeneration) Hin); lia.
           ++ exact (Hunpublished q e a observer Hget Ha Hin).
Qed.

Lemma task_detach_preserves_in_range : forall sg st p entry tid rest image,
  task_in_range sg st -> task_detach_guard st p entry tid rest image ->
  task_in_range sg (task_detach_head st p entry tid rest image).
Proof.
  intros sg st p entry tid rest image Hrange Hguard.
  destruct Hrange as
    [Hpool [Hactive [Hlinks [Hres [Hgen [Hreg [Hunique [Hprio Hreuse]]]]]]]].
  destruct Hguard as [Hlist [Hentry [Hnone Himage]]].
  assert (Hguard : task_detach_guard st p entry tid rest image).
  { repeat split; assumption. }
  split; [apply task_detach_preserves_pool_partition; assumption|].
  split; [apply task_detach_preserves_active_closure; exact Hactive|].
  split.
  - rewrite Hlist in Hlinks.
    destruct Hlinks as [headImage [Hget [Hnext Htail]]].
    cbn [task_detach_head taskLifecycle unUsedTaskStates taskFreeStorage].
    eapply task_free_links_storage_ext; [|exact Htail].
    intros slot Hin; destruct (Z.eq_dec slot tid) as [Heq|Hneq]; [|reflexivity].
    subst slot; destruct Hpool as [_ [_ [_ [Hnodup _]]]].
    rewrite Hlist in Hnodup; inversion Hnodup; contradiction.
  - split; [eapply task_detach_preserves_reservation_closure; eauto|].
    split; [apply task_detach_preserves_generation; exact Hgen|].
    split; [exact Hreg|]. split; [exact Hunique|]. split; [exact Hprio|].
    split; [|exact (proj2 Hreuse)].
    intros slot old Hget; simpl in Hget.
    destruct (Z.eq_dec slot tid); [discriminate|].
    apply (proj1 Hreuse slot old Hget).
Qed.

(** Fresh allocation cannot revive an old invocation merely by reusing a
    pool address.  The historical origin survives deletion and is bounded
    independently of current live/private entries. *)
Lemma task_detach_not_historical_lifetime : forall st inv slot generation,
  task_generation_closure st ->
  st.(taskLifecycle).(taskInvocations) inv = Some (RunningInvocation slot generation) ->
  st.(taskLifecycle).(taskNextGeneration) <> generation.
Proof.
  intros st inv slot generation [_ [_ [_ [Hhistory _]]]] Hget Heq.
  specialize (Hhistory inv slot generation Hget); lia.
Qed.

(** The creation authority is the actual reservation ledger.  A fragment is
    a partial map, composed only when its priority domains are disjoint.  This
    is a ghost resource algebra, not a second copy of the private C heap.
    In particular its singleton fragments cannot be duplicated.  Embedding
    this algebra in a concrete concurrent program logic is a separate client
    linking obligation; the agreement and transport facts below are proved. *)
Definition TaskCreationFragment := Priority -> option TaskCreationEntry.

Definition task_creation_fragment_agrees (st : Glob_TaskAbstractState)
  (fragment : TaskCreationFragment) : Prop :=
  forall p entry, fragment p = Some entry ->
    st.(taskLifecycle).(taskReservations) p = Some entry.

Definition task_creation_fragments_disjoint
  (left right : TaskCreationFragment) : Prop :=
  forall p entry, left p = Some entry -> right p = None.

Definition task_creation_fragment_empty : TaskCreationFragment := fun _ => None.

Definition task_creation_fragment_combine
  (left right : TaskCreationFragment) : TaskCreationFragment :=
  fun p => match left p with Some entry => Some entry | None => right p end.

Lemma task_creation_fragment_combine_empty : forall fragment,
  task_creation_fragment_combine task_creation_fragment_empty fragment = fragment /\
  task_creation_fragment_combine fragment task_creation_fragment_empty = fragment.
Proof.
  intros; split; apply functional_extensionality; intro p; unfold
    task_creation_fragment_combine, task_creation_fragment_empty; [reflexivity|].
  destruct (fragment p); reflexivity.
Qed.

Lemma task_creation_fragment_combine_assoc : forall first second third,
  task_creation_fragment_combine (task_creation_fragment_combine first second) third =
    task_creation_fragment_combine first (task_creation_fragment_combine second third).
Proof.
  intros; apply functional_extensionality; intro p; unfold task_creation_fragment_combine.
  destruct (first p); reflexivity.
Qed.

Lemma task_creation_fragments_disjoint_sym : forall left right,
  task_creation_fragments_disjoint left right ->
  task_creation_fragments_disjoint right left.
Proof.
  intros left right H p entry Hget; destruct (left p) as [other|] eqn:Hother; [|reflexivity].
  specialize (H p other Hother); congruence.
Qed.

Lemma task_creation_fragment_combine_comm : forall left right,
  task_creation_fragments_disjoint left right ->
  task_creation_fragment_combine left right = task_creation_fragment_combine right left.
Proof.
  intros left right H; apply functional_extensionality; intro p.
  unfold task_creation_fragment_combine.
  destruct (left p) as [entry|] eqn:Hget.
  - rewrite (H p entry Hget); reflexivity.
  - destruct (right p); reflexivity.
Qed.

Lemma task_creation_fragment_combine_disjoint : forall first second third,
  task_creation_fragments_disjoint (task_creation_fragment_combine first second) third <->
  task_creation_fragments_disjoint first third /\ task_creation_fragments_disjoint second third.
Proof.
  intros first second third; split.
  - intro H; split; intros p entry Hget; unfold task_creation_fragment_combine in H.
    + apply (H p entry); rewrite Hget; reflexivity.
    + destruct (first p) as [other|] eqn:Hfirst.
      * apply (H p other); rewrite Hfirst; reflexivity.
      * apply (H p entry); rewrite Hfirst; exact Hget.
  - intros [Hfirst Hsecond] p entry Hget; unfold task_creation_fragment_combine in Hget.
    destruct (first p) as [other|] eqn:Hgetfirst.
    + inversion Hget; subst; eapply Hfirst; eauto.
    + eapply Hsecond; eauto.
Qed.

Lemma task_creation_fragment_combine_agreement : forall st left right,
  task_creation_fragment_agrees st left -> task_creation_fragment_agrees st right ->
  task_creation_fragment_agrees st (task_creation_fragment_combine left right).
Proof.
  intros st left right Hleft Hright p entry Hget.
  unfold task_creation_fragment_combine in Hget; destruct (left p) as [other|] eqn:Hother.
  - inversion Hget; subst; eapply Hleft; eauto.
  - eapply Hright; eauto.
Qed.

Definition task_creation_singleton (p : Priority) (entry : TaskCreationEntry)
  : TaskCreationFragment :=
  fun q => if Z.eq_dec q p then Some entry else None.

Lemma task_creation_singleton_exclusive : forall p left right,
  ~ task_creation_fragments_disjoint
      (task_creation_singleton p left) (task_creation_singleton p right).
Proof.
  intros p left right H; specialize (H p left).
  unfold task_creation_singleton in H; destruct (Z.eq_dec p p); [|contradiction].
  specialize (H eq_refl); discriminate.
Qed.

Lemma task_creation_singleton_agreement : forall st p entry,
  task_creation_fragment_agrees st (task_creation_singleton p entry) <->
  st.(taskLifecycle).(taskReservations) p = Some entry.
Proof.
  intros; split.
  - intro H; apply (H p entry); unfold task_creation_singleton.
    destruct (Z.eq_dec p p); congruence.
  - intros H q e Hget; unfold task_creation_singleton in Hget.
    destruct (Z.eq_dec q p); congruence.
Qed.

Lemma task_creation_authority_agreement : forall st p left right,
  task_creation_fragment_agrees st (task_creation_singleton p left) ->
  task_creation_fragment_agrees st (task_creation_singleton p right) -> left = right.
Proof.
  intros; apply task_creation_singleton_agreement in H.
  apply task_creation_singleton_agreement in H0; congruence.
Qed.

(** A suspended invocation keeps precisely its own keys.  Neither this view
    nor its frame condition mentions the global next-generation counter. *)
Definition task_creation_view (st : Glob_TaskAbstractState) (invocation : nat)
  : TaskCreationFragment :=
  fun p => match st.(taskLifecycle).(taskReservations) p with
  | Some entry => if Nat.eq_dec entry.(creationInvocation) invocation
      then Some entry else None
  | None => None
  end.

Definition task_creation_frame (invocation : nat)
  (before after : Glob_TaskAbstractState) : Prop :=
  task_creation_view after invocation = task_creation_view before invocation.

Lemma task_creation_frame_lookup : forall invocation before after p entry,
  task_creation_frame invocation before after ->
  before.(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationInvocation) = invocation ->
  after.(taskLifecycle).(taskReservations) p = Some entry.
Proof.
  intros invocation before after p entry Hframe Hentry Hinv.
  pose proof (f_equal (fun f => f p) Hframe) as Hget.
  unfold task_creation_view in Hget; rewrite Hentry in Hget.
  destruct (Nat.eq_dec entry.(creationInvocation) invocation); [|contradiction].
  destruct (after.(taskLifecycle).(taskReservations) p) as [other|] eqn:Hother;
    [destruct (Nat.eq_dec other.(creationInvocation) invocation)|]; congruence.
Qed.

Lemma task_creation_frame_private_storage : forall sg invocation before after,
  task_creation_frame invocation before after ->
  task_private_storage sg after invocation =
    task_private_storage sg before invocation.
Proof.
  intros sg invocation before after Hframe.
  assert (Halloc : task_private_allocations_for_invocation after invocation =
      task_private_allocations_for_invocation before invocation).
  { apply functional_extensionality; intro p.
    pose proof (f_equal (fun f => f p) Hframe) as Hget.
    unfold task_creation_view in Hget.
    unfold task_private_allocations_for_invocation.
    destruct (after.(taskLifecycle).(taskReservations) p) as [a|];
      destruct (before.(taskLifecycle).(taskReservations) p) as [b|];
      repeat match goal with
      | |- context [Nat.eq_dec ?x ?y] => destruct (Nat.eq_dec x y)
      end; try discriminate; congruence. }
  unfold task_private_storage; rewrite Halloc; reflexivity.
Qed.

Lemma task_creation_view_update_foreign : forall before after p observer,
  (forall q, q <> p -> after.(taskLifecycle).(taskReservations) q =
    before.(taskLifecycle).(taskReservations) q) ->
  (forall entry, before.(taskLifecycle).(taskReservations) p = Some entry ->
    entry.(creationInvocation) <> observer) ->
  (forall entry, after.(taskLifecycle).(taskReservations) p = Some entry ->
    entry.(creationInvocation) <> observer) ->
  task_creation_frame observer before after.
Proof.
  intros before after p observer Hother Hbefore Hafter.
  unfold task_creation_frame; apply functional_extensionality; intro q.
  unfold task_creation_view; destruct (Z.eq_dec q p) as [->|Hneq].
  - assert (Hfilter : forall candidate : option TaskCreationEntry,
        (forall entry, candidate = Some entry -> entry.(creationInvocation) <> observer) ->
        (match candidate with Some entry =>
           if Nat.eq_dec entry.(creationInvocation) observer then Some entry else None
         | None => None end) = None).
    { intros [entry|] Hall; [|reflexivity].
      destruct (Nat.eq_dec entry.(creationInvocation) observer) as [Heq|Hneq]; [|reflexivity].
      exfalso; exact (Hall entry eq_refl Heq). }
    rewrite (Hfilter _ Hafter), (Hfilter _ Hbefore); reflexivity.
  - rewrite Hother by exact Hneq; reflexivity.
Qed.

Lemma task_detach_frames_other_invocation :
  forall st p entry tid rest image observer,
  st.(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationInvocation) <> observer ->
  task_creation_frame observer st (task_detach_head st p entry tid rest image).
Proof.
  intros; eapply task_creation_view_update_foreign with (p := p).
  - intros; simpl; destruct (Z.eq_dec q p); congruence.
  - intros; congruence.
  - intros other Hget; simpl in Hget; destruct (Z.eq_dec p p); [|contradiction].
    inversion Hget; subst; exact H0.
Qed.

Lemma task_private_image_frames_other_invocation :
  forall st p entry allocation image observer,
  st.(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationInvocation) <> observer ->
  task_creation_frame observer st
    (task_update_private_image st p entry allocation image).
Proof.
  intros; eapply task_creation_view_update_foreign with (p := p).
  - intros; simpl; destruct (Z.eq_dec q p); congruence.
  - intros; congruence.
  - intros other Hget; simpl in Hget; destruct (Z.eq_dec p p); [|contradiction].
    inversion Hget; subst; exact H0.
Qed.

Definition task_bind_identity (t : TaskAbstractState)
  (slot : TaskID) (generation : nat) : TaskAbstractState :=
  {| taskID := slot; taskGeneration := generation; tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := t.(stat); statPend := t.(statPend);
     dly := t.(dly); eventPtr := t.(eventPtr); eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy); msg := t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_identity_has_no_physical_bytes : forall sg t slot generation,
  task_tcb64_image sg (task_bind_identity t slot generation) =
  task_tcb64_image sg t.
Proof. reflexivity. Qed.

Definition task_commit_identity (st : Glob_TaskAbstractState)
  (p : Priority) (invocation : nat) (node : TaskAbstractState) : Prop :=
  exists entry allocation,
    st.(taskLifecycle).(taskReservations) p = Some entry /\
    entry.(creationInvocation) = invocation /\
    entry.(creationAllocation) = Some allocation /\
    node.(taskID) = allocation.(privateSlot) /\
    node.(taskGeneration) = allocation.(privateGeneration) /\
    node.(curPrio) = p.

Lemma task_commit_identity_private : forall st p invocation node,
  task_commit_identity st p invocation node ->
  task_private_slot st node.(taskID).
Proof.
  intros st p invocation node [entry [allocation [Hentry [_ [Ha [Hslot _]]]]]].
  exists p, entry, allocation; repeat split; try assumption; symmetry; exact Hslot.
Qed.

Lemma task_commit_identity_unpublished : forall sg st p invocation node,
  task_in_range sg st -> task_commit_identity st p invocation node ->
  forall observer,
    ~ task_publication_happened st observer node.(taskID) node.(taskGeneration).
Proof.
  intros sg st p invocation node [_ [_ [_ [_ [Hgeneration _]]]]]
    [entry [allocation [Hentry [_ [Ha [Hslot [Hg _]]]]]]] observer.
  destruct Hgeneration as [_ [_ [_ [_ [_ Hunpublished]]]]].
  unfold task_publication_happened; rewrite Hslot, Hg.
  exact (Hunpublished p entry allocation observer Hentry Ha).
Qed.

(** A source commit changes an old node only at the old head's Prev field.
    This observation transports priority, readiness, event links and lifetime
    facts without pretending that the old complete TCB values are equal. *)
Lemma task_commit_observation : forall (A : Type)
  (observe : TaskAbstractState -> A) st p invocation node slot,
  (forall t next previous, observe (task_set_links t next previous) = observe t) ->
  option_map observe
    ((task_commit st p invocation node).(inUsedTaskStates) slot) =
  (if Z.eq_dec slot node.(taskID) then Some (observe node)
   else option_map observe (st.(inUsedTaskStates) slot)).
Proof.
  intros A observe st p invocation node slot Hlinks.
  cbn [task_commit inUsedTaskStates].
  destruct (Z.eq_dec slot (taskID node)); [simpl; rewrite Hlinks; reflexivity|].
  destruct (tcbListHead st); destruct (inUsedTaskStates st slot); simpl;
    try reflexivity.
  destruct Z.eq_dec; simpl; [rewrite Hlinks|]; reflexivity.
Qed.

Lemma task_commit_transports_old_fields : forall tasks p invocation node tid old,
  tasks.(inUsedTaskStates) node.(taskID) = None ->
  tasks.(inUsedTaskStates) tid = Some old -> exists new,
    (task_commit tasks p invocation node).(inUsedTaskStates) tid = Some new /\
    task_set_links new None None = task_set_links old None None.
Proof.
  intros tasks p invocation node tid old Hnone Hold.
  pose proof (task_commit_observation TaskAbstractState
    (fun t => task_set_links t None None) tasks p invocation node tid
    (fun _ _ _ => eq_refl)) as Hfields.
  destruct (Z.eq_dec tid node.(taskID)); [subst; congruence|].
  rewrite Hold in Hfields.
  destruct ((task_commit tasks p invocation node).(inUsedTaskStates) tid)
    as [new|] eqn:Hnew; [|discriminate].
  exists new; split; [reflexivity|]. simpl in Hfields; congruence.
Qed.

Lemma task_commit_lookup_old_fields : forall tasks p invocation node tid new,
  tid <> node.(taskID) ->
  (task_commit tasks p invocation node).(inUsedTaskStates) tid = Some new ->
  exists old, tasks.(inUsedTaskStates) tid = Some old /\
    task_set_links new None None = task_set_links old None None.
Proof.
  intros tasks p invocation node tid new Hneq Hnew.
  pose proof (task_commit_observation TaskAbstractState
    (fun t => task_set_links t None None) tasks p invocation node tid
    (fun _ _ _ => eq_refl)) as Hfields.
  destruct (Z.eq_dec tid node.(taskID)); [contradiction|].
  rewrite Hnew in Hfields.
  destruct (tasks.(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
  exists old; split; [reflexivity|]. simpl in Hfields; congruence.
Qed.

Lemma task_commit_live_iff : forall st p invocation node slot,
  (exists t, (task_commit st p invocation node).(inUsedTaskStates) slot = Some t) <->
  slot = node.(taskID) \/ exists t, st.(inUsedTaskStates) slot = Some t.
Proof.
  intros st p invocation node slot.
  cbn [task_commit inUsedTaskStates].
  destruct (Z.eq_dec slot (taskID node)) as [Heq|Hneq].
  - split; [auto|intros; eexists; reflexivity].
  - destruct (tcbListHead st) as [head|];
      destruct (inUsedTaskStates st slot) as [t|] eqn:Hget;
      try destruct (Z.eq_dec slot head).
    all: split; intros H; try (right; eauto); try (eexists; reflexivity).
    all: first [destruct H as [other Hother]; discriminate |
      destruct H as [Heq | [other Hother]]; congruence].
Qed.

Lemma task_commit_private_slot_iff : forall sg st p invocation node slot,
  task_pool_partition sg st -> task_commit_identity st p invocation node ->
  (task_private_slot (task_commit st p invocation node) slot <->
   task_private_slot st slot /\ slot <> node.(taskID)).
Proof.
  intros sg st p invocation node slot [_ [_ [_ [_ [_ Hunique]]]]]
    [entry [allocation [Hentry [Hinv [Ha [Hid [Hgen Hp]]]]]]].
  split.
  - intros [q [e [a [Hq [He Hslot]]]]].
    simpl in Hq; destruct (Z.eq_dec q p) as [->|Hqp]; [discriminate|].
    split; [exists q, e, a; auto|].
    intro Heq; apply Hqp; eapply Hunique; eauto; congruence.
  - intros [[q [e [a [Hq [He Hslot]]]]] Hneq].
    exists q, e, a; split; [|auto].
    simpl; destruct (Z.eq_dec q p) as [->|Hqp]; [|exact Hq].
    rewrite Hentry in Hq; inversion Hq; subst e.
    rewrite Ha in He; inversion He; subst a; congruence.
Qed.

Lemma task_commit_preserves_pool_partition : forall sg st p invocation node,
  task_pool_partition sg st -> task_commit_identity st p invocation node ->
  task_pool_partition sg (task_commit st p invocation node).
Proof.
  intros sg st p invocation node Hpool Hidentity.
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg st node.(taskID) Hpool Hprivate)
    as [Hnone Hnotfree].
  pose proof (task_commit_private_slot_iff sg st p invocation node) as Hnewprivate.
  pose proof Hpool as Hpartition.
  destruct Hpool as [Hcover [Hused [Hfree [Hnodup [Hstorage Hunique]]]]].
  rename Hpartition into Hpool.
  unfold task_pool_partition; split.
  - intro slot; rewrite task_commit_live_iff.
    rewrite Hnewprivate by assumption.
    change (task_slot_in_range sg slot <->
      (slot = taskID node \/ exists t, inUsedTaskStates st slot = Some t) \/
      In slot (unUsedTaskStates st) \/ (task_private_slot st slot /\ slot <> taskID node)).
    rewrite Hcover; destruct (Z.eq_dec slot node.(taskID)); subst; tauto.
  - split.
    + intros slot t Hget.
      assert (Hlive : slot = node.(taskID) \/ exists old, st.(inUsedTaskStates) slot = Some old).
      { apply (proj1 (task_commit_live_iff st p invocation node slot)); eauto. }
      rewrite Hnewprivate by assumption; simpl.
      destruct Hlive as [->|[old Hold]]; [tauto|].
      destruct (Hused slot old Hold); tauto.
    + split.
      * intros slot Hin; rewrite Hnewprivate by assumption; simpl in Hin.
        specialize (Hfree slot Hin); tauto.
      * split; [exact Hnodup|]. split; [exact Hstorage|].
        intros q r e1 e2 a1 a2 Hq Hr Ha1 Ha2 Hslots.
        simpl in Hq, Hr.
        destruct (Z.eq_dec q p); [discriminate|].
        destruct (Z.eq_dec r p); [discriminate|].
        eapply Hunique; eauto.
Qed.

Lemma task_active_links_ext : forall ids old new previous,
  (forall tid, In tid ids -> new tid = old tid) ->
  task_active_links old previous ids -> task_active_links new previous ids.
Proof.
  induction ids as [|tid rest IH]; intros old new previous Heq Hlinks; [exact I|].
  destruct Hlinks as [t [Hget [Hid [Hprev [Hnext Htail]]]]].
  exists t; split; [rewrite Heq by (left; reflexivity); exact Hget|].
  split; [exact Hid|]. split; [exact Hprev|]. split; [exact Hnext|].
  eapply IH; [intros q Hin; apply Heq; right; exact Hin|exact Htail].
Qed.

Lemma task_commit_preserves_active_closure : forall st p invocation node,
  task_active_closure st -> st.(inUsedTaskStates) node.(taskID) = None ->
  task_active_closure (task_commit st p invocation node).
Proof.
  intros st p invocation node [Hnodup [Hhead [Hcount [Hcover Hlinks]]]] Hnone.
  assert (Hfresh : ~ In node.(taskID) st.(taskLifecycle).(taskActiveOrder)).
  { intro Hin; apply Hcover in Hin; destruct Hin as [t Ht]; congruence. }
  split; [simpl; constructor; assumption|].
  split; [reflexivity|]. split; [simpl; rewrite Hcount; lia|]. split.
  - intro slot; rewrite task_commit_live_iff; simpl.
    rewrite Hcover; intuition congruence.
  - simpl; exists (task_set_links node st.(tcbListHead) None).
    split.
    + simpl; destruct (Z.eq_dec (taskID node) (taskID node)); congruence.
    + split; [reflexivity|]. split; [reflexivity|]. split; [exact Hhead|].
      destruct (taskActiveOrder (taskLifecycle st)) as [|head rest] eqn:Horder; [exact I|].
      simpl in Hhead.
      change (task_active_links
        (inUsedTaskStates (task_commit st p invocation node))
        (Some (taskID node)) (head :: rest)).
      simpl in Hlinks, Hfresh.
      destruct Hlinks as [t [Hget [Hid [Hprev [Hnext Htail]]]]].
      apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hnothead Hrest].
      exists (task_set_links t t.(nextTCB) (Some node.(taskID))).
      split.
      * cbn [task_commit inUsedTaskStates].
        destruct (Z.eq_dec head (taskID node)); [subst; tauto|].
        rewrite Hhead, Hget; destruct (Z.eq_dec head head); congruence.
      * split; [exact Hid|]. split; [reflexivity|]. split; [exact Hnext|].
        eapply task_active_links_ext; [|exact Htail].
        intros slot Hin; apply task_commit_non_target_frame.
        -- intro Heq; subst slot; tauto.
        -- rewrite Hhead; intro Heq; inversion Heq; subst slot; contradiction.
Qed.

Lemma task_commit_preserves_registration : forall st p invocation node,
  task_current_prio_registered st -> st.(prioTbl) p = PTReserved -> node.(curPrio) = p ->
  task_current_prio_registered (task_commit st p invocation node).
Proof.
  intros st p invocation node Hregistered Hreserved Hp slot t Hget.
  pose proof (task_commit_observation Z curPrio st p invocation node slot
    (fun _ _ _ => eq_refl)) as Hobs.
  rewrite Hget in Hobs; simpl in Hobs.
  simpl; destruct (Z.eq_dec slot node.(taskID)) as [->|Hneq].
  - injection Hobs as Hcur; rewrite Hcur, Hp; destruct (Z.eq_dec p p); congruence.
  - destruct (st.(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
    simpl in Hobs; injection Hobs as Hcur; rewrite Hcur.
    pose proof (Hregistered slot old Hold) as Hreg.
    destruct (Z.eq_dec old.(curPrio) p) as [Heq|Hne].
    + rewrite Heq, Hreserved in Hreg; discriminate.
    + exact Hreg.
Qed.

Lemma task_registration_implies_priority_unique : forall st,
  task_current_prio_registered st -> task_priority_unique st.
Proof.
  intros st Hregistered tid1 tid2 t1 t2 H1 H2 Hp.
  pose proof (Hregistered _ _ H1); pose proof (Hregistered _ _ H2); congruence.
Qed.

Lemma task_commit_preserves_in_range : forall sg st p invocation node,
  task_in_range sg st -> task_commit_identity st p invocation node ->
  task_in_range sg (task_commit st p invocation node).
Proof.
  intros sg st p invocation node Hrange Hidentity.
  destruct Hrange as
    [Hpool [Hactive [Hlinks [Hres [Hgen [Hreg [Hunique [Hprio Hreuse]]]]]]]].
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg st node.(taskID) Hpool Hprivate)
    as [Hnone Hnotfree].
  destruct Hidentity as [entry [allocation [Hentry [Hinv [Ha [Hid [Hg Hp]]]]]]].
  assert (Hidentity : task_commit_identity st p invocation node).
  { exists entry, allocation; repeat split; assumption. }
  destruct (proj1 Hres p entry Hentry) as [Hpvalid [Hreserved Hledger]].
  assert (Hregpost : task_current_prio_registered (task_commit st p invocation node)).
  { apply task_commit_preserves_registration; assumption. }
  split; [apply task_commit_preserves_pool_partition; assumption|].
  split; [apply task_commit_preserves_active_closure; assumption|].
  split; [exact Hlinks|]. split.
  - destruct Hres as [Hbinding Hresunique]; split.
    + intros q e Hq; simpl in Hq |- *.
      destruct (Z.eq_dec q p); [discriminate|].
      exact (Hbinding q e Hq).
    + intros q r e1 e2 Hq Hr Hsame; simpl in Hq, Hr.
      destruct (Z.eq_dec q p); [discriminate|].
      destruct (Z.eq_dec r p); [discriminate|].
      eapply Hresunique; eauto.
  - split.
    + destruct Hgen as [Husedgen [Hprivategen [Hinvgen [Hhistory [Hpub Hunpublished]]]]].
      assert (Hnodegen : (node.(taskGeneration) < st.(taskLifecycle).(taskNextGeneration))%nat).
      { rewrite Hg; eapply Hprivategen; eauto. }
      split.
      * intros slot t Hget.
        pose proof (task_commit_observation nat taskGeneration st p invocation node slot
          (fun _ _ _ => eq_refl)) as Hobs.
        rewrite Hget in Hobs; simpl in Hobs |- *.
        destruct (Z.eq_dec slot node.(taskID)).
        -- injection Hobs as Hgeneration; rewrite Hgeneration; exact Hnodegen.
        -- destruct (st.(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
           simpl in Hobs; injection Hobs as Hgeneration; rewrite Hgeneration.
           eapply Husedgen; eauto.
      * split.
        -- intros q e a Hq Halloc; simpl in Hq |- *.
           destruct (Z.eq_dec q p); [discriminate|].
           eapply Hprivategen; eauto.
        -- split; [exact Hinvgen|]. split; [exact Hhistory|]. split.
           ++ intros inv tid generation Hin; simpl in Hin |- *.
              destruct Hin as [Heq|Hin]; [inversion Heq; subst; exact Hnodegen|eapply Hpub; eauto].
           ++ intros q e a observer Hq Halloc Hin; simpl in Hq, Hin.
              destruct (Z.eq_dec q p) as [Heq|Hqp]; [discriminate|].
              destruct Hin as [Heq|Hin].
              ** assert (Hslot : a.(privateSlot) = node.(taskID)) by congruence.
                 pose proof (proj2 (proj2 (proj2 (proj2 (proj2 Hpool))))) as Hslots.
                 apply Hqp; eapply Hslots; [exact Hq|exact Hentry|exact Halloc|exact Ha|].
                 rewrite Hslot; exact Hid.
              ** exact (Hunpublished q e a observer Hq Halloc Hin).
    + split; [exact Hregpost|].
      split; [apply task_registration_implies_priority_unique; exact Hregpost|]. split; [|exact Hreuse].
      intros slot t Hget.
      pose proof (task_commit_observation Z curPrio st p invocation node slot
        (fun _ _ _ => eq_refl)) as Hobs.
      rewrite Hget in Hobs; simpl in Hobs.
      destruct (Z.eq_dec slot node.(taskID)).
      * injection Hobs as Hcur; rewrite Hcur, Hp; exact Hpvalid.
      * destruct (st.(inUsedTaskStates) slot) as [old|] eqn:Hold; [|discriminate].
        simpl in Hobs; injection Hobs as Hcur; rewrite Hcur; eapply Hprio; eauto.
Qed.

Definition tcb_init_free_image (sg : StableGlobVars)
  (next : option TaskID) (name : addr) : TCBLayoutImage :=
  fun f => match f with
  | TCBCommonField TCBNext => Some (encode_task_link sg next)
  | TCBCommonField TCBTaskName => Some name
  | _ => Some 0 end.

Lemma tcb_init_free_flags_rdy_eq : forall sg next name,
  tcb_init_free_image sg next name (TCBCommonField TCBFlagsRdy) = Some 0.
Proof. reflexivity. Qed.

(** OS_TaskDel's return-to-free-list write changes Next, not FlagsRdy.
    Together with InitTCBList's zeroing, this is the definedness producer
    used by OS_TCBInit's arbitrary-free-image decoder.  This is the direct
    store footprint, not a contract for an arbitrary preceding delete hook;
    that hook must itself return ownership of a readable FlagsRdy cell. *)
Definition tcb_recycle_image (sg : StableGlobVars) (next : option TaskID)
  (image : TCBLayoutImage) : TCBLayoutImage :=
  tcb_layout_write image (TCBCommonField TCBNext) (Some (encode_task_link sg next)).

Lemma tcb_recycle_preserves_flags_rdy : forall sg next image flags,
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  tcb_recycle_image sg next image (TCBCommonField TCBFlagsRdy) = Some flags.
Proof. intros; exact H. Qed.

Lemma task_count_in_pool_range : forall sg st,
  selected_kernel_profile sg -> task_in_range sg st ->
  0 <= st.(taskCount) <= 22.
Proof.
  intros sg st [_ [Hcapacity [Hsystem _]]]
    [[Hpool _] [[Hnd [_ [Hcount [Hactive _]]]] _]].
  assert (Hincl : incl st.(taskLifecycle).(taskActiveOrder)
    (map Z.of_nat (seq 0 22))).
  { intros tid Hin.
    pose proof (proj1 (Hactive tid) Hin) as Hused.
    assert (Hslot : task_slot_in_range sg tid).
    { apply (proj2 (Hpool tid)); left; exact Hused. }
    unfold task_slot_in_range in Hslot; rewrite Hcapacity, Hsystem in Hslot.
    apply in_map_iff; exists (Z.to_nat tid); split.
    - apply Z2Nat.id; lia.
    - apply in_seq; split; [lia|].
      apply (proj1 (Z2Nat.inj_lt tid 22 ltac:(lia) ltac:(lia))); lia. }
  assert (Hlen : (List.length st.(taskLifecycle).(taskActiveOrder) <=
    List.length (map Z.of_nat (seq 0 22)))%nat).
  { apply NoDup_incl_length; assumption. }
  rewrite map_length, seq_length in Hlen.
  rewrite Hcount; lia.
Qed.

Lemma task_free_storage_rep_ext : forall sg ids before after,
  (forall tid, In tid ids -> before tid = after tid) ->
  task_free_storage_rep sg before ids = task_free_storage_rep sg after ids.
Proof.
  intros sg ids; induction ids as [|tid rest IH]; intros before after Heq; [reflexivity|].
  simpl; rewrite Heq by (left; reflexivity).
  rewrite (IH before after); [reflexivity|intros q Hin; apply Heq; right; exact Hin].
Qed.

Definition task_public_storage_without_free_head (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (rest : list TaskID) : Assertion :=
  store_used_task_map sg st.(inUsedTaskStates) **
  task_free_storage_rep sg st.(taskLifecycle).(taskFreeStorage) rest **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg st.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount) **
  store_prio_tbl sg st.(prioTbl) ** task_reg_allocator_rep sg st.

Lemma task_public_storage_split_free_head : forall sg st tid rest,
  st.(unUsedTaskStates) = tid :: rest ->
  task_public_storage sg st |--
  sg.(g_OSTCBFreeList) # Ptr |->
    task_slot_addr sg tid **
  (EX image, coq_prop (st.(taskLifecycle).(taskFreeStorage) tid = Some image) &&
    task_slot_storage_rep sg tid image) **
  task_public_storage_without_free_head sg st rest.
Proof.
  intros sg st tid rest Hhead.
  unfold task_public_storage, task_public_storage_without_free_head.
  rewrite Hhead; cbn [task_free_storage_rep hd_error encode_task_link].
  Intros image; Exists image; entailer!.
Qed.

Lemma task_public_storage_merge_detached_free_head :
  forall sg st p entry tid rest image,
    NoDup st.(unUsedTaskStates) -> st.(unUsedTaskStates) = tid :: rest ->
    sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error rest) **
    task_public_storage_without_free_head sg st rest |--
    task_public_storage sg (task_detach_head st p entry tid rest image).
Proof.
  intros sg st p entry tid rest image Hnd Hhead.
  rewrite Hhead in Hnd; apply NoDup_cons_iff in Hnd; destruct Hnd as [Hfresh Hnd].
  unfold task_public_storage, task_public_storage_without_free_head.
  cbn [task_detach_head inUsedTaskStates unUsedTaskStates tcbListHead
    taskCount prioTbl taskLifecycle taskFreeStorage task_reg_allocator_rep taskRegNextID].
  rewrite (task_free_storage_rep_ext sg rest
    (fun slot => if Z.eq_dec slot tid then None else taskFreeStorage (taskLifecycle st) slot)
    st.(taskLifecycle).(taskFreeStorage)).
  - entailer!.
  - intros slot Hin; destruct (Z.eq_dec slot tid); [subst; contradiction|reflexivity].
Qed.

Lemma task_commit_frames_other_invocation : forall st p invocation node observer,
  task_commit_identity st p invocation node -> invocation <> observer ->
  task_creation_frame observer st (task_commit st p invocation node).
Proof.
  intros st p invocation node observer [entry [a [Hentry [Hinv Hrest]]]] Hneq.
  eapply task_creation_view_update_foreign with (p := p).
  - intros; simpl; destruct (Z.eq_dec q p); congruence.
  - intros; congruence.
  - intros other Hget; simpl in Hget; destruct (Z.eq_dec p p); [discriminate|contradiction].
Qed.

Lemma task_commit_preserves_invocation_active : forall sg st p invocation node observer origin,
  task_in_range sg st -> task_commit_identity st p invocation node ->
  task_invocation_active st observer origin ->
  task_invocation_active (task_commit st p invocation node) observer origin.
Proof.
  intros sg st p invocation node observer origin Hrange Hidentity [Hinv [Hactive Hlive]].
  split; [exact Hinv|]. split; [exact Hactive|].
  destruct origin as [|tid generation]; [exact I|].
  destruct Hlive as [old [Hold Hgen]].
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg st node.(taskID) (proj1 Hrange) Hprivate)
    as [Hnone _].
  assert (Hneq : tid <> node.(taskID)) by congruence.
  pose proof (task_commit_observation nat taskGeneration st p invocation node tid
    (fun _ _ _ => eq_refl)) as Hobs.
  rewrite Hold in Hobs; destruct (Z.eq_dec tid node.(taskID)); [contradiction|].
  destruct ((task_commit st p invocation node).(inUsedTaskStates) tid)
    as [post|] eqn:Hpost; [|discriminate].
  exists post; split; [exact Hpost|]. simpl in Hobs; congruence.
Qed.

Lemma task_creation_frame_transports_fragment : forall invocation before after fragment,
  task_creation_frame invocation before after ->
  (forall p entry, fragment p = Some entry -> entry.(creationInvocation) = invocation) ->
  task_creation_fragment_agrees before fragment ->
  task_creation_fragment_agrees after fragment.
Proof.
  intros invocation before after fragment Hframe Howner Hagree p entry Hget.
  eapply task_creation_frame_lookup; [exact Hframe|apply Hagree; exact Hget|].
  eapply Howner; eauto.
Qed.

Lemma task_reserve_pending_fragment : forall st p invocation origin,
  task_creation_fragment_agrees (task_reserve st p invocation origin)
    (task_creation_singleton p
      {| creationInvocation := invocation; creationOrigin := origin; creationAllocation := None |}).
Proof.
  intros; apply task_creation_singleton_agreement.
  exact (proj1 (proj2 (task_reserve_state_fields_eq st p invocation origin))).
Qed.

(** Invocation registration is ghost bookkeeping at a real call boundary.
    It writes no TCB or priority-table byte.  The caller supplies its actual
    live origin; freshness follows from the existing invocation counter. *)
Lemma task_begin_invocation_preserves_generation : forall st origin,
  task_generation_closure st -> task_invocation_origin_live st origin ->
  task_generation_closure (task_begin_invocation origin st).
Proof.
  intros st origin [Hused [Hprivate [Hbound [Horigin Hpublication]]]] Hlive.
  split; [exact Hused|]; split; [exact Hprivate|]; split.
  - intros invocation caller Hget; simpl in Hget |- *.
    destruct (Nat.eq_dec invocation st.(taskLifecycle).(taskNextInvocation)) as [->|Hne].
    + lia.
    + specialize (Hbound _ _ Hget); lia.
  - split; [|exact Hpublication].
    intros invocation tid generation Hget; simpl in Hget |- *.
    destruct (Nat.eq_dec invocation st.(taskLifecycle).(taskNextInvocation)) as [->|Hne].
    + injection Hget as Heq; subst origin.
      destruct Hlive as [t [Ht Hg]]; specialize (Hused tid t Ht); congruence.
    + eapply Horigin; exact Hget.
Qed.

Lemma task_begin_invocation_preserves_reservation_closure : forall sg st origin,
  task_reservation_closure sg st -> task_generation_closure st ->
  task_reservation_closure sg (task_begin_invocation origin st).
Proof.
  intros sg st origin [Hbinding Hunique] [_ [_ [Hbound _]]].
  split; [|exact Hunique].
  intros p entry Hentry; simpl in Hentry |- *.
  destruct (Hbinding p entry Hentry) as [Hp [Hslot Hledger]].
  split; [exact Hp|]; split; [exact Hslot|].
  destruct (Nat.eq_dec entry.(creationInvocation) st.(taskLifecycle).(taskNextInvocation)) as [Heq|Hne].
  - specialize (Hbound _ _ Hledger); lia.
  - exact Hledger.
Qed.

Lemma task_begin_invocation_preserves_in_range : forall sg st origin,
  task_in_range sg st -> task_invocation_origin_live st origin ->
  task_in_range sg (task_begin_invocation origin st).
Proof.
  intros sg st origin [Hpool [Hactive [Hlinks [Hres [Hgen Hrest]]]]] Hlive.
  split; [exact Hpool|]; split; [exact Hactive|]; split; [exact Hlinks|]; split.
  - apply task_begin_invocation_preserves_reservation_closure; assumption.
  - split; [apply task_begin_invocation_preserves_generation; assumption|exact Hrest].
Qed.

Lemma task_begin_invocation_active : forall st origin,
  task_invocation_origin_live st origin ->
  task_invocation_active (task_begin_invocation origin st)
    st.(taskLifecycle).(taskNextInvocation) origin.
Proof.
  intros st origin Hlive; split; [apply task_begin_invocation_token|].
  split; [simpl; destruct Nat.eq_dec; [reflexivity|contradiction]|exact Hlive].
Qed.

Lemma task_begin_invocation_preserves_invocation_active : forall st origin observer caller,
  task_generation_closure st -> task_invocation_active st observer caller ->
  task_invocation_active (task_begin_invocation origin st) observer caller.
Proof.
  intros st origin observer caller [_ [_ [Hbound _]]] [Hget [Hretired Hlive]].
  assert (Hforeign : observer <> st.(taskLifecycle).(taskNextInvocation)).
  { specialize (Hbound _ _ Hget); lia. }
  split; [simpl; destruct Nat.eq_dec; [contradiction|exact Hget]|].
  split; [simpl; destruct Nat.eq_dec; [contradiction|exact Hretired]|exact Hlive].
Qed.

Lemma task_begin_invocation_reserve_guard : forall sg st origin p,
  task_in_range sg st -> task_invocation_origin_live st origin ->
  task_priority_in_range sg p -> st.(prioTbl) p = PTFree ->
  task_reserve_guard sg (task_begin_invocation origin st) p
    st.(taskLifecycle).(taskNextInvocation) origin.
Proof.
  intros sg st origin p Htasks Hlive Hp Hfree.
  destruct (task_begin_invocation_active st origin Hlive) as [Hinv [Hactive Horigin]].
  split; [exact Hp|]; split; [exact Hfree|]; split; [exact Hinv|].
  split; [exact Hactive|]; split; [exact Horigin|].
  intros q entry Hentry; eapply task_begin_invocation_unreserved;
    [exact (proj1 (proj2 (proj2 (proj2 Htasks))))|
     exact (proj1 (proj2 (proj2 (proj2 (proj2 Htasks)))))|exact Hentry].
Qed.

(** TCBInit's no-free result leaves an allocation-free reservation.  The
    wrapper clears only that slot; it neither releases a private TCB nor
    restores an old snapshot of the global free list. *)
Lemma task_rollback_private_slot_iff : forall st p invocation tid,
  task_rollback_guard st p invocation ->
  (task_private_slot (task_rollback_reservation st p) tid <-> task_private_slot st tid).
Proof.
  intros st p invocation tid [entry [Hentry [Hinv Hempty]]]; split.
  - intros [q [e [a [Hq [Ha Htid]]]]].
    simpl in Hq; destruct (Z.eq_dec q p); [discriminate|].
    exists q, e, a; auto.
  - intros [q [e [a [Hq [Ha Htid]]]]].
    exists q, e, a; simpl.
    destruct (Z.eq_dec q p) as [->|Hne]; [rewrite Hentry in Hq; injection Hq as Heq; subst e; congruence|].
    auto.
Qed.

Lemma task_rollback_preserves_in_range : forall sg st p invocation,
  task_in_range sg st -> task_rollback_guard st p invocation ->
  task_in_range sg (task_rollback_reservation st p).
Proof.
  intros sg st p invocation
    [Hpool [Hactive [Hlinks [Hres [Hgen [Hreg [Hunique [Hpriority Hrest]]]]]]]] Hguard.
  pose proof Hguard as [entry [Hentry [Hinv Hempty]]].
  pose proof (proj1 Hres p entry Hentry) as [Hp [Hreserved Hledger]].
  pose proof (task_rollback_private_slot_iff st p invocation) as Hprivate.
  split.
  - destruct Hpool as [Hcover [Hused [Hfree [Hnd [Hstorage Hslots]]]]].
    split.
    + intro tid; cbn [task_rollback_reservation inUsedTaskStates unUsedTaskStates].
      rewrite Hprivate by exact Hguard; apply Hcover.
    + split.
      * intros tid t Ht; destruct (Hused tid t Ht) as [Hnotfree Hnotprivate].
        split; [exact Hnotfree|rewrite Hprivate by exact Hguard; exact Hnotprivate].
      * split.
        -- intros tid Hin; rewrite Hprivate by exact Hguard; exact (Hfree tid Hin).
        -- split; [exact Hnd|]; split; [exact Hstorage|].
           intros q r e1 e2 a1 a2 Hq Hr Ha1 Ha2 Hsame; simpl in Hq, Hr.
           destruct (Z.eq_dec q p); [discriminate|].
           destruct (Z.eq_dec r p); [discriminate|].
           eapply Hslots; eauto.
  - split; [exact Hactive|]; split; [exact Hlinks|]; split.
    + destruct Hres as [Hbinding Hsingle]; split.
      * intros q e Hq; simpl in Hq |- *.
        destruct (Z.eq_dec q p); [discriminate|]; exact (Hbinding q e Hq).
      * intros q r e1 e2 Hq Hr Hsame; simpl in Hq, Hr.
        destruct (Z.eq_dec q p); [discriminate|].
        destruct (Z.eq_dec r p); [discriminate|].
        eapply Hsingle; eauto.
    + split.
      * destruct Hgen as [Hused [Halloc [HinvBound [Hhistory [Hpub Hunpublished]]]]].
        split; [exact Hused|]; split.
        -- intros q e a Hq Ha; simpl in Hq |- *.
           destruct (Z.eq_dec q p); [discriminate|]; eapply Halloc; eauto.
        -- split; [exact HinvBound|]. split; [exact Hhistory|]. split; [exact Hpub|].
           intros q e a observer Hq Ha Hin; simpl in Hq, Hin.
           destruct (Z.eq_dec q p); [discriminate|].
           exact (Hunpublished q e a observer Hq Ha Hin).
      * split.
        -- intros tid t Ht; specialize (Hreg tid t Ht); simpl.
           destruct (Z.eq_dec t.(curPrio) p) as [Heq|Hne]; [rewrite Heq, Hreserved in Hreg; discriminate|exact Hreg].
        -- split; [exact Hunique|]; split; assumption.
Qed.

Lemma task_reserve_frames_other_invocation : forall st p invocation origin observer,
  st.(taskLifecycle).(taskReservations) p = None -> invocation <> observer ->
  task_creation_frame observer st (task_reserve st p invocation origin).
Proof.
  intros st p invocation origin observer Hnone Hforeign.
  eapply task_creation_view_update_foreign with (p := p).
  - intros; simpl; destruct (Z.eq_dec q p); congruence.
  - intros; rewrite Hnone in H; discriminate.
  - intros entry Hentry; simpl in Hentry; destruct (Z.eq_dec p p); [|contradiction].
    injection Hentry as Heq; subst entry; exact Hforeign.
Qed.

Lemma task_rollback_frames_other_invocation : forall st p invocation observer,
  task_rollback_guard st p invocation -> invocation <> observer ->
  task_creation_frame observer st (task_rollback_reservation st p).
Proof.
  intros st p invocation observer [entry [Hentry [Hinv Hempty]]] Hforeign.
  eapply task_creation_view_update_foreign with (p := p).
  - intros; simpl; destruct (Z.eq_dec q p); congruence.
  - intros; assert (entry0 = entry) by congruence; subst entry0; congruence.
  - intros e Hget; simpl in Hget; destruct (Z.eq_dec p p); [discriminate|contradiction].
Qed.

(** Synchronizing the invocation-owned byte image before publication has no
    effect on the final public state: commit consumes this very reservation.
    This equality is proved from the two exact transformers, not post-validity. *)
Lemma task_commit_after_private_image_eq : forall st p entry allocation image invocation node,
  task_commit (task_update_private_image st p entry allocation image)
    p invocation node = task_commit st p invocation node.
Proof.
  intros; unfold task_commit, task_update_private_image,
    glob_task_set_lifecycle, task_lifecycle_set_reservation; simpl.
  f_equal; f_equal; apply functional_extensionality; intro q.
  destruct (Z.eq_dec q p); reflexivity.
Qed.

(** Physical priority-table aliases. The maximum/minimum characterizations
    describe the real bounded scans; they do not add a synthetic base-priority
    field to the TCB. Mutex demand may add lower aliases and release may remove
    them, independently of a mutex's acquisition-time priority snapshot. *)
Definition update_prio_tbl (table : Priority -> PrioTblEntry)
  (p : Priority) (entry : PrioTblEntry) : Priority -> PrioTblEntry :=
  fun q => if Z.eq_dec q p then entry else table q.

Definition task_priority_alias (sg : StableGlobVars)
  (table : Priority -> PrioTblEntry) (tid : TaskID) (p : Priority) : Prop :=
  task_priority_in_range sg p /\ table p = PTTask tid.

Definition task_base_priority (sg : StableGlobVars)
  (table : Priority -> PrioTblEntry) (tid : TaskID) (base : Priority) : Prop :=
  task_priority_alias sg table tid base /\
  forall p, task_priority_alias sg table tid p -> p <= base.

Definition task_effective_priority (sg : StableGlobVars)
  (table : Priority -> PrioTblEntry) (tid : TaskID) (effective : Priority) : Prop :=
  task_priority_alias sg table tid effective /\
  forall p, task_priority_alias sg table tid p -> effective <= p.

Lemma update_prio_tbl_same : forall table p entry,
  update_prio_tbl table p entry p = entry.
Proof. intros; unfold update_prio_tbl; destruct Z.eq_dec; congruence. Qed.

Lemma update_prio_tbl_other : forall table p q entry,
  q <> p -> update_prio_tbl table p entry q = table q.
Proof. intros; unfold update_prio_tbl; destruct Z.eq_dec; congruence. Qed.

Lemma update_prio_tbl_put_back : forall table p,
  update_prio_tbl table p (table p) = table.
Proof.
  intros; apply functional_extensionality; intro q; unfold update_prio_tbl.
  destruct Z.eq_dec; congruence.
Qed.

Lemma update_prio_tbl_overwrite : forall table p first last,
  update_prio_tbl (update_prio_tbl table p first) p last = update_prio_tbl table p last.
Proof.
  intros; apply functional_extensionality; intro q; unfold update_prio_tbl.
  destruct Z.eq_dec; reflexivity.
Qed.

Lemma task_base_priority_unique : forall sg table tid p q,
  task_base_priority sg table tid p -> task_base_priority sg table tid q -> p = q.
Proof. intros sg table tid p q [Hp Hmaxp] [Hq Hmaxq]; specialize (Hmaxp q Hq); specialize (Hmaxq p Hp); lia. Qed.

Lemma task_effective_priority_unique : forall sg table tid p q,
  task_effective_priority sg table tid p -> task_effective_priority sg table tid q -> p = q.
Proof. intros sg table tid p q [Hp Hminp] [Hq Hminq]; specialize (Hminp q Hq); specialize (Hminq p Hp); lia. Qed.

Lemma task_effective_priority_le_base : forall sg table tid base effective,
  task_base_priority sg table tid base ->
  task_effective_priority sg table tid effective -> effective <= base.
Proof. intros sg table tid base effective [Hbase _] [_ Hmin]; apply Hmin; exact Hbase. Qed.

Lemma task_priority_alias_add_iff : forall sg table tid p q,
  task_priority_in_range sg p ->
  (task_priority_alias sg (update_prio_tbl table p (PTTask tid)) tid q <->
   q = p \/ task_priority_alias sg table tid q).
Proof.
  intros sg table tid p q Hp; unfold task_priority_alias, update_prio_tbl.
  destruct (Z.eq_dec q p) as [->|Hneq]; split; intros H; intuition congruence.
Qed.

Lemma task_priority_alias_remove_iff : forall sg table tid p q entry,
  entry <> PTTask tid ->
  (task_priority_alias sg (update_prio_tbl table p entry) tid q <->
   q <> p /\ task_priority_alias sg table tid q).
Proof.
  intros sg table tid p q entry Hentry; unfold task_priority_alias, update_prio_tbl.
  destruct (Z.eq_dec q p) as [->|Hneq]; split; intros H; intuition congruence.
Qed.

Lemma task_priority_alias_foreign_write_iff : forall sg table tid p q entry,
  table p <> PTTask tid -> entry <> PTTask tid ->
  (task_priority_alias sg (update_prio_tbl table p entry) tid q <->
   task_priority_alias sg table tid q).
Proof.
  intros sg table tid p q entry Hbefore Hafter.
  rewrite task_priority_alias_remove_iff by assumption.
  split; [tauto|]. intros [Hrange Hget]; split; [congruence|split; assumption].
Qed.

Lemma task_alias_add_preserves_base_priority : forall sg table tid base p,
  task_base_priority sg table tid base -> task_priority_in_range sg p -> p <= base ->
  task_base_priority sg (update_prio_tbl table p (PTTask tid)) tid base.
Proof.
  intros sg table tid base p [Hbase Hmax] Hp Hle; split.
  - apply task_priority_alias_add_iff; [exact Hp|right; exact Hbase].
  - intros q Hq; apply task_priority_alias_add_iff in Hq; [|exact Hp].
    destruct Hq as [->|Hq]; [exact Hle|apply Hmax; exact Hq].
Qed.

Lemma task_alias_add_effective_priority : forall sg table tid effective p,
  task_effective_priority sg table tid effective -> task_priority_in_range sg p ->
  task_effective_priority sg (update_prio_tbl table p (PTTask tid)) tid (Z.min effective p).
Proof.
  intros sg table tid effective p [Heffective Hmin] Hp.
  split.
  - apply task_priority_alias_add_iff; [exact Hp|].
    destruct (Z_le_dec effective p).
    + rewrite Z.min_l by assumption; right; exact Heffective.
    + rewrite Z.min_r by lia; left; reflexivity.
  - intros q Hq; apply task_priority_alias_add_iff in Hq; [|exact Hp].
    destruct Hq as [->|Hq].
    + apply Z.le_min_r.
    + eapply Z.le_trans; [apply Z.le_min_l|apply Hmin; exact Hq].
Qed.

Lemma task_alias_remove_preserves_base_priority : forall sg table tid base p entry,
  task_base_priority sg table tid base -> p <> base -> entry <> PTTask tid ->
  task_base_priority sg (update_prio_tbl table p entry) tid base.
Proof.
  intros sg table tid base p entry [Hbase Hmax] Hneq Hentry; split.
  - apply task_priority_alias_remove_iff; [exact Hentry|split; [congruence|exact Hbase]].
  - intros q Hq; apply task_priority_alias_remove_iff in Hq; [|exact Hentry].
    apply Hmax; exact (proj2 Hq).
Qed.

Lemma task_alias_remove_preserves_effective_priority : forall sg table tid effective p entry,
  task_effective_priority sg table tid effective -> p <> effective -> entry <> PTTask tid ->
  task_effective_priority sg (update_prio_tbl table p entry) tid effective.
Proof.
  intros sg table tid effective p entry [Heffective Hmin] Hneq Hentry; split.
  - apply task_priority_alias_remove_iff; [exact Hentry|split; [congruence|exact Heffective]].
  - intros q Hq; apply task_priority_alias_remove_iff in Hq; [|exact Hentry].
    apply Hmin; exact (proj2 Hq).
Qed.

Lemma task_alias_remove_effective_priority_monotone : forall sg table tid before after p entry,
  task_effective_priority sg table tid before -> entry <> PTTask tid ->
  task_effective_priority sg (update_prio_tbl table p entry) tid after -> before <= after.
Proof.
  intros sg table tid before after p entry [_ Hmin] Hentry [Hafter _].
  apply Hmin; apply task_priority_alias_remove_iff in Hafter; [tauto|exact Hentry].
Qed.

Lemma task_base_priority_alias_ext : forall sg before after tid base,
  (forall q, task_priority_alias sg before tid q <-> task_priority_alias sg after tid q) ->
  task_base_priority sg before tid base -> task_base_priority sg after tid base.
Proof.
  intros sg before after tid base Hext [Hbase Hmax]; split.
  - apply Hext; exact Hbase.
  - intros q Hq; apply Hmax; apply Hext; exact Hq.
Qed.

Lemma task_effective_priority_alias_ext : forall sg before after tid effective,
  (forall q, task_priority_alias sg before tid q <-> task_priority_alias sg after tid q) ->
  task_effective_priority sg before tid effective -> task_effective_priority sg after tid effective.
Proof.
  intros sg before after tid effective Hext [Hcurrent Hmin]; split.
  - apply Hext; exact Hcurrent.
  - intros q Hq; apply Hmin; apply Hext; exact Hq.
Qed.

Lemma task_commit_transports_old_priority : forall tasks p invocation node tid old,
  tasks.(inUsedTaskStates) node.(taskID) = None ->
  tasks.(inUsedTaskStates) tid = Some old -> exists new,
    (task_commit tasks p invocation node).(inUsedTaskStates) tid = Some new /\
    new.(curPrio) = old.(curPrio).
Proof.
  intros tasks p invocation node tid old Hnone Hold.
  pose proof (task_commit_observation Z curPrio tasks p invocation node tid
    (fun _ _ _ => eq_refl)) as Hprio.
  destruct (Z.eq_dec tid node.(taskID)); [subst; congruence|].
  rewrite Hold in Hprio.
  destruct ((task_commit tasks p invocation node).(inUsedTaskStates) tid)
    as [new|] eqn:Hnew; [|discriminate].
  simpl in Hprio; injection Hprio as Hprio; exists new; auto.
Qed.

Lemma task_commit_old_priority_alias_iff : forall sg tasks p invocation node tid q,
  tasks.(prioTbl) p = PTReserved -> tid <> node.(taskID) ->
  (task_priority_alias sg (task_commit tasks p invocation node).(prioTbl) tid q <->
   task_priority_alias sg tasks.(prioTbl) tid q).
Proof.
  intros sg tasks p invocation node tid q Hreserved Hforeign.
  change (task_priority_alias sg (update_prio_tbl tasks.(prioTbl) p (PTTask node.(taskID))) tid q <->
    task_priority_alias sg tasks.(prioTbl) tid q).
  apply task_priority_alias_foreign_write_iff; [rewrite Hreserved; discriminate|congruence].
Qed.

Lemma task_commit_new_priority_alias_iff : forall sg tasks p invocation node q,
  task_priority_in_range sg p ->
  (forall r, task_priority_in_range sg r -> tasks.(prioTbl) r <> PTTask node.(taskID)) ->
  (task_priority_alias sg (task_commit tasks p invocation node).(prioTbl) node.(taskID) q <->
   q = p).
Proof.
  intros sg tasks p invocation node q Hp Habsent.
  change (task_priority_alias sg (update_prio_tbl tasks.(prioTbl) p (PTTask node.(taskID))) node.(taskID) q <-> q = p).
  rewrite task_priority_alias_add_iff by exact Hp.
  split; [intros [Hq|[Hrange Hq]]; [exact Hq|exfalso; exact (Habsent q Hrange Hq)]|auto].
Qed.

(** OSTaskRegGetID's allocator core, executed with the actual perr storage
    and critical-section contract supplied by its function specification.
    Safety-critical NULL-perr handling precedes this core in C. *)
Definition task_set_reg_next_id (st : Glob_TaskAbstractState) (id : Z)
  : Glob_TaskAbstractState :=
  {| inUsedTaskStates := st.(inUsedTaskStates); unUsedTaskStates := st.(unUsedTaskStates);
     tcbListHead := st.(tcbListHead); prioTbl := st.(prioTbl); taskCount := st.(taskCount);
     parkedTaskStacks := st.(parkedTaskStacks);
     taskLifecycle := st.(taskLifecycle); taskRegNextID := id |}.

Definition task_reg_get_id (sg : StableGlobVars) (st : Glob_TaskAbstractState)
  : Z * OSErrCode * Glob_TaskAbstractState :=
  if Z.leb sg.(osKernelConfig).(cfgTaskRegisters) st.(taskRegNextID) then
    (sg.(osKernelConfig).(cfgTaskRegisters) mod 256, OS_ERR_NO_MORE_ID_AVAIL, st)
  else (st.(taskRegNextID), OS_ERR_NONE,
    task_set_reg_next_id st ((st.(taskRegNextID) + 1) mod 256)).

Lemma task_set_reg_next_id_same : forall st id,
  (task_set_reg_next_id st id).(taskRegNextID) = id.
Proof. reflexivity. Qed.
Lemma task_set_reg_next_id_put_back : forall st,
  task_set_reg_next_id st st.(taskRegNextID) = st.
Proof. intros []; reflexivity. Qed.
Lemma task_set_reg_next_id_last_write : forall st first last,
  task_set_reg_next_id (task_set_reg_next_id st first) last = task_set_reg_next_id st last.
Proof. reflexivity. Qed.

Lemma task_reg_get_id_exhausted : forall sg st,
  st.(taskRegNextID) >= sg.(osKernelConfig).(cfgTaskRegisters) ->
  task_reg_get_id sg st =
    (sg.(osKernelConfig).(cfgTaskRegisters) mod 256, OS_ERR_NO_MORE_ID_AVAIL, st).
Proof.
  intros sg st H; unfold task_reg_get_id.
  assert (Htest : Z.leb (cfgTaskRegisters (osKernelConfig sg)) (taskRegNextID st) = true)
    by (apply Z.leb_le; lia).
  rewrite Htest; reflexivity.
Qed.

Lemma task_reg_get_id_available : forall sg st,
  valid_task_reg_allocator sg st -> sg.(osKernelConfig).(cfgTaskRegisters) <= 255 ->
  st.(taskRegNextID) < sg.(osKernelConfig).(cfgTaskRegisters) ->
  task_reg_get_id sg st =
    (st.(taskRegNextID), OS_ERR_NONE, task_set_reg_next_id st (st.(taskRegNextID) + 1)).
Proof.
  intros sg st Hvalid Hmax Havailable; unfold task_reg_get_id.
  assert (Htest : Z.leb (cfgTaskRegisters (osKernelConfig sg)) (taskRegNextID st) = false)
    by (apply Z.leb_gt; lia).
  rewrite Htest; unfold valid_task_reg_allocator in Hvalid.
  rewrite Z.mod_small by lia; reflexivity.
Qed.

Lemma task_set_reg_next_id_preserves_in_range : forall sg st id,
  task_in_range sg st -> 0 <= id <= sg.(osKernelConfig).(cfgTaskRegisters) ->
  task_in_range sg (task_set_reg_next_id st id).
Proof.
  intros sg st id Hvalid Hid; unfold task_in_range in *.
  destruct Hvalid as [Hp [Ha [Hf [Hr [Hg [Hregistered [Hunique [Hprio [Hreuse _]]]]]]]]].
  split; [exact Hp|]. split; [exact Ha|]. split; [exact Hf|]. split; [exact Hr|].
  split; [exact Hg|]. split; [exact Hregistered|]. split; [exact Hunique|].
  split; [exact Hprio|]. split; [exact Hreuse|exact Hid].
Qed.

Lemma task_reg_get_id_preserves_in_range : forall sg st id err post,
  task_in_range sg st -> sg.(osKernelConfig).(cfgTaskRegisters) <= 255 ->
  task_reg_get_id sg st = (id, err, post) -> task_in_range sg post.
Proof.
  intros sg st id err post Hvalid Hmax Hstep.
  assert (Hallocator : valid_task_reg_allocator sg st)
    by (unfold task_in_range in Hvalid; tauto).
  destruct (Z_le_dec sg.(osKernelConfig).(cfgTaskRegisters) st.(taskRegNextID)).
  - rewrite task_reg_get_id_exhausted in Hstep by lia.
    inversion Hstep; subst; exact Hvalid.
  - rewrite task_reg_get_id_available in Hstep by (assumption || lia).
    inversion Hstep; subst; apply task_set_reg_next_id_preserves_in_range; [exact Hvalid|].
    unfold valid_task_reg_allocator in Hallocator; lia.
Qed.

Lemma task_reg_get_id_success : forall sg st id post,
  valid_task_reg_allocator sg st -> sg.(osKernelConfig).(cfgTaskRegisters) <= 255 ->
  task_reg_get_id sg st = (id, OS_ERR_NONE, post) ->
  id = st.(taskRegNextID) /\ 0 <= id < sg.(osKernelConfig).(cfgTaskRegisters) /\
  post = task_set_reg_next_id st (id + 1).
Proof.
  intros sg st id post Hvalid Hmax Hstep.
  destruct (Z_le_dec sg.(osKernelConfig).(cfgTaskRegisters) st.(taskRegNextID)).
  - rewrite task_reg_get_id_exhausted in Hstep by lia; discriminate.
  - rewrite task_reg_get_id_available in Hstep by (assumption || lia).
    inversion Hstep; subst; unfold valid_task_reg_allocator in Hvalid.
    repeat split; auto; lia.
Qed.

Lemma task_reg_get_id_failure_no_change : forall sg st id post,
  task_reg_get_id sg st = (id, OS_ERR_NO_MORE_ID_AVAIL, post) -> post = st.
Proof.
  intros sg st id post H; unfold task_reg_get_id in H.
  destruct (Z.leb (cfgTaskRegisters (osKernelConfig sg)) (taskRegNextID st));
    inversion H; reflexivity.
Qed.

Lemma task_reg_get_id_successive_ids : forall sg st first mid second post,
  valid_task_reg_allocator sg st -> sg.(osKernelConfig).(cfgTaskRegisters) <= 255 ->
  task_reg_get_id sg st = (first, OS_ERR_NONE, mid) ->
  task_reg_get_id sg mid = (second, OS_ERR_NONE, post) -> second = first + 1.
Proof.
  intros sg st first mid second post Hvalid Hmax Hfirst Hsecond.
  destruct (task_reg_get_id_success sg st first mid Hvalid Hmax Hfirst) as [Hid [Hrange Hmid]].
  assert (HmidValid : valid_task_reg_allocator sg mid).
  { rewrite Hmid; unfold valid_task_reg_allocator; simpl; lia. }
  destruct (task_reg_get_id_success sg mid second post HmidValid Hmax Hsecond) as [HsecondId _].
  rewrite HsecondId, Hmid; reflexivity.
Qed.

Lemma task_reg_allocator_initial_valid : forall sg st,
  0 <= sg.(osKernelConfig).(cfgTaskRegisters) ->
  valid_task_reg_allocator sg (task_set_reg_next_id st 0).
Proof. intros; unfold valid_task_reg_allocator; simpl; lia. Qed.

Definition task_public_storage_without_reg_allocator (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  store_used_task_map sg st.(inUsedTaskStates) **
  task_free_storage_rep sg st.(taskLifecycle).(taskFreeStorage) st.(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error st.(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg st.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount) ** store_prio_tbl sg st.(prioTbl).

Lemma task_public_storage_split_reg_allocator : forall sg st,
  task_public_storage sg st |--
  task_reg_allocator_rep sg st ** task_public_storage_without_reg_allocator sg st.
Proof.
  intros; unfold task_public_storage, task_public_storage_without_reg_allocator; entailer!.
Qed.
Lemma task_public_storage_merge_updated_reg_allocator : forall sg st id,
  task_reg_allocator_rep sg (task_set_reg_next_id st id) **
  task_public_storage_without_reg_allocator sg st |--
  task_public_storage sg (task_set_reg_next_id st id).
Proof.
  intros; unfold task_public_storage, task_public_storage_without_reg_allocator.
  cbn [task_set_reg_next_id inUsedTaskStates unUsedTaskStates tcbListHead prioTbl taskCount taskLifecycle].
  entailer!.
Qed.

(** OS_InitTCBList: the zeroed image is updated at Next and at the configured default Name. *)
Definition task_boot_image (sg : StableGlobVars) (name : addr) (next : option TaskID) : TCBLayoutImage :=
  tcb_init_free_image sg next name.

Fixpoint task_boot_storage (sg : StableGlobVars) (name : addr) (ids : list TaskID)
  : TaskID -> option TCBLayoutImage :=
  match ids with
  | [] => fun _ => None
  | tid :: rest => fun slot => if Z.eq_dec slot tid
      then Some (task_boot_image sg name (hd_error rest))
      else task_boot_storage sg name rest slot
  end.

Lemma task_boot_storage_domain : forall sg name ids tid,
  (exists image, task_boot_storage sg name ids tid = Some image) <-> In tid ids.
Proof.
  intros sg name ids; induction ids as [|head rest IH]; intro tid; simpl.
  - split; [intros [image H]; discriminate|contradiction].
  - destruct (Z.eq_dec tid head) as [->|Hne].
    + split; [auto|intros; eexists; reflexivity].
    + rewrite IH; split; [auto|intros [H|H]; [congruence|exact H]].
Qed.

Lemma task_boot_storage_flags_zero : forall sg name ids tid image,
  task_boot_storage sg name ids tid = Some image -> image (TCBCommonField TCBFlagsRdy) = Some 0.
Proof.
  intros sg name ids; induction ids as [|head rest IH]; intros tid image H; simpl in H.
  - discriminate.
  - destruct (Z.eq_dec tid head).
    + inversion H; reflexivity.
    + eapply IH; eauto.
Qed.

Lemma task_free_links_storage_frame : forall sg ids before after,
  (forall tid image, In tid ids -> before tid = Some image -> after tid = Some image) ->
  task_free_links sg before ids -> task_free_links sg after ids.
Proof.
  intros sg ids; induction ids as [|head rest IH]; intros before after Hframe Hlinks; simpl in *.
  - exact I.
  - destruct Hlinks as [image [Himage [Hnext Hrest]]].
    exists image; split; [eapply Hframe; eauto|]. split; [exact Hnext|].
    eapply IH; [|exact Hrest]. intros; eapply Hframe; eauto.
Qed.

Lemma task_boot_storage_links : forall sg name ids,
  NoDup ids -> task_free_links sg (task_boot_storage sg name ids) ids.
Proof.
  intros sg name ids Hnd; induction Hnd as [|head rest Hnot Hnd IH]; simpl.
  - exact I.
  - exists (task_boot_image sg name (hd_error rest)); split.
    + destruct (Z.eq_dec head head); [reflexivity|contradiction].
    + split; [reflexivity|].
      eapply task_free_links_storage_frame; [|exact IH].
      intros tid image Hin Himage; destruct (Z.eq_dec tid head); [subst; contradiction|exact Himage].
Qed.

Definition task_boot (sg : StableGlobVars) (name : addr) : Glob_TaskAbstractState :=
  let ids := Zrange 0 (sg.(osMaxTasks) + sg.(osNSysTasks)) in
  {| inUsedTaskStates := fun _ => None; unUsedTaskStates := ids;
     tcbListHead := None; prioTbl := fun _ => PTFree; taskCount := 0; taskRegNextID := 0;
     parkedTaskStacks := fun _ => None;
     taskLifecycle := {| taskFreeStorage := task_boot_storage sg name ids;
       taskReservations := fun _ => None; taskActiveOrder := []; taskNextGeneration := 0;
       taskInvocations := fun _ => None; taskRetiredInvocations := fun _ => false;
       taskNextInvocation := 0; taskPublications := [] |} |}.

Lemma task_boot_no_private_slot : forall sg name tid,
  ~ task_private_slot (task_boot sg name) tid.
Proof. intros sg name tid [p [entry [allocation [H _]]]]; discriminate. Qed.

Lemma task_boot_pool_partition : forall sg name,
  task_pool_partition sg (task_boot sg name).
Proof.
  intros sg name; split.
  - intro tid; split.
    + intro H; right; left; apply In_Zrange; exact H.
    + intros [[t H]|[Hin|Hprivate]]; [discriminate|apply In_Zrange; exact Hin|].
      exfalso; exact (task_boot_no_private_slot sg name tid Hprivate).
  - split; [intros tid t H; discriminate|].
    split; [intros tid _; apply task_boot_no_private_slot|].
    split; [apply NoDup_Zrange|]. split.
    + intro tid; symmetry; apply task_boot_storage_domain.
    + intros p q e1 e2 a1 a2 H; discriminate.
Qed.

Lemma task_boot_in_range : forall sg name,
  0 <= sg.(osKernelConfig).(cfgTaskRegisters) -> task_in_range sg (task_boot sg name).
Proof.
  intros sg name Hregs; split; [apply task_boot_pool_partition|].
  split.
  - split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
    split; [intro tid; split; [contradiction|intros [t H]; discriminate]|exact I].
  - split; [apply task_boot_storage_links; apply NoDup_Zrange|].
    split.
    + split; intros; discriminate.
    + split.
      * split; [intros tid t H; discriminate|].
        split; [intros p entry allocation H; discriminate|].
        split; [intros invocation origin H; discriminate|].
        split; [intros invocation tid generation H; discriminate|].
        split; [intros invocation tid generation H; contradiction|].
        intros p entry allocation observer H; discriminate.
      * split; [intros tid t H; discriminate|].
        split; [intros p i j a b Ha; discriminate|].
        split; [intros tid t H; discriminate|]. split.
        -- intros tid image Himage; exists 0; eapply task_boot_storage_flags_zero; exact Himage.
        -- unfold valid_task_reg_allocator; simpl; lia.
Qed.

(** An observation of a live-slot update is framed whenever that field is
    unchanged. This does not assert that arbitrary native bytes or external
    object references satisfy their resource/cross-module obligations. *)
Lemma glob_task_set_usedtask_observation : forall (A : Type) (observe : TaskAbstractState -> A)
  tasks tid old new slot,
  tasks.(inUsedTaskStates) tid = Some old -> observe new = observe old ->
  option_map observe ((glob_task_set_usedtask tasks tid new).(inUsedTaskStates) slot) =
  option_map observe (tasks.(inUsedTaskStates) slot).
Proof.
  intros A observe tasks tid old new slot Hold Hfield.
  cbn [glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb slot tid) eqn:Hslot; [|reflexivity].
  apply Z.eqb_eq in Hslot; subst slot; rewrite Hold; simpl; rewrite Hfield; reflexivity.
Qed.

Lemma glob_task_set_usedtask_live_iff : forall tasks tid old new slot,
  tasks.(inUsedTaskStates) tid = Some old ->
  (exists t, (glob_task_set_usedtask tasks tid new).(inUsedTaskStates) slot = Some t) <->
  (exists t, tasks.(inUsedTaskStates) slot = Some t).
Proof.
  intros tasks tid old new slot Hold; simpl.
  destruct (Z.eqb slot tid) eqn:Hslot; [|reflexivity].
  apply Z.eqb_eq in Hslot; subst slot; rewrite Hold; split; intros; eauto.
Qed.

Lemma task_active_links_update : forall tasks tid old new previous ids,
  tasks.(inUsedTaskStates) tid = Some old -> new.(taskID) = old.(taskID) ->
  new.(nextTCB) = old.(nextTCB) -> new.(prevTCB) = old.(prevTCB) ->
  task_active_links tasks.(inUsedTaskStates) previous ids ->
  task_active_links (glob_task_set_usedtask tasks tid new).(inUsedTaskStates) previous ids.
Proof.
  intros tasks tid old new previous ids Hold Hid Hnext Hprev.
  revert previous; induction ids as [|slot rest IH]; intros previous Hlinks; [exact I|].
  destruct Hlinks as [t [Ht [HidSlot [Hprevious [Hsuccessor Hrest]]]]].
  simpl; destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; assert (Heq : t = old) by congruence; subst t.
    exists new; split; [reflexivity|]. split; [congruence|].
    split; [congruence|]. split; [congruence|apply IH; exact Hrest].
  - exists t; split; [exact Ht|]. split; [exact HidSlot|]. split; [exact Hprevious|].
    split; [exact Hsuccessor|apply IH; exact Hrest].
Qed.

(** Task-pool validity depends on slot/generation, list links and priority.
    Updates to status, timeout, messages and native fields share this
    structural theorem. Their bit encodings, readiness and IPC/name/stack
    relationships still need their own actual update/transport proofs. *)
Lemma task_update_preserves_in_range : forall sg tasks tid old new,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  new.(taskID) = old.(taskID) -> new.(taskGeneration) = old.(taskGeneration) ->
  new.(curPrio) = old.(curPrio) -> new.(nextTCB) = old.(nextTCB) ->
  new.(prevTCB) = old.(prevTCB) ->
  task_in_range sg (glob_task_set_usedtask tasks tid new).
Proof.
  intros sg tasks tid old new
    [Hpool [Hactive [Hfree [Hreservations [Hgenerations [Hregistered [Hunique [Hpriority Hrest]]]]]]]]
    Hold Hid Hg Hp Hnext Hprev.
  assert (Horigin : forall slot t,
    (glob_task_set_usedtask tasks tid new).(inUsedTaskStates) slot = Some t ->
    exists before, tasks.(inUsedTaskStates) slot = Some before /\
      t.(taskGeneration) = before.(taskGeneration) /\ t.(curPrio) = before.(curPrio)).
  { intros slot t Ht; simpl in Ht; destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Ht as Heq; subst t; exists old; auto.
    - exists t; auto. }
  split.
  - destruct Hpool as [Hdomain [Hused [Hprivate [Hnd [Hstorage HreservationUnique]]]]].
    split.
    + intro slot; rewrite glob_task_set_usedtask_live_iff by exact Hold; exact (Hdomain slot).
    + split.
      * intros slot t Ht; destruct (Horigin slot t Ht) as [before [Hb _]]; exact (Hused slot before Hb).
      * split; [exact Hprivate|]. split; [exact Hnd|]. split; [exact Hstorage|exact HreservationUnique].
  - split.
    + destruct Hactive as [Hnd [Hhead [Hcount [Hcover Hlinks]]]].
      split; [exact Hnd|]. split; [exact Hhead|]. split; [exact Hcount|]. split.
      * intro slot; rewrite glob_task_set_usedtask_live_iff by exact Hold; exact (Hcover slot).
      * apply task_active_links_update with (old := old); assumption.
    + split; [exact Hfree|]. split; [exact Hreservations|]. split.
      * destruct Hgenerations as [Hlive Hother]; split; [|exact Hother].
        intros slot t Ht; destruct (Horigin slot t Ht) as [before [Hb [Hgen Hprio]]].
        simpl; rewrite Hgen; exact (Hlive slot before Hb).
      * split.
        -- eapply glob_task_set_usedtask_preserves_current_prio_registered; eauto.
        -- split.
           ++ intros i j a b Ha Hb Hprio.
              destruct (Horigin i a Ha) as [beforeA [HbeforeA [_ HprioA]]].
              destruct (Horigin j b Hb) as [beforeB [HbeforeB [_ HprioB]]].
              eapply Hunique; [exact HbeforeA|exact HbeforeB|congruence].
           ++ split; [|exact Hrest].
              intros slot t Ht; destruct (Horigin slot t Ht) as [before [Hb [_ Hprio]]].
              rewrite Hprio; exact (Hpriority slot before Hb).
Qed.

Definition task_set_flag_node (t : TaskAbstractState) (p : addr) : TaskAbstractState :=
  {| taskID := t.(taskID);
     taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := p;
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio);
     stat := t.(stat);
     statPend := t.(statPend);
     dly := t.(dly);
     eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg);
     nextTCB := t.(nextTCB);
     prevTCB := t.(prevTCB);
     delReq := t.(delReq) |}.

Lemma task_set_flag_node_image_eq : forall sg t p,
  task_tcb64_image sg (task_set_flag_node t p) =
  tcb_write (task_tcb64_image sg t) TCBFlagNode (Some p).
Proof.
  intros sg t p; apply functional_extensionality; intro f.
  destruct f; reflexivity.
Qed.


Definition task_clear_flag_status (status : TaskStatus) : TaskStatus :=
  task_clear_pending_status status PendFlag.

Lemma task_clear_flag_status_encoding : forall status,
  encode_task_status (task_clear_flag_status status) = Z.land (encode_task_status status) 223.
Proof.
  intro status; apply task_clear_pending_status_encoding.
Qed.

(** Combined TCB effect of OS_FlagTaskRdy and its OS_FlagUnlink call.
    Intermediate stores require their focused raw representations. It
    clears only the FLAG bit and retains suspension/other pending bits. *)
Definition task_flag_wake (t : TaskAbstractState) (flags : Z) (result : PendStatus) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := 0;
     tcbFlagsRdy := flags;
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := task_clear_flag_status t.(stat); statPend := result; dly := 0;
     eventPtr := t.(eventPtr); eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg); nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_flag_wake_preserves_in_range : forall sg tasks tid old flags result,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_flag_wake old flags result)).
Proof. intros; eapply task_update_preserves_in_range; eauto; reflexivity. Qed.

Lemma task_flag_wake_clears_registration : forall t flags result,
  (task_flag_wake t flags result).(tcbFlagNode) = 0 /\
  (task_non_suspension_bits (task_flag_wake t flags result).(stat)) <> task_pend_mask PendFlag.
Proof.
  intros t flags result; split; [reflexivity|].
  apply task_clear_pending_status_not_same_kind.
Qed.

Lemma task_flag_wake_ready_iff_not_suspended : forall t flags result,
  task_linked_wait_phase t PendFlag ->
  is_effectively_ready (task_flag_wake t flags result).(stat) (task_flag_wake t flags result).(dly) =
  negb (task_is_suspended t.(stat)).
Proof.
  intros t flags result [Hpending|[Hpending _]].
  - change (is_effectively_ready (task_clear_pending_status t.(stat) PendFlag) 0 = negb (task_is_suspended t.(stat))).
    unfold is_effectively_ready; rewrite task_clear_pending_status_same_kind by exact Hpending.
    rewrite task_clear_pending_status_preserves_suspension; destruct (task_is_suspended t.(stat)); reflexivity.
  - change (is_effectively_ready (task_clear_pending_status t.(stat) PendFlag) 0 = negb (task_is_suspended t.(stat))).
    rewrite task_clear_pending_status_none by exact Hpending.
    unfold is_effectively_ready; rewrite Hpending; destruct (task_is_suspended t.(stat)); reflexivity.
Qed.

Lemma task_flag_wake_keeps_ready_task_ready : forall t flags result,
  is_effectively_ready t.(stat) t.(dly) = true ->
  is_effectively_ready (task_flag_wake t flags result).(stat) (task_flag_wake t flags result).(dly) = true.
Proof.
  intros t flags result Hready.
  pose proof (task_effectively_ready_has_no_pending t Hready) as Hp.
  change (is_effectively_ready (task_clear_pending_status t.(stat) PendFlag) 0 = true).
  rewrite task_clear_pending_status_none by exact Hp.
  unfold is_effectively_ready in *; rewrite Hp in *.
  destruct (task_is_suspended t.(stat)); [discriminate|reflexivity].
Qed.

Lemma task_flag_wake_image_eq : forall sg t flags result,
  task_tcb64_image sg (task_flag_wake t flags result) =
  tcb_write
    (tcb_write
      (tcb_write
        (tcb_write
          (tcb_write (task_tcb64_image sg t) TCBDly (Some 0))
          TCBFlagsRdy (Some flags))
        TCBStat (Some (Z.land (encode_task_status t.(stat)) 223)))
      TCBStatPend (Some (encode_pend_status result)))
    TCBFlagNode (Some 0).
Proof.
  intros sg t flags result; apply functional_extensionality; intro f.
  destruct f; try reflexivity.
  change (Some (encode_task_status (task_clear_flag_status t.(stat))) =
    Some (Z.land (encode_task_status t.(stat)) 223)).
  rewrite task_clear_flag_status_encoding; reflexivity.
Qed.

Lemma task_update_preserves_idle_tail : forall sg tasks tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  task_idle_tail sg tasks ->
  task_idle_tail sg (glob_task_set_usedtask tasks tid new).
Proof.
  intros sg tasks tid old new Hold Hprio [prefix [idle [t [Horder [Ht [Hp Hothers]]]]]].
  exists prefix, idle; simpl; destruct (Z.eqb idle tid) eqn:E.
  - apply Z.eqb_eq in E; subst idle; rewrite Hold in Ht; injection Ht as Ht; subst t.
    exists new; split; [exact Horder|]. split; [reflexivity|]. split; [congruence|].
    intros slot other Hin Hother; destruct (Z.eqb slot tid) eqn:F.
    + apply Z.eqb_eq in F; subst slot; exfalso; exact (Hothers tid old Hin Hold Hp).
    + eapply Hothers; eauto.
  - exists t; split; [exact Horder|]. split; [exact Ht|]. split; [exact Hp|].
    intros slot other Hin Hother; destruct (Z.eqb slot tid) eqn:F.
    + apply Z.eqb_eq in F; subst slot; injection Hother as Heq; subst other.
      rewrite Hprio; eapply Hothers; eauto.
    + eapply Hothers; eauto.
Qed.

(** Non-live-map public resources: free storage, roots, table and allocator. *)
Definition task_public_storage_without_used_map (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) : Assertion :=
  task_free_storage_rep sg st.(taskLifecycle).(taskFreeStorage) st.(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error st.(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg st.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> st.(taskCount) **
  store_prio_tbl sg st.(prioTbl) ** task_reg_allocator_rep sg st.

Lemma task_public_storage_used_map_equiv : forall sg st,
  task_public_storage sg st --||--
  store_used_task_map sg st.(inUsedTaskStates) **
    task_public_storage_without_used_map sg st.
Proof.
  intros; unfold task_public_storage, task_public_storage_without_used_map;
    split; entailer!.
Qed.

(** Retains every other live TCB and the non-live-map resources. The
    focused live TCB is not also owned by this residual. *)
Definition task_public_storage_without_task (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (tid : TaskID) : Assertion :=
  store_map_missing_i (used_task_rep sg)
    st.(inUsedTaskStates) tid ** task_public_storage_without_used_map sg st.

Lemma task_public_storage_split_task : forall sg st tid t,
  st.(inUsedTaskStates) tid = Some t ->
  task_public_storage sg st |--
  used_task_rep sg tid t **
    task_public_storage_without_task sg st tid.
Proof.
  intros sg st tid t Ht.
  rewrite task_public_storage_used_map_equiv.
  unfold task_public_storage_without_task, store_used_task_map.
  sep_apply_l_atomic (store_map_split (used_task_rep sg) tid t _ Ht).
  entailer!.
Qed.

Lemma task_public_storage_merge_task : forall sg st tid t,
  st.(inUsedTaskStates) tid = Some t ->
  used_task_rep sg tid t **
    task_public_storage_without_task sg st tid |-- task_public_storage sg st.
Proof.
  intros sg st tid t Ht.
  rewrite task_public_storage_used_map_equiv.
  unfold task_public_storage_without_task, store_used_task_map.
  rewrite (logic_equiv_sepcon_assoc _ _ _).
  eapply derivable1_sepcon_mono; [|reflexivity].
  rewrite (logic_equiv_sepcon_comm _ _).
  apply (store_map_merge (used_task_rep sg) tid t _ Ht).
Qed.

Lemma task_public_storage_merge_updated_task : forall sg st tid new,
  used_task_rep sg tid new **
    task_public_storage_without_task sg st tid |--
  task_public_storage sg (glob_task_set_usedtask st tid new).
Proof.
  intros sg st tid new.
  assert (Hlookup : (glob_task_set_usedtask st tid new).(inUsedTaskStates) tid = Some new).
  { simpl; rewrite Z.eqb_refl; reflexivity. }
  assert (Hoff : forall slot, slot <> tid -> st.(inUsedTaskStates) slot =
    (glob_task_set_usedtask st tid new).(inUsedTaskStates) slot).
  { intros slot Hne; simpl; apply Z.eqb_neq in Hne; rewrite Hne; reflexivity. }
  eapply derivable1_trans;
    [|apply (task_public_storage_merge_task sg (glob_task_set_usedtask st tid new) tid new Hlookup)].
  apply derivable1_sepcon_mono; [reflexivity|].
  unfold task_public_storage_without_task.
  apply derivable1_sepcon_mono; [|reflexivity].
  apply (proj1 (store_map_missing_i_equiv (used_task_rep sg) _ _ tid Hoff)).
Qed.

Definition task_public_storage_without_field (sg : StableGlobVars)
  (st : Glob_TaskAbstractState) (tid : TaskID) (t : TaskAbstractState)
  (field : TCBLayoutField) : Assertion :=
  tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) (task_layout_image sg t) field **
    task_public_storage_without_task sg st tid.

Lemma task_public_storage_split_field : forall sg st tid t field,
  st.(inUsedTaskStates) tid = Some t ->
  In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  task_public_storage sg st |--
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field (task_layout_image sg t field) **
    task_public_storage_without_field sg st tid t field.
Proof.
  intros sg st tid t field Ht Hin; unfold task_public_storage_without_field.
  sep_apply_l_atomic (task_public_storage_split_task sg st tid t Ht).
  unfold used_task_rep, task_slot_storage_rep.
  sep_apply_l_atomic (tcb_configured_storage_split_field _ _
    (task_slot_addr sg tid) (task_layout_image sg t) field Hin).
  entailer!.
Qed.

Lemma task_public_storage_merge_field : forall sg st tid t field,
  st.(inUsedTaskStates) tid = Some t ->
  In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field (task_layout_image sg t field) **
    task_public_storage_without_field sg st tid t field |-- task_public_storage sg st.
Proof.
  intros sg st tid t field Ht Hin; unfold task_public_storage_without_field.
  rewrite (logic_equiv_sepcon_assoc _ _ _).
  eapply derivable1_trans;
    [apply derivable1_sepcon_mono; [apply tcb_configured_storage_merge_field; exact Hin|reflexivity]|].
  apply task_public_storage_merge_task; exact Ht.
Qed.

Lemma task_public_storage_merge_updated_field : forall sg st tid old new field value,
  In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  task_layout_image sg new = tcb_layout_write (task_layout_image sg old) field value ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field value **
    task_public_storage_without_field sg st tid old field |--
  task_public_storage sg (glob_task_set_usedtask st tid new).
Proof.
  intros sg st tid old new field value Hin Himage; unfold task_public_storage_without_field.
  rewrite (logic_equiv_sepcon_assoc _ _ _).
  eapply derivable1_trans;
    [apply derivable1_sepcon_mono; [apply tcb_configured_storage_merge_updated_field; exact Hin|reflexivity]|].
  rewrite <- Himage.
  apply task_public_storage_merge_updated_task.
Qed.

(** A two-field residual is useful only when a real source operation writes
    two distinct TCB cells before the task object is reassembled.  The
    residual removes both fields from the same configured field inventory;
    it is not a second task representation and does not discard the other
    TCB fields. *)
Definition task_public_storage_without_two_fields
  (sg : StableGlobVars) (st : Glob_TaskAbstractState)
  (tid : TaskID) (t : TaskAbstractState)
  (field1 field2 : TCBLayoutField) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg tid))
    (remove TCBLayoutField_eq_dec field2
      (remove TCBLayoutField_eq_dec field1
        (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
          sg.(osKernelConfig).(cfgTaskProfile))))
    (task_layout_image sg t) **
  task_public_storage_without_task sg st tid.

Lemma tcb_configured_fields_remove_nodup : forall fields field,
  NoDup fields -> NoDup (remove TCBLayoutField_eq_dec field fields).
Proof.
  intros fields field Hnd.
  induction Hnd as [|head rest Hnot Hrest IH].
  - simpl; constructor.
  - simpl; destruct (TCBLayoutField_eq_dec field head) as [->|Hneq].
    + exact IH.
    + constructor.
      * intros Hin; apply Hnot; apply in_remove in Hin; tauto.
      * exact IH.
Qed.

Lemma task_public_storage_split_two_fields : forall sg st tid t field1 field2,
  field1 <> field2 ->
  st.(inUsedTaskStates) tid = Some t ->
  In field1 (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  In field2 (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  task_public_storage sg st |--
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field1 (task_layout_image sg t field1) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field2 (task_layout_image sg t field2) **
  task_public_storage_without_two_fields sg st tid t field1 field2.
Proof.
  intros sg st tid t field1 field2 Hdistinct Ht Hfield1 Hfield2.
  assert (Hfield2_removed :
    In field2
      (remove TCBLayoutField_eq_dec field1
        (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
          sg.(osKernelConfig).(cfgTaskProfile)))).
  { eapply in_in_remove.
    - intro Heq; apply Hdistinct; symmetry; exact Heq.
    - exact Hfield2.
  }
  unfold task_public_storage_without_two_fields.
  sep_apply_l_atomic (task_public_storage_split_task sg st tid t Ht).
  unfold used_task_rep, task_slot_storage_rep.
  sep_apply_l_atomic (tcb_configured_storage_split_field
    sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) (task_layout_image sg t) field1 Hfield1).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field
    TCBLayoutField (option Z) TCBLayoutField_eq_dec
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg tid))
    (remove TCBLayoutField_eq_dec field1
      (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile)))
    (task_layout_image sg t) field2
    (tcb_configured_fields_remove_nodup _ _
      (tcb_configured_fields_nodup _ _)) Hfield2_removed).
  entailer!.
Qed.

(** Distinct concrete fields commute at the image level.  This is the
    representation fact needed when the spatial proof merges the second
    store first and the first store second. *)
Lemma task_layout_write_commute : forall image field1 field2 value1 value2,
  field1 <> field2 ->
  tcb_layout_write (tcb_layout_write image field1 value1) field2 value2 =
  tcb_layout_write (tcb_layout_write image field2 value2) field1 value1.
Proof.
  intros image field1 field2 value1 value2 Hdistinct.
  apply functional_extensionality; intro field.
  unfold tcb_layout_write, field_update.
  destruct (TCBLayoutField_eq_dec field field1) as [H1|H1].
  - subst field.
    destruct (TCBLayoutField_eq_dec field1 field2) as [H12|H12].
    + exfalso; apply Hdistinct; exact H12.
    + reflexivity.
  - destruct (TCBLayoutField_eq_dec field field2) as [H2|H2].
    + subst field; reflexivity.
    + reflexivity.
Qed.

(** Merge two actual field stores into the configured public TCB storage.
    The theorem deliberately takes an image equation instead of inventing a
    task setter: each caller supplies the source-faithful abstract update
    and may then connect the resulting image to its own state transformer. *)
Lemma task_public_storage_merge_updated_two_fields : forall sg st tid old new
  field1 field2 value1 value2,
  field1 <> field2 ->
  In field1 (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  In field2 (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile)) ->
  task_layout_image sg new =
    tcb_layout_write
      (tcb_layout_write (task_layout_image sg old) field1 value1)
      field2 value2 ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field1 value1 **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) field2 value2 **
  task_public_storage_without_two_fields sg st tid old field1 field2 |--
  task_public_storage sg (glob_task_set_usedtask st tid new).
Proof.
  intros sg st tid old new field1 field2 value1 value2 Hdistinct Hfield1 Hfield2 Himage.
  unfold task_public_storage_without_two_fields.
  change
    (((tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
        (task_slot_addr sg tid) field1 value1 **
      tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
        (task_slot_addr sg tid) field2 value2) **
      (TaskFieldStorage.store_fields TCBLayoutField_eq_dec
        (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
          (task_slot_addr sg tid))
        (remove TCBLayoutField_eq_dec field2
          (remove TCBLayoutField_eq_dec field1
            (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
              sg.(osKernelConfig).(cfgTaskProfile))))
        (task_layout_image sg old) **
       task_public_storage_without_task sg st tid)) |--
    task_public_storage sg (glob_task_set_usedtask st tid new)).
  assert (Hfield2_removed :
    In field2
      (remove TCBLayoutField_eq_dec field1
        (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
          sg.(osKernelConfig).(cfgTaskProfile)))).
  { eapply in_in_remove.
    - intro Heq; apply Hdistinct; symmetry; exact Heq.
    - exact Hfield2.
  }
  assert (Hfields1_nodup :
    NoDup (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile))) by
    apply tcb_configured_fields_nodup.
  assert (Hfields1_removed_nodup :
    NoDup (remove TCBLayoutField_eq_dec field1
      (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile)))).
  { apply tcb_configured_fields_remove_nodup; exact Hfields1_nodup. }
  set (image_after_field2 :=
    tcb_layout_write (task_layout_image sg old) field2 value2).
  set (image_after_both :=
    tcb_layout_write image_after_field2 field1 value1).
  assert (Hfield2_merge :
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
        (task_slot_addr sg tid) field2 value2 **
      TaskFieldStorage.store_fields TCBLayoutField_eq_dec
        (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
          (task_slot_addr sg tid))
        (remove TCBLayoutField_eq_dec field2
          (remove TCBLayoutField_eq_dec field1
            (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
              sg.(osKernelConfig).(cfgTaskProfile))))
        (task_layout_image sg old) |--
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec
      (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
        (task_slot_addr sg tid))
      (remove TCBLayoutField_eq_dec field1
        (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
          sg.(osKernelConfig).(cfgTaskProfile)))
      image_after_field2).
  { apply TaskFieldStorage.store_fields_merge_updated_field.
    - exact Hfields1_removed_nodup.
    - exact Hfield2_removed. }
  assert (Hfield1_merge :
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
        (task_slot_addr sg tid) field1 value1 **
      TaskFieldStorage.store_fields TCBLayoutField_eq_dec
        (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
          (task_slot_addr sg tid))
        (remove TCBLayoutField_eq_dec field1
          (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
            sg.(osKernelConfig).(cfgTaskProfile)))
        image_after_field2 |--
    tcb_configured_storage_rep sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile)
      (task_slot_addr sg tid) image_after_both).
  { unfold image_after_both.
    apply tcb_configured_storage_merge_updated_field.
    exact Hfield1. }
  assert (Hboth :
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
        (task_slot_addr sg tid) field1 value1 **
      (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
        (task_slot_addr sg tid) field2 value2 **
       (TaskFieldStorage.store_fields TCBLayoutField_eq_dec
        (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
          (task_slot_addr sg tid))
        (remove TCBLayoutField_eq_dec field2
          (remove TCBLayoutField_eq_dec field1
            (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
              sg.(osKernelConfig).(cfgTaskProfile))))
        (task_layout_image sg old) **
       task_public_storage_without_task sg st tid))) |--
    tcb_configured_storage_rep sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile)
      (task_slot_addr sg tid) image_after_both **
    task_public_storage_without_task sg st tid).
  { rewrite (logic_equiv_sepcon_swap _ _ _).
    rewrite (logic_equiv_sepcon_swap _ _ _).
    sep_apply_l_atomic Hfield2_merge.
    rewrite (logic_equiv_sepcon_swap _ _ _).
    sep_apply_l_atomic Hfield1_merge.
    entailer!. }
  rewrite <- (logic_equiv_sepcon_assoc _ _ _).
  eapply derivable1_trans; [exact Hboth|].
  unfold used_task_rep, task_slot_storage_rep.
  unfold image_after_both, image_after_field2.
  rewrite <- (task_layout_write_commute (task_layout_image sg old)
    field1 field2 value1 value2 Hdistinct).
  rewrite <- Himage.
  apply task_public_storage_merge_updated_task.
Qed.

Definition task_set_event_ptr (t : TaskAbstractState) (p : option EventID) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration); tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := t.(stat); statPend := t.(statPend); dly := t.(dly);
     eventPtr := p; eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg); nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

(** Reassemble the public pool after the selected task's actual profiling
    counter store. Scheduler selection and the platform call are separate. *)
Lemma task_public_storage_merge_context_switch : forall sg tasks tid old,
  sg.(osKernelConfig).(cfgTaskProfile) = true ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    TCBCtxSwCtr (Some (kernel_u32 (old.(tcbCtxSwCtr) + 1))) **
    task_public_storage_without_field sg tasks tid old TCBCtxSwCtr |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (task_record_context_switch old)).
Proof.
  intros sg tasks tid old Hprofile.
  apply task_public_storage_merge_updated_field.
  - rewrite Hprofile; apply tcb_configured_profile_field_in; simpl; tauto.
  - apply task_record_context_switch_layout_image_eq.
Qed.

Lemma task_record_context_switch_preserves_in_range : forall sg tasks tid old,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_record_context_switch old)).
Proof. intros; eapply task_update_preserves_in_range; eauto; reflexivity. Qed.

Lemma task_set_event_ptr_put_back : forall t, task_set_event_ptr t t.(eventPtr) = t.
Proof. intros []; reflexivity. Qed.

Lemma task_set_event_ptr_last_write : forall t first last,
  task_set_event_ptr (task_set_event_ptr t first) last = task_set_event_ptr t last.
Proof. reflexivity. Qed.

Lemma task_set_event_ptr_preserves_in_range : forall sg tasks tid old pointer,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_set_event_ptr old pointer)).
Proof. intros; eapply task_update_preserves_in_range; eauto; reflexivity. Qed.

Lemma task_set_event_ptr_image_eq : forall sg t pointer,
  task_tcb64_image sg (task_set_event_ptr t pointer) =
    tcb_write (task_tcb64_image sg t) TCBEventPtr (Some (encode_event_link sg pointer)).
Proof. intros; apply functional_extensionality; intros []; reflexivity. Qed.

(** OS_EventTaskRdy first writes Dly/Msg/Stat/StatPend.  The subsequent
    OS_EventTaskRemove call clears EventPtr after updating the Event bitmap;
    moving that clear into this prefix would lose the source ordering. *)
Definition task_event_wake_before_remove (t : TaskAbstractState) (kind : PendType)
  (message : addr) (result : PendStatus) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration); tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := task_clear_pending_status t.(stat) kind;
     statPend := result; dly := 0; eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := Some message; nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Definition task_event_wake_single (t : TaskAbstractState) (kind : PendType)
  (message : addr) (result : PendStatus) : TaskAbstractState :=
  task_set_event_ptr (task_event_wake_before_remove t kind message result) None.

Lemma task_event_wake_before_remove_image_eq : forall sg t kind message result,
  task_tcb64_image sg (task_event_wake_before_remove t kind message result) =
    tcb_event_wake_image (task_tcb64_image sg t) (encode_task_status t.(stat))
      (task_pend_mask kind) message result.
Proof.
  intros; apply functional_extensionality; intros []; try reflexivity.
  change (Some (encode_task_status (task_clear_pending_status t.(stat) kind)) =
    Some (Z.land (encode_task_status t.(stat)) (Z.lxor (encode_pend_type (Some kind)) 255))).
  rewrite task_clear_pending_status_encoding; reflexivity.
Qed.

Lemma task_event_wake_single_image_eq : forall sg t kind message result,
  task_tcb64_image sg (task_event_wake_single t kind message result) =
    tcb_write (task_tcb64_image sg (task_event_wake_before_remove t kind message result))
      TCBEventPtr (Some 0).
Proof. intros; apply task_set_event_ptr_image_eq. Qed.

Lemma task_event_wake_single_preserves_in_range : forall sg tasks tid old kind message result,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_event_wake_single old kind message result)).
Proof. intros; eapply task_update_preserves_in_range; eauto; reflexivity. Qed.

Lemma task_event_wake_single_clears_registration : forall t kind message result,
  task_linked_wait_phase t kind ->
  (task_event_wake_single t kind message result).(eventPtr) = None /\
    (task_non_suspension_bits (task_event_wake_single t kind message result).(stat)) = 0.
Proof.
  intros t kind message result Hphase; split; [reflexivity|].
  change ((task_non_suspension_bits (task_clear_pending_status t.(stat) kind)) = 0).
  destruct Hphase as [Hpending|[Hpending _]].
  - apply task_clear_pending_status_same_kind; exact Hpending.
  - rewrite task_clear_pending_status_none by exact Hpending; exact Hpending.
Qed.

Lemma task_event_wake_single_ready_iff_not_suspended : forall t kind message result,
  task_linked_wait_phase t kind ->
  is_effectively_ready (task_event_wake_single t kind message result).(stat)
    (task_event_wake_single t kind message result).(dly) = negb (task_is_suspended t.(stat)).
Proof.
  intros t kind message result Hphase.
  pose proof (proj2 (task_event_wake_single_clears_registration t kind message result Hphase)) as Hpending.
  unfold is_effectively_ready; rewrite Hpending; simpl.
  change ((negb (task_is_suspended (task_clear_pending_status t.(stat) kind)) && true)%bool =
    negb (task_is_suspended t.(stat))).
  rewrite task_clear_pending_status_preserves_suspension, Bool.andb_true_r; reflexivity.
Qed.

Lemma task_event_wake_single_keeps_ready_task_ready : forall t kind message result,
  is_effectively_ready t.(stat) t.(dly) = true ->
  is_effectively_ready (task_event_wake_single t kind message result).(stat)
    (task_event_wake_single t kind message result).(dly) = true.
Proof.
  intros t kind message result Hready.
  pose proof (task_effectively_ready_has_no_pending t Hready) as Hpending.
  change (is_effectively_ready (task_clear_pending_status t.(stat) kind) 0 = true).
  rewrite task_clear_pending_status_none by exact Hpending.
  unfold is_effectively_ready in *; rewrite Hpending in *.
  destruct (task_is_suspended t.(stat)); [discriminate|reflexivity].
Qed.

(** This rule consumes the real final EventPtr store and the exact prefix
    residual.  It neither writes a TCB cell nor updates an Event bitmap. *)
Lemma task_event_wake_single_merge_event_ptr : forall sg base t kind message result,
  tcb_cell base TCBEventPtr (Some 0) **
    tcb64_storage_without base TCBEventPtr
      (task_tcb64_image sg (task_event_wake_before_remove t kind message result)) |--
  tcb64_storage_rep base (task_tcb64_image sg (task_event_wake_single t kind message result)).
Proof.
  intros; rewrite task_event_wake_single_image_eq; apply tcb64_storage_merge_updated.
Qed.

Lemma task_current_prio_table_owner_eq : forall sg tasks tid t owner,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some t ->
  tasks.(prioTbl) t.(curPrio) = PTTask owner -> owner = tid.
Proof.
  intros sg tasks tid t owner [_ [_ [_ [_ [_ [Hregistered _]]]]]] Hget Howner.
  specialize (Hregistered tid t Hget); congruence.
Qed.

(** Sem/Mbox/Queue/Mutex Pend write Stat, StatPend and Dly before calling
    OS_EventTaskWait.  EventPtr still has its old value at this stage.
    The OR store retains every previously set bit of the canonical byte. *)
Definition task_prepare_event_wait (t : TaskAbstractState) (kind : PendType)
  (timeout : Z) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration); tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio);
     stat := Byte.repr (task_status_set_wait (encode_task_status t.(stat)) kind);
     statPend := PendOK; dly := timeout; eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg); nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_prepare_event_wait_status_encoding : forall t kind timeout,
  encode_task_status (task_prepare_event_wait t kind timeout).(stat) =
    Z.lor (encode_task_status t.(stat)) (encode_pend_type (Some kind)).
Proof.
  intros; apply encode_task_status_repr, task_status_set_wait_in_range, encode_task_status_in_range.
Qed.

Lemma task_prepare_event_wait_pending_bits : forall t kind timeout,
  task_non_suspension_bits t.(stat) = 0 ->
  task_non_suspension_bits (task_prepare_event_wait t kind timeout).(stat) = task_pend_mask kind.
Proof.
  intros t kind timeout Hnone.
  change (task_non_suspension_bits
    (Byte.repr (task_status_set_wait (encode_task_status t.(stat)) kind)) = task_pend_mask kind).
  rewrite (task_status_single_of_mask t.(stat) None Hnone).
  destruct kind; destruct (task_is_suspended t.(stat)); reflexivity.
Qed.

Lemma task_prepare_event_wait_image_eq : forall sg t kind timeout,
  task_tcb64_image sg (task_prepare_event_wait t kind timeout) =
    tcb_prepare_wait_image (task_tcb64_image sg t)
      (task_status_set_wait (encode_task_status t.(stat)) kind) timeout.
Proof.
  intros sg t kind timeout; apply functional_extensionality; intros []; try reflexivity.
  change (Some (encode_task_status (task_prepare_event_wait t kind timeout).(stat)) =
    Some (Z.lor (encode_task_status t.(stat)) (encode_pend_type (Some kind)))).
  f_equal; apply task_prepare_event_wait_status_encoding.
Qed.

Lemma task_prepare_event_wait_not_ready : forall t kind timeout,
  is_effectively_ready (task_prepare_event_wait t kind timeout).(stat)
    (task_prepare_event_wait t kind timeout).(dly) = false.
Proof.
  intros t kind timeout; unfold is_effectively_ready.
  destruct (Z.eqb (task_non_suspension_bits (stat (task_prepare_event_wait t kind timeout))) 0) eqn:E;
    [apply Z.eqb_eq in E; exfalso; exact (task_status_set_wait_non_suspension_nonzero t.(stat) kind E)|reflexivity].
Qed.

Lemma task_prepare_event_wait_preserves_in_range : forall sg tasks tid old kind timeout,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_prepare_event_wait old kind timeout)).
Proof. intros; eapply task_update_preserves_in_range; eauto; reflexivity. Qed.

(** Source fields of OS_EventTaskWaitMulti and its callers.  The event
    sequence is a logical observation for subsequent registration/cleanup;
    it is not converted into an OS_EVENT ** value or array ownership. *)

Definition task_set_multi_fields (t : TaskAbstractState) (array : addr)
  (events : list EventID) (ready : option EventID) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := array;
     curPrio := t.(curPrio); stat := t.(stat); statPend := t.(statPend); dly := t.(dly);
     eventPtr := t.(eventPtr); eventMultiWaitEvents := events; eventMultiRdy := ready;
     msg := t.(msg); nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_set_multi_fields_layout_image_eq : forall sg t array events ready,
  task_layout_image sg (task_set_multi_fields t array events ready) =
    tcb_layout_set_multi (task_layout_image sg t) array
      (encode_event_link sg ready).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |];
    try destruct field; reflexivity.
Qed.

Lemma task_set_multi_fields_common_frame : forall sg t array events ready,
  tcb_layout_common_image (task_layout_image sg (task_set_multi_fields t array events ready)) =
    tcb_layout_common_image (task_layout_image sg t).
Proof. intros; apply functional_extensionality; intros []; reflexivity. Qed.

Lemma task_register_multi_wait_image_eq : forall sg t array events,
  task_layout_image sg (task_set_multi_fields t array events None) =
    tcb_multi_wait_image (task_layout_image sg t) array.
Proof. intros; apply task_set_multi_fields_layout_image_eq. Qed.

Lemma task_set_multi_fields_preserves_in_range : forall sg tasks tid old array events ready,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_set_multi_fields old array events ready)).
Proof. intros; eapply task_update_preserves_in_range; eauto; reflexivity. Qed.

Definition task_public_storage_without_multi (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  tcb_configured_without_multi sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid) (task_layout_image sg t) **
    task_public_storage_without_task sg tasks tid.

Lemma task_public_storage_split_multi : forall sg tasks tid t,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true ->
  tasks.(inUsedTaskStates) tid = Some t ->
  task_public_storage sg tasks |--
    task_multi_fields_rep (task_slot_addr sg tid) t.(tcbEventMultiPtr)
      (encode_event_link sg t.(eventMultiRdy)) **
    task_public_storage_without_multi sg tasks tid t.
Proof.
  intros sg tasks tid t Hmulti Hget; unfold task_public_storage_without_multi.
  sep_apply_l_atomic (task_public_storage_split_task sg tasks tid t Hget).
  unfold used_task_rep, task_slot_storage_rep; rewrite Hmulti.
  sep_apply_l_atomic (tcb_configured_storage_split_multi sg.(osKernelConfig).(cfgTaskProfile)
    (task_slot_addr sg tid)
    (task_layout_image sg t) t.(tcbEventMultiPtr)
    (encode_event_link sg t.(eventMultiRdy)) eq_refl eq_refl).
  entailer!.
Qed.

(** Restores the actual public-map ownership after the two pointer stores.
    Event registration, array borrowing and scheduler validity remain
    separate obligations; this is not a global-invariant preservation claim. *)
Lemma task_public_storage_merge_updated_multi : forall sg tasks tid t array events ready,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true ->
  task_multi_fields_rep (task_slot_addr sg tid) array (encode_event_link sg ready) **
    task_public_storage_without_multi sg tasks tid t |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (task_set_multi_fields t array events ready)).
Proof.
  intros sg tasks tid t array events ready Hmulti; unfold task_public_storage_without_multi.
  rewrite (logic_equiv_sepcon_assoc _ _ _).
  eapply derivable1_trans;
    [apply derivable1_sepcon_mono; [apply tcb_configured_storage_merge_multi|reflexivity]|].
  rewrite <- (task_set_multi_fields_layout_image_eq sg t array events ready).
  rewrite <- Hmulti; apply task_public_storage_merge_updated_task.
Qed.

(** PendMulti's caller prefix, before WaitMulti registers the actual array.
    Empty event arrays can yield mask zero; that execution is not removed
    by a fabricated nonempty-input guard. *)
Definition task_prepare_multi_wait (t : TaskAbstractState) (mask timeout : Z) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration); tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio);
     stat := Byte.repr (task_status_set_multi_wait (encode_task_status t.(stat)) mask);
     statPend := PendOK; dly := timeout; eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg); nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_prepare_multi_wait_layout_image_eq : forall sg t mask timeout,
  0 <= mask < 8 ->
  task_layout_image sg (task_prepare_multi_wait t mask timeout) =
    tcb_layout_update_common
      (fun image => tcb_prepare_multi_wait_image image (encode_task_status t.(stat)) mask timeout)
      (task_layout_image sg t).
Proof.
  intros sg t mask timeout Hmask; apply functional_extensionality; intros [field| | | | | | |];
    try destruct field; try reflexivity.
  change (Some (encode_task_status (Byte.repr (task_status_set_multi_wait (encode_task_status t.(stat)) mask))) =
    Some (task_status_set_multi_wait (encode_task_status t.(stat)) mask)).
  f_equal; apply encode_task_status_repr, task_status_set_multi_wait_in_range;
    [apply encode_task_status_in_range|exact Hmask].
Qed.

Lemma task_multi_pend_layout_image_eq : forall sg t mask timeout array events,
  0 <= mask < 8 ->
  task_layout_image sg (task_set_multi_fields (task_prepare_multi_wait t mask timeout) array events None) =
    tcb_multi_pend_image (task_layout_image sg t) (encode_task_status t.(stat)) mask timeout array.
Proof.
  intros; rewrite task_set_multi_fields_layout_image_eq, task_prepare_multi_wait_layout_image_eq by assumption.
  reflexivity.
Qed.

(** TCB suffix of EventTaskRdy when the actual MultiPtr is non-NULL.
    Event-list removal is owned by Event; the original logical input order
    remains available for the caller's continuation after MultiPtr is zero. *)
Definition task_multi_wake (t : TaskAbstractState) (kind : PendType)
  (message : addr) (result : PendStatus) (selected : EventID) : TaskAbstractState :=
  task_set_multi_fields (task_event_wake_single t kind message result)
    0 t.(eventMultiWaitEvents) (Some selected).

Lemma task_multi_wake_layout_image_eq : forall sg t kind message result selected,
  task_layout_image sg (task_multi_wake t kind message result selected) =
    tcb_multi_wake_image (task_layout_image sg t) (encode_task_status t.(stat))
      (task_pend_mask kind) message result (event_pool_addr sg selected).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |]; try destruct field; try reflexivity.
  change (Some (encode_task_status (task_clear_pending_status t.(stat) kind)) =
    Some (task_status_clear_wait (encode_task_status t.(stat)) (task_pend_mask kind))).
  f_equal; apply task_clear_pending_status_encoding.
Qed.

Lemma task_multi_wake_woken_fields : forall sg t kind message result selected,
  task_status_is_multi (encode_task_status t.(stat)) = true -> kind <> PendMulti ->
  event_pool_addr sg selected <> 0 ->
  task_multi_woken_fields (task_layout_image sg (task_multi_wake t kind message result selected))
    (event_pool_addr sg selected) result.
Proof. intros; rewrite task_multi_wake_layout_image_eq; apply tcb_multi_wake_woken_fields; assumption. Qed.

(** Common status endpoint, without registration writes.  Whether Msg
    is cleared is selected by the actual caller, not by a kernel guard.
    The corresponding field image retains the source assignment order. *)
Definition task_clear_pend_status (clear_message : bool) (t : TaskAbstractState) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := Byte.zero; statPend := PendOK; dly := t.(dly);
     eventPtr := t.(eventPtr); eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy);
     msg := if clear_message then None else t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Definition task_clear_pend_status_message (t : TaskAbstractState) : TaskAbstractState :=
  task_clear_pend_status true t.

(** Normal PendMulti cleanup only.  The invalid-readied-type early return
    skips these writes.  Dly and the single EventPtr are not cleared here. *)
Definition task_multi_cleanup (t : TaskAbstractState) : TaskAbstractState :=
  task_set_multi_fields (task_clear_pend_status_message t) 0 [] None.

Lemma task_multi_cleanup_layout_image_eq : forall sg t,
  task_layout_image sg (task_multi_cleanup t) =
    tcb_multi_cleanup_image (task_layout_image sg t).
Proof. intros; apply functional_extensionality; intros [field| | | | | | |]; try destruct field; reflexivity. Qed.

(** Canonical endpoint for single-Event Pend cleanup.  Sem instantiates
    clear_message=false; Queue uses true.  Disabled Multi fields remain
    unchanged, and no new abstract TCB or wait phase is introduced. *)
Definition task_event_pend_cleanup (multi clear_message : bool)
  (t : TaskAbstractState) : TaskAbstractState :=
  task_set_event_ptr
    (if multi then task_set_multi_fields (task_clear_pend_status clear_message t) 0 [] None
     else task_clear_pend_status clear_message t) None.

Definition task_message_pend_cleanup (multi : bool) (t : TaskAbstractState) : TaskAbstractState :=
  task_event_pend_cleanup multi true t.

Lemma task_event_pend_cleanup_layout_image_eq : forall sg multi clear_message t,
  task_layout_image sg (task_event_pend_cleanup multi clear_message t) =
    tcb_event_pend_cleanup_image multi clear_message (task_layout_image sg t).
Proof.
  intros; destruct multi, clear_message; apply functional_extensionality;
    intros [field| | | | | | |]; try destruct field; reflexivity.
Qed.

Lemma task_message_pend_cleanup_layout_image_eq : forall sg multi t,
  task_layout_image sg (task_message_pend_cleanup multi t) =
    tcb_message_pend_cleanup_image multi (task_layout_image sg t).
Proof. intros; apply task_event_pend_cleanup_layout_image_eq. Qed.

Lemma task_event_pend_cleanup_observations : forall multi clear_message t,
  let after := task_event_pend_cleanup multi clear_message t in
  after.(stat) = Byte.zero /\ after.(statPend) = PendOK /\ after.(eventPtr) = None /\
  after.(msg) = (if clear_message then None else t.(msg)) /\ after.(dly) = t.(dly) /\
  after.(tcbFlagNode) = t.(tcbFlagNode) /\
  after.(eventMultiWaitEvents) = (if multi then [] else t.(eventMultiWaitEvents)).
Proof. intros [] [] t; repeat split; reflexivity. Qed.

Lemma task_message_pend_cleanup_observations : forall multi t,
  let after := task_message_pend_cleanup multi t in
  after.(stat) = Byte.zero /\ after.(statPend) = PendOK /\
  after.(eventPtr) = None /\ after.(msg) = None /\ after.(dly) = t.(dly) /\
  after.(tcbFlagNode) = t.(tcbFlagNode) /\
  after.(eventMultiWaitEvents) = (if multi then [] else t.(eventMultiWaitEvents)).
Proof. intros [] t; repeat split; reflexivity. Qed.

Lemma task_event_pend_cleanup_preserves_in_range : forall sg tasks tid old multi clear_message,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg
    (glob_task_set_usedtask tasks tid (task_event_pend_cleanup multi clear_message old)).
Proof.
  intros; eapply task_update_preserves_in_range; try eassumption;
    destruct multi, clear_message; reflexivity.
Qed.

Lemma task_message_pend_cleanup_preserves_in_range : forall sg tasks tid old multi,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg
    (glob_task_set_usedtask tasks tid (task_message_pend_cleanup multi old)).
Proof. intros; eapply task_event_pend_cleanup_preserves_in_range; eassumption. Qed.

Lemma task_event_pend_cleanup_preserves_ready : forall multi clear_message t,
  is_effectively_ready t.(stat) t.(dly) = true ->
  is_effectively_ready (task_event_pend_cleanup multi clear_message t).(stat)
    (task_event_pend_cleanup multi clear_message t).(dly) = true.
Proof.
  intros multi clear_message t Hready; unfold is_effectively_ready in Hready.
  destruct (Z.eqb (task_non_suspension_bits t.(stat)) 0); [|discriminate].
  apply Bool.andb_true_iff in Hready; destruct Hready as [_ Hdelay].
  destruct multi; exact Hdelay.
Qed.

Lemma task_message_pend_cleanup_preserves_ready : forall multi t,
  is_effectively_ready t.(stat) t.(dly) = true ->
  is_effectively_ready (task_message_pend_cleanup multi t).(stat)
    (task_message_pend_cleanup multi t).(dly) = true.
Proof. intros; apply task_event_pend_cleanup_preserves_ready; assumption. Qed.

(** One status-cell update, shared by Suspend and Resume.  The caller's
    delay, result, registrations, message and native storage are frames. *)
Definition task_set_status (t : TaskAbstractState) (status : TaskStatus) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration); tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := status; statPend := t.(statPend); dly := t.(dly);
     eventPtr := t.(eventPtr); eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy); msg := t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_set_status_layout_image_eq : forall sg t status,
  task_layout_image sg (task_set_status t status) =
    tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBStat)
      (Some (encode_task_status status)).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |]; try reflexivity;
    destruct field; reflexivity.
Qed.

Definition task_suspend (t : TaskAbstractState) : TaskAbstractState :=
  task_set_status t (task_status_suspend t.(stat)).

Definition task_resume (t : TaskAbstractState) : TaskAbstractState :=
  task_set_status t (task_status_resume t.(stat)).

Lemma task_suspend_layout_image_eq : forall sg t,
  task_layout_image sg (task_suspend t) =
    tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBStat)
      (Some (Z.lor (encode_task_status t.(stat)) task_suspend_mask)).
Proof.
  intros; unfold task_suspend; rewrite task_set_status_layout_image_eq.
  unfold encode_task_status; rewrite task_status_suspend_encoding; reflexivity.
Qed.

Lemma task_resume_layout_image_eq : forall sg t,
  task_layout_image sg (task_resume t) =
    tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBStat)
      (Some (task_status_clear_wait (encode_task_status t.(stat)) task_suspend_mask)).
Proof.
  intros; unfold task_resume; rewrite task_set_status_layout_image_eq.
  unfold encode_task_status; rewrite task_status_resume_encoding; reflexivity.
Qed.

Lemma task_suspend_not_ready : forall t,
  is_effectively_ready (task_suspend t).(stat) (task_suspend t).(dly) = false.
Proof.
  intro t; change (is_effectively_ready (task_status_suspend t.(stat)) t.(dly) = false).
  unfold is_effectively_ready; rewrite (proj2 (task_status_suspend_observations t.(stat))).
  destruct (Z.eqb (task_non_suspension_bits (task_status_suspend t.(stat))) 0); reflexivity.
Qed.

Lemma task_suspend_preserves_linked_phase : forall t kind,
  task_linked_wait_phase (task_suspend t) kind <-> task_linked_wait_phase t kind.
Proof.
  intros; unfold task_linked_wait_phase; cbn [task_suspend task_set_status stat statPend dly].
  rewrite (proj1 (task_status_suspend_observations t.(stat))); reflexivity.
Qed.

Lemma task_resume_preserves_linked_phase : forall t kind,
  task_linked_wait_phase (task_resume t) kind <-> task_linked_wait_phase t kind.
Proof.
  intros; unfold task_linked_wait_phase; cbn [task_resume task_set_status stat statPend dly].
  rewrite (proj1 (task_status_resume_observations t.(stat))); reflexivity.
Qed.

(** The source tests PEND_ANY after clearing SUSPEND, then Dly.  This is
    not the single-wait is_effectively_ready test: MULTI is outside that
    mask, whereas a remaining SEM/MBOX/Q bit prevents ready insertion. *)
Definition task_resume_ready_test (t : TaskAbstractState) : bool :=
  negb (task_status_has_pending (encode_task_status (task_resume t).(stat))) && Z.eqb t.(dly) 0.

Lemma task_resume_ready_test_iff : forall t,
  task_resume_ready_test t = true <->
    Z.land (encode_task_status t.(stat)) task_pend_any_mask = 0 /\ t.(dly) = 0.
Proof.
  intro t; unfold task_resume_ready_test.
  change ((negb (task_status_has_pending
    (encode_task_status (task_status_resume t.(stat)))) && Z.eqb t.(dly) 0)%bool = true <->
    Z.land (encode_task_status t.(stat)) task_pend_any_mask = 0 /\ t.(dly) = 0).
  unfold encode_task_status; rewrite task_status_resume_encoding.
  unfold task_status_has_pending, task_status_clear_wait.
  rewrite <- Z.land_assoc.
  change ((negb (negb (Z.eqb (Z.land (task_status.encode_task_status t.(stat)) task_pend_any_mask) 0))
    && Z.eqb t.(dly) 0)%bool = true <->
    Z.land (task_status.encode_task_status t.(stat)) task_pend_any_mask = 0 /\ t.(dly) = 0).
  rewrite Bool.negb_involutive, Bool.andb_true_iff, !Z.eqb_eq; reflexivity.
Qed.

(** Task-owned source protocol, separate from raw field storage and pool
    structure.  It has no ghost field: it observes the existing status
    bytes and the actual Multi configuration. *)
Definition task_reserved_bits_clear (sg : StableGlobVars) (tasks : Glob_TaskAbstractState) : Prop :=
  forall tid t, tasks.(inUsedTaskStates) tid = Some t ->
    task_status_reserved_bits_clear sg.(osKernelConfig).(cfgEventMultiEnabled) t.(stat).

Lemma task_effectively_ready_reserved_bits_clear : forall multi t,
  is_effectively_ready t.(stat) t.(dly) = true -> task_status_reserved_bits_clear multi t.(stat).
Proof.
  intros; apply task_status_no_pending_reserved_bits_clear.
  apply task_effectively_ready_has_no_pending; assumption.
Qed.

Lemma task_boot_reserved_bits_clear : forall sg name,
  task_reserved_bits_clear sg (task_boot sg name).
Proof. intros sg name tid t H; discriminate. Qed.

Lemma task_reserved_bits_clear_update_task : forall sg tasks tid t,
  task_reserved_bits_clear sg tasks ->
  task_status_reserved_bits_clear sg.(osKernelConfig).(cfgEventMultiEnabled) t.(stat) ->
  task_reserved_bits_clear sg (glob_task_set_usedtask tasks tid t).
Proof.
  intros sg tasks tid t Htasks Hstatus slot node Hnode; simpl in Hnode.
  destruct (Z.eqb slot tid); [injection Hnode as Hnode; subst node; exact Hstatus|].
  exact (Htasks slot node Hnode).
Qed.

Lemma task_commit_preserves_reserved_bits_clear : forall sg tasks p invocation node,
  task_reserved_bits_clear sg tasks ->
  task_status_reserved_bits_clear sg.(osKernelConfig).(cfgEventMultiEnabled) node.(stat) ->
  task_reserved_bits_clear sg (task_commit tasks p invocation node).
Proof.
  intros sg tasks p invocation node Htasks Hstatus slot after Hafter.
  pose proof (task_commit_observation TaskStatus stat tasks p invocation node slot
    (fun _ _ _ => eq_refl)) as Hstat.
  rewrite Hafter in Hstat; destruct (Z.eq_dec slot node.(taskID)).
  - injection Hstat as Hstat; rewrite Hstat; exact Hstatus.
  - destruct (tasks.(inUsedTaskStates) slot) as [before|] eqn:Hbefore; [|discriminate].
    injection Hstat as Hstat; rewrite Hstat; exact (Htasks slot before Hbefore).
Qed.

Lemma task_resume_effectively_ready_eq_test : forall t,
  task_status_reserved_bits_clear false t.(stat) ->
  is_effectively_ready (task_resume t).(stat) (task_resume t).(dly) = task_resume_ready_test t.
Proof.
  intros t Hclear; unfold task_resume_ready_test.
  change (is_effectively_ready (task_status_resume t.(stat)) t.(dly) =
    (negb (task_status_has_pending (encode_task_status (task_status_resume t.(stat)))) && Z.eqb t.(dly) 0)%bool).
  unfold is_effectively_ready.
  rewrite (proj1 (task_status_resume_observations t.(stat))),
    (proj2 (task_status_resume_observations t.(stat))).
  unfold encode_task_status; rewrite task_status_resume_encoding.
  unfold task_status_has_pending, task_status_clear_wait; rewrite <- Z.land_assoc.
  change ((if Z.eqb (task_non_suspension_bits t.(stat)) 0 then (true && Z.eqb t.(dly) 0)%bool else false) =
    (negb (negb (Z.eqb (Z.land (task_status.encode_task_status t.(stat)) task_pend_any_mask) 0)) && Z.eqb t.(dly) 0)%bool).
  rewrite (task_status_no_multi_pending_mask_eq t.(stat) Hclear), Bool.negb_involutive.
  destruct (Z.eqb (Z.land (task_status.encode_task_status t.(stat)) task_pend_any_mask) 0); reflexivity.
Qed.
