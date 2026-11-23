Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
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
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.mutex.

Import ListNotations.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(* L3 representation/localization support for the literal Create path. *)

(* The disabled PCP is a stored tag.  It never denotes an OSTCBPrioTbl
   cell, so only an enabled PCP changes the concrete priority-table list. *)
Definition mutex_create_priotbl_after
  (sg : StableGlobVars) (pcp : Priority) (before : list addr)
  : list addr :=
  if Z.eqb pcp sg.(osPrioMutexCeilDis)
  then before
  else replace_Znth pcp 1 before.

Definition mutex_create_pcp_slot_available_prop
  (sg : StableGlobVars) (pcp : Priority) (before : list addr) : Prop :=
  pcp = sg.(osPrioMutexCeilDis) \/
  (pcp <> sg.(osPrioMutexCeilDis) /\ Znth pcp before 0 = 0).

Definition mutex_create_free_snapshot_prop
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (eid : EventID) (rest : list EventID) (head next : addr) : Prop :=
  (head = 0 /\ event_free_list_exact_prop ls0.(EventState) []) \/
  (head <> 0 /\ valid_event_id sg eid /\
   task_event_id_unreferenced_prop ls0 eid /\
   event_free_head_snapshot_prop
     sg ls0.(EventState) eid rest head next).

(* Keep the immutable C parameter linked to the mathematical PCP without
   exposing that equality to QCP's local-store normalizer at full joins. *)
Definition mutex_create_priority_input_prop
  (actual input : Priority) : Prop :=
  actual = input.

(* The concrete priority table and OSEventFreeList head are exposed; every
   other component of the entry invariant remains in this residual. *)
Definition mutex_create_head_open_inv
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  verification_slice_task_inv_no_priotbl sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv_no_free_head sg s.(TskState) s.(EventState) **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

(* After the nonempty head is detached, the tail remains in the residual and
   the detached node is owned separately until all mutex fields are ready. *)
Definition mutex_create_node_open_inv
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (rest : list EventID) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  verification_slice_task_inv_no_priotbl sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv_free_head_rest sg s.(TskState) s.(EventState) rest **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

Definition mutex_create_unused_event_no_ptr (base : addr) : Assertion :=
  (base + OSEventType_off) # UChar |->
    encode_event_type OS_EVENT_TYPE_UNUSED **
  (base + OSEventCnt_off) # UShort |->_ **
  (base + OSEventGrp_off) # UChar |->_ **
  (base + OSEventTbl_off + 0) # UChar |->_ **
  (base + OSEventTbl_off + 1) # UChar |->_ **
  (base + OSEventTbl_off + 2) # UChar |->_ **
  (base + OSEventTbl_off + 3) # UChar |->_ **
  (base + OSEventTbl_off + 4) # UChar |->_ **
  (base + OSEventTbl_off + 5) # UChar |->_ **
  (base + OSEventTbl_off + 6) # UChar |->_ **
  (base + OSEventTbl_off + 7) # UChar |->_ .

Definition mutex_create_wait_table_uninitialized (base : addr) : Assertion :=
  (base + OSEventGrp_off) # UChar |->_ **
  (base + OSEventTbl_off + 0) # UChar |->_ **
  (base + OSEventTbl_off + 1) # UChar |->_ **
  (base + OSEventTbl_off + 2) # UChar |->_ **
  (base + OSEventTbl_off + 3) # UChar |->_ **
  (base + OSEventTbl_off + 4) # UChar |->_ **
  (base + OSEventTbl_off + 5) # UChar |->_ **
  (base + OSEventTbl_off + 6) # UChar |->_ **
  (base + OSEventTbl_off + 7) # UChar |->_ .

Definition mutex_create_wait_table_zero (base : addr) : Assertion :=
  (base + OSEventGrp_off) # UChar |-> 0 **
  (base + OSEventTbl_off + 0) # UChar |-> 0 **
  (base + OSEventTbl_off + 1) # UChar |-> 0 **
  (base + OSEventTbl_off + 2) # UChar |-> 0 **
  (base + OSEventTbl_off + 3) # UChar |-> 0 **
  (base + OSEventTbl_off + 4) # UChar |-> 0 **
  (base + OSEventTbl_off + 5) # UChar |-> 0 **
  (base + OSEventTbl_off + 6) # UChar |-> 0 **
  (base + OSEventTbl_off + 7) # UChar |-> 0.

(* The implementation restores interrupts before initializing the detached
   event.  This frame deliberately does not claim the whole invariant: the
   node is absent from the global free root and remains privately owned. *)
Definition mutex_create_transient_frame
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (pcp : Priority) (eid : EventID) (rest : list EventID)
  (prio_before : list addr) : Assertion :=
  coq_prop
    (valid_stable_glob_vars sg /\
     valid_mutex_pcp sg pcp /\
     valid_event_id sg eid /\
     task_event_id_unreferenced_prop ls0 eid /\
     ls0.(EventState).(unUsedEventStates) = eid :: rest /\
     prio_tbl_list_rel sg ls0.(TskState) prio_before /\
     mutex_create_pcp_slot_available_prop sg pcp prio_before) &&
  mutex_create_node_open_inv sg ls0 rest **
  verification_slice_store_priotbl_list sg
    (mutex_create_priotbl_after sg pcp prio_before) **
  sg.(g_OSEventFreeList) # Ptr |-> free_event_head sg rest **
  unused_complete_event sg (event_addr sg eid) eid.

Definition mutex_create_restore_frame
  (sg : StableGlobVars) (ls0 : UCOS2_Verify_State)
  (pcp : Priority) (eid : EventID) (rest : list EventID)
  (prio_before : list addr) (success : bool) : Assertion :=
  if success
  then mutex_create_transient_frame sg ls0 pcp eid rest prio_before
  else UCOS2_verification_slice_inv sg ls0.

(* L5: exact abstract endpoint and public observation. *)

Definition mutex_create_fresh_event (pcp : Priority)
  : OSEventAbstractState :=
  {| eventGeneration := 0%nat;
     eventName := 0; eventPadding1 := None; eventPadding2 := None;
     eventPadding3 := None; eventPadding19 := None;
     eventType   := OS_EVENT_TYPE_MUTEX;
     mutexFields := Some
       {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None |};
     semFields   := None;
     mboxFields  := None;
     queueFields := None;
     waitList    := [] |}.

Definition mutex_create_initialized_event
  (sg : StableGlobVars) (ls_post : UCOS2_Verify_State)
  (pcp : Priority) (eid : EventID) : Assertion :=
  used_complete_event sg ls_post.(TskState) (event_addr sg eid) eid
    (mutex_create_fresh_event pcp).

Definition mutex_create_task_after
  (sg : StableGlobVars) (pcp : Priority)
  (before : Glob_TaskAbstractState) : Glob_TaskAbstractState :=
  {| inUsedTaskStates := before.(inUsedTaskStates);
     unUsedTaskStates := before.(unUsedTaskStates);
     tcbListHead      := before.(tcbListHead);
     prioTbl          :=
       if Z.eqb pcp sg.(osPrioMutexCeilDis)
       then before.(prioTbl)
       else fun p =>
         if Z.eqb p pcp then PTReserved else before.(prioTbl) p;
     taskRegNextID := before.(taskRegNextID);
     parkedTaskStacks := before.(parkedTaskStacks);
     taskLifecycle := before.(taskLifecycle);
     taskCount        := before.(taskCount) |}.

Definition mutex_create_event_after
  (pcp : Priority) (eid : EventID) (rest : list EventID)
  (before : Glob_EventAbstractState) : Glob_EventAbstractState :=
  {| inUsedEventStates := fun eid' =>
       if Z.eqb eid' eid
       then Some (mutex_create_fresh_event pcp)
       else before.(inUsedEventStates) eid';
     eventLifecycle := before.(eventLifecycle);
     publishedQueueBytes := before.(publishedQueueBytes);
     unUsedEventStates := rest |}.

Definition mutex_create_state_after
  (sg : StableGlobVars) (pcp : Priority) (eid : EventID)
  (rest : list EventID) (ls0 : UCOS2_Verify_State)
  : UCOS2_Verify_State :=
  {| IntrState  := ls0.(IntrState);
     TskState   := mutex_create_task_after sg pcp ls0.(TskState);
     SchedState := ls0.(SchedState);
     EventState := mutex_create_event_after pcp eid rest ls0.(EventState);
     TickState  := ls0.(TickState);
     FlagState := ls0.(FlagState);
     MemoryState := ls0.(MemoryState);
     TimerState := ls0.(TimerState);
     StatsState := ls0.(StatsState);
     ControlState := ls0.(ControlState);
     NameState := ls0.(NameState) |}.

Definition mutex_create_success_transition_prop
  (sg : StableGlobVars) (ls0 ls_post : UCOS2_Verify_State)
  (pcp : Priority) (eid : EventID) (rest : list EventID) : Prop :=
  ls0.(EventState).(unUsedEventStates) = eid :: rest /\
  task_event_id_unreferenced_prop ls0 eid /\
  ls_post = mutex_create_state_after sg pcp eid rest ls0 /\
  atomic_mutex_create sg pcp ls0 (Some eid) ls_post /\
  crit_rel_task_event ls0 ls_post.

Definition mutex_create_restore_transition_prop
  (sg : StableGlobVars)
  (ls0 ls_inside ls_post : UCOS2_Verify_State)
  (pcp : Priority) (eid : EventID) (rest : list EventID)
  (success : bool) : Prop :=
  crit_rel_no_os_state_change ls0 ls_inside /\
  if success
  then mutex_create_success_transition_prop
         sg ls0 ls_post pcp eid rest /\
       crit_rel_task_event ls_inside ls_post
  else ls_post = ls0.

(* Every alternative includes the negation of earlier guards.  Error values
   are tied to the current profile's canonical error-code owner. *)
Definition mutex_create_result_prop
  (sg : StableGlobVars) (ls0 ls_post : UCOS2_Verify_State)
  (pcp isr : Z) (prio_before : list addr) (free_head : addr)
  (eid : EventID) (rest : list EventID) (ret err : Z) : Prop :=
  (pcp <> sg.(osPrioMutexCeilDis) /\
   pcp >= sg.(osLowestPrio) /\
   ret = 0 /\ err = encode_os_err_code OS_ERR_PRIO_INVALID /\
   ls_post = ls0) \/
  (valid_mutex_pcp sg pcp /\ isr > 0 /\
   ret = 0 /\ err = encode_os_err_code OS_ERR_CREATE_ISR /\
   ls_post = ls0) \/
  (pcp <> sg.(osPrioMutexCeilDis) /\
   0 <= pcp < sg.(osLowestPrio) /\ isr <= 0 /\
   Znth pcp prio_before 0 <> 0 /\
   ret = 0 /\ err = encode_os_err_code OS_ERR_PRIO_EXIST /\
   ls_post = ls0) \/
  (valid_mutex_pcp sg pcp /\ isr <= 0 /\
   (pcp = sg.(osPrioMutexCeilDis) \/
    (pcp <> sg.(osPrioMutexCeilDis) /\
     Znth pcp prio_before 0 = 0)) /\
   free_head = 0 /\
   ret = 0 /\ err = encode_os_err_code OS_ERR_PEVENT_NULL /\
   ls_post = ls0) \/
  (valid_mutex_pcp sg pcp /\ isr <= 0 /\
   (pcp = sg.(osPrioMutexCeilDis) \/
    (pcp <> sg.(osPrioMutexCeilDis) /\
     Znth pcp prio_before 0 = 0)) /\
   free_head <> 0 /\ free_head = event_addr sg eid /\
   ret = event_addr sg eid /\ err = encode_os_err_code OS_ERR_NONE /\
   mutex_create_success_transition_prop
     sg ls0 ls_post pcp eid rest).

Require Import Coq.Logic.FunctionalExtensionality.
Lemma mutex_create_pcp_cnt_encoding_exact__leaf_pure_and_global_localization :
  forall p : Z, 0 <= p < 64 ->
    Z.lor (unsigned_last_nbits (Z.shiftl p 8) 16) 255 =
    p * 256 + 255.
Proof.
  intros p Hp.
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 8) with 256 by reflexivity.
  rewrite unsigned_last_nbits_eq by (cbn; lia).
  assert (Hland : Z.land (p * 256) 255 = 0).
  {
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    replace (2 ^ 8) with 256 by reflexivity.
    apply Z.mod_mul.
    lia.
  }
  pose proof (Z.add_lor_land (p * 256) 255) as Hsum.
  rewrite Hland in Hsum.
  lia.
Qed.
Lemma prio_tbl_list_rel_canonical__leaf_pure_and_global_localization :
  forall sg st l,
    prio_tbl_list_rel sg st l ->
    l = verification_slice_prioTbl_to_addrs sg st.(prioTbl).
Proof.
  intros sg st l [Hlen Hnth].
  apply (proj2 (list_eq_ext l (verification_slice_prioTbl_to_addrs sg st.(prioTbl)) 0)).
  split.
  - rewrite Hlen.
    unfold verification_slice_prioTbl_to_addrs, verification_slice_prioTbl_to_addrs_rec.
    reflexivity.
  - intros i Hi.
    rewrite Hlen in Hi.
    assert (Hrange : 0 <= i < OS_PRIO_TBL_SIZE).
    { unfold OS_PRIO_TBL_SIZE. exact Hi. }
    specialize (Hnth i Hrange).
    rewrite Hnth.
    unfold verification_slice_prioTbl_to_addrs, verification_slice_prioTbl_to_addrs_rec, Znth.
    replace i with (Z.of_nat (Z.to_nat i)) by
      (rewrite Z2Nat.id by lia; reflexivity).
    remember (Z.to_nat i) as n eqn:Hn.
    assert (Hn64 : (n < 64)%nat).
    {
      subst n.
      apply (proj1 (Z2Nat.inj_lt i 64 ltac:(lia) ltac:(lia))).
      unfold OS_PRIO_TBL_SIZE in Hrange.
      exact (proj2 Hrange).
    }
    do 64 (destruct n as [|n]; [reflexivity|]).
    lia.
Qed.
Lemma prio_tbl_list_rel_eq__entry_and_critical_restore :
  forall sg st l,
    prio_tbl_list_rel sg st l ->
    l = verification_slice_prioTbl_to_addrs sg st.(prioTbl).
Proof.
  intros sg st l [Hlen Hnth].
  assert (Hrec : forall n acc,
    verification_slice_prioTbl_to_addrs_rec sg st.(prioTbl) n acc =
      map (fun k => verification_slice_prio_tbl_entry_to_addr sg (st.(prioTbl) (Z.of_nat k)))
        (seq 0 n) ++ acc).
  {
    induction n as [| n IH]; intros acc.
    - reflexivity.
    - unfold verification_slice_prioTbl_to_addrs_rec at 1.
      rewrite IH.
      rewrite seq_S, map_app.
      simpl.
      rewrite <- app_assoc.
      reflexivity.
  }
  unfold verification_slice_prioTbl_to_addrs.
  rewrite Hrec.
  rewrite app_nil_r.
  apply (proj2 (list_eq_ext l
    (map (fun k => verification_slice_prio_tbl_entry_to_addr sg (st.(prioTbl) (Z.of_nat k)))
      (seq 0 64)) 0)).
  split.
  - rewrite Hlen, Zlength_correct, map_length, seq_length.
    reflexivity.
  - intros i Hi.
    assert (Hi64 : 0 <= i < OS_PRIO_TBL_SIZE).
    { rewrite <- Hlen. exact Hi. }
    unfold OS_PRIO_TBL_SIZE in Hi64.
    assert (Hin : (Z.to_nat i < 64)%nat).
    {
      change (Z.to_nat i < Z.to_nat 64)%nat.
      apply Z2Nat.inj_lt; lia.
    }
    specialize (Hnth i Hi64).
    rewrite Hnth.
    unfold Znth.
    rewrite map_nth_len with (dy := 0%nat).
    2: rewrite seq_length; exact Hin.
    rewrite seq_nth.
    2: exact Hin.
    simpl.
    rewrite Z2Nat.id by lia.
    reflexivity.
Qed.
Lemma mutex_create_head_open_rebuild__entry_and_critical_restore :
  forall sg s l head p,
    prio_tbl_list_rel sg s.(TskState) l ->
    event_free_list_head_prop sg s.(EventState) head ->
    os_event_free_list_addr sg p ->
    mutex_create_head_open_inv sg s **
    verification_slice_store_priotbl_list sg l **
    p # Ptr |-> head |--
    UCOS2_verification_slice_inv sg s.
Proof.
  intros sg s l head p Hprio Hhead Haddr.
  pose proof (prio_tbl_list_rel_eq__entry_and_critical_restore
    sg s.(TskState) l Hprio) as Hl.
  unfold event_free_list_head_prop in Hhead.
  unfold os_event_free_list_addr in Haddr.
  subst l head p.
  unfold mutex_create_head_open_inv, UCOS2_verification_slice_inv.
  unfold verification_slice_task_inv_no_priotbl, verification_slice_task_inv, verification_slice_store_prio_tbl.
  unfold verification_slice_event_inv_no_free_head, verification_slice_event_inv, store_free_event_list.
  entailer!.
Qed.
Lemma replace_Znth_reserved_rollback__priority_table_localization :
  forall (A : Type) (l : list A) (i : Z) (old reserved d : A),
    Znth i l d = old ->
    replace_Znth i old (replace_Znth i reserved l) = l.
Proof.
  intros A l i old reserved d Hlookup.
  unfold Znth, replace_Znth in *.
  remember (Z.to_nat i) as n eqn:Hn.
  clear i Hn.
  revert n old Hlookup.
  induction l as [| x xs IH]; intros [| n] old Hlookup; simpl in *.
  - reflexivity.
  - reflexivity.
  - subst old. reflexivity.
  - f_equal. apply IH. exact Hlookup.
Qed.
Lemma mutex_create_task_valid_after__event_detach_initialize_publish :
  forall sg pcp before prio_before,
    valid_stable_glob_vars sg ->
    stable_glob_vars.valid_mutex_pcp sg pcp ->
    prio_tbl_list_rel sg before prio_before ->
    mutex_create_pcp_slot_available_prop sg pcp prio_before ->
    task.verification_slice_task_validity sg before ->
    task.verification_slice_task_validity sg (mutex_create_task_after sg pcp before).
Proof.
  intros sg pcp before prio_before Hstable Hpcp Hprio_rel Havailable
    Hvalid.
  unfold task.verification_slice_task_validity in *.
  destruct Hvalid as [Hrange Hused].
  unfold task.verification_slice_task_in_range in Hrange.
  destruct Hrange as
    [Hids [Hnodup [Hfreeids [Hfree [Hprio [Hregistered Hunique]]]]]].
  assert (Hregistered_after :
    task_current_prio_registered
      (mutex_create_task_after sg pcp before)).
  {
    pose proof Hpcp as Hpcp_case.
    destruct Hpcp_case as [Hdisabled | Hpcp_range].
    - subst pcp.
      unfold task_current_prio_registered in *.
      intros tid t Hlookup.
      unfold mutex_create_task_after in Hlookup |- *.
      simpl in Hlookup |- *.
      rewrite Z.eqb_refl.
      exact (Hregistered tid t Hlookup).
    - pose proof Hstable as Hstable_shape.
      unfold valid_stable_glob_vars in Hstable_shape.
      destruct Hstable_shape as
        [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]].
      assert (Hpcp_ne :
        pcp <> stable_glob_vars.osPrioMutexCeilDis sg) by lia.
      assert (Hpcp_bound : 0 <= pcp < OS_PRIO_TBL_SIZE).
      { unfold OS_PRIO_TBL_SIZE. lia. }
      unfold mutex_create_pcp_slot_available_prop in Havailable.
      destruct Havailable as [Havailable_disabled | [_ Hzero]].
      { contradiction. }
      unfold prio_tbl_list_rel in Hprio_rel.
      destruct Hprio_rel as [_ Hprio_nth].
      specialize (Hprio_nth pcp Hpcp_bound).
      assert (Hencoded_zero :
        verification_slice_prio_tbl_entry_to_addr sg (before.(prioTbl) pcp) = 0).
      { rewrite <- Hprio_nth. exact Hzero. }
      assert (Hslot_free : before.(prioTbl) pcp = PTFree).
      {
        eapply verification_slice_prio_tbl_entry_to_addr_zero_is_free.
        - exact Hstable.
        - unfold task.verification_slice_task_in_range, task.verification_slice_task_in_range.
          exact
            (conj Hids
              (conj Hnodup
                (conj Hfreeids
                  (conj Hfree
                    (conj Hprio (conj Hregistered Hunique)))))).
        - exact Hencoded_zero.
      }
      pose proof
        (task_current_prio_registered_free_slot_is_unused
          before pcp Hregistered Hslot_free) as Hno_live.
      unfold task_current_prio_registered in *.
      intros tid t Hlookup.
      unfold mutex_create_task_after in Hlookup |- *.
      simpl in Hlookup |- *.
      assert (Hpcp_eqb :
        Z.eqb pcp (stable_glob_vars.osPrioMutexCeilDis sg) = false).
      { apply Z.eqb_neq. exact Hpcp_ne. }
      rewrite Hpcp_eqb.
      destruct (Z.eqb t.(curPrio) pcp) eqn:Hcur_prio.
      + apply Z.eqb_eq in Hcur_prio.
        exfalso.
        exact (Hno_live tid t Hlookup Hcur_prio).
      + exact (Hregistered tid t Hlookup).
  }
  unfold mutex_create_task_after.
  simpl.
  split.
  - unfold task.verification_slice_task_in_range, task.verification_slice_task_in_range.
    refine (conj _
      (conj Hnodup
        (conj Hfreeids
          (conj Hfree
            (conj _ (conj Hregistered_after Hunique)))))).
    + intros tid t Hget.
      simpl in Hget.
      eapply Hids; eauto.
    + intros p tid Hptask.
      destruct (Z.eqb pcp (stable_glob_vars.osPrioMutexCeilDis sg)) eqn:Hdisabled.
      * cbn in Hptask.
        eapply Hprio; eauto.
      * destruct (Z.eqb p pcp) eqn:Hp.
        -- cbn in Hptask.
           rewrite Hp in Hptask.
           discriminate.
        -- cbn in Hptask.
           rewrite Hp in Hptask.
           eapply Hprio; eauto.
  - exact Hused.
Qed.

(* The concrete NULL check performed by Create is the representation-level
   source of abstract PCP freshness.  This bridge is kept separate from the
   state transformer so the lifecycle proof below does not assume a branch
   result: it derives [PTFree] from the actual priority-table snapshot. *)
Lemma mutex_create_pcp_slot_available_abstract__event_detach_initialize_publish :
  forall sg pcp before prio_before,
    valid_stable_glob_vars sg ->
    stable_glob_vars.valid_mutex_pcp sg pcp ->
    prio_tbl_list_rel sg before prio_before ->
    mutex_create_pcp_slot_available_prop sg pcp prio_before ->
    task.verification_slice_task_validity sg before ->
    pcp = sg.(stable_glob_vars.osPrioMutexCeilDis) \/
    before.(TaskStateDef.prioTbl) pcp = PTFree.
Proof.
  intros sg pcp before prio_before Hstable Hpcp Hprio_rel Havailable
    Htask.
  unfold mutex_create_pcp_slot_available_prop in Havailable.
  destruct Havailable as [Hdisabled | [Henabled Hzero]].
  - left. exact Hdisabled.
  - right.
    destruct Hpcp as [Hpcp_disabled | Hpcp_range].
    { contradiction. }
    pose proof Hstable as Hstable_shape.
    unfold valid_stable_glob_vars in Hstable_shape.
    destruct Hstable_shape as
      [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled_value _]]]]]]]]].
    assert (Hbound : 0 <= pcp < OS_PRIO_TBL_SIZE).
    { unfold OS_PRIO_TBL_SIZE. rewrite Hlowest in Hpcp_range. lia. }
    unfold prio_tbl_list_rel in Hprio_rel.
    destruct Hprio_rel as [_ Hprio_nth].
    specialize (Hprio_nth pcp Hbound).
    eapply verification_slice_prio_tbl_entry_to_addr_zero_is_free.
    + exact Hstable.
    + exact (proj1 Htask).
    + rewrite <- Hprio_nth. exact Hzero.
Qed.

Lemma mutex_create_task_inv_after__event_detach_initialize_publish :
  forall sg pcp before prio_before,
    valid_stable_glob_vars sg ->
    stable_glob_vars.valid_mutex_pcp sg pcp ->
    prio_tbl_list_rel sg before prio_before ->
    mutex_create_pcp_slot_available_prop sg pcp prio_before ->
    verification_slice_task_inv_no_priotbl sg before **
      verification_slice_store_priotbl_list sg
        (verification_slice_prioTbl_to_addrs sg
          (TaskStateDef.prioTbl (mutex_create_task_after sg pcp before)))
    |-- verification_slice_task_inv sg (mutex_create_task_after sg pcp before).
Proof.
  intros sg pcp before prio_before Hstable Hpcp Hprio_rel Havailable.
  unfold verification_slice_task_inv_no_priotbl, verification_slice_task_inv, verification_slice_store_prio_tbl.
  pureIntros.
  entailer!.
  eapply mutex_create_task_valid_after__event_detach_initialize_publish;
    eauto.
Qed.
Lemma mutex_create_event_valid_after__event_detach_initialize_publish :
  forall sg pcp eid rest before_t before_e,
    stable_glob_vars.valid_event_id sg eid ->
    EventStateDef.unUsedEventStates before_e = eid :: rest ->
    verification_slice_event_in_range sg before_t before_e ->
    verification_slice_event_in_range sg
      (mutex_create_task_after sg pcp before_t)
      (mutex_create_event_after pcp eid rest before_e).
Proof.
  intros sg pcp eid rest before_t before_e Heid Hfree Hvalid.
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in *.
  destruct Hvalid as
    [Hids [Hnodup [Hfreeids [Hnone [Hfields [Hpayload [Hqueue Hwait]]]]]]].
  rewrite Hfree in Hnodup, Hfreeids.
  apply NoDup_cons_iff in Hnodup.
  destruct Hnodup as [Heid_notin Hrest_nodup].
  inversion Hfreeids as [|? ? Heid_range Hrest_range]; subst.
  unfold mutex_create_event_after, mutex_create_task_after.
  simpl.
  refine (conj _
    (conj Hrest_nodup
      (conj Hrest_range
        (conj _
          (conj _
            (conj _ (conj _ _))))))).
  - intros eid0 e Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0.
      inversion Hget; subst e. exact Heid.
    + eapply Hids; eauto.
  - eapply event_slot_partition_preserved_create; eauto.
  - intros eid0 e Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget; subst e.
      unfold mutex_create_fresh_event, event_fields_consistency.
      simpl. repeat split; congruence.
    + eapply Hfields; eauto.
  - intros eid0 e Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget; subst e.
      unfold mutex_create_fresh_event, event_payload_consistency,
        mutex_fields_consistency.
      simpl. auto.
    + eapply Hpayload; eauto.
  - intros eid1 eid2 e1 e2 qid Hget1 Hget2 Hq1 Hq2.
    destruct (Z.eqb eid1 eid) eqn:Heq1.
    + inversion Hget1; subst e1.
      unfold mutex_create_fresh_event, event_queue_id in Hq1.
      discriminate.
    + destruct (Z.eqb eid2 eid) eqn:Heq2.
      * inversion Hget2; subst e2.
        unfold mutex_create_fresh_event, event_queue_id in Hq2.
        discriminate.
      * eapply Hqueue; eauto.
  - intros eid0 e Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0.
      inversion Hget; subst e.
      apply verification_slice_event_wait_entry_consistency_empty_waitList_general.
      reflexivity.
    + eapply event_wait.verification_slice_event_wait_entry_consistency_preserved_by_tskSt_ext.
      * intros tid. reflexivity.
      * eapply Hwait; eauto.
Qed.
Lemma mutex_create_old_event_none__event_detach_initialize_publish :
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
Lemma mutex_create_old_event_lookup_after__event_detach_initialize_publish :
  forall pcp eid rest before mid e,
    EventStateDef.inUsedEventStates before eid = None ->
    EventStateDef.inUsedEventStates before mid = Some e ->
    EventStateDef.inUsedEventStates
      (mutex_create_event_after pcp eid rest before) mid = Some e.
Proof.
  intros pcp eid rest before mid e Hnone Hget.
  unfold mutex_create_event_after. simpl.
  destruct (Z.eqb mid eid) eqn:Heq; auto.
  apply Z.eqb_eq in Heq. subst mid. rewrite Hnone in Hget. discriminate.
Qed.
Lemma mutex_create_priotbl_consistency__event_detach_initialize_publish :
  forall sg pcp eid rest ls0,
    EventStateDef.inUsedEventStates ls0.(EventState) eid = None ->
    priotbl_consistency sg ls0 ->
    priotbl_consistency sg
      (mutex_create_state_after sg pcp eid rest ls0).
Proof.
  intros sg pcp eid rest ls0 Hnone Hpt p.
  unfold priotbl_consistency in Hpt.
  unfold mutex_create_state_after, mutex_create_task_after,
    mutex_create_event_after. simpl.
  destruct (Z.eqb pcp (stable_glob_vars.osPrioMutexCeilDis sg))
    eqn:Hdisabled.
  - specialize (Hpt p).
    destruct (TaskStateDef.prioTbl (TskState ls0) p) eqn:Hold;
      simpl in Hpt |- *.
    + destruct Hpt as [Hnoready Hnomutex].
      split; [exact Hnoready|].
      intros [mid [e [m [Hget [Htype [Hfields Hreserve]]]]]].
      destruct (Z.eqb mid eid) eqn:Hmid.
      * inversion Hget; subst e.
        unfold mutex_create_fresh_event in Htype, Hfields, Hreserve.
        simpl in Htype, Hfields, Hreserve.
        inversion Hfields; subst m.
        destruct Hreserve as [Henabled _].
        unfold mutex.mutex_pcp_enabled in Henabled. simpl in Henabled.
        apply Henabled. apply Z.eqb_eq. exact Hdisabled.
      * apply Hnomutex.
        exists mid, e, m. split; [exact Hget|].
        split; [exact Htype|]. split; [exact Hfields|]. exact Hreserve.
    + destruct Hpt as [mid [e [m [Hget [Htype [Hfields [Hpcp Howner]]]]]]].
      exists mid, e, m. repeat split; auto.
      eapply (mutex_create_old_event_lookup_after__event_detach_initialize_publish
        pcp eid rest);
        eauto.
    + destruct Hpt as [t [Htask [Hprio | Hmutex]]].
      * exists t. split; auto.
      * destruct Hmutex as
          [mid [e [m [Hget [Htype [Hfields [Howner Hsource]]]]]]].
        exists t. split; auto. right.
        exists mid, e, m. repeat split; auto.
        eapply (mutex_create_old_event_lookup_after__event_detach_initialize_publish
          pcp eid rest);
          eauto.
  - destruct (Z.eqb p pcp) eqn:Hsame.
    + apply Z.eqb_eq in Hsame. subst p.
      exists eid, (mutex_create_fresh_event pcp),
        {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None |}.
      unfold mutex_create_fresh_event. simpl.
      rewrite Z.eqb_refl.
      repeat split; auto.
    + specialize (Hpt p).
      destruct (TaskStateDef.prioTbl (TskState ls0) p) eqn:Hold;
        simpl in Hpt |- *.
      * destruct Hpt as [Hnoready Hnomutex].
        split; [exact Hnoready|].
        intros [mid [e [m [Hget [Htype [Hfields Hreserve]]]]]].
        destruct (Z.eqb mid eid) eqn:Hmid.
        -- inversion Hget; subst e.
           unfold mutex_create_fresh_event in Htype, Hfields, Hreserve.
           simpl in Htype, Hfields, Hreserve.
           inversion Hfields; subst m.
           destruct Hreserve as [_ Hpcp].
           apply Z.eqb_neq in Hsame. apply Hsame. symmetry. exact Hpcp.
        -- apply Hnomutex.
           exists mid, e, m. split; [exact Hget|].
           split; [exact Htype|]. split; [exact Hfields|]. exact Hreserve.
      * destruct Hpt as
          [mid [e [m [Hget [Htype [Hfields [Hpcp Howner]]]]]]].
        exists mid, e, m. repeat split; auto.
        eapply (mutex_create_old_event_lookup_after__event_detach_initialize_publish
          pcp eid rest);
          eauto.
      * destruct Hpt as [t [Htask [Hprio | Hmutex]]].
        -- exists t. split; auto.
        -- destruct Hmutex as
             [mid [e [m [Hget [Htype [Hfields [Howner Hsource]]]]]]].
           exists t. split; auto. right.
           exists mid, e, m. repeat split; auto.
           eapply (mutex_create_old_event_lookup_after__event_detach_initialize_publish
             pcp eid rest);
             eauto.
Qed.
Lemma mutex_create_owner_consistency__event_detach_initialize_publish :
  forall sg pcp eid rest ls0,
    mutex_owner_consistency sg ls0 ->
    mutex_owner_consistency sg
      (mutex_create_state_after sg pcp eid rest ls0).
Proof.
  intros sg pcp eid rest ls0 Howner mid e m
    [Hget [Htype Hfields]].
  unfold mutex_create_state_after, mutex_create_event_after,
    mutex_create_task_after in *. simpl in *.
  destruct (Z.eqb mid eid) eqn:Hmid.
  - inversion Hget; subst e.
    unfold mutex_create_fresh_event in Htype, Hfields.
    simpl in Htype, Hfields.
    inversion Hfields; subst m. simpl. auto.
  - specialize (Howner mid e m).
    apply Howner. repeat split; assumption.
Qed.
Lemma mutex_create_waitlist_consistency__event_detach_initialize_publish :
  forall sg pcp eid rest ls0,
    task_event_id_unreferenced_prop ls0 eid ->
    verification_slice_event_wait_object_consistency sg ls0 ->
    verification_slice_event_wait_object_consistency sg
      (mutex_create_state_after sg pcp eid rest ls0).
Proof.
  intros sg pcp eid rest ls0 Hunref Hwait.
  unfold verification_slice_event_wait_object_consistency in *.
  destruct Hwait as [Hforward [Hrefback Hclosed]].
  split; [| split].
  - intros eid0 e Hget.
    unfold mutex_create_state_after, mutex_create_event_after,
      mutex_create_task_after in Hget |- *. simpl in *.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + inversion Hget; subst e.
      apply verification_slice_event_wait_entry_consistency_empty_waitList_general.
      reflexivity.
    + eapply event_wait.verification_slice_event_wait_entry_consistency_preserved_by_tskSt_ext.
      * intros tid. reflexivity.
      * eapply Hforward; eauto.
  - unfold event_wait.task_event_reference_backlink_consistency in *.
    intros tid t eid0 e Htask Hget Href.
    unfold mutex_create_state_after, mutex_create_event_after,
      mutex_create_task_after in Htask, Hget. simpl in Htask, Hget.
    destruct (Z.eqb eid0 eid) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst eid0.
      specialize (Hunref tid t Htask).
      destruct Hunref as [Hsingle Hmulti].
      destruct Href as [Hsingle_ref | Hmulti_ref]; contradiction.
    + eapply Hrefback; eauto.
  - eapply
      (event_wait.task_event_reference_closure_preserved_by_event_extension
        (mutex_create_state_after sg pcp eid rest ls0).(TskState)
        ls0.(EventState)
        (mutex_create_state_after sg pcp eid rest ls0).(EventState)).
    + intros eid0 [e Hget].
      unfold mutex_create_state_after, mutex_create_event_after,
        mutex_create_task_after. simpl.
      destruct (Z.eqb eid0 eid); [|eexists; exact Hget]. eexists. reflexivity.
    + eapply event_wait.task_event_reference_closure_preserved_by_tskSt_ext.
      * intros tid. reflexivity.
      * exact Hclosed.
Qed.
Lemma mutex_create_ceiling_free__event_detach_initialize_publish :
  forall sg pcp eid rest ls0,
    ceiling_priotbl_free sg ls0 ->
    ceiling_priotbl_free sg
      (mutex_create_state_after sg pcp eid rest ls0).
Proof.
  intros sg pcp eid rest ls0 Hfree.
  unfold ceiling_priotbl_free, mutex_create_state_after,
    mutex_create_task_after in *. simpl in *.
  destruct (Z.eqb pcp (stable_glob_vars.osPrioMutexCeilDis sg))
    eqn:Hdisabled; auto.
  destruct (Z.eqb (stable_glob_vars.osPrioMutexCeilDis sg) pcp)
    eqn:Hreverse; auto.
  apply Z.eqb_eq in Hreverse.
  apply Z.eqb_neq in Hdisabled. exfalso.
  apply Hdisabled. symmetry. exact Hreverse.
Qed.
Lemma mutex_create_cross_consistency__event_detach_initialize_publish :
  forall sg pcp eid rest ls0,
    stable_glob_vars.valid_mutex_pcp sg pcp ->
    (pcp = sg.(stable_glob_vars.osPrioMutexCeilDis) \/
     ls0.(TskState).(TaskStateDef.prioTbl) pcp = PTFree) ->
    EventStateDef.unUsedEventStates ls0.(EventState) = eid :: rest ->
    verification_slice_event_in_range sg ls0.(TskState) ls0.(EventState) ->
    task_event_id_unreferenced_prop ls0 eid ->
    verification_slice_cross_module_consistency sg ls0 ->
    verification_slice_cross_module_consistency sg
      (mutex_create_state_after sg pcp eid rest ls0).
Proof.
  intros sg pcp eid rest ls0 Hpcp Hslot_available Hfree Hevent Hunref
    Hcross.
  pose proof
    (mutex_create_old_event_none__event_detach_initialize_publish
      sg ls0.(TskState) ls0.(EventState) eid rest Hfree Hevent) as Hnone.
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
  - unfold osprio_cur_consistency, mutex_create_state_after,
      mutex_create_task_after in *. simpl in *. exact Hos.
  - eapply mutex_create_priotbl_consistency__event_detach_initialize_publish;
      eauto.
  - eapply mutex_create_owner_consistency__event_detach_initialize_publish;
      eauto.
  - eapply mutex_create_waitlist_consistency__event_detach_initialize_publish;
      eauto.
  - unfold ready_list_completeness, mutex_create_state_after,
      mutex_create_task_after in *. simpl in *. exact Hready.
  - unfold ready_list_order, mutex_create_state_after,
      mutex_create_task_after in *. simpl in *. exact Horder.
  - eapply mutex_create_ceiling_free__event_detach_initialize_publish;
      eauto.
  - unfold task_priority_unique_prop, mutex_create_state_after,
      mutex_create_task_after in *. simpl in *. exact Hunique.
  - intros mid e m Hget Htype Hfields.
    unfold mutex_create_state_after, mutex_create_event_after,
      mutex_create_task_after in Hget |- *. simpl in Hget |- *.
    destruct (Z.eqb mid eid) eqn:Hmid.
    + inversion Hget; subst e.
      unfold mutex_create_fresh_event in Htype, Hfields.
      simpl in Htype, Hfields.
      inversion Hfields; subst m. simpl.
      refine (conj Hpcp (conj I _)).
      destruct (Z.eqb pcp (stable_glob_vars.osPrioMutexCeilDis sg))
        eqn:Hdisabled.
      * left. apply Z.eqb_eq. exact Hdisabled.
      * right. split.
        -- apply Z.eqb_neq. exact Hdisabled.
        -- left. rewrite Z.eqb_refl. reflexivity.
    + pose proof (Hprotocol mid e m Hget Htype Hfields) as
        [Hmvalid [Hmowner Hmslot]].
      refine (conj Hmvalid (conj Hmowner _)).
      destruct (Z.eqb pcp (stable_glob_vars.osPrioMutexCeilDis sg))
        eqn:Hdisabled.
      * exact Hmslot.
      * destruct (Z.eqb (mfPCP m) pcp) eqn:Hsame.
        -- right. split.
           ++ apply Z.eqb_eq in Hsame. subst pcp.
              apply Z.eqb_neq. exact Hdisabled.
           ++ left. reflexivity.
        -- destruct Hmslot as [Hm_disabled | [Hm_enabled Hmoccupied]].
           ++ left. exact Hm_disabled.
           ++ right. split; [exact Hm_enabled|].
              destruct Hmoccupied as [Hmreserved | [owner [Hmowner_eq Hmtask]]].
              ** left. exact Hmreserved.
              ** right. exists owner. split; [exact Hmowner_eq|].
                 exact Hmtask.
  - unfold mutex_enabled_pcp_unique in Hpcp_unique |- *.
    intros mid1 e1 m1 mid2 e2 m2
      Hget1 Htype1 Hfields1 Hget2 Htype2 Hfields2 Hsame Henabled.
    unfold mutex_create_state_after, mutex_create_event_after in Hget1, Hget2.
    simpl in Hget1, Hget2.
    destruct (Z.eqb mid1 eid) eqn:Hmid1;
      destruct (Z.eqb mid2 eid) eqn:Hmid2.
    + apply Z.eqb_eq in Hmid1, Hmid2. congruence.
    + apply Z.eqb_eq in Hmid1. subst mid1.
      inversion Hget1; subst e1.
      unfold mutex_create_fresh_event in Htype1, Hfields1.
      simpl in Htype1, Hfields1.
      inversion Hfields1; subst m1. simpl in Hsame, Henabled.
      destruct Hslot_available as [Hdisabled | Hfree_slot].
      { contradiction. }
      specialize (Hpt pcp). rewrite Hfree_slot in Hpt.
      destruct Hpt as [_ Hno_mutex].
      exfalso. apply Hno_mutex.
      exists mid2, e2, m2.
      split; [exact Hget2|].
      split; [exact Htype2|].
      split; [exact Hfields2|].
      unfold mutex.mutex_reserves_priority_slot, mutex.mutex_pcp_enabled.
      split.
      * intro Hdisabled. apply Henabled. rewrite Hsame. exact Hdisabled.
      * symmetry. exact Hsame.
    + apply Z.eqb_eq in Hmid2. subst mid2.
      inversion Hget2; subst e2.
      unfold mutex_create_fresh_event in Htype2, Hfields2.
      simpl in Htype2, Hfields2.
      inversion Hfields2; subst m2. simpl in Hsame.
      destruct Hslot_available as [Hdisabled | Hfree_slot].
      { exfalso. apply Henabled. rewrite Hsame. exact Hdisabled. }
      specialize (Hpt pcp). rewrite Hfree_slot in Hpt.
      destruct Hpt as [_ Hno_mutex].
      exfalso. apply Hno_mutex.
      exists mid1, e1, m1.
      split; [exact Hget1|].
      split; [exact Htype1|].
      split; [exact Hfields1|].
      unfold mutex.mutex_reserves_priority_slot, mutex.mutex_pcp_enabled.
      split.
      * exact Henabled.
      * exact Hsame.
    + eapply Hpcp_unique; eauto.
Qed.
Lemma zlist_eq_by_Znth__event_detach_initialize_publish :
  forall l1 l2 : list Z,
    Zlength l1 = Zlength l2 ->
    (forall i, 0 <= i < Zlength l1 -> Znth i l1 0 = Znth i l2 0) ->
    l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] Hlen Hnth.
  - reflexivity.
  - pose proof (Zlength_nonneg l2).
    rewrite Zlength_nil, Zlength_cons in Hlen. lia.
  - pose proof (Zlength_nonneg l1).
    rewrite Zlength_cons, Zlength_nil in Hlen. lia.
  - pose proof (Zlength_nonneg l1) as Hnonneg.
    f_equal.
    + specialize (Hnth 0).
      rewrite !Znth0_cons in Hnth.
      apply Hnth. rewrite Zlength_cons. lia.
    + apply IH.
      * rewrite !Zlength_cons in Hlen. lia.
      * intros i Hi.
        specialize (Hnth (i + 1)).
        rewrite !Znth_cons in Hnth by lia.
        replace (i + 1 - 1) with i in Hnth by lia.
        apply Hnth. rewrite Zlength_cons. lia.
Qed.
Lemma verification_slice_prioTbl_to_addrs_rec_seq__event_detach_initialize_publish :
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
Lemma verification_slice_prioTbl_to_addrs_rel__event_detach_initialize_publish :
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
    rewrite verification_slice_prioTbl_to_addrs_rec_seq__event_detach_initialize_publish.
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
Lemma prio_tbl_list_rel_unique__event_detach_initialize_publish :
  forall sg st l,
    prio_tbl_list_rel sg st l ->
    l = verification_slice_prioTbl_to_addrs sg st.(TaskStateDef.prioTbl).
Proof.
  intros sg st l Hrel.
  pose proof
    (verification_slice_prioTbl_to_addrs_rel__event_detach_initialize_publish sg st) as Hcanon.
  unfold prio_tbl_list_rel in Hrel, Hcanon.
  destruct Hrel as [Hlen Hnth].
  destruct Hcanon as [Hcanon_len Hcanon_nth].
  assert (Hlength :
    Zlength l =
    Zlength (verification_slice_prioTbl_to_addrs sg (TaskStateDef.prioTbl st))).
  { rewrite Hlen, Hcanon_len. reflexivity. }
  refine (zlist_eq_by_Znth__event_detach_initialize_publish
    l (verification_slice_prioTbl_to_addrs sg (TaskStateDef.prioTbl st)) Hlength _).
  intros i Hi.
  assert (Hidx : 0 <= i < OS_PRIO_TBL_SIZE).
  { first [rewrite <- Hlen | rewrite <- Hcanon_len]; exact Hi. }
  rewrite Hnth by exact Hidx.
  rewrite Hcanon_nth by exact Hidx.
  reflexivity.
Qed.
Lemma mutex_create_priotbl_list_rel_after__event_detach_initialize_publish :
  forall sg pcp before l,
    valid_stable_glob_vars sg ->
    stable_glob_vars.valid_mutex_pcp sg pcp ->
    prio_tbl_list_rel sg before l ->
    prio_tbl_list_rel sg (mutex_create_task_after sg pcp before)
      (mutex_create_priotbl_after sg pcp l).
Proof.
  intros sg pcp before l Hstable Hpcp Hrel.
  destruct Hpcp as [Hdisabled | Hrange].
  - subst pcp.
    unfold mutex_create_task_after, mutex_create_priotbl_after.
    rewrite Z.eqb_refl. simpl. exact Hrel.
  - unfold valid_stable_glob_vars in Hstable.
    destruct Hstable as
      [_ [_ [_ [_ [_ [Hlowest [_ [_ [Hdisabled _]]]]]]]]].
    assert (Hpcp_ne : pcp <> stable_glob_vars.osPrioMutexCeilDis sg) by lia.
    assert (Hpcp_eqb :
      Z.eqb pcp (stable_glob_vars.osPrioMutexCeilDis sg) = false) by
      (apply Z.eqb_neq; exact Hpcp_ne).
    unfold prio_tbl_list_rel in Hrel |- *.
    destruct Hrel as [Hlen Hnth].
    unfold mutex_create_task_after, mutex_create_priotbl_after.
    simpl. rewrite Hpcp_eqb.
    split.
    + rewrite Zlength_replace_Znth. exact Hlen.
    + intros p Hp.
      destruct (Z.eq_dec p pcp) as [Heq | Hneq].
      * subst p.
        rewrite Znth_replace_Znth_eq_gen by (rewrite Hlen; lia).
        rewrite Z.eqb_refl. reflexivity.
      * assert (Hp_bound : 0 <= p < Zlength l) by
          (rewrite Hlen; exact Hp).
        assert (Hpcp_bound : 0 <= pcp < Zlength l) by
          (rewrite Hlen; unfold OS_PRIO_TBL_SIZE; lia).
        rewrite Znth_replace_Znth_neq_gen by
          (first [exact Hneq | exact Hp_bound | exact Hpcp_bound]).
        rewrite Hnth by exact Hp.
        apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity.
Qed.
Lemma encode_event_wait_grp_task_ext__event_detach_initialize_publish :
  forall wl t1 t2,
    TaskStateDef.inUsedTaskStates t1 = TaskStateDef.inUsedTaskStates t2 ->
    encode_event_wait_grp wl t1 = encode_event_wait_grp wl t2.
Proof.
  intros wl. induction wl as [|tid rest IH]; intros t1 t2 Hmap.
  - reflexivity.
  - simpl. rewrite Hmap. rewrite (IH t1 t2 Hmap). reflexivity.
Qed.
Lemma encode_event_wait_tbl_task_ext__event_detach_initialize_publish :
  forall wl t1 t2 y,
    TaskStateDef.inUsedTaskStates t1 = TaskStateDef.inUsedTaskStates t2 ->
    encode_event_wait_tbl_at wl t1 y = encode_event_wait_tbl_at wl t2 y.
Proof.
  intros wl t1 t2 y Hmap.
  unfold encode_event_wait_tbl_at.
  generalize 0 as acc.
  induction wl as [|tid rest IH]; intro acc.
  - reflexivity.
  - simpl. rewrite Hmap. reflexivity.
Qed.
Lemma used_complete_event_task_ext__event_detach_initialize_publish :
  forall sg t1 t2 base eid e,
    TaskStateDef.inUsedTaskStates t1 = TaskStateDef.inUsedTaskStates t2 ->
    used_complete_event sg t1 base eid e =
    used_complete_event sg t2 base eid e.
Proof.
  intros sg t1 t2 base eid e Hmap.
  unfold used_complete_event.
  rewrite (encode_event_wait_grp_task_ext__event_detach_initialize_publish
    _ _ _ Hmap).
  repeat rewrite
    (encode_event_wait_tbl_task_ext__event_detach_initialize_publish
      _ _ _ _ Hmap).
  reflexivity.
Qed.
Lemma mutex_create_used_event_map_after__event_detach_initialize_publish :
  forall sg pcp eid rest before_t before_e,
    EventStateDef.inUsedEventStates before_e eid = None ->
    store_used_event_map sg before_t
        (EventStateDef.inUsedEventStates before_e) **
      used_complete_event sg (mutex_create_task_after sg pcp before_t)
        (event_addr sg eid) eid (mutex_create_fresh_event pcp)
    |--
    store_used_event_map sg (mutex_create_task_after sg pcp before_t)
      (EventStateDef.inUsedEventStates
        (mutex_create_event_after pcp eid rest before_e)).
Proof.
  intros sg pcp eid rest before_t before_e Hnone.
  unfold store_used_event_map, mutex_create_event_after.
  simpl.
  assert (HP :
    (fun eid0 e =>
      used_complete_event sg before_t (event_addr sg eid0) eid0 e) =
    (fun eid0 e =>
      used_complete_event sg (mutex_create_task_after sg pcp before_t)
        (event_addr sg eid0) eid0 e)).
  { apply functional_extensionality. intro eid0.
    apply functional_extensionality. intro e.
    apply used_complete_event_task_ext__event_detach_initialize_publish.
    reflexivity. }
  rewrite HP.
  sep_apply_l_atomic
    (store_map_equiv_store_map_missing
      (fun eid0 e =>
        used_complete_event sg (mutex_create_task_after sg pcp before_t)
          (event_addr sg eid0) eid0 e)
      (EventStateDef.inUsedEventStates before_e) eid Hnone).
  assert (Hother : forall eid0, eid0 <> eid ->
    EventStateDef.inUsedEventStates before_e eid0 =
      (if Z.eqb eid0 eid
       then Some (mutex_create_fresh_event pcp)
       else EventStateDef.inUsedEventStates before_e eid0)).
  { intros eid0 Hneq.
    apply Z.eqb_neq in Hneq. rewrite Hneq. reflexivity. }
  pose proof
    (proj1 (store_map_missing_i_equiv
      (fun eid0 e =>
        used_complete_event sg (mutex_create_task_after sg pcp before_t)
          (event_addr sg eid0) eid0 e)
      (EventStateDef.inUsedEventStates before_e)
      (fun eid0 =>
        if Z.eqb eid0 eid
        then Some (mutex_create_fresh_event pcp)
        else EventStateDef.inUsedEventStates before_e eid0)
      eid Hother)) as Hmissing.
  sep_apply_l_atomic Hmissing.
  apply (store_map_merge
    (fun eid0 e =>
      used_complete_event sg (mutex_create_task_after sg pcp before_t)
        (event_addr sg eid0) eid0 e)
    eid (mutex_create_fresh_event pcp)
    (fun eid0 =>
      if Z.eqb eid0 eid
      then Some (mutex_create_fresh_event pcp)
      else EventStateDef.inUsedEventStates before_e eid0)).
  rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma mutex_create_full_inv_after__event_detach_initialize_publish :
  forall sg pcp eid rest before prio_before,
    valid_stable_glob_vars sg ->
    stable_glob_vars.valid_mutex_pcp sg pcp ->
    stable_glob_vars.valid_event_id sg eid ->
    prio_tbl_list_rel sg before.(TskState) prio_before ->
    mutex_create_pcp_slot_available_prop sg pcp prio_before ->
    EventStateDef.unUsedEventStates before.(EventState) = eid :: rest ->
    task_event_id_unreferenced_prop before eid ->
    mutex_create_node_open_inv sg before rest **
      verification_slice_store_priotbl_list sg
        (verification_slice_prioTbl_to_addrs sg
          (TaskStateDef.prioTbl
            (mutex_create_task_after sg pcp before.(TskState)))) **
      sg.(stable_glob_vars.g_OSEventFreeList) # Ptr |->
        free_event_head sg rest **
      mutex_create_initialized_event sg
        (mutex_create_state_after sg pcp eid rest before) pcp eid
    |-- UCOS2_verification_slice_inv sg
      (mutex_create_state_after sg pcp eid rest before).
Proof.
  intros sg pcp eid rest before prio_before Hstable Hpcp Heid Hprio_rel
    Havailable Hfree Hunref.
  unfold mutex_create_node_open_inv, verification_slice_event_inv_free_head_rest.
  sep_apply_l_atomic
    (verification_slice_task_inv_no_priotbl_expose_valid sg before.(TskState)).
  pureIntros.
  match goal with
  | Htask : task.verification_slice_task_validity sg before.(TskState),
    Hevent : verification_slice_event_in_range sg before.(TskState) before.(EventState),
    Hcross : verification_slice_cross_module_consistency sg before |- _ =>
      pose proof
        (mutex_create_pcp_slot_available_abstract__event_detach_initialize_publish
          sg pcp before.(TskState) prio_before Hstable Hpcp Hprio_rel
          Havailable Htask) as Hslot_available;
      pose proof
        (mutex_create_old_event_none__event_detach_initialize_publish
          sg before.(TskState) before.(EventState) eid rest
          Hfree Hevent) as Hnone;
      pose proof
        (mutex_create_event_valid_after__event_detach_initialize_publish
          sg pcp eid rest before.(TskState) before.(EventState)
          Heid Hfree Hevent) as Hevent_after;
      pose proof
        (mutex_create_cross_consistency__event_detach_initialize_publish
          sg pcp eid rest before Hpcp Hslot_available Hfree Hevent Hunref
          Hcross) as
        Hcross_after
  end.
  sep_apply_l_atomic
    (mutex_create_task_inv_after__event_detach_initialize_publish
      sg pcp before.(TskState) prio_before Hstable Hpcp Hprio_rel
      Havailable).
  unfold UCOS2_verification_slice_inv, verification_slice_event_inv, store_free_event_list,
    mutex_create_initialized_event, mutex_create_state_after.
  simpl.
  sep_apply_l_atomic
    (mutex_create_used_event_map_after__event_detach_initialize_publish
      sg pcp eid rest before.(TskState) before.(EventState) Hnone).
  assert (Hsched :
    verification_slice_sched_inv sg before.(TskState) before.(SchedState) =
    verification_slice_sched_inv sg (mutex_create_task_after sg pcp before.(TskState))
      before.(SchedState)).
  { apply verification_slice_sched_inv_ext. reflexivity. }
  rewrite <- Hsched.
  entailer!.
Qed.

Lemma atomic_mutex_create_enabled_slot_free__critical_state_threading :
  forall sg pcp lvs1 oid lvs2,
    pcp <> sg.(osPrioMutexCeilDis) ->
    atomic_mutex_create sg pcp lvs1 oid lvs2 ->
    lvs1.(TskState).(prioTbl) pcp = PTFree.
Proof.
  intros sg pcp lvs1 oid lvs2 Hpcp Hcreate.
  destruct Hcreate as [eid [rest [_ [Hslot _]]]].
  destruct Hslot as [Hdisabled|Hfree]; [contradiction|exact Hfree].
Qed.

(** Current complete-invariant interfaces.  The older slice declarations
    above remain reference-compatible but are not full-invariant bridges. *)
Module MutexCreateFull.

Definition head_residual (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  task_public_storage_without_prio_tbl sg s.(TskState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) **
  store_map (used_event_rep sg s.(TskState)) s.(EventState).(inUsedEventStates) **
  event_free_storage_rep sg s.(EventState) **
  UCOS2_raw_rep_missing_two sg s TaskModule EventModule.

Lemma head_split_merge : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (store_prio_tbl sg s.(TskState).(prioTbl) **
     event_free_root_rep sg s.(EventState) ** head_residual sg s).
Proof.
  intros sg s.
  rewrite (UCOS2_inv_split_two sg s TaskModule EventModule ltac:(discriminate)).
  unfold head_residual; cbn [UCOS2_module_rep].
  unfold task_shared_rep, event_raw_rep.
  rewrite task_public_storage_prio_tbl_equiv.
  split; entailer!.
Qed.

Lemma detached_allocation_lookup : forall events eid rest image,
  (event_detach_head events eid rest image).(eventLifecycle).(eventPrivate) eid =
    Some {| eventPrivateInvocation := events.(eventLifecycle).(eventNextInvocation);
            eventPrivateGeneration := events.(eventLifecycle).(eventNextGeneration);
            eventPrivateQueue := None; eventPrivateMutexPCP := None; eventPrivateStorage := image |}.
Proof. intros; apply kernel_map_set_same. Qed.

Lemma event_state_preserves_in_range : forall sg tasks before pcp eid rest,
  event_in_range sg tasks before -> before.(unUsedEventStates) = eid :: rest ->
  event_in_range sg tasks (mutex_create_event_state pcp eid rest before).
Proof.
  intros sg tasks before pcp eid rest Hvalid Hhead.
  unfold mutex_create_event_state.
  eapply event_publish_preserves_in_range.
  - eapply event_detach_head_preserves_in_range; eassumption.
  - apply detached_allocation_lookup.
  - reflexivity.
  - unfold event_fields_consistency, mutex_create_node; simpl; intuition discriminate.
  - unfold event_payload_consistency, mutex_create_node, mutex_fields_consistency;
      simpl; intuition.
  - intros other old q Hold Hqueue; discriminate.
  - apply event_wait_entry_consistency_empty; reflexivity.
Qed.

Lemma event_state_removes_free_storage : forall pcp eid rest before,
  (mutex_create_event_state pcp eid rest before).(eventLifecycle).(eventFreeStorage) eid = None.
Proof. intros; apply kernel_map_set_same. Qed.

Lemma event_state_frame_free_storage : forall pcp eid rest before other,
  other <> eid ->
  (mutex_create_event_state pcp eid rest before).(eventLifecycle).(eventFreeStorage) other =
    before.(eventLifecycle).(eventFreeStorage) other.
Proof. intros; apply kernel_map_set_other; assumption. Qed.

Lemma node_padding_eq : forall pcp eid before,
  let node := mutex_create_node pcp before.(eventLifecycle).(eventNextGeneration)
    (mutex_create_storage before eid) in
  node.(eventPadding1) = mutex_create_storage before eid EventPadding1 /\
  node.(eventPadding2) = mutex_create_storage before eid EventPadding2 /\
  node.(eventPadding3) = mutex_create_storage before eid EventPadding3 /\
  node.(eventPadding19) = mutex_create_storage before eid EventPadding19.
Proof. intros; repeat split; reflexivity. Qed.

Lemma priority_state_disabled : forall sg before pcp,
  pcp = sg.(osPrioMutexCeilDis) -> mutex_create_priority_state sg pcp before = before.
Proof.
  intros sg before pcp ->; unfold mutex_create_priority_state; rewrite Z.eqb_refl.
  destruct before; reflexivity.
Qed.

Lemma priority_state_preserves_in_range : forall sg before pcp,
  task_in_range sg before ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(prioTbl) pcp = PTFree) ->
  task_in_range sg (mutex_create_priority_state sg pcp before).
Proof.
  intros sg before pcp Hvalid [Hdisabled|Hfree].
  - rewrite priority_state_disabled by exact Hdisabled; exact Hvalid.
  - destruct (Z.eq_dec pcp sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled].
    { rewrite priority_state_disabled by exact Hdisabled; exact Hvalid. }
    destruct Hvalid as [Hpool [Hactive [Hlinks [Hreserve [Hgeneration
      [Hregistered [Hunique [Hpriorities [Hreuse Hregisters]]]]]]]]].
    assert (Hpcp : Z.eqb pcp sg.(osPrioMutexCeilDis) = false)
      by (apply Z.eqb_neq; exact Henabled).
    unfold task_in_range; cbn [mutex_create_priority_state].
    split; [exact Hpool|]. split; [exact Hactive|]. split; [exact Hlinks|].
    split.
    + destruct Hreserve as [Hentries Hinvocations].
      split; [|exact Hinvocations].
      intros p entry Hentry.
      destruct (Hentries p entry Hentry) as [Hp [Htable Hinvocation]].
      split; [exact Hp|]; split; [|exact Hinvocation].
      change ((if pcp =? osPrioMutexCeilDis sg then prioTbl before
        else update_prio_tbl (prioTbl before) pcp PTReserved) p = PTReserved).
      rewrite Hpcp; unfold update_prio_tbl; destruct (Z.eq_dec p pcp); congruence.
    + split; [exact Hgeneration|].
      split.
      * intros tid t Ht.
        change ((if pcp =? osPrioMutexCeilDis sg then prioTbl before
          else update_prio_tbl (prioTbl before) pcp PTReserved) t.(curPrio) = PTTask tid).
        rewrite Hpcp; unfold update_prio_tbl.
        specialize (Hregistered tid t Ht).
        destruct (Z.eq_dec t.(curPrio) pcp); congruence.
      * split; [exact Hunique|]. split; [exact Hpriorities|].
        split; assumption.
Qed.

Lemma event_state_priority_index_in_range : forall sg tasks events pcp eid rest,
  event_in_range sg tasks events -> events.(unUsedEventStates) = eid :: rest ->
  event_in_range sg (mutex_create_priority_state sg pcp tasks)
    (mutex_create_event_state pcp eid rest events).
Proof.
  intros sg tasks events pcp eid rest Hvalid Hhead.
  pose proof (event_state_preserves_in_range sg tasks events pcp eid rest Hvalid Hhead)
    as [Hpool [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hentries]]]]]].
  split; [exact Hpool|]. split; [exact Hfree|]. split; [exact Hidentity|].
  split; [exact Hfields|]. split; [exact Hpayload|]. split; [exact Hqueue|].
  intros slot node Hget.
  eapply event_wait_entry_task_lookup_ext; [intros; reflexivity|exact (Hentries slot node Hget)].
Qed.

Lemma event_state_lookup_other : forall pcp eid rest before other,
  other <> eid ->
  (mutex_create_event_state pcp eid rest before).(inUsedEventStates) other =
    before.(inUsedEventStates) other.
Proof. intros; apply kernel_map_set_other; assumption. Qed.

Lemma event_state_lookup_same : forall pcp eid rest before,
  (mutex_create_event_state pcp eid rest before).(inUsedEventStates) eid =
    Some (mutex_create_node pcp before.(eventLifecycle).(eventNextGeneration)
      (mutex_create_storage before eid)).
Proof. intros; apply kernel_map_set_same. Qed.

Lemma priority_state_alias_iff : forall sg tasks pcp tid p,
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  (task_priority_alias sg (mutex_create_priority_state sg pcp tasks).(prioTbl) tid p <->
   task_priority_alias sg tasks.(prioTbl) tid p).
Proof.
  intros sg tasks pcp tid p [Hdisabled|Hfree].
  - rewrite priority_state_disabled by exact Hdisabled; reflexivity.
  - cbn [mutex_create_priority_state prioTbl].
    destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)); [reflexivity|].
    apply task_priority_alias_foreign_write_iff; [rewrite Hfree|]; discriminate.
Qed.

Lemma event_state_preserves_owner_claim : forall sg before pcp eid rest tid p,
  before.(inUsedEventStates) eid = None ->
  mutex_task_enabled_pcp_claim sg before tid p ->
  mutex_task_enabled_pcp_claim sg (mutex_create_event_state pcp eid rest before) tid p.
Proof.
  intros sg before pcp eid rest tid p Hnone
    [mid [e [m [He [Htype [Hm Hrest]]]]]].
  exists mid, e, m; split; [|exact (conj Htype (conj Hm Hrest))].
  rewrite event_state_lookup_other; [exact He|congruence].
Qed.

Lemma priority_state_preserves_alias_consistency : forall sg tasks events pcp eid rest,
  events.(inUsedEventStates) eid = None ->
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  mutex_priority_alias_consistency sg tasks events ->
  mutex_priority_alias_consistency sg (mutex_create_priority_state sg pcp tasks)
    (mutex_create_event_state pcp eid rest events).
Proof.
  intros sg tasks events pcp eid rest Hnone Hslot Hvalid tid t Ht.
  destruct (Hvalid tid t Ht) as [base [Hbase [Heffective Hclaims]]].
  exists base; split.
  - eapply task_base_priority_alias_ext; [|exact Hbase].
    intros; symmetry; apply priority_state_alias_iff; exact Hslot.
  - split.
    + eapply task_effective_priority_alias_ext; [|exact Heffective].
      intros; symmetry; apply priority_state_alias_iff; exact Hslot.
    + intros p Hp.
      apply priority_state_alias_iff in Hp; [|exact Hslot].
      destruct (Hclaims p Hp) as [->|[Hless Hclaim]]; [left; reflexivity|].
      right; split; [exact Hless|].
      eapply event_state_preserves_owner_claim; eassumption.
Qed.

Lemma fresh_pcp_has_no_old_claim : forall sg tasks events pcp,
  valid_mutex_pcp sg pcp -> tasks.(prioTbl) pcp = PTFree ->
  task_mutex_priotbl_consistency sg tasks events ->
  ~ (exists mid e m, events.(inUsedEventStates) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m pcp).
Proof.
  intros sg tasks events pcp Hpcp Hfree [_ [Hslots _]] Hclaim.
  destruct Hpcp as [Hdisabled|Hrange].
  - destruct Hclaim as [mid [e [m [_ [_ [_ [Henabled Heq]]]]]]].
    unfold mutex_pcp_enabled in Henabled; congruence.
  - specialize (Hslots pcp ltac:(unfold task_priority_in_range; lia)).
    rewrite Hfree in Hslots; exact (Hslots Hclaim).
Qed.

Lemma priority_state_preserves_old_mutex_slot : forall sg tasks events pcp mid e m,
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  task_mutex_priotbl_consistency sg tasks events ->
  events.(inUsedEventStates) mid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m -> mutex_pcp_enabled sg m ->
  (mutex_create_priority_state sg pcp tasks).(prioTbl) m.(mfPCP) = tasks.(prioTbl) m.(mfPCP).
Proof.
  intros sg tasks events pcp mid e m Hpcp [Hdisabled|Hfree] Htable He Htype Hm Henabled.
  - rewrite priority_state_disabled by exact Hdisabled; reflexivity.
  - assert (Hne : m.(mfPCP) <> pcp).
    { intro Heq; apply (fresh_pcp_has_no_old_claim sg tasks events pcp Hpcp Hfree Htable).
      exists mid, e, m; exact (conj He (conj Htype (conj Hm (conj Henabled Heq)))). }
    cbn [mutex_create_priority_state prioTbl].
    destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)); [reflexivity|].
    unfold update_prio_tbl; destruct (Z.eq_dec m.(mfPCP) pcp); congruence.
Qed.

Lemma event_state_preserves_prio_claim : forall sg events pcp eid rest p,
  events.(inUsedEventStates) eid = None ->
  (exists mid e m, events.(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
    mutex_reserves_priority_slot sg m p) ->
  exists mid e m, (mutex_create_event_state pcp eid rest events).(inUsedEventStates) mid = Some e /\
    e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
    mutex_reserves_priority_slot sg m p.
Proof.
  intros sg events pcp eid rest p Hnone [mid [e [m [He Hrest]]]].
  exists mid, e, m; split; [|exact Hrest].
  rewrite event_state_lookup_other; [exact He|congruence].
Qed.

Lemma state_preserves_table_consistency : forall sg tasks events pcp eid rest,
  task_in_range sg tasks -> events.(inUsedEventStates) eid = None ->
  events.(eventLifecycle).(eventPrivate) eid = None ->
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  task_mutex_priotbl_consistency sg tasks events ->
  task_mutex_priotbl_consistency sg (mutex_create_priority_state sg pcp tasks)
    (mutex_create_event_state pcp eid rest events).
Proof.
  intros sg tasks events pcp eid rest Htasks Hnone Hprivate Hslot Htable.
  assert (Hleases : event_mutex_lease_view (mutex_create_event_state pcp eid rest events) =
    event_mutex_lease_view events).
  { apply functional_extensionality; intro other; unfold event_mutex_lease_view,
      mutex_create_event_state, event_publish, event_detach_head; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hprivate|]; reflexivity. }
  destruct Htable as [Hcreator [Hslots Halias]].
  split.
  - intros p entry Hentry [mid [e [m [He [Htype [Hm Hclaim]]]]]].
    destruct (Z.eq_dec mid eid) as [->|Hne].
    + rewrite event_state_lookup_same in He; injection He as He; subst e.
      cbn [mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m.
      destruct Hclaim as [Henabled Hp]; cbn [mfPCP] in Hp; subst p.
      unfold mutex_pcp_enabled in Henabled; cbn [mfPCP] in Henabled.
      destruct Hslot as [Hdisabled|Hfree]; [contradiction|].
      pose proof (proj1 (proj2 (proj2 (proj2 Htasks)))) as Hreservation.
      destruct (proj1 Hreservation pcp entry Hentry) as [_ [Hreserved _]].
      congruence.
    + rewrite event_state_lookup_other in He by exact Hne.
      apply (Hcreator p entry Hentry); exists mid, e, m;
        exact (conj He (conj Htype (conj Hm Hclaim))).
  - split.
    + intros p Hp.
      cbn [mutex_create_priority_state prioTbl].
      destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
      * apply Z.eqb_eq in Hdisabled.
        specialize (Hslots p Hp).
        destruct (tasks.(prioTbl) p).
        -- intros [mid [e [m [He [Htype [Hm Hclaim]]]]]].
           destruct (Z.eq_dec mid eid) as [->|Hne].
           ++ rewrite event_state_lookup_same in He; injection He as He; subst e.
              cbn [mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m.
              destruct Hclaim as [Henabled _]; apply Henabled; exact Hdisabled.
           ++ rewrite event_state_lookup_other in He by exact Hne.
              apply Hslots; exists mid, e, m; exact (conj He (conj Htype (conj Hm Hclaim))).
        -- destruct Hslots as [Hreservation|[Hclaim|Hpending]].
           ++ left; exact Hreservation.
           ++ right; left; eapply event_state_preserves_prio_claim; eassumption.
           ++ right; right; unfold pending_mutex_priority_claim in *; rewrite Hleases; exact Hpending.
        -- exact Hslots.
      * apply Z.eqb_neq in Hdisabled.
        unfold update_prio_tbl; destruct (Z.eq_dec p pcp) as [->|Hnep].
        -- right; left.
           exists eid, (mutex_create_node pcp events.(eventLifecycle).(eventNextGeneration)
             (mutex_create_storage events eid)),
             {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None |}.
           split; [apply event_state_lookup_same|].
           split; [reflexivity|]. split; [reflexivity|]. split; [exact Hdisabled|reflexivity].
        -- specialize (Hslots p Hp).
           destruct (tasks.(prioTbl) p).
           ++ intros [mid [e [m [He [Htype [Hm Hclaim]]]]]].
              destruct (Z.eq_dec mid eid) as [->|Hne].
              ** rewrite event_state_lookup_same in He; injection He as He; subst e.
                 cbn [mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m.
                 destruct Hclaim as [_ Hpcp]; apply Hnep; symmetry; exact Hpcp.
              ** rewrite event_state_lookup_other in He by exact Hne.
                 apply Hslots; exists mid, e, m; exact (conj He (conj Htype (conj Hm Hclaim))).
           ++ destruct Hslots as [Hreservation|[Hclaim|Hpending]].
              ** left; exact Hreservation.
              ** right; left; eapply event_state_preserves_prio_claim; eassumption.
              ** right; right; unfold pending_mutex_priority_claim in *; rewrite Hleases; exact Hpending.
           ++ exact Hslots.
    + eapply priority_state_preserves_alias_consistency; eassumption.
Qed.

Lemma state_preserves_owner_snapshots : forall sg tasks events pcp eid rest,
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  mutex_owner_snapshot_in_range sg tasks events ->
  mutex_owner_snapshot_in_range sg (mutex_create_priority_state sg pcp tasks)
    (mutex_create_event_state pcp eid rest events).
Proof.
  intros sg tasks events pcp eid rest Hslot Hvalid mid e m owner He Htype Hm Howner.
  destruct (Z.eq_dec mid eid) as [->|Hne].
  - rewrite event_state_lookup_same in He; injection He as He; subst e.
    cbn [mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m; discriminate.
  - rewrite event_state_lookup_other in He by exact Hne.
    destruct (Hvalid mid e m owner He Htype Hm Howner) as [t [base [snapshot [Ht [Hbase Hrest]]]]].
    exists t, base, snapshot; split; [exact Ht|]. split; [|exact Hrest].
    eapply task_base_priority_alias_ext; [|exact Hbase].
    intros; symmetry; apply priority_state_alias_iff; exact Hslot.
Qed.

Lemma state_preserves_mutex_protocol : forall sg before pcp eid rest,
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) ->
  task_mutex_priotbl_consistency sg before.(TskState) before.(EventState) ->
  mutex_protocol_consistency sg before ->
  mutex_protocol_consistency sg (mutex_create_state sg pcp eid rest before).
Proof.
  intros sg before pcp eid rest Hpcp Hslot Htable Hvalid mid e m He Htype Hm.
  change ((mutex_create_event_state pcp eid rest before.(EventState)).(inUsedEventStates) mid = Some e) in He.
  destruct (Z.eq_dec mid eid) as [->|Hne].
  - rewrite event_state_lookup_same in He; injection He as He; subst e.
    cbn [mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m.
    split; [exact Hpcp|]. split; [exact I|].
    destruct (Z.eq_dec pcp sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled].
    + left; exact Hdisabled.
    + right; split; [exact Henabled|left].
      change ((if pcp =? osPrioMutexCeilDis sg then prioTbl (TskState before)
        else update_prio_tbl (prioTbl (TskState before)) pcp PTReserved) pcp = PTReserved).
      rewrite (proj2 (Z.eqb_neq _ _) Henabled).
      unfold update_prio_tbl; destruct (Z.eq_dec pcp pcp); congruence.
  - rewrite event_state_lookup_other in He by exact Hne.
    destruct (Hvalid mid e m He Htype Hm) as [Hrange [Howner Hslots]].
    split; [exact Hrange|]. split; [exact Howner|].
    destruct Hslots as [Hdisabled|[Henabled Hreserved]].
    + left; exact Hdisabled.
    + right; split; [exact Henabled|].
      change ((mutex_create_priority_state sg pcp before.(TskState)).(prioTbl) m.(mfPCP) = PTReserved \/
        exists owner, m.(mfOwner) = Some owner /\
          (mutex_create_priority_state sg pcp before.(TskState)).(prioTbl) m.(mfPCP) = PTTask owner).
      rewrite (priority_state_preserves_old_mutex_slot sg before.(TskState) before.(EventState)
        pcp mid e m Hpcp Hslot Htable He Htype Hm Henabled).
      exact Hreserved.
Qed.

Lemma enabled_fresh_pcp_differs_old_mutex : forall sg tasks events pcp mid e m,
  valid_mutex_pcp sg pcp -> pcp <> sg.(osPrioMutexCeilDis) ->
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  task_mutex_priotbl_consistency sg tasks events ->
  events.(inUsedEventStates) mid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m -> m.(mfPCP) <> pcp.
Proof.
  intros sg tasks events pcp mid e m Hpcp Henabled [Hdisabled|Hfree] Htable He Htype Hm Heq.
  - contradiction.
  - apply (fresh_pcp_has_no_old_claim sg tasks events pcp Hpcp Hfree Htable).
    exists mid, e, m; split; [exact He|]. split; [exact Htype|]. split; [exact Hm|].
    split; [unfold mutex_pcp_enabled; congruence|exact Heq].
Qed.

Lemma state_preserves_pcp_unique : forall sg before pcp eid rest,
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) ->
  task_mutex_priotbl_consistency sg before.(TskState) before.(EventState) ->
  mutex_enabled_pcp_unique sg before ->
  mutex_enabled_pcp_unique sg (mutex_create_state sg pcp eid rest before).
Proof.
  intros sg before pcp eid rest Hpcp Hslot Htable Hunique mid1 e1 m1 mid2 e2 m2
    He1 Htype1 Hm1 He2 Htype2 Hm2 Hsame Henabled.
  change ((mutex_create_event_state pcp eid rest before.(EventState)).(inUsedEventStates) mid1 = Some e1) in He1.
  change ((mutex_create_event_state pcp eid rest before.(EventState)).(inUsedEventStates) mid2 = Some e2) in He2.
  destruct (Z.eq_dec mid1 eid) as [->|Hne1]; destruct (Z.eq_dec mid2 eid) as [->|Hne2].
  - reflexivity.
  - rewrite event_state_lookup_same in He1; injection He1 as He1; subst e1.
    cbn [mutex_create_node mutexFields] in Hm1; injection Hm1 as Hm1; subst m1.
    rewrite event_state_lookup_other in He2 by exact Hne2.
    exfalso; eapply enabled_fresh_pcp_differs_old_mutex;
      [exact Hpcp|exact Henabled|exact Hslot|exact Htable|exact He2|exact Htype2|exact Hm2|symmetry; exact Hsame].
  - rewrite event_state_lookup_same in He2; injection He2 as He2; subst e2.
    cbn [mutex_create_node mutexFields] in Hm2; injection Hm2 as Hm2; subst m2.
    rewrite event_state_lookup_other in He1 by exact Hne1.
    exfalso; eapply enabled_fresh_pcp_differs_old_mutex;
      [exact Hpcp|cbn [mfPCP] in Hsame; congruence|exact Hslot|exact Htable|exact He1|exact Htype1|exact Hm1|exact Hsame].
  - rewrite event_state_lookup_other in He1 by exact Hne1.
    rewrite event_state_lookup_other in He2 by exact Hne2.
    eapply Hunique; eassumption.
Qed.

Lemma state_preserves_cross_module_consistency : forall sg before pcp eid rest,
  task_in_range sg before.(TskState) -> before.(EventState).(inUsedEventStates) eid = None ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = None ->
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) ->
  cross_module_consistency sg before ->
  cross_module_consistency sg (mutex_create_state sg pcp eid rest before).
Proof.
  intros sg before pcp eid rest Htasks Hnone Hprivate Hpcp Hslot
    [Htable [Howners [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  split; [eapply state_preserves_table_consistency; eassumption|].
  split; [eapply state_preserves_owner_snapshots; eassumption|].
  split.
  - unfold mutex_create_state.
    eapply event_wait_object_consistency_event_publish with
      (node := mutex_create_node pcp before.(EventState).(eventLifecycle).(eventNextGeneration)
        (mutex_create_storage before.(EventState) eid)).
    + exact Hnone.
    + reflexivity.
    + reflexivity.
    + exact Hwait.
  - split; [eapply state_preserves_mutex_protocol; eassumption|].
    split; [eapply state_preserves_pcp_unique; eassumption|].
    split; [exact Hflags|exact Htimer].
Qed.

Lemma state_preserves_pending_consistency : forall sg tasks events pcp eid rest,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  pending_mutex_consistency sg tasks events ->
  pending_mutex_consistency sg (mutex_create_priority_state sg pcp tasks)
    (mutex_create_event_state pcp eid rest events).
Proof.
  intros sg tasks events pcp eid rest Hprivate Hslot Hpending slot p queue Hlease.
  assert (Hleases : event_mutex_lease_view (mutex_create_event_state pcp eid rest events) =
    event_mutex_lease_view events).
  { apply functional_extensionality; intro other; unfold event_mutex_lease_view,
      mutex_create_event_state, event_publish, event_detach_head; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hprivate|]; reflexivity. }
  rewrite Hleases in Hlease.
  destruct (Hpending slot p queue Hlease)
    as [Hpcp [Henabled [Hqueue [Hreserved [Hcreator [Hnolive Hunique]]]]]].
  assert (Hdifferent : p <> pcp).
  { destruct Hslot as [Hdisabled|Hfree]; congruence. }
  split; [exact Hpcp|]. split; [exact Henabled|]. split; [exact Hqueue|].
  split.
  - cbn [mutex_create_priority_state prioTbl].
    destruct (Z.eqb pcp sg.(osPrioMutexCeilDis)); [exact Hreserved|].
    unfold update_prio_tbl; destruct (Z.eq_dec p pcp); [contradiction|exact Hreserved].
  - split; [exact Hcreator|]. split.
    + intros [mid [node [m [Hnode [Htype [Hm Hclaim]]]]]].
      destruct (Z.eq_dec mid eid) as [->|Hne].
      * rewrite event_state_lookup_same in Hnode; injection Hnode as Hnode; subst node.
        cbn [mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m.
        destruct Hclaim as [_ Heq]; apply Hdifferent; symmetry; exact Heq.
      * rewrite event_state_lookup_other in Hnode by exact Hne.
        apply Hnolive; exists mid, node, m; exact (conj Hnode (conj Htype (conj Hm Hclaim))).
    + intros other other_queue Hother; rewrite Hleases in Hother; eapply Hunique; exact Hother.
Qed.

Lemma state_preserves_validity : forall sg before pcp eid rest,
  UCOS2_state_inv sg before ->
  before.(EventState).(unUsedEventStates) = eid :: rest ->
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) ->
  UCOS2_state_inv sg (mutex_create_state sg pcp eid rest before).
Proof.
  intros sg before pcp eid rest
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hbits
      [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames Hreferences]]]]]]]]]]]]]
    Hhead Hpcp Hslot.
  assert (Hnone : before.(EventState).(inUsedEventStates) eid = None).
  { exact (proj1 (event_pool_free_unallocated sg before.(EventState) eid
      (proj1 Hevents) ltac:(rewrite Hhead; left; reflexivity))). }
  assert (Hprivate : before.(EventState).(eventLifecycle).(eventPrivate) eid = None).
  { exact (proj2 (event_pool_free_unallocated sg before.(EventState) eid
      (proj1 Hevents) ltac:(rewrite Hhead; left; reflexivity))). }
  pose proof (state_preserves_pending_consistency sg before.(TskState) before.(EventState)
    pcp eid rest Hprivate Hslot (proj2 (proj2 Hreferences))) as HpendingAfter.
  assert (HnamesAfter : kernel_names_valid sg (mutex_create_state sg pcp eid rest before)).
  { eapply kernel_names_valid_root_subset; [exact (proj1 Hreferences)|reflexivity|].
    assert (Hdisabled : sg.(osKernelConfig).(cfgEventNames) = false)
      by (unfold selected_kernel_profile in Hprofile; tauto).
    intros p Hroot.
    unfold kernel_name_root in Hroot |- *.
    rewrite Hdisabled in Hroot |- *.
    destruct Hroot as [Htask|[[Hbad _]|[Hflag|[Hmem|HtimerRoot]]]].
    - left; exact Htask.
    - discriminate.
    - right; right; left; exact Hflag.
    - right; right; right; left; exact Hmem.
    - right; right; right; right; exact HtimerRoot. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|].
  split; [apply priority_state_preserves_in_range; assumption|].
  split; [exact Hsched|].
  split; [apply event_state_priority_index_in_range; assumption|].
  split; [apply state_preserves_cross_module_consistency; assumption|].
  split; [exact Hidle|]. split; [exact Hbits|].
  split; [exact Hflags|]. split; [exact Hmemory|].
  split; [exact Htimer|]. split; [exact Hstats|].
  split; [exact Hcontrol|]. split; [exact Hnames|].
  split; [exact HnamesAfter|]. split; [exact (proj1 (proj2 Hreferences))|exact HpendingAfter].
Qed.

Definition node_residual (sg : StableGlobVars) (s : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  task_public_storage_without_prio_tbl sg s.(TskState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) **
  store_map (used_event_rep sg s.(TskState)) s.(EventState).(inUsedEventStates) **
  event_free_storage_without_eid sg s.(EventState) eid **
  UCOS2_raw_rep_missing_two sg s TaskModule EventModule.

Lemma head_residual_split_node : forall sg s eid image,
  s.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  head_residual sg s |--
    event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
    node_residual sg s eid.
Proof.
  intros sg s eid image Himage; unfold head_residual, node_residual.
  sep_apply_l_atomic (event_free_storage_split_eid sg s.(EventState) eid image Himage).
  entailer!.
Qed.

Lemma event_state_preserves_queue_storage : forall sg before pcp eid rest,
  before.(inUsedEventStates) eid = None ->
  before.(eventLifecycle).(eventPrivate) eid = None ->
  queue_storage_rep sg before |-- queue_storage_rep sg (mutex_create_event_state pcp eid rest before).
Proof.
  intros sg before pcp eid rest Hnone Hprivate.
  eapply queue_storage_event_entry_frame with (before := None)
    (next := Some (mutex_create_node pcp before.(eventLifecycle).(eventNextGeneration)
      (mutex_create_storage before eid))).
  - exact Hnone.
  - intros; discriminate.
  - intros node Hnode; injection Hnode as Hnode; subst node; reflexivity.
  - reflexivity.
  - reflexivity.
  - intro owner; unfold queue_private_owner, mutex_create_event_state, event_publish, event_detach_head.
    cbn [eventLifecycle eventPrivate]; unfold kernel_map_set.
    destruct (Z.eq_dec owner eid) as [->|Hne]; [rewrite Hprivate|]; reflexivity.
Qed.

Lemma state_preserves_untouched_rep : forall sg before pcp eid rest,
  before.(EventState).(inUsedEventStates) eid = None ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = None ->
  UCOS2_raw_rep_missing_two sg before TaskModule EventModule |--
  UCOS2_raw_rep_missing_two sg (mutex_create_state sg pcp eid rest before) TaskModule EventModule.
Proof.
  intros sg before pcp eid rest Hnone Hprivate.
  unfold UCOS2_raw_rep_missing_two, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  unfold mutex_create_state.
  cbn [replace_EventS replace_TskS TskState SchedState IntrState EventState TickState
    FlagState MemoryState TimerState StatsState ControlState NameState].
  rewrite <- (sched_raw_rep_change_task_index sg before.(TskState)
    (mutex_create_priority_state sg pcp before.(TskState)) before.(SchedState) eq_refl).
  sep_apply_l_atomic (event_state_preserves_queue_storage sg before.(EventState) pcp eid rest Hnone Hprivate).
  entailer!.
Qed.

Lemma node_merge_event_state : forall sg tasks events pcp eid rest,
  events.(inUsedEventStates) eid = None ->
  used_event_rep sg (mutex_create_priority_state sg pcp tasks) eid
    (mutex_create_node pcp events.(eventLifecycle).(eventNextGeneration) (mutex_create_storage events eid)) **
  store_map (used_event_rep sg tasks) events.(inUsedEventStates) **
  event_free_storage_without_eid sg events eid **
  event_free_root_rep sg (mutex_create_event_state pcp eid rest events) |--
  event_raw_rep sg (mutex_create_priority_state sg pcp tasks)
    (mutex_create_event_state pcp eid rest events).
Proof.
  intros sg tasks events pcp eid rest Hnone.
  assert (Hrepr : used_event_rep sg tasks =
    used_event_rep sg (mutex_create_priority_state sg pcp tasks)).
  { apply functional_extensionality; intro other.
    apply functional_extensionality; intro node.
    unfold used_event_rep.
    assert (Himage : event_image sg tasks node =
      event_image sg (mutex_create_priority_state sg pcp tasks) node).
    { destruct (event_wait_encoding_priority_ext node.(waitList) tasks
        (mutex_create_priority_state sg pcp tasks) ltac:(intros; reflexivity)) as [Hgrp Htbl].
      apply functional_extensionality; intro field; unfold event_image.
      destruct field; try reflexivity; f_equal; [exact Hgrp|..]; apply Htbl. }
    rewrite Himage; reflexivity. }
  rewrite Hrepr.
  sep_apply_l_atomic (proj1 (event_free_storage_remove_eid_equiv sg events
    (mutex_create_event_state pcp eid rest events) eid
    (event_state_removes_free_storage pcp eid rest events)
    ltac:(intros; symmetry; apply event_state_frame_free_storage; assumption))).
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (used_event_rep sg (mutex_create_priority_state sg pcp tasks)) events.(inUsedEventStates) eid Hnone).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (used_event_rep sg (mutex_create_priority_state sg pcp tasks))
    events.(inUsedEventStates) (mutex_create_event_state pcp eid rest events).(inUsedEventStates) eid
    ltac:(intros; symmetry; apply event_state_lookup_other; assumption))).
  sep_apply_l_atomic (store_map_merge
    (used_event_rep sg (mutex_create_priority_state sg pcp tasks)) eid
    (mutex_create_node pcp events.(eventLifecycle).(eventNextGeneration) (mutex_create_storage events eid))
    (mutex_create_event_state pcp eid rest events).(inUsedEventStates)
    (event_state_lookup_same pcp eid rest events)).
  unfold event_raw_rep; entailer!.
Qed.

Lemma node_merge_updated_inv : forall sg before pcp eid rest,
  UCOS2_state_inv sg before -> before.(EventState).(unUsedEventStates) = eid :: rest ->
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) ->
  store_prio_tbl sg (mutex_create_priority_state sg pcp before.(TskState)).(prioTbl) **
  event_free_root_rep sg (mutex_create_event_state pcp eid rest before.(EventState)) **
  used_event_rep sg (mutex_create_priority_state sg pcp before.(TskState)) eid
    (mutex_create_node pcp before.(EventState).(eventLifecycle).(eventNextGeneration)
      (mutex_create_storage before.(EventState) eid)) ** node_residual sg before eid |--
  UCOS2_inv sg (mutex_create_state sg pcp eid rest before).
Proof.
  intros sg before pcp eid rest Hvalid Hhead Hpcp Hslot.
  pose proof (state_preserves_validity sg before pcp eid rest Hvalid Hhead Hpcp Hslot) as Hpost.
  destruct (event_pool_free_unallocated sg before.(EventState) eid
    (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid)))))
    ltac:(rewrite Hhead; left; reflexivity)) as [Hnone Hprivate].
  unfold node_residual.
  sepcon_assoc_change.
  sep_apply_l_atomic (node_merge_event_state sg before.(TskState) before.(EventState) pcp eid rest Hnone).
  sep_apply_l_atomic (state_preserves_untouched_rep sg before pcp eid rest Hnone Hprivate).
  rewrite (UCOS2_inv_split_two sg (mutex_create_state sg pcp eid rest before)
    TaskModule EventModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold task_shared_rep.
  rewrite task_public_storage_prio_tbl_equiv.
  cbn [mutex_create_state replace_EventS replace_TskS TskState EventState parkedTaskStacks].
  assert (Hstorage : task_public_storage_without_prio_tbl sg
      (mutex_create_priority_state sg pcp before.(TskState)) =
    task_public_storage_without_prio_tbl sg before.(TskState)) by reflexivity.
  rewrite Hstorage.
  entailer!.
Qed.

Lemma detached_lease_view_eq : forall sg events eid rest image pcp,
  event_mutex_lease_view (event_detach_mutex_head sg events eid rest image pcp) =
  kernel_map_set (event_mutex_lease_view events) eid
    (if pcp =? sg.(osPrioMutexCeilDis) then None else Some (pcp, None)).
Proof.
  intros; apply functional_extensionality; intro other.
  unfold event_mutex_lease_view, event_detach_mutex_head, event_private_set_mutex_pcp,
    event_set_lifecycle, event_detach_head; simpl; unfold kernel_map_set.
  destruct (Z.eq_dec other eid); [destruct (pcp =? osPrioMutexCeilDis sg)|]; reflexivity.
Qed.

Lemma detached_preserves_other_priority_claims : forall sg events eid rest image pcp p,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  pending_mutex_priority_claim events p ->
  pending_mutex_priority_claim (event_detach_mutex_head sg events eid rest image pcp) p.
Proof.
  intros sg events eid rest image pcp p Hnone [owner [queue Hlease]].
  exists owner, queue; rewrite detached_lease_view_eq; unfold kernel_map_set.
  destruct (Z.eq_dec owner eid) as [->|Hne]; [|exact Hlease].
  unfold event_mutex_lease_view in Hlease; rewrite Hnone in Hlease; discriminate.
Qed.

Lemma detached_event_preserves_in_range : forall sg tasks events eid rest image pcp,
  event_in_range sg tasks events -> events.(unUsedEventStates) = eid :: rest ->
  event_in_range sg tasks (event_detach_mutex_head sg events eid rest image pcp).
Proof.
  intros sg tasks events eid rest image pcp Hvalid Hhead.
  pose proof (event_detach_head_preserves_in_range sg tasks events eid rest image Hvalid Hhead)
    as [Hpart [Hfree [Hidentity Hpublished]]].
  pose proof (detached_allocation_lookup events eid rest image) as Hget.
  unfold event_detach_mutex_head; split.
  - eapply event_private_set_mutex_pcp_preserves_partition; eassumption.
  - split; [exact Hfree|]. split.
    + eapply event_private_set_mutex_pcp_preserves_identity; eassumption.
    + exact Hpublished.
Qed.

Lemma detached_preserves_pending_consistency : forall sg tasks events eid rest image pcp,
  task_in_range sg tasks -> task_mutex_priotbl_consistency sg tasks events ->
  pending_mutex_consistency sg tasks events -> valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  pending_mutex_consistency sg (mutex_create_priority_state sg pcp tasks)
    (event_detach_mutex_head sg events eid rest image pcp).
Proof.
  intros sg tasks events eid rest image pcp Htasks Htable Hpending Hpcp Hslot owner p queue Hlease.
  rewrite detached_lease_view_eq in Hlease; unfold kernel_map_set in Hlease.
  destruct (Z.eq_dec owner eid) as [->|Howner].
  - destruct (pcp =? sg.(osPrioMutexCeilDis)) eqn:Hdisabled; [discriminate|].
    injection Hlease as Hp Hqueue; subst p queue.
    apply Z.eqb_neq in Hdisabled.
    assert (Hfree : tasks.(prioTbl) pcp = PTFree) by (destruct Hslot; [contradiction|assumption]).
    assert (Hcreator : tasks.(taskLifecycle).(taskReservations) pcp = None).
    { destruct (tasks.(taskLifecycle).(taskReservations) pcp) as [entry|] eqn:Hentry; [|reflexivity].
      pose proof (proj1 (proj2 (proj2 (proj2 Htasks)))) as Hreservations.
      destruct (proj1 Hreservations pcp entry Hentry) as [_ [Hreserved _]]; congruence. }
    split; [exact Hpcp|]. split; [exact Hdisabled|]. split; [reflexivity|].
    split.
    + cbn [mutex_create_priority_state prioTbl].
      rewrite (proj2 (Z.eqb_neq _ _) Hdisabled).
      unfold update_prio_tbl; destruct (Z.eq_dec pcp pcp); congruence.
    + split; [exact Hcreator|]. split.
      * exact (fresh_pcp_has_no_old_claim sg tasks events pcp Hpcp Hfree Htable).
      * intros other other_queue Hother; rewrite detached_lease_view_eq in Hother.
        unfold kernel_map_set in Hother; destruct (Z.eq_dec other eid) as [->|Hne]; [reflexivity|].
        destruct (Hpending other pcp other_queue Hother) as [_ [_ [_ [Hreserved _]]]]; congruence.
  - destruct (Hpending owner p queue Hlease)
      as [Hrange [Henabled [Hqueue [Hreserved [Hcreator [Hnolive Hunique]]]]]].
    assert (Hdifferent : p <> pcp) by (destruct Hslot; congruence).
    split; [exact Hrange|]. split; [exact Henabled|]. split; [exact Hqueue|].
    split.
    + cbn [mutex_create_priority_state prioTbl].
      destruct (pcp =? osPrioMutexCeilDis sg); [exact Hreserved|].
      unfold update_prio_tbl; destruct (Z.eq_dec p pcp); [contradiction|exact Hreserved].
    + split; [exact Hcreator|]. split; [exact Hnolive|].
      intros other other_queue Hother; rewrite detached_lease_view_eq in Hother.
      unfold kernel_map_set in Hother; destruct (Z.eq_dec other eid) as [->|Hne].
      * destruct (pcp =? sg.(osPrioMutexCeilDis)); [discriminate|].
        injection Hother as Hp Hq; congruence.
      * eapply Hunique; exact Hother.
Qed.

Lemma detached_preserves_table_consistency : forall sg tasks events eid rest image pcp,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  (pcp = sg.(osPrioMutexCeilDis) \/ tasks.(prioTbl) pcp = PTFree) ->
  task_mutex_priotbl_consistency sg tasks events ->
  task_mutex_priotbl_consistency sg (mutex_create_priority_state sg pcp tasks)
    (event_detach_mutex_head sg events eid rest image pcp).
Proof.
  intros sg tasks events eid rest image pcp Hprivate Hslot [Hcreator [Hslots Halias]].
  split; [exact Hcreator|]. split.
  - intros p Hp; cbn [mutex_create_priority_state prioTbl].
    destruct (pcp =? sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
    + specialize (Hslots p Hp); destruct (tasks.(prioTbl) p); try exact Hslots.
      destruct Hslots as [Hreservation|[Hlive|Hpending]].
      * left; exact Hreservation.
      * right; left; exact Hlive.
      * right; right; eapply detached_preserves_other_priority_claims; eassumption.
    + unfold update_prio_tbl; destruct (Z.eq_dec p pcp) as [->|Hne].
      * right; right; exists eid, None.
        rewrite detached_lease_view_eq, kernel_map_set_same, Hdisabled; reflexivity.
      * specialize (Hslots p Hp); destruct (tasks.(prioTbl) p); try exact Hslots.
        destruct Hslots as [Hreservation|[Hlive|Hpending]].
        -- left; exact Hreservation.
        -- right; left; exact Hlive.
        -- right; right; eapply detached_preserves_other_priority_claims; eassumption.
  - intros tid t Ht; destruct (Halias tid t Ht) as [base [Hbase [Heffective Hclaims]]].
    exists base; split.
    + eapply task_base_priority_alias_ext; [|exact Hbase].
      intros; symmetry; apply priority_state_alias_iff; exact Hslot.
    + split.
      * eapply task_effective_priority_alias_ext; [|exact Heffective].
        intros; symmetry; apply priority_state_alias_iff; exact Hslot.
      * intros p Hp; apply priority_state_alias_iff in Hp; [|exact Hslot].
        exact (Hclaims p Hp).
Qed.

Lemma detached_events_preserve_cross_module_consistency : forall sg before eid rest image pcp,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = None ->
  cross_module_consistency sg before ->
  cross_module_consistency sg
    (replace_EventS (event_detach_mutex_head sg before.(EventState) eid rest image pcp) before).
Proof.
  intros sg before eid rest image pcp Hprivate [[Hcreator [Hslots Halias]] Hrest].
  split; [|exact Hrest]. split; [exact Hcreator|]. split; [|exact Halias].
  intros p Hp; cbn [replace_EventS TskState EventState].
  specialize (Hslots p Hp); destruct (before.(TskState).(prioTbl) p); try exact Hslots.
  destruct Hslots as [Hreservation|[Hlive|Hpending]].
  - left; exact Hreservation.
  - right; left; exact Hlive.
  - right; right; eapply detached_preserves_other_priority_claims; eassumption.
Qed.

Lemma detached_state_preserves_cross_module_consistency : forall sg before pcp eid rest,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = None ->
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) ->
  cross_module_consistency sg before ->
  cross_module_consistency sg (mutex_create_detached_state sg pcp eid rest before).
Proof.
  intros sg before pcp eid rest Hprivate Hpcp Hslot Hcross.
  pose proof (proj1 Hcross) as Htable.
  pose proof (detached_events_preserve_cross_module_consistency sg before eid rest
    (mutex_create_storage before.(EventState) eid) pcp Hprivate Hcross) as Hdetached.
  change (cross_module_consistency sg
    (replace_TskS (mutex_create_priority_state sg pcp before.(TskState))
      (replace_EventS (event_detach_mutex_head sg before.(EventState) eid rest
        (mutex_create_storage before.(EventState) eid) pcp) before))).
  eapply cross_module_consistency_task_table_transport.
  - reflexivity.
  - apply detached_preserves_table_consistency; assumption.
  - intros; symmetry; apply priority_state_alias_iff; exact Hslot.
  - intros mid node m Hget Htype Hm Henabled.
    exact (priority_state_preserves_old_mutex_slot sg before.(TskState) before.(EventState)
      pcp mid node m Hpcp Hslot Htable Hget Htype Hm Henabled).
  - exact Hdetached.
Qed.

Lemma detached_state_preserves_validity : forall sg before pcp eid rest,
  UCOS2_state_inv sg before -> before.(EventState).(unUsedEventStates) = eid :: rest ->
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) ->
  UCOS2_state_inv sg (mutex_create_detached_state sg pcp eid rest before).
Proof.
  intros sg before pcp eid rest
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hbits
      [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]]
    Hhead Hpcp Hslot.
  destruct (event_pool_free_unallocated sg before.(EventState) eid
    (proj1 Hevents) ltac:(rewrite Hhead; left; reflexivity)) as [Hnone Hprivate].
  assert (HeventsAfter : event_in_range sg
    (mutex_create_priority_state sg pcp before.(TskState))
    (event_detach_mutex_head sg before.(EventState) eid rest
      (mutex_create_storage before.(EventState) eid) pcp)).
  { pose proof (detached_event_preserves_in_range sg before.(TskState) before.(EventState)
      eid rest (mutex_create_storage before.(EventState) eid) pcp Hevents Hhead)
      as [Hpart [Hfree [Hidentity [Hfields [Hpayload [Hqueues Hentries]]]]]].
    split; [exact Hpart|]. split; [exact Hfree|]. split; [exact Hidentity|].
    split; [exact Hfields|]. split; [exact Hpayload|]. split; [exact Hqueues|].
    intros slot node Hget; eapply event_wait_entry_task_lookup_ext;
      [intros; reflexivity|exact (Hentries slot node Hget)]. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]. split; [apply priority_state_preserves_in_range; assumption|].
  split; [exact Hsched|]. split; [exact HeventsAfter|].
  split; [apply detached_state_preserves_cross_module_consistency; assumption|].
  split; [exact Hidle|]. split; [exact Hbits|]. split; [exact Hflags|].
  split; [exact Hmemory|]. split; [exact Htimer|]. split; [exact Hstats|].
  split; [exact Hcontrol|]. split; [exact Hnames|]. split; [exact Hreferences|].
  split; [exact Hstacks|].
  apply detached_preserves_pending_consistency; [exact Htasks|exact (proj1 Hcross)|assumption..].
Qed.

Definition detached_allocation (sg : StableGlobVars) (events : Glob_EventAbstractState)
  (image : EventStorage) (pcp : Priority) : EventPrivateAllocation :=
  {| eventPrivateInvocation := events.(eventLifecycle).(eventNextInvocation);
     eventPrivateGeneration := events.(eventLifecycle).(eventNextGeneration);
     eventPrivateQueue := None;
     eventPrivateMutexPCP := if pcp =? sg.(osPrioMutexCeilDis) then None else Some pcp;
     eventPrivateStorage := image |}.

Lemma detached_private_lookup : forall sg events eid rest image pcp,
  (event_detach_mutex_head sg events eid rest image pcp).(eventLifecycle).(eventPrivate) eid =
    Some (detached_allocation sg events image pcp).
Proof. intros; apply kernel_map_set_same. Qed.

Lemma detached_event_raw_eq : forall sg tasks events eid rest image pcp,
  event_raw_rep sg tasks (event_detach_mutex_head sg events eid rest image pcp) =
  event_raw_rep sg tasks (event_detach_head events eid rest image).
Proof. reflexivity. Qed.

Lemma detached_queue_rep_eq : forall sg events eid rest image pcp,
  events.(eventLifecycle).(eventPrivate) eid = None ->
  queue_storage_rep sg (event_detach_mutex_head sg events eid rest image pcp) =
    queue_storage_rep sg events.
Proof.
  intros sg events eid rest image pcp Hprivate.
  assert (Howners : queue_private_owner (event_detach_mutex_head sg events eid rest image pcp) =
    queue_private_owner events).
  { apply functional_extensionality; intro other; unfold queue_private_owner,
      event_detach_mutex_head, event_private_set_mutex_pcp, event_set_lifecycle, event_detach_head;
      simpl; unfold kernel_map_set.
    destruct (Z.eq_dec other eid) as [->|Hne]; [rewrite Hprivate|]; reflexivity. }
  unfold queue_storage_rep, queue_pool_partition, queue_slot_private; rewrite Howners; reflexivity.
Qed.

Lemma detached_missing_rep_eq : forall sg before pcp eid rest,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = None ->
  UCOS2_raw_rep_missing_two sg before TaskModule EventModule =
  UCOS2_raw_rep_missing_two sg (mutex_create_detached_state sg pcp eid rest before) TaskModule EventModule.
Proof.
  intros sg before pcp eid rest Hprivate.
  apply UCOS2_raw_rep_missing_two_frame; intros module Htask Hevent;
    destruct module; try contradiction; try reflexivity.
  - apply sched_raw_rep_change_task_index; reflexivity.
  - symmetry; apply detached_queue_rep_eq; exact Hprivate.
Qed.

Lemma head_merge_detached_inv : forall sg before pcp eid rest image,
  UCOS2_state_inv sg before -> before.(EventState).(unUsedEventStates) = eid :: rest ->
  before.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  valid_mutex_pcp sg pcp ->
  (pcp = sg.(osPrioMutexCeilDis) \/ before.(TskState).(prioTbl) pcp = PTFree) ->
  head_residual sg before **
  store_prio_tbl sg (mutex_create_priority_state sg pcp before.(TskState)).(prioTbl) **
  sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) |--
  event_private_storage_rep sg eid (detached_allocation sg before.(EventState) image pcp) **
  UCOS2_inv sg (mutex_create_detached_state sg pcp eid rest before).
Proof.
  intros sg before pcp eid rest image Hvalid Hhead Himage Hpcp Hslot.
  pose proof (detached_state_preserves_validity sg before pcp eid rest Hvalid Hhead Hpcp Hslot) as Hpost.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_free_unallocated sg before.(EventState) eid Hpool
    ltac:(rewrite Hhead; left; reflexivity)) as [Hnone Hprivate].
  assert (Hstorage : mutex_create_storage before.(EventState) eid = image)
    by (unfold mutex_create_storage; rewrite Himage; reflexivity).
  unfold head_residual; sepcon_assoc_change.
  sep_apply_l_atomic (event_detach_head_reconstructs_raw_rep sg before.(TskState)
    before.(EventState) eid rest image Himage).
  rewrite <- (detached_event_raw_eq sg before.(TskState) before.(EventState) eid rest image pcp).
  assert (Hindex : event_raw_rep sg before.(TskState)
    (event_detach_mutex_head sg before.(EventState) eid rest image pcp) =
    event_raw_rep sg (mutex_create_priority_state sg pcp before.(TskState))
    (event_detach_mutex_head sg before.(EventState) eid rest image pcp)).
  { apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes.
    intros other node tid Hget Hin; reflexivity. }
  rewrite Hindex, (detached_missing_rep_eq sg before pcp eid rest Hprivate).
  rewrite (UCOS2_inv_split_two sg (mutex_create_detached_state sg pcp eid rest before)
    TaskModule EventModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold event_private_storage_rep, detached_allocation, task_shared_rep.
  rewrite task_public_storage_prio_tbl_equiv.
  cbn [mutex_create_detached_state replace_EventS replace_TskS TskState EventState parkedTaskStacks eventPrivateStorage].
  rewrite Hstorage.
  assert (HtaskStorage : task_public_storage_without_prio_tbl sg
    (mutex_create_priority_state sg pcp before.(TskState)) =
    task_public_storage_without_prio_tbl sg before.(TskState)) by reflexivity.
  rewrite HtaskStorage.
  entailer!.
Qed.

End MutexCreateFull.
