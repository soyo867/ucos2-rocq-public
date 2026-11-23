(** OSMutexAccept-specific semantics and proof helpers. Shared/global
    invariants do not import this function module. The legacy lib path is
    only a re-export for existing C annotations and generated consumers. *)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.
Import ListNotations.
Local Open Scope sets.
Local Open Scope sac_scope.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.cross_module_invariants.
Import TaskStateDef.
Import EventStateDef.

Local Open Scope Z_scope.

(* ================================================================== *)
(* L5: OSMutexAccept path semantics and exact state transitions         *)
(* ================================================================== *)

(* Only the positive source path may expose OSTCBCur and its task
   priority; the type-error and ISR paths return before that dereference.
   The runnable-task premise is supplied by the reusable task L3 focus. *)
Definition mutex_accept_task_sched_guard_prop
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState)
  (schedSt : SchedAbstractState) (etype isr : Z)
  (cur_tid : TaskID) (cur_t : TaskAbstractState)
  (tcbcur tcbprio : Z) : Prop :=
  etype <> 4 \/
  isr > 0 \/
  (etype = 4 /\ isr <= 0 /\ tcbcur <> 0 /\
   verification_slice_sched_tcb_cur_snapshot_prop sg schedSt tcbcur /\
   task_runnable_prio_snapshot_prop
     sg tskSt cur_tid cur_t tcbcur tcbprio).

(* Exact EventState selected after a successful non-blocking acquire. *)
Definition mutex_accept_acquire_post_state
  (ls0 : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) (tid : TaskID) (origPrio : Priority)
  : UCOS2_Verify_State :=
  match e.(mutexFields) with
  | Some m =>
      replace_EventS
        (owner_acquire_update ls0.(EventState) eid e m tid origPrio)
        ls0
  | None => ls0
  end.

(* Branch-local critical-exit relation.  The unavailable path restores the
   entry state; the acquire path restores the exact owner-acquire update. *)
Definition mutex_accept_restore_transition_prop
  (ls0 ls_inside ls_restored : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState)
  (tid : TaskID) (origPrio : Priority) (acquired : bool) : Prop :=
  crit_rel_event_only ls_inside ls_restored /\
  ls_restored =
    if acquired
    then mutex_accept_acquire_post_state ls0 eid e tid origPrio
    else ls0.

(* ================================================================== *)
(* Compatibility names for the accepted Accept source_goal_version      *)
(* ================================================================== *)

(* These aliases preserve the current generated witnesses while the C
   annotation is migrated in a fresh controller round.  New lib code must
   use the reusable event/task names on the right-hand side. *)
Notation mutex_accept_event_layout_prop :=
  event_core_fields_layout_prop (only parsing).

Notation mutex_accept_tcb_prio_layout_prop :=
  task_prio_field_layout_prop (only parsing).

Notation mutex_accept_entry_count_range_prop :=
  event_count_value_range_prop (only parsing).

Notation mutex_accept_current_task_ready_prop :=
  task_runnable_prio_snapshot_prop (only parsing).

Lemma mutex_accept_high_byte_raw__restore_and_returns : forall x,
  event_count_value_range_prop x ->
  unsigned_last_nbits (Z.shiftr x 8) 8 = Z.shiftr x 8.
Proof.
  intros x Hx.
  unfold event_count_value_range_prop in Hx.
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  rewrite Z.shiftr_div_pow2 by lia.
  cbn. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.
Lemma mutex_accept_u16_raw__restore_and_returns : forall x,
  0 <= x <= 255 -> unsigned_last_nbits x 16 = x.
Proof.
  intros x Hx. unfold unsigned_last_nbits.
  apply Z.mod_small. cbn. lia.
Qed.
Lemma mutex_accept_replace_low_byte__restore_and_returns : forall x p,
  event_count_value_range_prop x ->
  Z.land x 255 = 255 ->
  255 <= x ->
  0 <= p <= 255 ->
  Z.lor (Z.land x 65280) p = x - 255 + p.
Proof.
  intros x p Hx Hlow Hxmin Hp.
  unfold event_count_value_range_prop in Hx.
  assert (Hhigh : Z.land x 65280 = x - 255).
  {
    replace 65280 with (Z.land (Z.lnot 255) 65535) by reflexivity.
    rewrite Z.land_assoc.
    rewrite <- Z.sub_land_same_l.
    rewrite Hlow.
    replace 65535 with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia.
    apply Z.mod_small. lia.
  }
  rewrite Hhigh.
  assert (Hdisjoint : Z.land (x - 255) p = 0).
  {
    assert (Hp_mask : Z.land p 255 = p).
    {
      replace 255 with (Z.ones 8) by reflexivity.
      rewrite Z.land_ones by lia.
      apply Z.mod_small. lia.
    }
    rewrite <- Hp_mask.
    rewrite (Z.land_comm p 255).
    rewrite Z.land_assoc.
    replace 255 with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones by lia.
    assert (Hxmod : x mod 256 = 255).
    {
      replace 255 with (Z.ones 8) in Hlow by reflexivity.
      rewrite Z.land_ones in Hlow by lia.
      exact Hlow.
    }
    replace (2 ^ 8) with 256 by reflexivity.
    change (Z.land ((x - 255) mod 256) p = 0).
    rewrite Zminus_mod.
    rewrite Hxmod. reflexivity.
  }
  pose proof (Z.add_lor_land (x - 255) p) as Hsum.
  rewrite Hdisjoint in Hsum. lia.
Qed.
Lemma mutex_accept_pcp_decode__restore_and_returns :
  forall sg tskSt evSt eid e m etype ecnt eptr egrp etbl,
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    eventType e = OS_EVENT_TYPE_MUTEX ->
    mutexFields e = Some m ->
    mfOwner m = None ->
    mfOwnerOrigPrio m = None ->
    mfPCP m = Z.shiftr ecnt 8.
Proof.
  intros sg tskSt evSt eid e m etype ecnt eptr egrp etbl
    Hsnap Htype Hmf Howner Horig.
  unfold event_snapshot_of_prop in Hsnap.
  destruct Hsnap as [_ [_ [Hcnt _]]].
  unfold encode_event_cnt_value in Hcnt.
  rewrite Htype, Hmf, Howner, Horig in Hcnt. simpl in Hcnt.
  rewrite Hcnt. rewrite Z.shiftr_div_pow2 by lia. cbn.
  rewrite Z.add_comm, Z.div_add by lia. reflexivity.
Qed.
Lemma mutex_accept_acquire_snapshot__restore_and_returns :
  forall sg tskSt evSt eid e m tid prio tcbcur
         etype ecnt eptr egrp etbl,
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    eventType e = OS_EVENT_TYPE_MUTEX ->
    mutexFields e = Some m ->
    mfOwner m = None ->
    mfOwnerOrigPrio m = None ->
    event_count_value_range_prop ecnt ->
    0 <= prio <= 255 ->
    tcbcur = verification_slice_tcb_addr sg tid ->
    event_snapshot_of_prop sg tskSt
      (owner_acquire_update evSt eid e m tid prio) eid
      {| eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType := eventType e;
         mutexFields := Some
           {| mfPCP := mfPCP m;
              mfOwner := Some tid;
              mfOwnerOrigPrio := Some prio |};
         semFields := semFields e;
         mboxFields := mboxFields e;
         queueFields := queueFields e;
         waitList := waitList e |}
      4 (Z.lor (Z.land ecnt 65280) prio) tcbcur egrp etbl.
Proof.
  intros sg tskSt evSt eid e m tid prio tcbcur
    etype ecnt eptr egrp etbl Hsnap Htype Hmf Howner Horig
    Hrange Hprio Htcb.
  unfold event_snapshot_of_prop in *.
  destruct Hsnap as [Hget [Henc [Hcnt [Hptr [Hgrp Htbl]]]]].
  repeat split.
  - rewrite (owner_acquire_lookup_eq evSt eid e m tid prio eid Hget Hmf).
    rewrite Z.eqb_refl. reflexivity.
  - rewrite Htype. reflexivity.
  - simpl. unfold encode_event_cnt_value in Hcnt.
    rewrite Htype, Hmf, Howner, Horig in Hcnt. simpl in Hcnt.
    assert (Hmin : 255 <= ecnt).
    { unfold event_count_value_range_prop in Hrange. nia. }
    rewrite (mutex_accept_replace_low_byte__restore_and_returns
      ecnt prio Hrange).
    + unfold encode_event_cnt_value. simpl. rewrite Htype. simpl. lia.
    + rewrite Hcnt.
      replace 255 with (Z.ones 8) by
        (rewrite Z.ones_equiv; reflexivity).
      rewrite Z.land_ones by lia.
      replace (2 ^ 8) with 256 by reflexivity.
      rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
    + exact Hmin.
    + exact Hprio.
  - simpl. rewrite Htcb. unfold verification_slice_encode_event_ptr_value. simpl.
    rewrite Htype. reflexivity.
  - simpl. exact Hgrp.
  - simpl. exact Htbl.
Qed.
Lemma mutex_accept_complete_event__restore_and_returns :
  forall sg tskSt evSt eid e base type_addr ptr_addr cnt_addr
         etype ecnt eptr egrp etbl,
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    event_core_fields_layout_prop sg eid type_addr ptr_addr cnt_addr ->
    base = event_addr sg eid ->
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    used_event_rest_no_type_cnt_ptr sg tskSt base eid e |--
    used_complete_event sg tskSt (event_addr sg eid) eid e.
Proof.
  intros sg tskSt evSt eid e base type_addr ptr_addr cnt_addr
    etype ecnt eptr egrp etbl Hsnap Hlayout Hbase.
  unfold event_snapshot_of_prop in Hsnap.
  destruct Hsnap as [Heid [Hetype [Hecnt [Heptr [Hegrp Hetbl]]]]].
  unfold event_core_fields_layout_prop in Hlayout.
  destruct Hlayout as [Htypeaddr [Hptraddr Hcntaddr]].
  subst type_addr. subst ptr_addr. subst cnt_addr.
  subst etype. subst ecnt. subst eptr.
  subst base.
  unfold used_complete_event, used_event_rest_no_type_cnt_ptr.
  entailer!.
Qed.
Lemma mutex_accept_land_free_count__restore_and_returns :
  forall x : Z, Z.land (x * 256 + 255) 255 = 255.
Proof.
  intros x.
  replace 255 with (Z.ones 8) by
    (rewrite Z.ones_equiv; reflexivity).
  rewrite Z.land_ones by lia.
  replace (2 ^ 8) with 256 by reflexivity.
  rewrite Z.add_comm.
  rewrite Z.mod_add by lia.
  reflexivity.
Qed.
Lemma mutex_accept_land_low_byte__restore_and_returns :
  forall x y : Z,
    0 <= y < 256 -> Z.land (x * 256 + y) 255 = y.
Proof.
  intros x y Hy.
  replace 255 with (Z.ones 8) by
    (rewrite Z.ones_equiv; reflexivity).
  rewrite Z.land_ones by lia.
  replace (2 ^ 8) with 256 by reflexivity.
  rewrite Z.add_comm.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. exact Hy.
Qed.
Lemma mutex_accept_available_payload__restore_and_returns :
  forall sg tskSt evSt eid e etype ecnt eptr egrp etbl,
    valid_stable_glob_vars sg ->
    verification_slice_event_in_range sg tskSt evSt ->
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    etype = 4 ->
    Z.land ecnt 255 = 255 ->
    exists m,
      eventType e = OS_EVENT_TYPE_MUTEX /\
      mutexFields e = Some m /\
      mfOwner m = None /\
      mfOwnerOrigPrio m = None.
Proof.
  intros sg tskSt evSt eid e etype ecnt eptr egrp etbl
    Hvsg Hvalid Hsnap Htype Hfree.
  unfold event_snapshot_of_prop in Hsnap.
  destruct Hsnap as [Heid [Henc [Hcnt _]]].
  assert (Hetype : eventType e = OS_EVENT_TYPE_MUTEX).
  {
    destruct (eventType e) eqn:Ht;
      simpl in Henc;
      rewrite Htype in Henc;
      try discriminate;
      reflexivity.
  }
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [Hpayload _]]]]]].
  specialize (Hpayload eid e Heid).
  unfold event_payload_consistency in Hpayload.
  rewrite Hetype in Hpayload.
  destruct (mutexFields e) as [m |] eqn:Hmf; [|contradiction].
  exists m. split; [exact Hetype |]. split; [reflexivity |].
  destruct Hpayload as [Hmcons _].
  destruct (mfOwner m) as [owner |] eqn:Howner;
    destruct (mfOwnerOrigPrio m) as [op |] eqn:Horig.
  - unfold mutex_fields_consistency in Hmcons.
    rewrite Howner, Horig in Hmcons.
    destruct Hmcons as [Hop0 [Hoplt Hopceil]].
    unfold valid_stable_glob_vars in Hvsg.
    destruct Hvsg as [_ [_ [_ [_ [Hlowest [Hselected _]]]]]].
    exfalso.
    assert (Hop256 : 0 <= op < 256) by lia.
    rewrite Hcnt in Hfree.
    unfold encode_event_cnt_value in Hfree.
    rewrite Hetype, Hmf, Howner, Horig in Hfree.
    rewrite mutex_accept_land_low_byte__restore_and_returns in Hfree
      by exact Hop256.
    lia.
  - unfold mutex_fields_consistency in Hmcons.
    rewrite Howner, Horig in Hmcons. contradiction.
  - unfold mutex_fields_consistency in Hmcons.
    rewrite Howner, Horig in Hmcons. contradiction.
  - split; reflexivity.
Qed.
Lemma mutex_accept_unavailable_payload__restore_and_returns :
  forall sg tskSt evSt eid e etype ecnt eptr egrp etbl,
    verification_slice_event_in_range sg tskSt evSt ->
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    etype = 4 ->
    Z.land ecnt 255 <> 255 ->
    exists m,
      mutexFields e = Some m /\ mfOwner m <> None.
Proof.
  intros sg tskSt evSt eid e etype ecnt eptr egrp etbl
    Hvalid Hsnap Htype Hbusy.
  unfold event_snapshot_of_prop in Hsnap.
  destruct Hsnap as [Heid [Henc [Hcnt _]]].
  assert (Hetype : eventType e = OS_EVENT_TYPE_MUTEX).
  {
    destruct (eventType e) eqn:Ht;
      simpl in Henc;
      rewrite Htype in Henc;
      try discriminate;
      reflexivity.
  }
  unfold verification_slice_event_in_range, verification_slice_event_in_range,
    verification_slice_event_in_range in Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [Hpayload _]]]]]].
  specialize (Hpayload eid e Heid).
  unfold event_payload_consistency in Hpayload.
  rewrite Hetype in Hpayload.
  destruct (mutexFields e) as [m |] eqn:Hmf; [|contradiction].
  exists m. split; [reflexivity |].
  destruct Hpayload as [Hmcons _].
  destruct (mfOwner m) as [owner |] eqn:Howner;
    destruct (mfOwnerOrigPrio m) as [op |] eqn:Horig.
  - discriminate.
  - unfold mutex_fields_consistency in Hmcons.
    rewrite Howner, Horig in Hmcons. contradiction.
  - unfold mutex_fields_consistency in Hmcons.
    rewrite Howner, Horig in Hmcons. contradiction.
  - exfalso. apply Hbusy.
    rewrite Hcnt.
    unfold encode_event_cnt_value.
    rewrite Hetype, Hmf, Howner, Horig.
    apply mutex_accept_land_free_count__restore_and_returns.
Qed.
Lemma mutex_accept_event_rebuild__restore_and_returns :
  forall sg tskSt evSt eid e base type_addr ptr_addr cnt_addr
         etype ecnt eptr egrp etbl,
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    event_core_fields_layout_prop sg eid type_addr ptr_addr cnt_addr ->
    base = event_addr sg eid ->
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    used_event_rest_no_type_cnt_ptr sg tskSt base eid e **
    verification_slice_event_inv_no_eid sg tskSt evSt eid |--
    verification_slice_event_inv sg tskSt evSt.
Proof.
  intros sg tskSt evSt eid e base type_addr ptr_addr cnt_addr
    etype ecnt eptr egrp etbl Hsnap Hlayout Hbase.
  pose proof Hsnap as Hsnap0.
  unfold event_snapshot_of_prop in Hsnap0.
  destruct Hsnap0 as [Heid _].
  sep_apply_l_atomic
    (mutex_accept_complete_event__restore_and_returns
       sg tskSt evSt eid e base type_addr ptr_addr cnt_addr
       etype ecnt eptr egrp etbl Hsnap Hlayout Hbase).
  unfold verification_slice_event_inv, verification_slice_event_inv_no_eid.
  unfold store_used_event_map, store_used_event_map_missing_i.
  entailer!.
  sep_apply_l_atomic (store_map_merge
    (fun eid0 e0 => used_complete_event sg tskSt
      (event_addr sg eid0) eid0 e0)
    eid e (inUsedEventStates evSt) Heid).
  entailer!.
Qed.
Lemma mutex_accept_event_rebuild_residual__restore_and_returns :
  forall sg tskSt evSt eid e base type_addr ptr_addr cnt_addr
         etype ecnt eptr egrp etbl,
    verification_slice_event_in_range sg tskSt evSt ->
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    event_core_fields_layout_prop sg eid type_addr ptr_addr cnt_addr ->
    base = event_addr sg eid ->
    type_addr # UChar |-> etype **
    ptr_addr # Ptr |-> eptr **
    cnt_addr # UShort |-> ecnt **
    used_event_rest_no_type_cnt_ptr sg tskSt base eid e **
    store_used_event_map_missing_i
      sg tskSt (inUsedEventStates evSt) eid **
    store_free_event_list sg (unUsedEventStates evSt) |--
    verification_slice_event_inv sg tskSt evSt.
Proof.
  intros sg tskSt evSt eid e base type_addr ptr_addr cnt_addr
    etype ecnt eptr egrp etbl Hvalid Hsnap Hlayout Hbase.
  pose proof Hsnap as Hsnap0.
  unfold event_snapshot_of_prop in Hsnap0.
  destruct Hsnap0 as [Heid _].
  sep_apply_l_atomic
    (mutex_accept_complete_event__restore_and_returns
       sg tskSt evSt eid e base type_addr ptr_addr cnt_addr
       etype ecnt eptr egrp etbl Hsnap Hlayout Hbase).
  unfold verification_slice_event_inv, store_used_event_map, store_used_event_map_missing_i.
  entailer!.
  sep_apply_l_atomic (store_map_merge
    (fun eid0 e0 => used_complete_event sg tskSt
      (event_addr sg eid0) eid0 e0)
    eid e (inUsedEventStates evSt) Heid).
  entailer!.
Qed.
Lemma mutex_accept_safe_return__restore_and_returns :
  forall (A B : Type)
         (c : program UCOS2_Verify_State A)
         (observe : A -> program (UCOS2_Verify_State -> Prop) B)
         (ls0 ls2 : UCOS2_Verify_State) (ret : A) (n : B)
         (X : B -> (UCOS2_Verify_State -> Prop) -> Prop),
    c ls0 ret ls2 ->
    (forall P : UCOS2_Verify_State -> Prop, observe ret P n P) ->
    safeExec (LastSeen ls0)
      (bind (atomic_cmd c) observe) X ->
    safeExec (LastSeen ls2)
      (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) B n) X.
Proof.
  intros A B c observe ls0 ls2 retv n X Hsem Hobserve Hexec.
  assert (Hatomic : hs_eval (atomic_cmd c)
    (LastSeen ls0) (LastSeen ls2) retv).
  {
    unfold hs_eval, LastSeen, atomic_cmd.
    intros P0 HP0.
    exists (RTrans_Abs ls2).
    split.
    - exists ls0, ls2.
      split.
      + apply HP0. exact I.
      + split; [exact Hsem | reflexivity].
    - reflexivity.
  }
  pose proof (highstepbind_derive _ _ _ retv (LastSeen ls2)
    Hatomic X Hexec) as Hobs.
  eapply (highstependret_derive
    (observe retv) (LastSeen ls2) n
    (fun _ => LastSeen ls2)).
  2: exact Hobs.
  unfold hs_eval, LastSeen.
  intros P0 HP0.
  exists P0.
  split.
  - apply Hobserve.
  - exact HP0.
Qed.
Lemma mutex_accept_interrupt_rebuild__restore_and_returns :
  forall sg s isr,
    isr = intNesting s ->
    sg.(g_OSIntNesting) # UChar |-> isr **
    interrupt_inv_no_int_nesting sg s |--
    interrupt_inv sg s.
Proof.
  intros sg s isr Hisr.
  subst isr.
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  entailer!.
Qed.
Lemma mutex_accept_complete_task__restore_and_returns :
  forall sg st tid t tcb prio prio_addr,
    task_prio_snapshot_of_prop sg st tid t tcb prio ->
    task_prio_field_layout_prop tcb prio_addr ->
    prio_addr # UChar |-> prio **
    used_task_no_prio sg tcb tid t |--
    verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid) tid t.
Proof.
  intros sg st tid t tcb prio prio_addr Hsnap Hlayout.
  unfold task_prio_snapshot_of_prop in Hsnap.
  destruct Hsnap as [Htid [Htcb Hprio]].
  unfold task_prio_field_layout_prop in Hlayout.
  subst tcb. subst prio. subst prio_addr.
  unfold verification_slice_used_complete_task, used_task_no_prio.
  entailer!.
Qed.
Lemma mutex_accept_task_rebuild__restore_and_returns :
  forall sg st tid t tcb prio prio_addr,
    task_runnable_prio_snapshot_prop sg st tid t tcb prio ->
    task_prio_field_layout_prop tcb prio_addr ->
    prio_addr # UChar |-> prio **
    used_task_no_prio sg tcb tid t **
    verification_slice_task_inv_no_tid sg st tid |--
    verification_slice_task_inv sg st.
Proof.
  intros sg st tid t tcb prio prio_addr Hready Hlayout.
  unfold task_runnable_prio_snapshot_prop in Hready.
  destruct Hready as [Hsnap Hpend].
  pose proof Hsnap as Hsnap0.
  unfold task_prio_snapshot_of_prop in Hsnap0.
  destruct Hsnap0 as [Htid _].
  sep_apply_l_atomic
    (mutex_accept_complete_task__restore_and_returns
       sg st tid t tcb prio prio_addr Hsnap Hlayout).
  unfold verification_slice_task_inv, verification_slice_task_inv_no_tid.
  unfold verification_slice_store_used_task_map, verification_slice_store_used_task_map_missing_i.
  entailer!.
  sep_apply_l_atomic (store_map_merge
    (fun tid0 t0 => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t0)
    tid t (inUsedTaskStates st) Htid).
  entailer!.
Qed.
Lemma mutex_accept_sched_rebuild__restore_and_returns :
  forall sg st sched addr tcbcur,
    os_tcb_cur_addr sg addr ->
    verification_slice_sched_tcb_cur_snapshot_prop sg sched tcbcur ->
    addr # Ptr |-> tcbcur **
    verification_slice_sched_inv_no_tcb_cur sg st sched |--
    verification_slice_sched_inv sg st sched.
Proof.
  intros sg st sched addr tcbcur Haddr Hsnap.
  unfold os_tcb_cur_addr in Haddr.
  unfold verification_slice_sched_tcb_cur_snapshot_prop in Hsnap.
  subst addr. subst tcbcur.
  unfold verification_slice_sched_inv, verification_slice_sched_inv_no_tcb_cur.
  unfold verification_slice_store_sched_state, verification_slice_store_sched_state_no_tcb_cur.
  entailer!.
Qed.
Lemma mutex_accept_acquire_event_rebuild__restore_and_returns :
  forall sg tskSt evSt eid e m tid prio tcbcur base
         type_addr ptr_addr cnt_addr ecnt egrp etbl,
    verification_slice_event_in_range sg tskSt
      (owner_acquire_update evSt eid e m tid prio) ->
    event_snapshot_of_prop sg tskSt
      (owner_acquire_update evSt eid e m tid prio) eid
      {| eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType := eventType e;
         mutexFields := Some
           {| mfPCP := mfPCP m; mfOwner := Some tid;
              mfOwnerOrigPrio := Some prio |};
         semFields := semFields e; mboxFields := mboxFields e;
         queueFields := queueFields e;
         waitList := waitList e |}
      4 ecnt tcbcur egrp etbl ->
    tcbcur = verification_slice_tcb_addr sg tid ->
    event_core_fields_layout_prop sg eid
      type_addr ptr_addr cnt_addr ->
    base = event_addr sg eid ->
    type_addr # UChar |-> 4 **
    ptr_addr # Ptr |-> tcbcur **
    cnt_addr # UShort |-> ecnt **
    used_event_rest_no_type_cnt_ptr sg tskSt base eid e **
    store_used_event_map_missing_i sg tskSt
      (inUsedEventStates (owner_acquire_update evSt eid e m tid prio)) eid **
    store_free_event_list sg
      (unUsedEventStates (owner_acquire_update evSt eid e m tid prio)) |--
    verification_slice_event_inv sg tskSt (owner_acquire_update evSt eid e m tid prio).
Proof.
  intros sg tskSt evSt eid e m tid prio tcbcur base
    type_addr ptr_addr cnt_addr ecnt egrp etbl
    Hvalid Hsnap Htcb Hlayout Hbase.
  change (
    type_addr # UChar |-> 4 **
    ptr_addr # Ptr |-> tcbcur **
    cnt_addr # UShort |-> ecnt **
    used_event_rest_no_type_cnt_ptr sg tskSt base eid
      {| eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType := eventType e;
         mutexFields := Some
           {| mfPCP := mfPCP m; mfOwner := Some tid;
              mfOwnerOrigPrio := Some prio |};
         semFields := semFields e; mboxFields := mboxFields e;
         queueFields := queueFields e;
         waitList := waitList e |} **
    store_used_event_map_missing_i sg tskSt
      (inUsedEventStates (owner_acquire_update evSt eid e m tid prio)) eid **
    store_free_event_list sg
      (unUsedEventStates (owner_acquire_update evSt eid e m tid prio)) |--
    verification_slice_event_inv sg tskSt (owner_acquire_update evSt eid e m tid prio)).
  sep_apply_l_atomic
    (mutex_accept_event_rebuild_residual__restore_and_returns
      sg tskSt (owner_acquire_update evSt eid e m tid prio) eid
      {| eventGeneration := e.(eventGeneration);
         eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19);
         eventType := eventType e;
         mutexFields := Some
           {| mfPCP := mfPCP m; mfOwner := Some tid;
              mfOwnerOrigPrio := Some prio |};
         semFields := semFields e; mboxFields := mboxFields e;
         queueFields := queueFields e;
         waitList := waitList e |}
      base type_addr ptr_addr cnt_addr 4 ecnt tcbcur
      egrp etbl Hvalid Hsnap Hlayout Hbase).
  entailer!.
Qed.

Lemma mutex_accept_task_inv_valid_prio__restore_and_returns :
  forall sg st tid t tcb prio,
    task_runnable_prio_snapshot_prop sg st tid t tcb prio ->
    verification_slice_task_inv sg st |-- “ valid_task_prio sg prio ”.
Proof.
  intros sg st tid t tcb prio Hready h Hinv.
  unfold coq_prop.
  unfold verification_slice_task_inv, andp, coq_prop in Hinv.
  destruct Hinv as [Hvalid _].
  unfold verification_slice_task_validity in Hvalid.
  destruct Hvalid as [_ Hall].
  unfold task_runnable_prio_snapshot_prop,
    task_prio_snapshot_of_prop in Hready.
  destruct Hready as [[Hlookup [_ Hprio]] _].
  specialize (Hall tid t Hlookup).
  destruct Hall as [Hvalidprio _].
  rewrite Hprio.
  exact Hvalidprio.
Qed.
