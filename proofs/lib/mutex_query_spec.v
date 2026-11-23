Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.array_abstraction.
From SimpleC.SL Require Import SeparationLogic.

Import ListNotations.
Import UCOS2_C_Rules.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Before the handle guards, no Event has been removed from the heap. *)
Definition mutex_query_whole_frame
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  UCOS2_raw_rep_missing_module sg s InterruptModule.

(** Once the lookup is known, retain every other module and every other ECB.
    Task storage (including parked stacks), scheduler and tick remain opaque. *)
Definition mutex_query_raw_frame
  (sg : StableGlobVars) (s : UCOS2_Verify_State) (eid : EventID) : Assertion :=
  UCOS2_raw_rep_missing_two sg s InterruptModule EventModule **
  event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid.

(** Query never reads the owner pointer, padding, or optional name.  Keep their
    current full-profile encoding; the legacy snapshot pointer is not used as
    a physical pointer value. *)
Definition mutex_query_event_unread
  (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  event_cell (event_addr sg eid) EventPadding1 e.(eventPadding1) **
  event_cell (event_addr sg eid) EventPadding2 e.(eventPadding2) **
  event_cell (event_addr sg eid) EventPadding3 e.(eventPadding3) **
  event_cell (event_addr sg eid) EventPtrField (Some (encode_event_ptr_value sg e)) **
  event_cell (event_addr sg eid) EventPadding19 e.(eventPadding19) **
  (if sg.(osKernelConfig).(cfgEventNames)
   then event_cell (event_addr sg eid) EventNameField (Some e.(eventName))
   else emp).

(** Coq propositions embedded with separating conjunction leave real [TT]
    heap tails.  Several such tails may be combined, never discarded. *)
Lemma mutex_query_truep_sepcon_merge : (TT ** TT) |-- TT.
Proof. apply derivable1_truep_intros. Qed.

Lemma mutex_query_truep_sepcon_equiv : (TT ** TT) --||-- TT.
Proof.
  split; [apply mutex_query_truep_sepcon_merge|].
  apply sepcon_cancel_res_emp.
  apply derivable1_truep_intros.
Qed.

Lemma mutex_query_whole_frame_split_event : forall sg s eid e,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  mutex_query_whole_frame sg s |--
    used_event_rep sg s.(TskState) eid e ** mutex_query_raw_frame sg s eid.
Proof.
  intros sg s eid e Hget.
  unfold mutex_query_whole_frame, mutex_query_raw_frame.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg s
    InterruptModule EventModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  sep_apply_l_atomic (event_raw_rep_split_eid sg s.(TskState) s.(EventState) eid e Hget).
  entailer!.
Qed.

Lemma mutex_query_whole_frame_merge_event : forall sg s eid e,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  used_event_rep sg s.(TskState) eid e ** mutex_query_raw_frame sg s eid |--
    mutex_query_whole_frame sg s.
Proof.
  intros sg s eid e Hget.
  unfold mutex_query_whole_frame, mutex_query_raw_frame.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg s
    InterruptModule EventModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  sep_apply_l_atomic (event_raw_rep_merge_eid sg s.(TskState) s.(EventState) eid e Hget).
  entailer!.
Qed.

Lemma mutex_query_event_rep_read_fields_equiv : forall sg s eid e,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  used_event_rep sg s.(TskState) eid e --||--
  (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type e.(eventType) **
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value e **
  used_event_rest_no_type_cnt_ptr sg s.(TskState) (event_addr sg eid) eid e **
  mutex_query_event_unread sg s.(TskState) eid e.
Proof.
  intros sg s eid e Hstate Hget.
  assert (Hunique : task_priority_unique s.(TskState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, task_in_range in Hstate.
    tauto. }
  assert (Hcanonical : event_waitList_canonical sg s.(TskState) e.(waitList)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hstate.
    destruct Hstate as [_ [_ [_ [Hevents _]]]].
    unfold event_in_range in Hevents.
    destruct Hevents as [_ [_ [_ [_ [_ [_ Hwait]]]]]].
    exact (proj1 (Hwait eid e Hget)). }
  assert (Hencode : forall row,
    encode_event_wait_tbl_at e.(waitList) s.(TskState) row =
    encode_event_wait_tbl_at_or e.(waitList) s.(TskState) row).
  { intros row.
    destruct Hcanonical as [Hnodup [_ Hrange]].
    apply encode_event_wait_tbl_at_eq_or; auto.
    intros tid task Hin Hlookup.
    destruct (Hrange tid Hin) as [found [Hfound Hbound]].
    rewrite Hlookup in Hfound; injection Hfound as Heq; subst found.
    exact (proj1 Hbound). }
  unfold used_event_rep, event_storage_rep, event_fields.
  destruct (cfgEventNames (osKernelConfig sg)) eqn:Hnames;
    cbn [app];
    repeat rewrite EventFieldStorage.store_fields_cons by
      (repeat constructor; simpl; intuition discriminate);
    rewrite EventFieldStorage.store_fields_nil;
    unfold used_event_rest_no_type_cnt_ptr, mutex_query_event_unread;
    rewrite Hnames;
    cbn [event_image event_cell event_field_offset];
    rewrite !Hencode;
    unfold OSEventType_off, OSEventCnt_off, OSEventGrp_off, OSEventTbl_off;
    split; entailer!.
  all: rewrite <- !Z.add_assoc; entailer!.
Qed.

(* ================================================================== *)
(* L5: complete source-order semantics of OSMutexQuery                 *)
(* ================================================================== *)

(* The first true guard determines the observable return code.  The event
   type is consulted only after the ISR and null-pointer checks, exactly as
   in the executable C source. *)
Definition mutex_query_result_prop
  (isr pevent p_mutex_data etype ret : Z) : Prop :=
  (isr > 0 /\ ret = 6) \/
  (isr <= 0 /\ pevent = 0 /\ ret = 4) \/
  (isr <= 0 /\ pevent <> 0 /\ p_mutex_data = 0 /\ ret = 9) \/
  (isr <= 0 /\ pevent <> 0 /\ p_mutex_data <> 0 /\
   etype <> 4 /\ ret = 1) \/
  (isr <= 0 /\ pevent <> 0 /\ p_mutex_data <> 0 /\
   etype = 4 /\ ret = 0).

(* OSMutexQuery reads the kernel snapshot while inside the critical section;
   neither critical transition changes the abstract kernel state. *)
Definition mutex_query_critical_transition_prop
  (ls0 ls_inside ls_restored : UCOS2_Verify_State) : Prop :=
  crit_rel_no_os_state_change ls0 ls_inside /\
  crit_rel_no_os_state_change ls_inside ls_restored /\
  ls_restored = ls0.

(* Compatibility name for the accepted Query source_goal_version.  The
   representation fact is canonically owned by event.v and shared by all
   event clients; new annotation must use the name on the right. *)
Notation mutex_query_event_wait_layout_prop :=
  event_wait_fields_layout_prop (only parsing).

Lemma store_array_missing_index_bounds__array_loop_and_returns :
  forall (A : Type) (storeA : Z -> Z -> A -> UCOS2_C_Rules.expr)
         (x i lo hi : Z) (l : list A),
    derivable1 (store_array_missing_i_rec storeA x i lo hi l)
      (coq_prop (lo <= i < hi)).
Proof.
  intros A storeA x i lo hi l.
  revert i lo hi.
  induction l as [| a l IH]; intros i lo hi; simpl.
  - entailer!.
  - Split; Intros.
    + prop_apply (store_array_rec_Zlength A storeA x (lo + 1) hi l).
      Intros_p Hlen.
      rewrite Zlength_correct in Hlen.
      simpl in Hlen.
      entailer!.
    + prop_apply (IH i (lo + 1) hi).
      entailer!.
Qed.
Lemma list_copy_prefix_step__array_loop_and_returns :
  forall (A : Type) (src dst : list A) (i : Z) (d : A),
    0 <= i < Zlength src ->
    Zlength (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) dst) =
      Zlength src ->
    replace_Znth i (Znth i src d)
      (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) dst) =
      firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) dst.
Proof.
  intros A src dst i d Hi Hlen.
  unfold Znth, replace_Znth.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  assert (Hnat :
    forall (n : nat) (xs ys : list A),
      (n < length xs)%nat ->
      length (firstn n xs ++ skipn n ys) = length xs ->
      replace_nth n (firstn n xs ++ skipn n ys) (nth n xs d) =
        firstn (S n) xs ++ skipn (S n) ys).
  {
    induction n as [| n IH]; intros xs ys Hbound Hsame.
    - destruct xs as [| x xs]; [simpl in Hbound; lia |].
      destruct ys as [| y ys]; [simpl in Hsame; lia |].
      reflexivity.
    - destruct xs as [| x xs]; [simpl in Hbound; lia |].
      destruct ys as [| y ys].
      + simpl in Hsame, Hbound.
        rewrite app_length, firstn_length in Hsame.
        rewrite Nat.min_l in Hsame by lia.
        apply Nat.succ_lt_mono in Hbound.
        injection Hsame as Heq.
        simpl in Heq.
        lia.
      + simpl in Hbound, Hsame |- *.
        f_equal.
        apply IH; lia.
  }
  apply Hnat.
  - rewrite Zlength_correct in Hi.
    lia.
  - rewrite !Zlength_correct in Hlen.
    lia.
Qed.
Lemma list_copy_prefix_complete_at_bound__array_loop_and_returns :
  forall (A : Type) (src dst : list A) (i : Z),
    Zlength src <= i ->
    Zlength (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) dst) =
      Zlength src ->
    firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) dst = src.
Proof.
  intros A src dst i Hi Hlen.
  rewrite Zlength_correct in Hi.
  assert (Hfirst : firstn (Z.to_nat i) src = src).
  {
    apply firstn_all2.
    apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia.
    exact Hi.
  }
  rewrite Hfirst in Hlen |- *.
  destruct (skipn (Z.to_nat i) dst) as [| a l] eqn:Hskip.
  - apply app_nil_r.
  - rewrite !Zlength_correct, length_app in Hlen.
    simpl in Hlen.
    lia.
Qed.
Lemma store_array_Zlength__array_loop_and_returns :
  forall (A : Type) (storeA : Z -> Z -> A -> UCOS2_C_Rules.expr)
         (base n : Z) (l : list A),
    derivable1 (store_array storeA base n l)
      (coq_prop (Zlength l = n)).
Proof.
  intros A storeA base n l.
  unfold store_array.
  prop_apply (store_array_rec_Zlength A storeA base 0 n l).
  entailer!.
Qed.
Lemma mutex_query_table_group_to_event_rest__array_loop_and_returns :
  forall sg tskSt evSt eid e base grp_addr
         etype ecnt eptr egrp etbl,
    event_snapshot_of_prop sg tskSt evSt eid e
      etype ecnt eptr egrp etbl ->
    grp_addr = event_addr sg eid + OSEventGrp_off ->
    base = event_addr sg eid ->
    derivable1
      (sepcon
        (store_array
          (fun array_base idx value =>
             store_uchar (array_base + idx * 1) value)
          (base + OSEventTbl_off) 8 etbl)
        (store_uchar grp_addr egrp))
      (used_event_rest_no_type_cnt_ptr sg tskSt base eid e).
Proof.
  intros sg tskSt evSt eid e base grp_addr
    etype ecnt eptr egrp etbl Hsnap Hgrpaddr Hbase.
  unfold event_snapshot_of_prop in Hsnap.
  destruct Hsnap as [_ [_ [_ [_ [Hegrp Hetbl]]]]].
  subst base. subst grp_addr. subst egrp. subst etbl.
  unfold store_array.
  unfold used_event_rest_no_type_cnt_ptr.
  unfold encode_event_wait_tbl_values.
  simpl.
  entailer!.
Qed.

Lemma mutex_query_event_read_fields_merge :
  forall sg s eid e base type_addr cnt_addr etype cnt eptr grp tbl ptr_addr,
  UCOS2_state_inv sg s ->
  event_snapshot_of_prop sg s.(TskState) s.(EventState) eid e
    etype cnt eptr grp tbl ->
  event_core_fields_layout_prop sg eid type_addr ptr_addr cnt_addr ->
  base = event_addr sg eid ->
  type_addr # UChar |-> etype ** cnt_addr # UShort |-> cnt **
  used_event_rest_no_type_cnt_ptr sg s.(TskState) base eid e **
  mutex_query_event_unread sg s.(TskState) eid e |--
  used_event_rep sg s.(TskState) eid e.
Proof.
  intros sg s eid e base type_addr cnt_addr etype cnt eptr grp tbl ptr_addr
    Hstate Hsnapshot Hlayout Hbase.
  destruct Hsnapshot as [Hget [Htype [Hcnt _]]].
  destruct Hlayout as [Htypeaddr [_ Hcntaddr]].
  rewrite Hbase, Htypeaddr, Hcntaddr, Htype, Hcnt.
  apply (proj2 (mutex_query_event_rep_read_fields_equiv sg s eid e Hstate Hget)).
Qed.

Lemma mutex_query_frame_merge_inv : forall sg s eid e,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e ->
  interrupt_inv sg s.(IntrState) ** used_event_rep sg s.(TskState) eid e **
  mutex_query_raw_frame sg s eid |-- UCOS2_inv sg s.
Proof.
  intros sg s eid e Hstate Hget.
  sep_apply_l_atomic (mutex_query_whole_frame_merge_event sg s eid e Hget).
  unfold UCOS2_inv, mutex_query_whole_frame.
  rewrite (UCOS2_raw_rep_split_module sg s InterruptModule).
  cbn [UCOS2_module_rep]; entailer!.
Qed.

(** Source-order Query call semantics. The ISR/null/type guards observe
    [before]; the protected copy observes the fresh state acquired by Save.
    Query itself makes no kernel-state update after acquisition. *)
Definition mutex_query_observe_error (code : Z)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun initial observed final => observed = code /\ final = initial.

Definition mutex_query_lookup (s : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) : Prop := s.(EventState).(inUsedEventStates) eid = Some e.

(** Explicit caller lifetime protocol: foreign clients may change payload,
    waiters and other modules, but do not delete/reuse/retype this live handle.
    This is not supplied by the CPU primitive or asserted as a kernel axiom. *)
Definition mutex_query_handle_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) : Prop :=
  forall action before after previous,
    critical_region_clients critical action ->
    kernel_client_actor action <> Some invocation ->
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    mutex_query_lookup before eid previous ->
    exists current, mutex_query_lookup after eid current /\
      current.(eventGeneration) = previous.(eventGeneration) /\
      current.(eventType) = previous.(eventType).

Lemma mutex_query_handle_interval_preserves_identity :
  forall critical sg invocation eid before after previous,
  mutex_query_handle_protocol critical sg invocation eid ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before -> mutex_query_lookup before eid previous ->
  exists current, mutex_query_lookup after eid current /\
    current.(eventGeneration) = previous.(eventGeneration) /\
    current.(eventType) = previous.(eventType).
Proof.
  intros critical sg invocation eid before after previous Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval; revert previous.
  induction Hinterval as
    [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros previous Hvalid Hlookup.
  - exists previous; repeat split; assumption || reflexivity.
  - destruct (Hprotocol action before middle previous Hin Hforeign Hvalid Hstep Hlookup)
      as [next [Hnext [Hgen Htype]]].
    pose proof (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action Hin)
      sg before middle Hvalid Hstep) as Hmiddle.
    destruct (IH next Hmiddle Hnext) as [current [Hcurrent [Hgen' Htype']]].
    exists current; split; [exact Hcurrent|]; split; congruence.
Qed.

Definition mutex_query_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation state).

Lemma mutex_query_closed_equiv : forall platform critical sg invocation origin mask state,
  mutex_query_closed platform critical sg invocation origin mask state --||--
    (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg state).
Proof.
  intros; unfold mutex_query_closed, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  unfold UCOS2_inv; split; entailer!.
Qed.

Lemma mutex_query_closed_save_pre : forall platform critical sg invocation origin mask state,
  mutex_query_closed platform critical sg invocation origin mask state |--
    interrupt_platform_running platform invocation origin mask **
    critical_region_outside critical sg invocation state.
Proof. intros; unfold mutex_query_closed; entailer!. Qed.

Definition mutex_query_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  mutex_query_lookup before eid observed /\ mutex_query_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_MUTEX /\
  current.(eventType) = OS_EVENT_TYPE_MUTEX /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma mutex_query_save_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed,
  mutex_query_handle_protocol critical sg invocation eid ->
  UCOS2_state_inv sg before -> mutex_query_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_MUTEX ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_raw_rep sg entry |--
  EX current, coq_prop (mutex_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current) &&
    (critical_region_masked platform critical sg invocation origin saved entry **
     UCOS2_inv sg entry).
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed
    Hprotocol Hvalid Hlookup Htype Hinterval Hsaved.
  destruct (mutex_query_handle_interval_preserves_identity critical sg invocation eid
    before entry observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgeneration HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : mutex_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current).
  { unfold mutex_query_acquire_facts.
    split; [exact Hinterval|]; split; [exact Hentry|]; split; [exact Hsaved|].
    split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
    split; [congruence|exact Hgeneration]. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Definition mutex_query_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (entry : UCOS2_Verify_State) : Assertion :=
  critical_region_masked platform critical sg invocation origin saved entry **
  UCOS2_inv sg entry.

Lemma mutex_query_restore_pre_exposes_saved_token :
  forall platform critical sg invocation origin saved entry,
  mutex_query_restore_pre platform critical sg invocation origin saved entry --||--
    (interrupt_platform_running platform invocation origin 192 **
     interrupt_platform_saved platform (save_token saved invocation origin) **
     critical_region_inside critical sg invocation entry ** UCOS2_inv sg entry).
Proof.
  intros; unfold mutex_query_restore_pre, critical_region_masked; split; entailer!.
Qed.

Lemma mutex_query_restore_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed current,
  mutex_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation entry |--
  mutex_query_closed platform critical sg invocation origin mask entry.
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed current
    [_ [Hentry [[Hsaved Hmask] _]]].
  rewrite Hmask; unfold mutex_query_closed; entailer!.
Qed.

Definition mutex_query_type_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (observed : OSEventAbstractState) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) observed) EventTypeField **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  UCOS2_raw_rep_missing_module sg state EventModule.

Lemma mutex_query_type_split_full : forall sg state eid observed,
  mutex_query_lookup state eid observed ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type observed.(eventType) **
     mutex_query_type_frame sg state eid observed).
Proof.
  intros sg state eid observed Hlookup.
  rewrite (UCOS2_inv_split_module sg state EventModule); Intros.
  cbn [UCOS2_module_rep].
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState)
    eid observed Hlookup).
  unfold used_event_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) observed) EventTypeField
    ltac:(simpl; tauto)).
  cbn [event_image event_cell event_field_offset].
  unfold mutex_query_type_frame, OSEventType_off; entailer!.
Qed.

Lemma mutex_query_type_merge_full : forall sg state eid observed,
  UCOS2_state_inv sg state -> mutex_query_lookup state eid observed ->
  (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type observed.(eventType) **
    mutex_query_type_frame sg state eid observed |-- UCOS2_inv sg state.
Proof.
  intros sg state eid observed Hvalid Hlookup.
  unfold mutex_query_type_frame.
  eapply derivable1_trans with (event_cell (event_addr sg eid) EventTypeField
    ((event_image sg state.(TskState) observed) EventTypeField) **
    event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg state.(TskState) observed) EventTypeField **
    event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
    UCOS2_raw_rep_missing_module sg state EventModule).
  { cbn [event_image event_cell event_field_offset]; unfold OSEventType_off; entailer!. }
  sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) observed) EventTypeField
    ltac:(simpl; tauto)).
  fold (used_event_rep sg state.(TskState) eid observed).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg state.(TskState) state.(EventState)
    eid observed Hlookup).
  rewrite (UCOS2_inv_split_module sg state EventModule).
  cbn [UCOS2_module_rep]; entailer!.
Qed.

Lemma mutex_query_encoded_type_is_mutex : forall observed,
  encode_event_type observed.(eventType) = 4 -> observed.(eventType) = OS_EVENT_TYPE_MUTEX.
Proof. intros observed H; destruct observed.(eventType); simpl in H; try lia; reflexivity. Qed.

Definition mutex_query_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent pdata : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  before.(IntrState).(intNesting) > 0 \/
  (before.(IntrState).(intNesting) <= 0 /\
    (pevent = 0 \/ (pevent <> 0 /\ pdata = 0) \/
     (pevent <> 0 /\ pdata <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
      mutex_query_lookup before eid observed /\
      (observed.(eventType) = OS_EVENT_TYPE_MUTEX ->
        mutex_query_handle_protocol critical sg invocation eid)))).

Definition mutex_query_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent pdata : addr)
  : program UCOS2_Verify_State Z :=
  fun before code after =>
    (before.(IntrState).(intNesting) > 0 /\ code = 6 /\ after = before) \/
    (before.(IntrState).(intNesting) <= 0 /\ pevent = 0 /\ code = 4 /\ after = before) \/
    (before.(IntrState).(intNesting) <= 0 /\ pevent <> 0 /\ pdata = 0 /\
       code = 9 /\ after = before) \/
    (before.(IntrState).(intNesting) <= 0 /\ pevent <> 0 /\ pdata <> 0 /\
     exists eid observed,
       pevent = event_addr sg eid /\ valid_event_id sg eid /\
       mutex_query_lookup before eid observed /\
       ((observed.(eventType) <> OS_EVENT_TYPE_MUTEX /\ code = 1 /\ after = before) \/
        (observed.(eventType) = OS_EVENT_TYPE_MUTEX /\ exists entry current,
         critical_region_interval critical sg invocation before entry /\
         mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_MUTEX /\
         current.(eventGeneration) = observed.(eventGeneration) /\ code = 0 /\ after = entry))).

Definition mutex_query_call_post_prop critical sg invocation pevent pdata before code after : Prop :=
  mutex_query_call_program critical sg invocation pevent pdata before code after.

Lemma mutex_query_call_input_live : forall critical sg invocation pevent pdata before eid observed,
  mutex_query_call_input critical sg invocation pevent pdata before eid observed ->
  before.(IntrState).(intNesting) <= 0 -> pevent <> 0 -> pdata <> 0 ->
  pevent = event_addr sg eid /\ valid_event_id sg eid /\ mutex_query_lookup before eid observed /\
  (observed.(eventType) = OS_EVENT_TYPE_MUTEX -> mutex_query_handle_protocol critical sg invocation eid).
Proof.
  intros critical sg invocation pevent pdata before eid observed Hinput Hisr Hpe Hpd.
  destruct Hinput as [Hpositive|[_ [Hnull|[[_ Hdata]|[_ [_ Hlive]]]]]];
    try lia; try contradiction; exact Hlive.
Qed.

Lemma mutex_query_call_success :
  forall critical sg invocation pevent pdata before eid observed mask saved entry current,
  before.(IntrState).(intNesting) <= 0 -> pevent <> 0 -> pdata <> 0 ->
  pevent = event_addr sg eid -> valid_event_id sg eid ->
  mutex_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  mutex_query_call_program critical sg invocation pevent pdata before 0 entry.
Proof.
  intros critical sg invocation pevent pdata before eid observed mask saved entry current
    Hisr Hpe Hpd Haddr Hid [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]].
  unfold mutex_query_call_program; right; right; right.
  split; [exact Hisr|]; split; [exact Hpe|]; split; [exact Hpd|].
  exists eid, observed; split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hbefore|].
  right; split; [exact Htype|]; exists entry, current; repeat split; assumption || reflexivity.
Qed.

Lemma mutex_query_call_program_preserves_validity :
  forall critical sg invocation pevent pdata before code after,
  UCOS2_state_inv sg before ->
  mutex_query_call_program critical sg invocation pevent pdata before code after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation pevent pdata before code after Hvalid Hprogram.
  unfold mutex_query_call_program in Hprogram.
  destruct Hprogram as [Hisr | Hprogram].
  - destruct Hisr as [_ [_ ->]]; exact Hvalid.
  - destruct Hprogram as [Hnull | Hprogram].
    + destruct Hnull as [_ [_ [_ ->]]]; exact Hvalid.
    + destruct Hprogram as [Hpdata | Hprogram].
      * destruct Hpdata as [_ [_ [_ [_ ->]]]]; exact Hvalid.
      * destruct Hprogram as [_ [_ [_ [eid [observed [_ [_ [_ Hbranch]]]]]]]].
        destruct Hbranch as [Hwrong | Hsuccess].
        -- destruct Hwrong as [_ [_ ->]]; exact Hvalid.
        -- destruct Hsuccess as [_ [entry [current Hentry]]].
           destruct Hentry as [Hinterval [_ [_ [_ [_ ->]]]]].
           exact (proj1 (critical_region_interval_transports_resources
             critical sg invocation before entry Hinterval Hvalid)).
Qed.

Definition mutex_query_copy_snapshot (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) (count group : Z)
  (table : list Z) : Prop :=
  mutex_query_lookup entry eid current /\
  count = encode_event_cnt_value current /\
  group = encode_event_wait_grp current.(waitList) entry.(TskState) /\
  table = encode_event_wait_tbl_values current entry.(TskState).

Lemma mutex_query_interrupt_split_full : forall sg state,
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    (sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
     interrupt_inv_no_int_nesting sg state.(IntrState) ** mutex_query_whole_frame sg state).
Proof.
  intros; unfold UCOS2_inv, mutex_query_whole_frame.
  rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state; entailer!.
Qed.

Lemma mutex_query_interrupt_merge_full : forall sg state isr,
  UCOS2_state_inv sg state -> isr = state.(IntrState).(intNesting) ->
  sg.(g_OSIntNesting) # UChar |-> isr **
    interrupt_inv_no_int_nesting sg state.(IntrState) ** mutex_query_whole_frame sg state
  |-- UCOS2_inv sg state.
Proof.
  intros sg state isr Hvalid ->; unfold UCOS2_inv, mutex_query_whole_frame.
  rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state; entailer!.
Qed.

Lemma mutex_query_copy_fields_split_full : forall sg entry eid current,
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_MUTEX ->
  UCOS2_inv sg entry |--
  EX count group table,
    coq_prop (UCOS2_state_inv sg entry /\ mutex_query_copy_snapshot entry eid current count group table) &&
    (interrupt_inv sg entry.(IntrState) **
     (event_addr sg eid + OSEventType_off) # UChar |-> 4 **
     (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
     used_event_rest_no_type_cnt_ptr sg entry.(TskState) (event_addr sg eid) eid current **
     mutex_query_event_unread sg entry.(TskState) eid current **
     mutex_query_raw_frame sg entry eid).
Proof.
  intros sg entry eid current Hlookup Htype.
  rewrite (UCOS2_inv_split_module sg entry InterruptModule); Intros.
  cbn [UCOS2_module_rep]; fold (mutex_query_whole_frame sg entry).
  sep_apply_l_atomic (mutex_query_whole_frame_split_event sg entry eid current Hlookup).
  match goal with Hvalid : UCOS2_state_inv sg entry |- _ =>
    sep_apply_l_atomic (proj1 (mutex_query_event_rep_read_fields_equiv
      sg entry eid current Hvalid Hlookup)) end.
  rewrite Htype; cbn [encode_event_type].
  Exists (encode_event_cnt_value current)
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (encode_event_wait_tbl_values current entry.(TskState)).
  unfold mutex_query_copy_snapshot; entailer!.
Qed.

Lemma mutex_query_copy_table_group_merge : forall sg entry eid current base group_addr count group table,
  mutex_query_copy_snapshot entry eid current count group table ->
  base = event_addr sg eid -> group_addr = event_addr sg eid + OSEventGrp_off ->
  store_oseventtbl sg base table ** group_addr # UChar |-> group |--
  used_event_rest_no_type_cnt_ptr sg entry.(TskState) base eid current.
Proof.
  intros sg entry eid current base group_addr count group table [_ [_ [Hgroup Htable]]] Hbase Haddr.
  subst base group_addr group table.
  unfold store_oseventtbl, store_array, oseventtbl_element_store,
    used_event_rest_no_type_cnt_ptr, encode_event_wait_tbl_values,
    sizeof_OS_PRIO, OS_EVENT_TBL_SIZE.
  simpl; entailer!.
Qed.

Lemma mutex_query_copy_table_group_split : forall sg entry eid current base group_addr count group table,
  mutex_query_copy_snapshot entry eid current count group table ->
  base = event_addr sg eid -> group_addr = event_addr sg eid + OSEventGrp_off ->
  used_event_rest_no_type_cnt_ptr sg entry.(TskState) base eid current |--
  store_oseventtbl sg base table ** group_addr # UChar |-> group.
Proof.
  intros sg entry eid current base group_addr count group table [_ [_ [Hgroup Htable]]] Hbase Haddr.
  subst base group_addr group table.
  unfold store_oseventtbl, store_array, oseventtbl_element_store,
    used_event_rest_no_type_cnt_ptr, encode_event_wait_tbl_values,
    sizeof_OS_PRIO, OS_EVENT_TBL_SIZE.
  simpl; entailer!.
Qed.

Lemma mutex_query_copy_fields_merge_full :
  forall sg entry eid current base type_addr count_addr count group table,
  UCOS2_state_inv sg entry ->
  mutex_query_copy_snapshot entry eid current count group table ->
  current.(eventType) = OS_EVENT_TYPE_MUTEX ->
  base = event_addr sg eid -> type_addr = event_addr sg eid + OSEventType_off ->
  count_addr = event_addr sg eid + OSEventCnt_off ->
  interrupt_inv sg entry.(IntrState) ** type_addr # UChar |-> 4 ** count_addr # UShort |-> count **
    used_event_rest_no_type_cnt_ptr sg entry.(TskState) base eid current **
    mutex_query_event_unread sg entry.(TskState) eid current ** mutex_query_raw_frame sg entry eid
  |-- UCOS2_inv sg entry.
Proof.
  intros sg entry eid current base type_addr count_addr count group table
    Hvalid [Hlookup [Hcount _]] Htype Hbase Htypeaddr Hcntaddr.
  rewrite Hbase, Htypeaddr, Hcntaddr, Hcount.
  pose proof (proj2 (mutex_query_event_rep_read_fields_equiv sg entry eid current Hvalid Hlookup))
    as Hmerge.
  rewrite Htype in Hmerge; cbn [encode_event_type] in Hmerge.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (mutex_query_frame_merge_inv sg entry eid current Hvalid Hlookup).
  entailer!.
Qed.

Lemma mutex_query_call_isr_return : forall critical sg invocation pevent pdata before,
  before.(IntrState).(intNesting) > 0 ->
  mutex_query_call_program critical sg invocation pevent pdata before 6 before.
Proof. intros; left; auto. Qed.

Lemma mutex_query_call_null_event_return : forall critical sg invocation pdata before,
  before.(IntrState).(intNesting) <= 0 ->
  mutex_query_call_program critical sg invocation 0 pdata before 4 before.
Proof. intros; right; left; auto. Qed.

Lemma mutex_query_call_null_data_return : forall critical sg invocation pevent before,
  before.(IntrState).(intNesting) <= 0 -> pevent <> 0 ->
  mutex_query_call_program critical sg invocation pevent 0 before 9 before.
Proof. intros; right; right; left; auto. Qed.

Lemma mutex_query_call_wrong_type_return : forall critical sg invocation pevent pdata before eid observed,
  before.(IntrState).(intNesting) <= 0 -> pevent <> 0 -> pdata <> 0 ->
  pevent = event_addr sg eid -> valid_event_id sg eid -> mutex_query_lookup before eid observed ->
  observed.(eventType) <> OS_EVENT_TYPE_MUTEX ->
  mutex_query_call_program critical sg invocation pevent pdata before 1 before.
Proof.
  intros critical sg invocation pevent pdata before eid observed Hisr Hpe Hpd Haddr Hid Hlookup Htype.
  right; right; right; split; [exact Hisr|]; split; [exact Hpe|]; split; [exact Hpd|].
  exists eid, observed; split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hlookup|].
  left; auto.
Qed.

(** Exact caller-owned scalar output cells, in the same QCP arrow vocabulary
    as the selected C. This is not a second ECB layout interpretation. *)
Definition mutex_query_output_fields (pdata count group : Z) : Assertion :=
  (&(pdata # "os_mutex_data" ->ₛ "OSMutexPCP")) # UChar |-> decode_PCP_from_cnt count **
  (&(pdata # "os_mutex_data" ->ₛ "OSOwnerPrio")) # UChar |-> decode_OwnerPrio_from_cnt count **
  (&(pdata # "os_mutex_data" ->ₛ "OSValue")) # UChar |-> decode_OSValue_from_cnt count **
  (&(pdata # "os_mutex_data" ->ₛ "OSEventGrp")) # UChar |-> group.

(** The loop may change only the destination array prefix. All state-indexed
    facts travel in this view together, so rebinding the loop's existential
    table cannot lose its connection to the acquired Event and saved token. *)
Definition mutex_query_copy_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (eid : EventID)
  (observed current : OSEventAbstractState) (pdata count group : Z)
  (table : list Z) : Assertion :=
  coq_prop (mutex_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current /\ mutex_query_copy_snapshot entry eid current count group table) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   interrupt_inv sg entry.(IntrState) ** mutex_query_raw_frame sg entry eid **
   mutex_query_event_unread sg entry.(TskState) eid current **
   (event_addr sg eid + OSEventType_off) # UChar |-> 4 **
   (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
   (event_addr sg eid + OSEventGrp_off) # UChar |-> group **
   mutex_query_output_fields pdata count group).

Lemma mutex_query_copy_frame_restore :
  forall platform critical sg invocation origin mask saved before entry eid observed current
    pdata count group table base,
  base = event_addr sg eid ->
  mutex_query_copy_frame platform critical sg invocation origin mask saved
    before entry eid observed current pdata count group table ** store_oseventtbl sg base table |--
  coq_prop (mutex_query_acquire_facts critical sg invocation eid mask saved before entry observed current /\
    mutex_query_copy_snapshot entry eid current count group table) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   UCOS2_inv sg entry ** mutex_query_output_fields pdata count group).
Proof.
  intros platform critical sg invocation origin mask saved before entry eid observed current
    pdata count group table base Hbase.
  unfold mutex_query_copy_frame; Intros.
  assert (Hfacts : mutex_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current) by tauto.
  assert (Hsnapshot : mutex_query_copy_snapshot entry eid current count group table) by tauto.
  pose proof Hfacts as [_ [Hvalid [_ [_ [_ [_ [Htype _]]]]]]].
  sep_apply_l_atomic (mutex_query_copy_table_group_merge sg entry eid current base
    (event_addr sg eid + OSEventGrp_off) count group table Hsnapshot Hbase eq_refl).
  sep_apply_l_atomic (mutex_query_copy_fields_merge_full sg entry eid current base
    (event_addr sg eid + OSEventType_off) (event_addr sg eid + OSEventCnt_off)
    count group table Hvalid Hsnapshot Htype Hbase eq_refl eq_refl).
  entailer!.
Qed.
