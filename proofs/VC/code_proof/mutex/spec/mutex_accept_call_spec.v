Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Import SetsClass.SetsClass.
Require Import AUXLib.ListLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.array_abstraction.
From SimpleC.SL Require Import SeparationLogic.

Import ListNotations.
Import SetsNotation.
Import UCOS2_C_Rules.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Definition mutex_accept_observe_error (code : Z)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun initial observed final => observed = code /\ final = initial.

Definition mutex_accept_lookup (s : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) : Prop := s.(EventState).(inUsedEventStates) eid = Some e.

(** Explicit caller lifetime protocol: foreign clients may change payload,
    waiters and other modules, but do not delete/reuse/retype this live handle.
    This is not supplied by the CPU primitive or asserted as a kernel axiom. *)
Definition mutex_accept_handle_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) : Prop :=
  forall action before after previous,
    critical_region_clients critical action ->
    kernel_client_actor action <> Some invocation ->
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    mutex_accept_lookup before eid previous ->
    exists current, mutex_accept_lookup after eid current /\
      current.(eventGeneration) = previous.(eventGeneration) /\
      current.(eventType) = previous.(eventType).

Lemma mutex_accept_handle_interval_preserves_identity :
  forall critical sg invocation eid before after previous,
  mutex_accept_handle_protocol critical sg invocation eid ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before -> mutex_accept_lookup before eid previous ->
  exists current, mutex_accept_lookup after eid current /\
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

Definition mutex_accept_current_task (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (tid : TaskID) (task : TaskAbstractState) : Prop :=
  s.(SchedState).(curTaskID) = Some tid /\
  s.(TskState).(inUsedTaskStates) tid = Some task /\
  task_priority_in_range sg task.(curPrio) /\
  task.(curPrio) <> sg.(osPrioMutexCeilDis).

Lemma mutex_accept_current_task_from_lookup : forall sg s tid task,
  valid_stable_glob_vars sg -> UCOS2_state_inv sg s ->
  s.(SchedState).(curTaskID) = Some tid ->
  s.(TskState).(inUsedTaskStates) tid = Some task ->
  mutex_accept_current_task sg s tid task.
Proof.
  intros sg s tid task Hsg [_ [Htasks _]] Hcur Htask.
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [_ [Hrange _]]]]]]]].
  specialize (Hrange tid task Htask).
  unfold mutex_accept_current_task; split; [exact Hcur|]; split; [exact Htask|].
  split; [exact Hrange|].
  unfold task_priority_in_range in *; unfold valid_stable_glob_vars in Hsg; lia.
Qed.

Definition mutex_accept_sched_without_current (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(readyList) tasks **
  sched_rows_rep sg tasks s.(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Lemma mutex_accept_sched_current_equiv : forall sg tasks s tid,
  s.(curTaskID) = Some tid ->
  sched_raw_rep sg tasks s --||--
    (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
     mutex_accept_sched_without_current sg tasks s).
Proof.
  intros sg tasks s tid Hcur; unfold sched_raw_rep, sched_physical_rep,
    mutex_accept_sched_without_current; rewrite Hcur; cbn [encode_task_link]; split; entailer!.
Qed.

Definition mutex_accept_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation state).

Lemma mutex_accept_closed_equiv : forall platform critical sg invocation origin mask state,
  mutex_accept_closed platform critical sg invocation origin mask state --||--
    (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg state).
Proof.
  intros; unfold mutex_accept_closed, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  unfold UCOS2_inv; split; entailer!.
Qed.

Lemma mutex_accept_closed_save_pre : forall platform critical sg invocation origin mask state,
  mutex_accept_closed platform critical sg invocation origin mask state |--
    interrupt_platform_running platform invocation origin mask **
    critical_region_outside critical sg invocation state.
Proof. intros; unfold mutex_accept_closed; entailer!. Qed.

Definition mutex_accept_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  mutex_accept_lookup before eid observed /\ mutex_accept_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_MUTEX /\
  current.(eventType) = OS_EVENT_TYPE_MUTEX /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma mutex_accept_save_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed,
  mutex_accept_handle_protocol critical sg invocation eid ->
  UCOS2_state_inv sg before -> mutex_accept_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_MUTEX ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_raw_rep sg entry |--
  EX current, coq_prop (mutex_accept_acquire_facts critical sg invocation eid mask saved
    before entry observed current) &&
    (critical_region_masked platform critical sg invocation origin saved entry **
     UCOS2_inv sg entry).
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed
    Hprotocol Hvalid Hlookup Htype Hinterval Hsaved.
  destruct (mutex_accept_handle_interval_preserves_identity critical sg invocation eid
    before entry observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgeneration HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : mutex_accept_acquire_facts critical sg invocation eid mask saved
    before entry observed current).
  { unfold mutex_accept_acquire_facts.
    split; [exact Hinterval|]; split; [exact Hentry|]; split; [exact Hsaved|].
    split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
    split; [congruence|exact Hgeneration]. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Definition mutex_accept_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (entry after : UCOS2_Verify_State) : Assertion :=
  critical_region_masked platform critical sg invocation origin saved entry **
  UCOS2_inv sg after.

Lemma mutex_accept_restore_pre_exposes_saved_token :
  forall platform critical sg invocation origin saved entry after,
  mutex_accept_restore_pre platform critical sg invocation origin saved entry after --||--
    (interrupt_platform_running platform invocation origin 192 **
     interrupt_platform_saved platform (save_token saved invocation origin) **
     critical_region_inside critical sg invocation entry ** UCOS2_inv sg after).
Proof.
  intros; unfold mutex_accept_restore_pre, critical_region_masked; split; entailer!.
Qed.

Lemma mutex_accept_restore_consequence :
  forall platform critical sg invocation origin eid mask saved before entry after observed current,
  mutex_accept_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  UCOS2_state_inv sg after ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation after |--
  mutex_accept_closed platform critical sg invocation origin mask after.
Proof.
  intros platform critical sg invocation origin eid mask saved before entry after observed current
    [_ [Hentry [[Hsaved Hmask] _]]] Hafter.
  rewrite Hmask; unfold mutex_accept_closed; entailer!.
Qed.

Definition mutex_accept_type_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (observed : OSEventAbstractState) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) observed) EventTypeField **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  UCOS2_raw_rep_missing_module sg state EventModule.

Lemma mutex_accept_type_split_full : forall sg state eid observed,
  mutex_accept_lookup state eid observed ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type observed.(eventType) **
     mutex_accept_type_frame sg state eid observed).
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
  unfold mutex_accept_type_frame, OSEventType_off; entailer!.
Qed.

Lemma mutex_accept_type_merge_full : forall sg state eid observed,
  UCOS2_state_inv sg state -> mutex_accept_lookup state eid observed ->
  (event_addr sg eid + OSEventType_off) # UChar |-> encode_event_type observed.(eventType) **
    mutex_accept_type_frame sg state eid observed |-- UCOS2_inv sg state.
Proof.
  intros sg state eid observed Hvalid Hlookup.
  unfold mutex_accept_type_frame.
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

Lemma mutex_accept_encoded_type_is_mutex : forall observed,
  encode_event_type observed.(eventType) = 4 -> observed.(eventType) = OS_EVENT_TYPE_MUTEX.
Proof. intros observed H; destruct observed.(eventType); simpl in H; try lia; reflexivity. Qed.
Lemma mutex_accept_interrupt_split_full : forall sg state,
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    (sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
     interrupt_inv_no_int_nesting sg state.(IntrState) ** UCOS2_raw_rep_missing_module sg state InterruptModule).
Proof.
  intros; unfold UCOS2_inv.
  rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state; entailer!.
Qed.

Lemma mutex_accept_interrupt_merge_full : forall sg state isr,
  UCOS2_state_inv sg state -> isr = state.(IntrState).(intNesting) ->
  sg.(g_OSIntNesting) # UChar |-> isr **
    interrupt_inv_no_int_nesting sg state.(IntrState) ** UCOS2_raw_rep_missing_module sg state InterruptModule
  |-- UCOS2_inv sg state.
Proof.
  intros sg state isr Hvalid ->; unfold UCOS2_inv.
  rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state; entailer!.
Qed.

(** The three stores modify only the owner snapshot, preserving the Event
    instance, waiters, name/padding and every non-Mutex payload. *)
Definition mutex_accept_owned_event (e : OSEventAbstractState) (m : MutexFields)
  (tid : TaskID) (priority : Priority) : OSEventAbstractState :=
  {| eventGeneration := e.(eventGeneration); eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1); eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3); eventPadding19 := e.(eventPadding19);
     eventType := e.(eventType);
     mutexFields := Some {| mfPCP := m.(mfPCP); mfOwner := Some tid;
                            mfOwnerOrigPrio := Some priority |};
     semFields := e.(semFields); mboxFields := e.(mboxFields);
     queueFields := e.(queueFields); waitList := e.(waitList) |}.

Definition mutex_accept_owned_state (s : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) (m : MutexFields) (tid : TaskID) (priority : Priority)
  : UCOS2_Verify_State :=
  replace_EventS (owner_acquire_update s.(EventState) eid e m tid priority) s.

Lemma mutex_accept_acquire_reservation_claim_iff : forall sg events eid e m tid priority,
  events.(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m ->
  forall p,
  (exists other node fields,
    (owner_acquire_update events eid e m tid priority).(inUsedEventStates) other = Some node /\
    node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some fields /\
    mutex_reserves_priority_slot sg fields p) <->
  (exists other node fields, events.(inUsedEventStates) other = Some node /\
    node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some fields /\
    mutex_reserves_priority_slot sg fields p).
Proof.
  intros sg events eid e m tid priority He Htype Hm p; split;
    intros [other [node [fields [Hnode [HnodeType [Hfields Hclaim]]]]]].
  - rewrite (owner_acquire_lookup_eq events eid e m tid priority other He Hm) in Hnode.
    destruct (Z.eqb other eid) eqn:E.
    + apply Z.eqb_eq in E; subst other; injection Hnode as Enode; subst node.
      cbn in Hfields; injection Hfields as Efields; subst fields.
      exists eid, e, m; split; [exact He|]. split; [exact Htype|].
      split; [exact Hm|exact Hclaim].
    + exists other, node, fields; exact (conj Hnode (conj HnodeType (conj Hfields Hclaim))).
  - destruct (Z.eqb other eid) eqn:E.
    + apply Z.eqb_eq in E; subst other; rewrite He in Hnode.
      injection Hnode as Enode; subst node; rewrite Hm in Hfields.
      injection Hfields as Efields; subst fields.
      exists eid, (mutex_accept_owned_event e m tid priority),
        {| mfPCP := m.(mfPCP); mfOwner := Some tid; mfOwnerOrigPrio := Some priority |}.
      split; [unfold owner_acquire_update, update_event_field_raw; cbn; rewrite Z.eqb_refl; reflexivity|].
      split; [exact Htype|]. split; [reflexivity|exact Hclaim].
    + exists other, node, fields; split.
      * rewrite (owner_acquire_lookup_eq events eid e m tid priority other He Hm), E; exact Hnode.
      * exact (conj HnodeType (conj Hfields Hclaim)).
Qed.

Lemma mutex_accept_acquire_preserves_table : forall sg s eid e m tid priority,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) = None ->
  task_mutex_priotbl_consistency sg s.(TskState) s.(EventState) ->
  task_mutex_priotbl_consistency sg s.(TskState)
    (owner_acquire_update s.(EventState) eid e m tid priority).
Proof.
  intros sg s eid e m tid priority He Htype Hm Hnone [Hcreator [Hslots Halias]].
  pose proof (mutex_accept_acquire_reservation_claim_iff sg s.(EventState)
    eid e m tid priority He Htype Hm) as Hclaims.
  split.
  - intros p entry Hentry Hclaim; apply (Hcreator p entry Hentry); apply Hclaims; exact Hclaim.
  - split.
    + intros p Hp; specialize (Hslots p Hp); destruct (s.(TskState).(prioTbl) p).
      * intros Hclaim; apply Hslots; apply Hclaims; exact Hclaim.
      * destruct Hslots as [Hreservation|[Hclaim|Hpending]].
        -- left; exact Hreservation.
        -- right; left; apply Hclaims; exact Hclaim.
        -- right; right; exact Hpending.
      * exact Hslots.
    + eapply mutex_priority_alias_consistency_ext; [reflexivity|reflexivity| |exact Halias].
      intros owner p [other [node [fields [Hnode [HnodeType [Hfields [Howner Hclaim]]]]]]].
      assert (Hne : Z.eqb other eid = false).
      { apply Z.eqb_neq; intro E; subst other; rewrite He in Hnode.
        injection Hnode as E; subst node; rewrite Hm in Hfields.
        injection Hfields as E; subst fields; rewrite Hnone in Howner; discriminate. }
      exists other, node, fields; split.
      * rewrite (owner_acquire_lookup_eq s.(EventState) eid e m tid priority other He Hm), Hne;
          exact Hnode.
      * exact (conj HnodeType (conj Hfields (conj Howner Hclaim))).
Qed.

Lemma mutex_accept_acquire_preserves_waiting : forall sg s eid e m tid priority,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(mutexFields) = Some m ->
  event_wait_object_consistency sg s ->
  event_wait_object_consistency sg (mutex_accept_owned_state s eid e m tid priority).
Proof.
  intros sg s eid e m tid priority He Hm [Hentries [Hback Hclosed]].
  assert (Horigin : forall other node,
    (owner_acquire_update s.(EventState) eid e m tid priority).(inUsedEventStates) other = Some node ->
    exists old, s.(EventState).(inUsedEventStates) other = Some old /\
      node.(eventType) = old.(eventType) /\ node.(waitList) = old.(waitList)).
  { intros other node Hnode.
    rewrite (owner_acquire_lookup_eq s.(EventState) eid e m tid priority other He Hm) in Hnode.
    destruct (Z.eqb other eid) eqn:E.
    - apply Z.eqb_eq in E; subst other; injection Hnode as E; subst node; exists e; auto.
    - exists node; auto. }
  unfold event_wait_object_consistency, mutex_accept_owned_state; cbn [replace_EventS TskState EventState].
  split.
  - intros other node Hnode; destruct (Horigin other node Hnode) as [old [Hold [Htype Hwait]]].
    unfold event_wait_entry_consistency; rewrite Htype, Hwait; exact (Hentries other old Hold).
  - split.
    + intros owner task other node Htask Hnode Href.
      destruct (Horigin other node Hnode) as [old [Hold [Htype Hwait]]].
      rewrite Hwait; eapply Hback; eassumption.
    + eapply task_event_reference_closure_preserved_by_event_extension; [|exact Hclosed].
      intros other [old Hold].
      rewrite (owner_acquire_lookup_eq s.(EventState) eid e m tid priority other He Hm).
      destruct (Z.eqb other eid); [eexists; reflexivity|exists old; exact Hold].
Qed.

Lemma mutex_accept_acquire_preserves_pending : forall sg s eid e m tid priority,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m -> pending_mutex_consistency sg s.(TskState) s.(EventState) ->
  pending_mutex_consistency sg s.(TskState)
    (owner_acquire_update s.(EventState) eid e m tid priority).
Proof.
  intros sg s eid e m tid priority He Htype Hm Hpending.
  eapply pending_mutex_consistency_frame with (tasks := s.(TskState)) (events := s.(EventState));
    [reflexivity|reflexivity|reflexivity| |exact Hpending].
  intros p Hclaim; apply (mutex_accept_acquire_reservation_claim_iff
    sg s.(EventState) eid e m tid priority He Htype Hm p); exact Hclaim.
Qed.

Lemma mutex_accept_acquire_preserves_events : forall sg s eid e m tid priority,
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m -> task_priority_in_range sg priority -> priority <> sg.(osPrioMutexCeilDis) ->
  event_in_range sg s.(TskState) s.(EventState) ->
  event_in_range sg s.(TskState) (owner_acquire_update s.(EventState) eid e m tid priority).
Proof.
  intros sg s eid e m tid priority He Htype Hm Hprio Hdisabled Hvalid.
  pose proof Hvalid as [_ [_ [_ [Hfields [_ [_ Hwait]]]]]].
  specialize (Hfields eid e He); specialize (Hwait eid e He).
  unfold owner_acquire_update; eapply event_update_preserves_in_range;
    [exact Hvalid|exact He|reflexivity| | | |].
  - unfold event_fields_consistency in *; cbn; rewrite Htype in *; cbn; intuition discriminate.
  - unfold event_payload_consistency; cbn; rewrite Htype; cbn.
    split; [unfold mutex_fields_consistency; cbn; unfold task_priority_in_range in Hprio; tauto|discriminate].
  - unfold event_queue_id; cbn; rewrite Htype; reflexivity.
  - unfold event_wait_entry_consistency in *; exact Hwait.
Qed.

(** Full-invariant closure is proved independently of the C guard and does
    not assume PCP < caller priority.  In particular it covers the actual
    acquire-then-PCP_LOWER endpoint. The caller-task facts here belong to a
    separately justified task execution boundary, not to Save. *)
Lemma mutex_accept_acquire_preserves_validity : forall sg s eid e m tid task,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) = None ->
  s.(TskState).(inUsedTaskStates) tid = Some task ->
  task_priority_in_range sg task.(curPrio) -> task.(curPrio) <> sg.(osPrioMutexCeilDis) ->
  UCOS2_state_inv sg (mutex_accept_owned_state s eid e m tid task.(curPrio)).
Proof.
  intros sg s eid e m tid task Hvalid He Htype Hm Hnone Htask Hprio Hdisabled.
  pose proof Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]].
  pose proof Hcross as [Htable [Howners [Hwaiting [Hprotocol [Hunique [Hflags Htimer]]]]]].
  pose proof Hevents as [_ [_ [_ [_ [Hpayload _]]]]].
  specialize (Hpayload eid e He); unfold event_payload_consistency in Hpayload.
  rewrite Htype, Hm in Hpayload.
  assert (Hempty : e.(waitList) = []) by (apply (proj2 Hpayload); exact Hnone).
  assert (Hnotwait : ~ In tid e.(waitList)) by (rewrite Hempty; simpl; tauto).
  assert (HafterCross : cross_module_consistency sg (mutex_accept_owned_state s eid e m tid task.(curPrio))).
  { unfold cross_module_consistency, mutex_accept_owned_state; cbn [replace_EventS TskState EventState FlagState TimerState].
    split; [eapply mutex_accept_acquire_preserves_table; eassumption|].
    split.
    - eapply owner_acquire_preserves_owner_snapshots; try eassumption; exact (proj2 (proj2 Htable)).
    - split; [eapply mutex_accept_acquire_preserves_waiting; eassumption|].
      split.
      + eapply mutex_protocol_consistency_preserved_by_acquire; try eassumption; [reflexivity|].
        eapply mutex_priority_alias_consistency_current_registered; exact (proj2 (proj2 Htable)).
      + split; [eapply mutex_enabled_pcp_unique_preserved_by_acquire; eassumption|].
        exact (conj Hflags Htimer). }
  assert (HafterNames : kernel_names_valid sg (mutex_accept_owned_state s eid e m tid task.(curPrio))).
  { apply kernel_names_valid_replace_event; [unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto|].
    eapply event_update_preserves_name_references; [exact He|reflexivity]. }
  assert (HafterPending : pending_mutex_consistency sg s.(TskState)
    (owner_acquire_update s.(EventState) eid e m tid task.(curPrio))).
  { eapply mutex_accept_acquire_preserves_pending; try eassumption.
    eapply UCOS2_state_inv_pending_mutex; exact Hvalid. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, mutex_accept_owned_state;
    cbn [replace_EventS IntrState TskState SchedState EventState TickState FlagState MemoryState TimerState StatsState ControlState NameState].
  split; [exact Hprofile|]. split; [exact Htasks|]. split; [exact Hsched|].
  split; [eapply mutex_accept_acquire_preserves_events; eassumption|].
  split; [exact HafterCross|].
  cbn [mutex_accept_owned_state replace_EventS] in HafterNames; tauto.
Qed.

Definition mutex_accept_observe_result (result : Z * Z)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun before value after => value = snd result /\ after = before.

Definition mutex_accept_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    mutex_accept_lookup before eid observed /\
    (observed.(eventType) = OS_EVENT_TYPE_MUTEX -> before.(IntrState).(intNesting) <= 0 ->
      mutex_accept_handle_protocol critical sg invocation eid)).

(** This is the exact source effect, not an invariant-closure guard.  The
    unavailable branch never reads OSTCBCur. On the available branch the
    priority/pointer stores precede the PCP diagnostic. *)
Definition mutex_accept_protected_result (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) (current : OSEventAbstractState)
  (code value : Z) (after : UCOS2_Verify_State) : Prop :=
  exists m, current.(mutexFields) = Some m /\
    ((Z.land (encode_event_cnt_value current) 255 <> 255 /\ code = 0 /\ value = 0 /\ after = entry) \/
     (Z.land (encode_event_cnt_value current) 255 = 255 /\ exists tid task,
       entry.(SchedState).(curTaskID) = Some tid /\
       entry.(TskState).(inUsedTaskStates) tid = Some task /\
       value = 1 /\ after = mutex_accept_owned_state entry eid current m tid task.(curPrio) /\
       ((decode_PCP_from_cnt (encode_event_cnt_value current) <> 255 /\
         task.(curPrio) <= decode_PCP_from_cnt (encode_event_cnt_value current) /\ code = 120) \/
        ((decode_PCP_from_cnt (encode_event_cnt_value current) = 255 \/
          task.(curPrio) > decode_PCP_from_cnt (encode_event_cnt_value current)) /\ code = 0)))).

Definition mutex_accept_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  : program UCOS2_Verify_State (Z * Z) :=
  fun before result after =>
    (pe = 0 /\ result = (4, 0) /\ after = before) \/
    (pe <> 0 /\ exists eid observed,
      pe = event_addr sg eid /\ valid_event_id sg eid /\ mutex_accept_lookup before eid observed /\
      ((observed.(eventType) <> OS_EVENT_TYPE_MUTEX /\ result = (1, 0) /\ after = before) \/
       (observed.(eventType) = OS_EVENT_TYPE_MUTEX /\
        ((before.(IntrState).(intNesting) > 0 /\ result = (2, 0) /\ after = before) \/
         (before.(IntrState).(intNesting) <= 0 /\ exists entry current,
           critical_region_interval critical sg invocation before entry /\
           mutex_accept_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_MUTEX /\
           current.(eventGeneration) = observed.(eventGeneration) /\
           mutex_accept_protected_result sg eid entry current (fst result) (snd result) after))))).

Definition mutex_accept_call_post critical sg invocation pe before code value after : Prop :=
  mutex_accept_call_program critical sg invocation pe before (code, value) after.

Lemma mutex_accept_call_input_live : forall critical sg invocation pe before eid observed,
  mutex_accept_call_input critical sg invocation pe before eid observed -> pe <> 0 ->
  pe = event_addr sg eid /\ valid_event_id sg eid /\ mutex_accept_lookup before eid observed /\
  (observed.(eventType) = OS_EVENT_TYPE_MUTEX -> before.(IntrState).(intNesting) <= 0 ->
    mutex_accept_handle_protocol critical sg invocation eid).
Proof. intros; unfold mutex_accept_call_input in H; tauto. Qed.

Lemma mutex_accept_call_null_return : forall critical sg invocation before,
  mutex_accept_call_program critical sg invocation 0 before (4, 0) before.
Proof. intros; left; auto. Qed.

Lemma mutex_accept_call_wrong_type_return : forall critical sg invocation pe before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  mutex_accept_lookup before eid observed -> observed.(eventType) <> OS_EVENT_TYPE_MUTEX ->
  mutex_accept_call_program critical sg invocation pe before (1, 0) before.
Proof.
  intros; right; split; [assumption|]; exists eid, observed.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. left; auto.
Qed.

Lemma mutex_accept_call_isr_return : forall critical sg invocation pe before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  mutex_accept_lookup before eid observed -> observed.(eventType) = OS_EVENT_TYPE_MUTEX ->
  before.(IntrState).(intNesting) > 0 ->
  mutex_accept_call_program critical sg invocation pe before (2, 0) before.
Proof.
  intros; right; split; [assumption|]; exists eid, observed.
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  right; split; [assumption|]. left; auto.
Qed.

Lemma mutex_accept_call_protected_return :
  forall critical sg invocation pe before eid observed mask saved entry current code value after,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  before.(IntrState).(intNesting) <= 0 ->
  mutex_accept_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  mutex_accept_protected_result sg eid entry current code value after ->
  mutex_accept_call_program critical sg invocation pe before (code, value) after.
Proof.
  intros critical sg invocation pe before eid observed mask saved entry current code value after
    Hpe Haddr Hid Hisr [Hinterval [_ [_ [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]] Hresult.
  right; split; [exact Hpe|]; exists eid, observed.
  split; [exact Haddr|]. split; [exact Hid|]. split; [exact Hbefore|].
  right; split; [exact Htype|]. right; split; [exact Hisr|].
  exists entry, current; repeat split; assumption.
Qed.

Definition mutex_accept_interrupt_frame (sg : StableGlobVars) (s : UCOS2_Verify_State) :=
  UCOS2_raw_rep_missing_module sg s InterruptModule.

Definition mutex_accept_event_snapshot (sg : StableGlobVars) (entry : UCOS2_Verify_State) (eid : EventID)
  (current : OSEventAbstractState) (m : MutexFields) (count ptr : Z) : Prop :=
  mutex_accept_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_MUTEX /\
  current.(mutexFields) = Some m /\ count = encode_event_cnt_value current /\
  ptr = encode_event_ptr_value sg current.

Definition mutex_accept_owner_rest (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_addr sg eid))
    (remove EventField_eq_dec EventCntField
      (remove EventField_eq_dec EventPtrField (event_fields sg.(osKernelConfig).(cfgEventNames))))
    (event_image sg s.(TskState) e).

Definition mutex_accept_event_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  mutex_accept_owner_rest sg s eid e ** event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid **
  task_public_storage sg s.(TskState) ** sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s.

Lemma mutex_accept_owner_fields_equiv : forall sg s eid e,
  used_event_rep sg s.(TskState) eid e --||--
  ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value e **
   (event_addr sg eid + OSEventPtr_off) # Ptr |-> encode_event_ptr_value sg e **
   mutex_accept_owner_rest sg s eid e).
Proof.
  intros sg s eid e.
  assert (Hptr : In EventPtrField (event_fields sg.(osKernelConfig).(cfgEventNames)))
    by (unfold event_fields; simpl; tauto).
  assert (Hcnt : In EventCntField
    (remove EventField_eq_dec EventPtrField (event_fields sg.(osKernelConfig).(cfgEventNames))))
    by (destruct sg.(osKernelConfig).(cfgEventNames); simpl; tauto).
  assert (Hnd : NoDup
    (remove EventField_eq_dec EventPtrField (event_fields sg.(osKernelConfig).(cfgEventNames)))).
  { destruct sg.(osKernelConfig).(cfgEventNames); simpl;
      repeat constructor; simpl; intuition discriminate. }
  unfold used_event_rep, mutex_accept_owner_rest; split.
  - sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
      (event_addr sg eid) (event_image sg s.(TskState) e) EventPtrField Hptr).
    unfold event_storage_without_field.
    sep_apply_l_atomic (EventFieldStorage.store_fields_split_field EventField (option Z)
      EventField_eq_dec (event_cell (event_addr sg eid))
      (remove EventField_eq_dec EventPtrField (event_fields sg.(osKernelConfig).(cfgEventNames)))
      (event_image sg s.(TskState) e) EventCntField Hnd Hcnt).
    cbn [event_cell event_image event_field_offset]; unfold OSEventCnt_off, OSEventPtr_off; entailer!.
  - eapply derivable1_trans with
      (event_cell (event_addr sg eid) EventPtrField (event_image sg s.(TskState) e EventPtrField) **
       event_cell (event_addr sg eid) EventCntField (event_image sg s.(TskState) e EventCntField) **
       EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_addr sg eid))
         (remove EventField_eq_dec EventCntField
           (remove EventField_eq_dec EventPtrField (event_fields sg.(osKernelConfig).(cfgEventNames))))
         (event_image sg s.(TskState) e)).
    { cbn [event_cell event_image event_field_offset]; unfold OSEventCnt_off, OSEventPtr_off; entailer!. }
    sep_apply_l_atomic (EventFieldStorage.store_fields_merge_field EventField (option Z)
      EventField_eq_dec (event_cell (event_addr sg eid))
      (remove EventField_eq_dec EventPtrField (event_fields sg.(osKernelConfig).(cfgEventNames)))
      (event_image sg s.(TskState) e) EventCntField Hnd Hcnt).
    sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
      (event_addr sg eid) (event_image sg s.(TskState) e) EventPtrField Hptr); entailer!.
Qed.

Lemma mutex_accept_event_fields_split_full : forall sg s eid e,
  mutex_accept_lookup s eid e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  UCOS2_inv sg s |-- EX m,
    coq_prop (UCOS2_state_inv sg s /\
      mutex_accept_event_snapshot sg s eid e m (encode_event_cnt_value e) (encode_event_ptr_value sg e)) &&
    ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value e **
     (event_addr sg eid + OSEventPtr_off) # Ptr |-> encode_event_ptr_value sg e **
     mutex_accept_event_frame sg s eid e).
Proof.
  intros sg s eid e He Htype; rewrite UCOS2_inv_open_task_storage_sched_event; Intros.
  match goal with Hvalid : UCOS2_state_inv sg s |- _ =>
    pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]] end.
  pose proof Hcross as [_ [_ [_ [Hprotocol _]]]].
  match goal with Hvalid : UCOS2_state_inv sg s |- _ =>
    pose proof Hvalid as [_ [_ [_ [Hevents _]]]] end.
  pose proof Hevents as [_ [_ [_ [Hfields _]]]].
  specialize (Hfields eid e He); unfold event_fields_consistency in Hfields.
  rewrite Htype in Hfields; destruct e.(mutexFields) as [m|] eqn:Hm; [|tauto].
  sep_apply_l_atomic (event_raw_rep_split_eid sg s.(TskState) s.(EventState) eid e He).
  sep_apply_l_atomic (proj1 (mutex_accept_owner_fields_equiv sg s eid e)).
  Exists m; unfold mutex_accept_event_snapshot, mutex_accept_event_frame, mutex_accept_lookup; entailer!.
Qed.

Lemma mutex_accept_event_fields_merge_full : forall sg s eid e count ptr,
  UCOS2_state_inv sg s -> mutex_accept_lookup s eid e ->
  count = encode_event_cnt_value e -> ptr = encode_event_ptr_value sg e ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> ptr **
  mutex_accept_event_frame sg s eid e |-- UCOS2_inv sg s.
Proof.
  intros sg s eid e count ptr Hvalid He -> ->; unfold mutex_accept_event_frame.
  sep_apply_l_atomic (proj2 (mutex_accept_owner_fields_equiv sg s eid e)).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg s.(TskState) s.(EventState) eid e He).
  rewrite UCOS2_inv_open_task_storage_sched_event; entailer!.
Qed.

Definition mutex_accept_current_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState) (tid : TaskID) (task : TaskAbstractState) : Assertion :=
  mutex_accept_owner_rest sg s eid e ** event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid **
  task_public_storage_without_field sg s.(TskState) tid task (TCBCommonField TCBPrio) **
  mutex_accept_sched_without_current sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s.

Lemma mutex_accept_current_fields_split : forall sg s eid e tid task,
  mutex_accept_current_task sg s tid task ->
  mutex_accept_event_frame sg s eid e |--
    sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
    (tcb_field_address (task_slot_addr sg tid) TCBPrio) # UChar |-> task.(curPrio) **
    mutex_accept_current_frame sg s eid e tid task.
Proof.
  intros sg s eid e tid task [Hcur [Htask Hbounds]].
  unfold mutex_accept_event_frame, mutex_accept_current_frame.
  sep_apply_l_atomic (task_public_storage_split_field sg s.(TskState) tid task
    (TCBCommonField TCBPrio) Htask (tcb_configured_common_field_in _ _ _)).
  sep_apply_l_atomic (proj1 (mutex_accept_sched_current_equiv sg s.(TskState) s.(SchedState) tid Hcur)).
  cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image]; entailer!.
Qed.

Lemma mutex_accept_current_fields_merge : forall sg s eid e tid task,
  mutex_accept_current_task sg s tid task ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
    (tcb_field_address (task_slot_addr sg tid) TCBPrio) # UChar |-> task.(curPrio) **
    mutex_accept_current_frame sg s eid e tid task |-- mutex_accept_event_frame sg s eid e.
Proof.
  intros sg s eid e tid task [Hcur [Htask Hbounds]].
  unfold mutex_accept_current_frame, mutex_accept_event_frame.
  eapply derivable1_trans with
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
      (TCBCommonField TCBPrio) (task_layout_image sg task (TCBCommonField TCBPrio)) **
     task_public_storage_without_field sg s.(TskState) tid task (TCBCommonField TCBPrio) **
     mutex_accept_owner_rest sg s eid e ** event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
     mutex_accept_sched_without_current sg s.(TskState) s.(SchedState) **
     UCOS2_raw_rep_missing_task_storage_sched_event sg s).
  { cbn [tcb_layout_cell tcb_cell tcb_field_address task_layout_image tcb_layout_image task_tcb64_image]; entailer!. }
  sep_apply_l_atomic (task_public_storage_merge_field sg s.(TskState) tid task
    (TCBCommonField TCBPrio) Htask (tcb_configured_common_field_in _ _ _)).
  unfold sched_raw_rep, sched_physical_rep, mutex_accept_sched_without_current;
    rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma mutex_accept_owner_rest_acquire_eq : forall sg s eid e m tid priority,
  mutex_accept_owner_rest sg s eid (mutex_accept_owned_event e m tid priority) =
  mutex_accept_owner_rest sg s eid e.
Proof.
  intros; unfold mutex_accept_owner_rest, EventFieldStorage.store_fields.
  f_equal; apply functional_extensionality; intro field; unfold fields_map.
  destruct in_dec as [Hin|Hnot]; [|reflexivity].
  apply in_remove in Hin; destruct Hin as [Hin Hcnt].
  apply in_remove in Hin; destruct Hin as [Hin Hptr].
  destruct field; try contradiction; reflexivity.
Qed.

Lemma mutex_accept_owner_fields_merge_updated : forall sg s eid e m tid priority,
  e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> (m.(mfPCP) * 256 + priority) **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> task_slot_addr sg tid **
    mutex_accept_owner_rest sg s eid e |--
  used_event_rep sg s.(TskState) eid (mutex_accept_owned_event e m tid priority).
Proof.
  intros sg s eid e m tid priority Htype.
  rewrite <- (mutex_accept_owner_rest_acquire_eq sg s eid e m tid priority).
  eapply derivable1_trans; [|apply (proj2 (mutex_accept_owner_fields_equiv sg s eid
    (mutex_accept_owned_event e m tid priority)))].
  assert (Hcnt : encode_event_cnt_value (mutex_accept_owned_event e m tid priority) =
    m.(mfPCP) * 256 + priority).
  { unfold encode_event_cnt_value, mutex_accept_owned_event; cbn; rewrite Htype; reflexivity. }
  assert (Hptr : encode_event_ptr_value sg (mutex_accept_owned_event e m tid priority) = task_slot_addr sg tid).
  { unfold encode_event_ptr_value, mutex_accept_owned_event; cbn; rewrite Htype; reflexivity. }
  rewrite Hcnt, Hptr; reflexivity.
Qed.

Lemma mutex_accept_acquire_merge_full : forall sg s eid e m tid task,
  UCOS2_state_inv sg s -> mutex_accept_lookup s eid e ->
  e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) = None ->
  mutex_accept_current_task sg s tid task ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> (m.(mfPCP) * 256 + task.(curPrio)) **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> task_slot_addr sg tid **
    sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
    (tcb_field_address (task_slot_addr sg tid) TCBPrio) # UChar |-> task.(curPrio) **
    mutex_accept_current_frame sg s eid e tid task |--
  UCOS2_inv sg (mutex_accept_owned_state s eid e m tid task.(curPrio)).
Proof.
  intros sg s eid e m tid task Hvalid He Htype Hm Hnone Hcurrent.
  pose proof Hcurrent as [_ [Htask [Hprio Hdisabled]]].
  pose proof (mutex_accept_acquire_preserves_validity sg s eid e m tid task
    Hvalid He Htype Hm Hnone Htask Hprio Hdisabled) as Hafter.
  sep_apply_l_atomic (mutex_accept_current_fields_merge sg s eid e tid task Hcurrent).
  unfold mutex_accept_event_frame.
  sep_apply_l_atomic (mutex_accept_owner_fields_merge_updated sg s eid e m tid task.(curPrio) Htype).
  eapply derivable1_trans; [|apply (UCOS2_inv_merge_updated_event sg s eid e
    (mutex_accept_owned_event e m tid task.(curPrio)) Hafter He eq_refl eq_refl)].
  unfold UCOS2_raw_rep_missing_task_storage_sched_event,
    UCOS2_raw_rep_missing_event_queue, UCOS2_raw_rep_missing_two, UCOS2_selected_rep;
    cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep];
    unfold task_shared_rep; entailer!.
Qed.

Definition mutex_accept_pcp_code (pcp priority : Z) : Z :=
  if (Z.eqb pcp 255 || Z.ltb pcp priority)%bool then 0 else 120.

Lemma mutex_accept_pcp_code_none : forall pcp priority,
  pcp = 255 \/ priority > pcp -> mutex_accept_pcp_code pcp priority = 0.
Proof.
  intros pcp priority [->|Hhigher]; unfold mutex_accept_pcp_code.
  - reflexivity.
  - assert (Hlt : Z.ltb pcp priority = true) by (apply Z.ltb_lt; lia).
    rewrite Hlt, Bool.orb_true_r; reflexivity.
Qed.

Lemma mutex_accept_pcp_code_none_inv : forall pcp priority,
  mutex_accept_pcp_code pcp priority = 0 -> pcp = 255 \/ priority > pcp.
Proof.
  intros pcp priority; unfold mutex_accept_pcp_code.
  destruct (Z.eqb pcp 255) eqn:Heq; [left; apply Z.eqb_eq; exact Heq|].
  destruct (Z.ltb pcp priority) eqn:Hlt; simpl; [|discriminate].
  intros; right; apply Z.ltb_lt in Hlt; lia.
Qed.

Lemma mutex_accept_u16_of_byte : forall x,
  0 <= x <= 255 -> unsigned_last_nbits x 16 = x.
Proof. intros x Hx; unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia. Qed.

Lemma mutex_accept_u32_of_byte : forall x,
  0 <= x <= 255 -> unsigned_last_nbits x 32 = x.
Proof. intros x Hx; unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia. Qed.

Lemma mutex_accept_high_byte_cast : forall count,
  0 <= count <= 65535 -> unsigned_last_nbits (Z.shiftr count 8) 8 = Z.shiftr count 8.
Proof.
  intros count Hcount; unfold unsigned_last_nbits; apply Z.mod_small.
  rewrite Z.shiftr_div_pow2 by lia; cbn; split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma mutex_accept_low_byte : forall pcp value,
  0 <= value < 256 -> Z.land (pcp * 256 + value) 255 = value.
Proof.
  intros pcp value Hvalue; replace 255 with (Z.ones 8) by reflexivity.
  rewrite Z.land_ones by lia; replace (2 ^ 8) with 256 by reflexivity.
  rewrite Z.add_comm, Z.mod_add by lia; apply Z.mod_small; exact Hvalue.
Qed.

Lemma mutex_accept_available_snapshot : forall sg s eid e m count ptr,
  UCOS2_state_inv sg s -> mutex_accept_event_snapshot sg s eid e m count ptr ->
  Z.land count 255 = 255 ->
  m.(mfOwner) = None /\ m.(mfOwnerOrigPrio) = None /\
  count = m.(mfPCP) * 256 + 255 /\ 0 <= m.(mfPCP) <= 255.
Proof.
  intros sg s eid e m count ptr Hvalid [He [Htype [Hm [Hcount Hptr]]]] Hlow.
  pose proof Hvalid as [Hprofile [_ [_ [Hevents [Hcross _]]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof Hevents as [_ [_ [_ [_ [Hpayload _]]]]].
  specialize (Hpayload eid e He); unfold event_payload_consistency in Hpayload.
  rewrite Htype, Hm in Hpayload; destruct Hpayload as [Howner _].
  pose proof Hcross as [_ [_ [_ [Hprotocol _]]]].
  specialize (Hprotocol eid e m He Htype Hm); destruct Hprotocol as [Hpcp _].
  assert (Hpcprange : 0 <= m.(mfPCP) <= 255).
  { unfold valid_mutex_pcp in Hpcp; unfold valid_stable_glob_vars in Hsg; lia. }
  unfold encode_event_cnt_value in Hcount; rewrite Htype, Hm in Hcount.
  unfold mutex_fields_consistency in Howner.
  destruct m.(mfOwner) as [owner|] eqn:Ho;
    destruct m.(mfOwnerOrigPrio) as [priority|] eqn:Hp; try contradiction.
  - exfalso; rewrite Hcount, mutex_accept_low_byte in Hlow.
    + unfold valid_stable_glob_vars in Hsg; lia.
    + unfold valid_stable_glob_vars in Hsg; lia.
  - split; [reflexivity|]; split; [reflexivity|]; split; assumption.
Qed.

Lemma mutex_accept_replace_low_byte : forall count priority,
  0 <= count <= 65535 -> Z.land count 255 = 255 -> 255 <= count ->
  0 <= priority <= 255 ->
  Z.lor (Z.land count 65280) priority = count - 255 + priority.
Proof.
  intros count priority Hcount Hlow Hmin Hpriority.
  assert (Hhigh : Z.land count 65280 = count - 255).
  { replace 65280 with (Z.land (Z.lnot 255) 65535) by reflexivity.
    rewrite Z.land_assoc, <- Z.sub_land_same_l, Hlow.
    replace 65535 with (Z.ones 16) by reflexivity; rewrite Z.land_ones by lia.
    apply Z.mod_small; cbn; lia. }
  rewrite Hhigh.
  assert (Hdisjoint : Z.land (count - 255) priority = 0).
  { assert (Hmask : Z.land priority 255 = priority).
    { replace 255 with (Z.ones 8) by reflexivity; rewrite Z.land_ones by lia.
      apply Z.mod_small; cbn; lia. }
    rewrite <- Hmask, (Z.land_comm priority 255), Z.land_assoc.
    replace 255 with (Z.ones 8) by reflexivity; rewrite Z.land_ones by lia.
    assert (Hmod : count mod 256 = 255).
    { replace 255 with (Z.ones 8) in Hlow by reflexivity.
      rewrite Z.land_ones in Hlow by lia; exact Hlow. }
    replace (2 ^ 8) with 256 by reflexivity.
    change (Z.land ((count - 255) mod 256) priority = 0).
    rewrite Zminus_mod, Hmod; reflexivity. }
  pose proof (Z.add_lor_land (count - 255) priority) as Hsum; rewrite Hdisjoint in Hsum; lia.
Qed.

Lemma mutex_accept_call_safe_return :
  forall critical sg invocation pe before after code value X,
  mutex_accept_call_program critical sg invocation pe before (code, value) after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_accept_call_program critical sg invocation pe)) mutex_accept_observe_result) X ->
  safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z value) X.
Proof.
  intros critical sg invocation pe before after code value X Hsem Hexec.
  assert (Hatomic : hs_eval (atomic_cmd (mutex_accept_call_program critical sg invocation pe))
    (LastSeen before) (LastSeen after) (code, value)).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P HP.
    exists (RTrans_Abs after); split; [|reflexivity].
    exists before, after; split; [apply HP; exact I|].
    split; [exact Hsem|reflexivity]. }
  pose proof (highstepbind_derive _ _ _ (code, value) (LastSeen after) Hatomic X Hexec) as Hobs.
  eapply (highstependret_derive (mutex_accept_observe_result (code, value)) (LastSeen after) value
    (fun _ => LastSeen after)); [|exact Hobs].
  unfold hs_eval, LastSeen; intros P HP; exists P; split; [split; reflexivity|exact HP].
Qed.
