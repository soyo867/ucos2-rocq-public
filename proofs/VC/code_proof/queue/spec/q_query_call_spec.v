Require Export Ucos2Verify.VC.code.queue.spec.q_query_spec.
Require Export Ucos2Verify.lib.mutex_query_spec.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.queue_core.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic MapLib.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected public API shares the established live/free discriminator
    and critical-region ownership. Queue contents are read at acquisition,
    never frozen at the earlier unmasked type test. *)
Definition q_query_public_slot (state : UCOS2_Verify_State)
  (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  mutex_query_lookup state eid observed \/
  (state.(EventState).(inUsedEventStates) eid = None /\
   In eid state.(EventState).(unUsedEventStates)).

Definition q_query_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent pdata : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/ (pevent <> 0 /\ pdata = 0) \/
  (pevent <> 0 /\ pdata <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
   q_query_public_slot before eid observed /\
   (event_slot_type_value before.(EventState) eid = 2 ->
    mutex_query_handle_protocol critical sg invocation eid)).

Definition q_query_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  mutex_query_lookup before eid observed /\ mutex_query_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_Q /\ current.(eventType) = OS_EVENT_TYPE_Q /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma q_query_save_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed,
  mutex_query_handle_protocol critical sg invocation eid ->
  UCOS2_state_inv sg before -> mutex_query_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_Q ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_raw_rep sg entry |--
  EX current, coq_prop (q_query_acquire_facts critical sg invocation eid mask saved
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
  assert (Hfacts : q_query_acquire_facts critical sg invocation eid mask saved
    before entry observed current).
  { unfold q_query_acquire_facts.
    split; [exact Hinterval|]; split; [exact Hentry|]; split; [exact Hsaved|].
    split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
    split; [congruence|exact Hgeneration]. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Lemma q_query_restore_consequence :
  forall platform critical sg invocation origin eid mask saved before entry observed current,
  q_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation entry |--
  mutex_query_closed platform critical sg invocation origin mask entry.
Proof.
  intros platform critical sg invocation origin eid mask saved before entry observed current
    [_ [Hentry [[Hsaved Hmask] _]]].
  rewrite Hmask; unfold mutex_query_closed; entailer!.
Qed.

(** Original-value merge. Query does not own a second QCB/buffer alongside
    the global invariant: these cells are removed from its Queue map and
    returned to that same map. Every other Queue and every other module stays
    in the residual. *)
Definition q_query_queue_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (free : list QueueID) : Assertion :=
  event_raw_rep sg state.(TskState) state.(EventState) **
  store_map_missing_i (published_queue_node_rep sg state.(EventState))
    state.(EventState).(inUsedEventStates) eid **
  store_free_queue_list sg free ** UCOS2_raw_rep_missing_event_queue sg state.

Lemma q_query_queue_split : forall sg state eid node q,
  state.(EventState).(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  UCOS2_inv sg state |-- EX free, EX slots,
    coq_prop (UCOS2_state_inv sg state /\
      queue_published_storage_binding state.(EventState) /\
      queue_pool_partition sg state.(EventState) free /\
      state.(EventState).(publishedQueueBytes) q.(qID) = Some slots) &&
    (used_queue_control_block sg q ** queue_buffer_rep q slots **
     q_query_queue_frame sg state eid free).
Proof.
  intros sg state eid node q Hnode Hq.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (queue_storage_split_event sg state.(EventState) eid node q Hnode Hq).
  Intros free slots; Exists free slots; unfold q_query_queue_frame; entailer!.
Qed.

Lemma q_query_queue_merge : forall sg state eid node q free slots,
  UCOS2_state_inv sg state ->
  queue_published_storage_binding state.(EventState) ->
  queue_pool_partition sg state.(EventState) free ->
  state.(EventState).(inUsedEventStates) eid = Some node -> node.(queueFields) = Some q ->
  state.(EventState).(publishedQueueBytes) q.(qID) = Some slots ->
  used_queue_control_block sg q ** queue_buffer_rep q slots **
    q_query_queue_frame sg state eid free |-- UCOS2_inv sg state.
Proof.
  intros sg state eid node q free slots Hvalid Hbinding Hpart Hnode Hq Hslots.
  assert (Hfocus : used_queue_control_block sg q ** queue_buffer_rep q slots |--
    published_queue_node_rep sg state.(EventState) eid node).
  { unfold published_queue_node_rep; rewrite Hq; Exists slots; entailer!. }
  unfold q_query_queue_frame.
  sep_apply_l_atomic Hfocus.
  sep_apply_l_atomic (store_map_merge (published_queue_node_rep sg state.(EventState))
    eid node state.(EventState).(inUsedEventStates) Hnode).
  rewrite UCOS2_inv_split_event_queue.
  unfold queue_storage_rep; entailer!; Exists free; entailer!.
Qed.

(** Source-ordered return plus protected snapshot. None is reserved for an
    error; Some snapshot records all five output components on success.
    This is a semantic interface, not a claim that the C VC is discharged. *)
Definition q_query_call_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent pdata : addr)
  : program UCOS2_Verify_State (Z * option QueueQuerySnapshot) :=
  fun before result after =>
    (pevent = 0 /\ result = (4, None) /\ after = before) \/
    (pevent <> 0 /\ pdata = 0 /\ result = (9, None) /\ after = before) \/
    (pevent <> 0 /\ pdata <> 0 /\ exists eid observed,
      pevent = event_addr sg eid /\ valid_event_id sg eid /\
      q_query_public_slot before eid observed /\
      ((event_slot_type_value before.(EventState) eid <> 2 /\
        result = (1, None) /\ after = before) \/
       (mutex_query_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q /\
        exists entry current snapshot,
          critical_region_interval critical sg invocation before entry /\
          mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_Q /\
          current.(eventGeneration) = observed.(eventGeneration) /\
          q_query_critical sg eid entry snapshot after /\ result = (0, Some snapshot)))).

Lemma q_query_call_null_event : forall critical sg invocation pdata before,
  q_query_call_program critical sg invocation 0 pdata before (4, None) before.
Proof. intros; left; auto. Qed.

Lemma q_query_call_null_output : forall critical sg invocation pevent before,
  pevent <> 0 ->
  q_query_call_program critical sg invocation pevent 0 before (9, None) before.
Proof. intros; right; left; auto. Qed.

Lemma q_query_call_wrong_type : forall critical sg invocation pevent pdata before eid observed,
  pevent <> 0 -> pdata <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  q_query_public_slot before eid observed -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_query_call_program critical sg invocation pevent pdata before (1, None) before.
Proof.
  intros critical sg invocation pevent pdata before eid observed Hpe Hpd Haddr Hid Hslot Htype.
  right; right; split; [exact Hpe|]; split; [exact Hpd|].
  exists eid, observed; split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hslot|].
  left; auto.
Qed.

Lemma q_query_call_success :
  forall critical sg invocation pevent pdata before eid observed mask saved entry current snapshot,
  pevent <> 0 -> pdata <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  q_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  q_query_critical sg eid entry snapshot entry ->
  q_query_call_program critical sg invocation pevent pdata before (0, Some snapshot) entry.
Proof.
  intros critical sg invocation pevent pdata before eid observed mask saved entry current snapshot
    Hpe Hpd Haddr Hid [Hinterval [Hvalid [Hsaved [Hbefore [Hlookup [Htype [Hcurrent Hgen]]]]]]] Hread.
  right; right; split; [exact Hpe|]; split; [exact Hpd|].
  exists eid, observed; split; [exact Haddr|]; split; [exact Hid|]; split; [left; exact Hbefore|].
  right; split; [exact Hbefore|]; split; [exact Htype|].
  exists entry, current, snapshot.
  split; [exact Hinterval|]; split; [exact Hlookup|]; split; [exact Hcurrent|].
  split; [exact Hgen|]; split; [exact Hread|reflexivity].
Qed.
