Require Export Ucos2Verify.VC.code.queue.spec.q_query_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Coq.Strings.String Coq.Lists.List Coq.ZArith.ZArith.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Import UCOS2_C_Rules ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Type-cell ownership is module-independent; reuse the proved live/free
    Event splitter rather than another Queue-specific representation. *)
Definition q_query_type_frame := sem_query_type_frame.
Definition q_query_output_table := sem_query_output_table.
Definition q_query_output_table_missing_i := sem_query_output_table_missing_i.

Definition q_query_observe_error (result : Z * option QueueQuerySnapshot)
  : program (UCOS2_Verify_State -> Prop) Z := return (fst result).

Definition q_query_call_post critical sg invocation pe pd before code after : Prop :=
  exists snapshot, q_query_call_program critical sg invocation pe pd before
    (code, snapshot) after.

Definition q_query_kernel_rest (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (free : list QueueID) : Assertion :=
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  store_map_missing_i (published_queue_node_rep sg entry.(EventState))
    entry.(EventState).(inUsedEventStates) eid **
  store_free_queue_list sg free ** UCOS2_raw_rep_missing_event_queue sg entry.

Definition q_query_event_unread (sg : StableGlobVars) (eid : EventID)
  (node : OSEventAbstractState) : Assertion :=
  event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type node.(eventType))) **
  event_cell (event_addr sg eid) EventPadding1 node.(eventPadding1) **
  event_cell (event_addr sg eid) EventPadding2 node.(eventPadding2) **
  event_cell (event_addr sg eid) EventPadding3 node.(eventPadding3) **
  event_cell (event_addr sg eid) EventCntField (Some (encode_event_cnt_value node)) **
  event_cell (event_addr sg eid) EventPadding19 node.(eventPadding19) **
  (if sg.(osKernelConfig).(cfgEventNames)
   then event_cell (event_addr sg eid) EventNameField (Some node.(eventName))
   else emp).

Definition q_query_qcb_unread (sg : StableGlobVars) (q : QueueFields) : Assertion :=
  (qcb_addr sg q.(qID) + OSQPtr_off) # Ptr |->_ **
  (qcb_addr sg q.(qID) + OSQStart_off) # Ptr |-> q.(qStart) **
  (qcb_addr sg q.(qID) + OSQEnd_off) # Ptr |-> queue_end_addr q **
  (qcb_addr sg q.(qID) + OSQIn_off) # Ptr |-> queue_in_addr q.

Definition q_query_read_facts (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (node : OSEventAbstractState) (q : QueueFields)
  (free : list QueueID) (slots : list (option addr)) (group : Z) (rows : list Z) : Prop :=
  UCOS2_state_inv sg entry /\ mutex_query_lookup entry eid node /\
  node.(eventType) = OS_EVENT_TYPE_Q /\ node.(queueFields) = Some q /\
  queue_fields_consistency sg node.(waitList) q /\
  queue_published_storage_binding entry.(EventState) /\
  queue_pool_partition sg entry.(EventState) free /\
  entry.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
  group = encode_event_wait_grp node.(waitList) entry.(TskState) /\
  rows = encode_event_wait_tbl_values_or node entry.(TskState).

Definition q_query_copy_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed node : OSEventAbstractState) (q : QueueFields)
  (free : list QueueID) (slots : list (option addr)) (group : Z) (rows : list Z) : Assertion :=
  coq_prop (q_query_acquire_facts critical sg invocation eid mask saved before entry observed node /\
    q_query_read_facts sg entry eid node q free slots group rows) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   q_query_event_unread sg eid node ** q_query_kernel_rest sg entry eid free).

Definition q_query_head_slot (q : QueueFields) (slots : list (option addr)) : Assertion :=
  coq_prop (0 < queue_entries q /\ queue_slots_model q slots) &&
  PtrArray.mixed_missing_i q.(qStart) q.(qOutIndex) 0 q.(qSize) slots.

Definition q_query_queue_valid (sg : StableGlobVars) (q : QueueFields) : Prop :=
  exists waiters, queue_fields_consistency sg waiters q.

Definition q_query_queue_at (sg : StableGlobVars) (base : addr) (q : QueueFields) : Prop :=
  base = qcb_addr sg q.(qID).

Definition q_query_queue_layout (sg : StableGlobVars) (q : QueueFields) : Prop :=
  let base := qcb_addr sg q.(qID) in
  (&(base # "os_q" ->ₛ "OSQOut")) = base + OSQOut_off /\
  (&(base # "os_q" ->ₛ "OSQSize")) = base + OSQSize_off /\
  (&(base # "os_q" ->ₛ "OSQEntries")) = base + OSQEntries_off.

(** ABI fact quantified over valid QCB IDs, not over a stale queue snapshot.
    After Save the current queue is selected from this stable layout. *)
Definition q_query_queue_layouts (sg : StableGlobVars) : Prop :=
  forall q, valid_queue_id sg q.(qID) -> q_query_queue_layout sg q.

Definition q_query_read_message (q : QueueFields) (slots : list (option addr))
  (message : addr) : Prop :=
  if Z.ltb 0 (queue_entries q) then Znth q.(qOutIndex) slots None = Some message
  else message = 0.

Definition q_query_layout (sg : StableGlobVars) (eid : EventID) : Prop :=
  let base := event_addr sg eid in
  event_core_fields_layout_prop sg eid
    (&(base # "os_event" ->ₛ "OSEventType"))
    (&(base # "os_event" ->ₛ "OSEventPtr"))
    (&(base # "os_event" ->ₛ "OSEventCnt")) /\
  event_wait_fields_layout_prop sg eid
    (&(base # "os_event" ->ₛ "OSEventGrp"))
    (&(base # "os_event" ->ₛ "OSEventTbl")) /\ q_query_queue_layouts sg.
