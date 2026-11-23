Require Export Ucos2Verify.VC.code.queue.spec.q_accept_call_spec.
Require Import Coq.Strings.String Coq.Lists.List Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

Definition q_accept_success := OS_ERR_NONE.
Definition q_accept_empty := OS_ERR_Q_EMPTY.

Definition q_accept_call_post critical sg invocation pe before message error after : Prop :=
  q_accept_call_program critical sg invocation pe before (message, error) after.

Definition q_accept_queue_layout (sg : StableGlobVars) (qid : QueueID) : Prop :=
  let base := qcb_addr sg qid in
  (&(base # "os_q" ->ₛ "OSQPtr")) = base + OSQPtr_off /\
  (&(base # "os_q" ->ₛ "OSQStart")) = base + OSQStart_off /\
  (&(base # "os_q" ->ₛ "OSQEnd")) = base + OSQEnd_off /\
  (&(base # "os_q" ->ₛ "OSQIn")) = base + OSQIn_off /\
  (&(base # "os_q" ->ₛ "OSQOut")) = base + OSQOut_off /\
  (&(base # "os_q" ->ₛ "OSQSize")) = base + OSQSize_off /\
  (&(base # "os_q" ->ₛ "OSQEntries")) = base + OSQEntries_off.

Definition q_accept_event_layout (sg : StableGlobVars) (eid : EventID) : Prop :=
  let base := event_addr sg eid in
  (&(base # "os_event" ->ₛ "OSEventType")) = base + OSEventType_off /\
  (&(base # "os_event" ->ₛ "OSEventPtr")) = base + OSEventPtr_off.

Definition q_accept_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgSafetyCritical) = false /\
  (forall eid, valid_event_id sg eid -> q_accept_event_layout sg eid) /\
  (forall qid, valid_queue_id sg qid -> q_accept_queue_layout sg qid).

Definition q_accept_type_frame := sem_query_type_frame.

Definition q_accept_pointer_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg entry.(TskState) current) EventPtrField **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry.

Definition q_accept_pointer_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed current : OSEventAbstractState) (q : QueueFields) : Assertion :=
  coq_prop (q_accept_acquire_facts critical sg invocation eid mask saved before entry observed current /\
    q_accept_profile sg /\ valid_event_id sg eid /\ current.(queueFields) = Some q) &&
  (critical_region_masked platform critical sg invocation origin saved entry ** q_accept_pointer_frame sg entry eid current).

Definition q_accept_store_facts (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) (q : QueueFields)
  (free : list QueueID) (slots : list (option addr)) (base : addr) : Prop :=
  q_accept_profile sg /\ valid_event_id sg eid /\ base = qcb_addr sg q.(qID) /\
  current.(queueFields) = Some q /\ queue_fields_consistency sg current.(waitList) q /\
  queue_published_storage_binding entry.(EventState) /\ queue_pool_partition sg entry.(EventState) free /\
  entry.(EventState).(publishedQueueBytes) q.(qID) = Some slots.

Definition q_accept_store_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed current : OSEventAbstractState) (q : QueueFields)
  (free : list QueueID) (slots : list (option addr)) (base : addr) : Assertion :=
  coq_prop (q_accept_acquire_facts critical sg invocation eid mask saved before entry observed current /\
    q_accept_store_facts sg entry eid current q free slots base) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   q_query_queue_frame sg entry eid free).

Definition q_accept_qcb_readonly (base : addr) (q : QueueFields) : Assertion :=
  (&(base # "os_q" ->ₛ "OSQPtr")) # Ptr |->_ **
  (&(base # "os_q" ->ₛ "OSQIn")) # Ptr |-> queue_in_addr q **
  (&(base # "os_q" ->ₛ "OSQSize")) # UShort |-> q.(qSize).

Definition q_accept_qcb_cells (base : addr) (q : QueueFields) (out count : Z) : Assertion :=
  (&(base # "os_q" ->ₛ "OSQOut")) # Ptr |-> out **
  (&(base # "os_q" ->ₛ "OSQEntries")) # UShort |-> count **
  (&(base # "os_q" ->ₛ "OSQEnd")) # Ptr |-> queue_end_addr q **
  (&(base # "os_q" ->ₛ "OSQStart")) # Ptr |-> q.(qStart) **
  q_accept_qcb_readonly base q.

Definition q_accept_head_slot (q : QueueFields) (slots : list (option addr)) : Assertion :=
  coq_prop (0 < queue_entries q /\ queue_slots_model q slots) &&
  PtrArray.mixed_missing_i q.(qStart) q.(qOutIndex) 0 q.(qSize) slots.

Definition q_accept_next_out (q : QueueFields) : addr :=
  if Z.eqb (queue_out_addr q + Ucos2Verify.lib.event.sizeof_ptr) (queue_end_addr q)
  then q.(qStart) else queue_out_addr q + Ucos2Verify.lib.event.sizeof_ptr.

Definition q_accept_dequeue_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (eid : EventID) (observed current : OSEventAbstractState) (q next : QueueFields)
  (free : list QueueID) (slots : list (option addr)) (base message : addr) : Assertion :=
  coq_prop (queue_dequeue_front q = Some (message, next) /\
    Znth q.(qOutIndex) slots None = Some message) &&
  q_accept_store_context platform critical sg invocation origin mask saved before entry eid observed current q free slots base.

Definition q_accept_after (entry : UCOS2_Verify_State) (eid : EventID)
  (current : OSEventAbstractState) (next : QueueFields) (slots : list (option addr)) : UCOS2_Verify_State :=
  replace_EventS (queue_update entry.(EventState) eid current next slots) entry.
