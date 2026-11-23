Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.lib.kernel_program_storage.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Coq.Lists.List Coq.Strings.String Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Import ListNotations UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Source-facing ABI facts, not a restriction on owner readiness or identity.
    The selected native source has the three extension switches disabled. *)
Definition mutex_del_parent_layout (sg : StableGlobVars) : Prop :=
  selected_kernel_profile sg /\ event_table_layout_prop sg /\
  &("OSIntNesting") = sg.(g_OSIntNesting) /\
  &("OSEventFreeList") = sg.(g_OSEventFreeList) /\
  &("OSTCBPrioTbl") = sg.(g_OSTCBPrioTbl) /\
  &("OSRdyTbl") = sg.(g_OSRdyTbl) /\ &("OSRdyGrp") = sg.(g_OSRdyGrp) /\
  &("OSTCBCur") = sg.(g_OSTCBCur) /\ &("OSPrioCur") = sg.(g_OSPrioCur) /\
  &("OSUnMapTbl") = sg.(g_OSUnMapTbl) /\
  (forall base, tcb_field_address base TCBStkPtr = base).

(** The final conjunct is the pinned os_tcb declaration's first pointer
    field at offset zero (Source/ucos_ii.h:560-561).  It is an ILP32 C-layout
    interpretation, checked against the original headers, not pointer <> 1.
    Non-sentinel pointers are still derived from owned typed storage. *)

(** No acquired owner-use, current-task, ready, scheduler-safety or Save
    return conclusion is assumed here. Those obligations must remain visible
    at their producer cuts. Public free ECBs retain the source type-error path. *)
Definition mutex_del_parent_input (sg : StableGlobVars) (pe : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed).

Definition mutex_del_parent_save_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved.

Definition mutex_del_parent_save_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State) : Assertion :=
  mutex_query_closed platform critical sg invocation origin mask before.

Definition mutex_del_parent_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z)
  (before entry checkpoint : UCOS2_Verify_State) : Assertion :=
  coq_prop (mutex_del_parent_save_facts critical sg invocation mask saved before entry) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   UCOS2_inv sg checkpoint).

Definition mutex_del_parent_entry (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) (event : OSEventAbstractState) (mutex : MutexFields) : Prop :=
  UCOS2_state_inv sg entry /\ mutex_query_lookup entry eid event /\
  event.(eventType) = OS_EVENT_TYPE_MUTEX /\ event.(mutexFields) = Some mutex /\
  mutex_owner_event_unlinked entry.(TskState) entry.(EventState).

(** Whole masked shared owner at Restore. The legacy dynamic-only C callee
    declaration cannot by itself return this program owner; the caller's
    post-call resource cut remains an explicit unresolved target. *)
Definition mutex_del_parent_program_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z)
  (before entry checkpoint : UCOS2_Verify_State) : Assertion :=
  coq_prop (mutex_del_parent_save_facts critical sg invocation mask saved before entry) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   kernel_program_inv sg checkpoint).

(** The protected type-error edge may be holding a creator's private
    ECB. That resource must be handed to the actual Restore source; it is
    neither discarded nor privately framed across an arbitrary client. *)
Definition mutex_del_parent_recheck_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (pointer eid : Z) : Assertion :=
  coq_prop (mutex_del_parent_save_facts critical sg invocation mask saved before entry) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
    mutex_del_recheck_whole sg pointer eid entry).

(** The observed public-slot index is retained in the physical read residual
    so QCP can instantiate the same acquired object after the type branch. *)
Definition mutex_del_parent_recheck_frame (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (eid : EventID) (acquired : OSEventAbstractState) : Assertion :=
  coq_prop (sem_query_public_slot entry eid acquired) &&
  (sem_query_type_frame sg entry eid ** unmap_table_rep sg).

(** Four mutable/read core ECB fields; the residual retains every other
    byte, the free-list root and all unrelated module resources. *)
Definition mutex_del_parent_event_rest (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (event : OSEventAbstractState) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventGrpField
      (remove EventField_eq_dec EventCntField
        (remove EventField_eq_dec EventPtrField
          (remove EventField_eq_dec EventTypeField (event_fields sg.(osKernelConfig).(cfgEventNames))))))
    (event_image sg state.(TskState) event) ** mutex_del_event_frame sg state eid.

Definition mutex_del_parent_event_values (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (event : OSEventAbstractState)
  (kind pointer count group free : Z) : Prop :=
  kind = encode_event_type event.(eventType) /\ pointer = encode_event_ptr_value sg event /\
  count = encode_event_cnt_value event /\
  group = encode_event_wait_grp event.(waitList) state.(TskState) /\
  free = event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)).

Definition mutex_del_parent_prepared (sg : StableGlobVars) (eid : EventID)
  (entry state : UCOS2_Verify_State) (event : OSEventAbstractState) (mutex : MutexFields) : Assertion :=
  coq_prop (mutex_del_parent_entry sg eid entry event mutex /\
    mutex_del_prepare sg mutex entry state) && mutex_del_wake_rep sg eid mutex state.

Definition mutex_del_parent_recycle_rest (sg : StableGlobVars) (eid : EventID)
  (entry state : UCOS2_Verify_State) (event : OSEventAbstractState) (mutex : MutexFields)
  : Assertion :=
  coq_prop (mutex_del_parent_entry sg eid entry event mutex /\
    mutex_del_prepare sg mutex entry state) &&
  mutex_del_parent_event_rest sg state eid event.

(** Exact resource packages of the independently checked helper Require.
    Packaging lets the C frontend infer proof-only With arguments from a
    spatial atom; it changes neither the helper's domain nor its effects. *)
Definition mutex_del_scan_pre (pointer : Z) (image : TCBCommonImage)
  (table : list Z) (fallback : Z) : Assertion :=
  coq_prop (0 <= fallback /\ fallback < 256 /\ Zlength table = 64 /\
    mutex_priority_fallback image fallback) &&
  (tcb64_storage_rep pointer image ** PtrArray.full &("OSTCBPrioTbl") 64 table).

Definition mutex_del_rdy_pre (pointer priority : Z) (image : TCBCommonImage)
  (table rows : list Z) (old_prio old_x old_y old_bitx old_bity group current current_prio : Z)
  : Assertion :=
  coq_prop (0 <= priority /\ priority < 64 /\ 0 <= old_y /\ old_y < 8 /\
    Zlength table = 64 /\ Zlength rows = 8 /\
    mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity) &&
  (tcb64_storage_rep pointer image ** PtrArray.full &("OSTCBPrioTbl") 64 table **
   UCharArray.full &("OSRdyTbl") 8 rows ** &("OSRdyGrp") # UChar |-> group **
   &("OSTCBCur") # Ptr |-> current ** &("OSPrioCur") # UChar |-> current_prio).

Definition mutex_del_parent_critical_observation (sg : StableGlobVars) (eid : EventID)
  (option result code request : Z) (entry checkpoint : UCOS2_Verify_State) : Prop :=
  exists error scheduled,
    mutex_del_critical sg eid option entry (result, (error, scheduled)) checkpoint /\
    code = encode_os_err_code error /\ request = if scheduled then 1 else 0.

Definition mutex_del_parent_waiting (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) : Prop :=
  exists event mutex, mutex_del_parent_entry sg eid entry event mutex /\
    encode_event_wait_grp event.(waitList) entry.(TskState) <> 0.

Definition mutex_del_parent_live (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) : Prop :=
  exists event mutex, mutex_del_parent_entry sg eid entry event mutex.

Definition mutex_del_parent_waiting_flag (entry : UCOS2_Verify_State)
  (event : OSEventAbstractState) (flag : Z) : Prop :=
  flag = if Z.eqb (encode_event_wait_grp event.(waitList) entry.(TskState)) 0 then 0 else 1.

Definition mutex_del_parent_ceiling (mutex : MutexFields) (ceiling : Z) : Prop :=
  ceiling = mutex.(mfPCP).

Definition mutex_del_parent_ceiling_at (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) (ceiling : Z) : Prop :=
  exists event mutex, mutex_del_parent_entry sg eid entry event mutex /\
    ceiling = Z.shiftr (encode_event_cnt_value event) 8.

Definition mutex_del_parent_owner_pointer (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) (ceiling pointer : Z) : Prop :=
  exists event mutex, mutex_del_parent_entry sg eid entry event mutex /\
    mutex_del_parent_ceiling mutex ceiling /\ pointer = encode_event_ptr_value sg event.

Definition mutex_del_parent_recycle_values (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (event : OSEventAbstractState) (group free : Z) : Prop :=
  group = encode_event_wait_grp event.(waitList) state.(TskState) /\
  free = event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)).

Definition mutex_del_parent_loop_facts (sg : StableGlobVars) (eid : EventID)
  (entry prepared state : UCOS2_Verify_State)
  (original event : OSEventAbstractState) (mutex : MutexFields) (priorities : list Z) : Prop :=
  mutex_del_parent_entry sg eid entry original mutex /\
  mutex_del_prepare sg mutex entry prepared /\
  mutex_del_wake_prefix sg eid prepared priorities state /\
  mutex_del_wake_state_inv sg eid mutex state /\
  mutex_query_lookup state eid event.

Definition mutex_del_parent_loop_rest (sg : StableGlobVars) (eid : EventID)
  (entry prepared state : UCOS2_Verify_State)
  (original event : OSEventAbstractState) (mutex : MutexFields) (priorities : list Z) : Assertion :=
  coq_prop (mutex_del_parent_loop_facts sg eid entry prepared state original event mutex priorities) &&
  (mutex_del_event_group_frame sg state eid event ** unmap_table_rep sg).

Definition mutex_del_parent_wake_call_rest (sg : StableGlobVars) (eid : EventID)
  (entry prepared state : UCOS2_Verify_State)
  (original event : OSEventAbstractState) (mutex : MutexFields) (priorities : list Z)
  (tid : Z) (old : TaskAbstractState) : Assertion :=
  coq_prop (mutex_del_parent_loop_facts sg eid entry prepared state original event mutex priorities /\
    encode_event_wait_grp event.(waitList) state.(TskState) <> 0 /\
    event_task_rdy_entry sg state.(TskState) eid event tid old) &&
  mutex_del_wake_frame sg state eid tid.

Definition mutex_del_parent_drained (sg : StableGlobVars) (eid : EventID)
  (entry prepared state : UCOS2_Verify_State)
  (original event : OSEventAbstractState) (mutex : MutexFields) (priorities : list Z) : Assertion :=
  coq_prop (mutex_del_parent_loop_facts sg eid entry prepared state original event mutex priorities /\
    encode_event_wait_grp event.(waitList) state.(TskState) = 0) &&
  (UCOS2_raw_rep sg state ** unmap_table_rep sg).

Definition mutex_del_parent_drained_rest (sg : StableGlobVars) (eid : EventID)
  (entry prepared state : UCOS2_Verify_State)
  (original event : OSEventAbstractState) (mutex : MutexFields) (priorities : list Z) : Assertion :=
  coq_prop (mutex_del_parent_loop_facts sg eid entry prepared state original event mutex priorities /\
    encode_event_wait_grp event.(waitList) state.(TskState) = 0) &&
  (mutex_del_parent_event_rest sg state eid event ** unmap_table_rep sg).

Definition mutex_del_parent_drained_without_priority (sg : StableGlobVars) (eid : EventID)
  (entry prepared state : UCOS2_Verify_State)
  (original event : OSEventAbstractState) (mutex : MutexFields) (priorities : list Z) : Assertion :=
  coq_prop (mutex_del_parent_loop_facts sg eid entry prepared state original event mutex priorities /\
    encode_event_wait_grp event.(waitList) state.(TskState) = 0) &&
  (UCOS2_raw_rep_missing_priority_table sg state ** unmap_table_rep sg).

Definition mutex_del_parent_prefix_ok (pe : Z) (before : UCOS2_Verify_State) (eid : EventID) : Prop :=
  mutex_del_before_save_error pe (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) = None.

Definition mutex_del_parent_unscheduled_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (context : OsSchedCallContext)
  (mask option : Z) (checkpoint : UCOS2_Verify_State) : Assertion :=
  mutex_del_callsite_unscheduled_post external platform critical sg context mask checkpoint.

(** The deletion's linearization observation is indexed by the historical
    checkpoint. Its result/error, owner-priority and waiter effects are
    unchanged. The physical return owner is indexed by the ACTUAL current
    cut after Restore (and OS_Sched when requested), not that history.
    Interference may recycle an ECB or alter runnable tasks before return;
    promising the old entire physical heap was therefore not sound.
    Producers for these source views remain explicit annotation targets. *)
Definition mutex_del_parent_original_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (pe option eid result error : Z) : Assertion :=
  (coq_prop (exists code, mutex_del_before_save_error pe
      (event_slot_type_value before.(EventState) eid) before.(IntrState).(intNesting) =
      Some (result, code) /\ error = encode_os_err_code code) &&
    mutex_del_callsite_entry_closed external platform critical sg context mask before) ||
  (EX entry, EX checkpoint, EX request,
    coq_prop (mutex_del_parent_prefix_ok pe before eid /\
      critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
      mutex_del_parent_critical_observation sg eid option result error request entry checkpoint) &&
    ((coq_prop (request = 0) && mutex_del_parent_unscheduled_post external platform critical sg
        context mask option checkpoint) ||
     (coq_prop (request = 1) && mutex_del_callsite_scheduled_post external platform critical sg
        context mask checkpoint))).

(** The new protected read can reject an ECB after the old unmasked prefix
    succeeded.  This observation refers to the acquired state, not before.
    Its resource producer is separate: private allocation storage cannot be
    inferred from event_slot_type_value's logical default. *)
Definition mutex_del_parent_recheck_error (sg : StableGlobVars) (pe eid result error : Z)
  (entry checkpoint : UCOS2_Verify_State) : Prop :=
  exists observed,
    mutex_del_recheck_observation sg eid entry observed /\ observed <> 4 /\
    checkpoint = entry /\ result = pe /\ error = encode_os_err_code OS_ERR_EVENT_TYPE.

Definition mutex_del_parent_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (pe option eid result error : Z) : Assertion :=
  mutex_del_parent_original_post external platform critical sg context mask
    before pe option eid result error ||
  (EX entry,
    coq_prop (mutex_del_parent_prefix_ok pe before eid /\
      critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
      mutex_del_parent_recheck_error sg pe eid result error entry entry) &&
    mutex_del_callsite_unscheduled_post external platform critical sg context mask entry).
